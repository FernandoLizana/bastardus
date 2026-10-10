"""OpenCL batch Width vs Δ checks on the discrete NVIDIA GPU.

Resolution width saturation for small Tseitin instances (≤32 vars) as bitmasks,
one work-item per instance. Classification runs two GPU kernels (at Δ and Δ+1).

Scratch lives in global memory (MAX_C=1536) so tricyclics that need ~900 clauses fit.

Example:
  python -m backend.proof_complexity.gpu_width_opencl --demo
  python -m backend.proof_complexity.gpu_width_opencl --classify --limit 2000
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, product
from pathlib import Path

import networkx as nx
import numpy as np

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf

MAX_C = 1536
HASH_N = 4096

def _kernel_src(max_c: int, hash_n: int) -> str:
    return rf"""
#define MAX_C {max_c}
#define HASH_N {hash_n}u
#define EMPTY_POS 0xffffffffu

typedef struct {{ uint pos; uint neg; }} Clause;
typedef struct {{ uint n_clauses; uint width_limit; uint pad0; uint pad1; }} Header;

uint width_of(Clause c) {{ return popcount(c.pos | c.neg); }}

Clause resolve(Clause a, Clause b) {{
    uint piv = (a.pos & b.neg) | (a.neg & b.pos);
    Clause bad; bad.pos = 0xffffffff; bad.neg = 0xffffffff;
    if (popcount(piv) != 1u) return bad;
    Clause out;
    out.pos = (a.pos | b.pos) & ~piv;
    out.neg = (a.neg | b.neg) & ~piv;
    if ((out.pos & out.neg) != 0u) return bad;
    return out;
}}

uint clause_hash(Clause c) {{
    uint x = c.pos * 0x9e3779b9u ^ c.neg * 0x85ebca6bu;
    x ^= x >> 16;
    return x & (HASH_N - 1u);
}}

int hash_insert(__global uint* hpos, __global uint* hneg, Clause c) {{
    uint i = clause_hash(c);
    for (uint probe = 0; probe < HASH_N; probe++) {{
        uint slot = (i + probe) & (HASH_N - 1u);
        if (hpos[slot] == EMPTY_POS) {{
            hpos[slot] = c.pos;
            hneg[slot] = c.neg;
            return 1;
        }}
        if (hpos[slot] == c.pos && hneg[slot] == c.neg) return 0;
    }}
    return -1;
}}

__kernel void width_sat(
    __global const Header* headers,
    __global const Clause* axioms_in,
    __global Clause* scratch,
    __global uint* hash_pos,
    __global uint* hash_neg,
    __global uint* results
) {{
    uint id = get_global_id(0);
    Header h = headers[id];
    uint n_ax = h.n_clauses;
    if (n_ax == 0 || n_ax > MAX_C) {{ results[id] = 0; return; }}

    __global Clause* buf = scratch + id * MAX_C;
    __global uint* hpos = hash_pos + id * HASH_N;
    __global uint* hneg = hash_neg + id * HASH_N;
    for (uint i = 0; i < HASH_N; i++) hpos[i] = EMPTY_POS;

    uint n = 0;
    uint abase = id * MAX_C;
    for (uint i = 0; i < n_ax; i++) {{
        Clause c = axioms_in[abase + i];
        if (width_of(c) > h.width_limit) continue;
        if (hash_insert(hpos, hneg, c) != 1) continue;
        buf[n++] = c;
        if (c.pos == 0 && c.neg == 0) {{ results[id] = 1; return; }}
    }}
    if (n == 0) {{ results[id] = 0; return; }}

    uint head = 0;
    ulong work = 0;
    /* Bound resolve work: enough for normal saturation, not open-ended hang. */
    ulong work_cap = ((ulong)MAX_C * (ulong)MAX_C) / 2ul;
    while (head < n) {{
        Clause a = buf[head++];
        uint cur_n = n;
        for (uint j = 0; j < cur_n; j++) {{
            if (++work > work_cap) {{ results[id] = 2; return; }}
            Clause r = resolve(a, buf[j]);
            if (r.pos == 0xffffffff) continue;
            if (width_of(r) > h.width_limit) continue;
            int ins = hash_insert(hpos, hneg, r);
            if (ins == 0) continue;
            if (ins < 0 || n >= MAX_C) {{ results[id] = 2; return; }}
            buf[n++] = r;
            if (r.pos == 0 && r.neg == 0) {{ results[id] = 1; return; }}
        }}
    }}
    results[id] = 0;
}}
"""


# Back-compat name used by older callers / docs
KERNEL = _kernel_src(MAX_C, HASH_N)


def clause_to_bits(lits: list[int]) -> tuple[int, int] | None:
    pos = neg = 0
    for lit in lits:
        v = abs(lit)
        if v == 0 or v > 32:
            return None
        bit = 1 << (v - 1)
        if lit > 0:
            pos |= bit
        else:
            neg |= bit
    if pos & neg:
        return None
    return pos, neg


def formula_to_bit_axioms(formula) -> list[tuple[int, int]]:
    out = []
    for cl in formula.clauses:
        b = clause_to_bits(list(cl.literals))
        if b is None:
            raise ValueError("cannot bit-encode clause")
        out.append(b)
    return out


def pick_nvidia_device():
    import pyopencl as cl

    for plat in cl.get_platforms():
        for dev in plat.get_devices():
            name = (dev.name or "").lower()
            if "nvidia" in name or "geforce" in name or "rtx" in name:
                return plat, dev
    for plat in cl.get_platforms():
        gpus = plat.get_devices(device_type=cl.device_type.GPU)
        if gpus:
            return plat, gpus[0]
    raise RuntimeError("No OpenCL GPU found")


_CL_CACHE: dict[tuple[int, int], dict] = {}


def reset_cl_runtime() -> None:
    """Drop cached OpenCL programs."""
    global _CL_CACHE
    _CL_CACHE = {}


def _cl_runtime(max_c: int = MAX_C, hash_n: int = HASH_N):
    import pyopencl as cl

    key = (max_c, hash_n)
    if key not in _CL_CACHE:
        _, dev = pick_nvidia_device()
        ctx = cl.Context([dev])
        queue = cl.CommandQueue(ctx)
        prg = cl.Program(ctx, _kernel_src(max_c, hash_n)).build()
        kernel = cl.Kernel(prg, "width_sat")
        _CL_CACHE[key] = {
            "cl": cl,
            "ctx": ctx,
            "queue": queue,
            "kernel": kernel,
            "dev": dev,
            "max_c": max_c,
            "hash_n": hash_n,
        }
    return _CL_CACHE[key]


def batch_has_refutation_gpu(
    axiom_lists: list[list[tuple[int, int]]],
    widths: list[int],
    max_c: int = MAX_C,
    chunk: int = 64,
) -> list[bool]:
    """True iff Closure_w contains □ (Width ≤ w). Incomplete runs count as False."""
    codes = batch_width_status_gpu(axiom_lists, widths, max_c=max_c, chunk=chunk)
    return [c == 1 for c in codes]


def batch_width_status_gpu(
    axiom_lists: list[list[tuple[int, int]]],
    widths: list[int],
    max_c: int = MAX_C,
    chunk: int = 32,
    hash_n: int | None = None,
) -> list[int]:
    """GPU width saturation status per instance.

    Returns:
      1 = found □ (Width ≤ w)
      0 = saturated, no □ (Width > w)
      2 = incomplete (hit MAX_C / hash full)
    """
    if not axiom_lists:
        return []
    if hash_n is None:
        hash_n = max(HASH_N, max_c * 2)
    # Keep VRAM bounded: scratch+hash ≈ chunk*(max_c*8 + hash_n*8)
    # For max_c=4096, hash_n=8192, chunk=16 ≈ 2 MB/instance → ~32 MB
    max_chunk = 64 if max_c <= 1536 else 16
    chunk = max(1, min(chunk, max_chunk))
    rt = _cl_runtime(max_c=max_c, hash_n=hash_n)
    cl = rt["cl"]
    ctx, queue, kernel = rt["ctx"], rt["queue"], rt["kernel"]
    mf = cl.mem_flags
    out: list[int] = []

    for start in range(0, len(axiom_lists), chunk):
        axs_chunk = axiom_lists[start : start + chunk]
        w_chunk = widths[start : start + chunk]
        n = len(axs_chunk)
        headers = np.zeros((n, 4), dtype=np.uint32)
        axioms = np.zeros((n * max_c, 2), dtype=np.uint32)
        for i, (axs, w) in enumerate(zip(axs_chunk, w_chunk)):
            take = min(len(axs), max_c)
            headers[i, 0] = take
            headers[i, 1] = int(w)
            base = i * max_c
            for j, (pos, neg) in enumerate(axs[:take]):
                axioms[base + j, 0] = pos
                axioms[base + j, 1] = neg
        results = np.zeros(n, dtype=np.uint32)
        h_buf = cl.Buffer(ctx, mf.READ_ONLY | mf.COPY_HOST_PTR, hostbuf=headers)
        a_buf = cl.Buffer(ctx, mf.READ_ONLY | mf.COPY_HOST_PTR, hostbuf=axioms)
        s_buf = cl.Buffer(ctx, mf.READ_WRITE, n * max_c * 8)
        hp_buf = cl.Buffer(ctx, mf.READ_WRITE, n * hash_n * 4)
        hn_buf = cl.Buffer(ctx, mf.READ_WRITE, n * hash_n * 4)
        r_buf = cl.Buffer(ctx, mf.WRITE_ONLY, results.nbytes)
        kernel(queue, (n,), None, h_buf, a_buf, s_buf, hp_buf, hn_buf, r_buf)
        cl.enqueue_copy(queue, results, r_buf)
        queue.finish()
        out.extend(int(x) for x in results)
        del headers, axioms, h_buf, a_buf, s_buf, hp_buf, hn_buf, r_buf
    return out


def classify_width_vs_delta_gpu(
    axiom_lists: list[list[tuple[int, int]]], deltas: list[int]
) -> list[str]:
    """Return per-instance label: eq | gt | inconclusive (all on GPU)."""
    at_d = batch_has_refutation_gpu(axiom_lists, deltas)
    need = [i for i, ok in enumerate(at_d) if not ok]
    labels = ["eq" if ok else "pending" for ok in at_d]
    if need:
        sub_ax = [axiom_lists[i] for i in need]
        sub_w = [deltas[i] + 1 for i in need]
        at_dp1 = batch_has_refutation_gpu(sub_ax, sub_w)
        for i, ok in zip(need, at_dp1):
            labels[i] = "gt" if ok else "inconclusive"
    return labels


def _jobs_from_tree_chords(
    n: int, n_chords: int, limit: int, label: str
) -> tuple[list[list[tuple[int, int]]], list[int], list[dict]]:
    jobs: list[list[tuple[int, int]]] = []
    deltas: list[int] = []
    meta: list[dict] = []
    if n <= 2:
        return jobs, deltas, meta
    for code in product(range(n), repeat=n - 2):
        tree = nx.from_prufer_sequence(list(code))
        if max(d for _, d in tree.degree()) > 3:
            continue
        edges = {tuple(sorted(e)) for e in tree.edges()}
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if (u, v) not in edges]
        for chords in combinations(non, n_chords):
            g = tree.copy()
            g.add_edges_from(chords)
            expected_e = (n - 1) + n_chords
            if g.number_of_edges() != expected_e:
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            inst = GraphInstance(g, charges, label, 0, {})
            bits = formula_to_bit_axioms(tseitin_cnf(inst))
            jobs.append(bits)
            deltas.append(delta)
            meta.append(
                {
                    "family": label,
                    "n": n,
                    "delta": delta,
                    "gamma": expected_e - n + 1,
                    "edges": [list(e) for e in g.edges()],
                }
            )
            if len(jobs) >= limit:
                return jobs, deltas, meta
    return jobs, deltas, meta


def classify_gamma_on_gpu(
    *, bic_limit: int = 1000, tri_limit: int = 720
) -> dict:
    jobs: list[list[tuple[int, int]]] = []
    deltas: list[int] = []
    meta: list[dict] = []

    for n, lim in ((5, bic_limit // 2), (6, bic_limit - bic_limit // 2)):
        j, d, m = _jobs_from_tree_chords(n, 2, lim, "bicyclic")
        jobs.extend(j)
        deltas.extend(d)
        meta.extend(m)

    j, d, m = _jobs_from_tree_chords(5, 3, tri_limit, "tricyclic")
    jobs.extend(j)
    deltas.extend(d)
    meta.extend(m)

    t0 = time.perf_counter()
    try:
        labels = classify_width_vs_delta_gpu(jobs, deltas)
        backend = "opencl_nvidia"
        device = _cl_runtime()["dev"].name
    except Exception as exc:  # noqa: BLE001
        return {
            "backend": f"opencl_failed:{exc}",
            "checked": 0,
            "hint": "pip install pyopencl; ensure NVIDIA OpenCL runtime is present",
        }

    summary: dict[str, dict[str, int]] = {}
    first_gt = None
    for lab, m in zip(labels, meta):
        fam = m["family"]
        bucket = summary.setdefault(fam, {"eq": 0, "gt": 0, "inconclusive": 0})
        bucket[lab] += 1
        if lab == "gt" and first_gt is None:
            first_gt = {**m, "label": lab}

    elapsed_ms = int((time.perf_counter() - t0) * 1000)
    return {
        "backend": backend,
        "device": device,
        "checked": len(jobs),
        "by_family": summary,
        "first_gt": first_gt,
        "elapsed_ms": elapsed_ms,
        "cpu_refine": False,
        "method": "gpu_bfs_sat_delta_and_delta_plus_1",
        "max_c": MAX_C,
    }


def demo_tricyclic_on_gpu(limit: int = 200) -> dict:
    jobs, deltas, meta = _jobs_from_tree_chords(5, 3, limit, "tricyclic")
    t0 = time.perf_counter()
    try:
        labels = classify_width_vs_delta_gpu(jobs, deltas)
        backend = "opencl_nvidia"
        device = _cl_runtime()["dev"].name
    except Exception as exc:  # noqa: BLE001
        return {
            "backend": f"opencl_failed:{exc}",
            "checked": 0,
            "hint": "pip install pyopencl; ensure NVIDIA OpenCL runtime is present",
        }
    eq = sum(1 for x in labels if x == "eq")
    gt = sum(1 for x in labels if x == "gt")
    inc = sum(1 for x in labels if x == "inconclusive")
    first_gt = next((m for lab, m in zip(labels, meta) if lab == "gt"), None)
    return {
        "backend": backend,
        "device": device,
        "checked": len(jobs),
        "width_eq_delta": eq,
        "width_gt_delta": gt,
        "inconclusive": inc,
        "first_gt": first_gt,
        "elapsed_ms": int((time.perf_counter() - t0) * 1000),
        "cpu_refine": False,
        "max_c": MAX_C,
    }


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--demo", action="store_true")
    p.add_argument("--classify", action="store_true")
    p.add_argument("--limit", type=int, default=200)
    p.add_argument("--bic-limit", type=int, default=1000)
    p.add_argument("--tri-limit", type=int, default=720)
    args = p.parse_args()
    try:
        import pyopencl  # noqa: F401
    except ImportError:
        print("Installing pyopencl is required for GPU: pip install pyopencl")
        return 2

    out_dir = Path("reports/discovery")
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.classify:
        report = classify_gamma_on_gpu(bic_limit=args.bic_limit, tri_limit=args.tri_limit)
        out = out_dir / "gpu_width_opencl_classify.json"
        out.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(json.dumps(report, indent=2))
        print(f"wrote {out}")
        return 0 if not str(report.get("backend", "")).startswith("opencl_failed") else 1
    if args.demo:
        report = demo_tricyclic_on_gpu(args.limit)
        out = out_dir / "gpu_width_opencl_demo.json"
        out.write_text(json.dumps(report, indent=2), encoding="utf-8")
        print(json.dumps(report, indent=2))
        print(f"wrote {out}")
        return 0 if not str(report.get("backend", "")).startswith("opencl_failed") else 1
    p.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
