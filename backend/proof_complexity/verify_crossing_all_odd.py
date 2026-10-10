"""All-odd crossing-law verifier — GPU-first, low host RAM.

Design:
  - No ProcessPool (that was cloning axioms into RAM across workers)
  - Stream charges in small GPU chunks (default 32)
  - OpenCL returns 1=□ found (eq), 0=saturated no □ (gt), 2=incomplete
  - Host only holds one mini-batch of bit-axioms at a time

Usage:
  python -u -m backend.proof_complexity.verify_crossing_all_odd \\
    --n-lo 9 --n-hi 9 --max-charges 64 \\
    --out reports/discovery/crossing_law_all_odd_n9.json --gpu-chunk 32
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.gpu_width_opencl import (
    batch_width_status_gpu,
    clause_to_bits,
    reset_cl_runtime,
)
from backend.proof_complexity.tseitin_family import xor_cnf

OUT = Path("reports/discovery/crossing_law_all_odd.json")


def odd_charges(n: int, max_masks: int | None = None) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    for mask in range(1, 1 << n):
        bits = tuple((mask >> i) & 1 for i in range(n))
        if sum(bits) % 2 == 0:
            continue
        out.append(bits)
        if max_masks is not None and len(out) >= max_masks:
            break
    return out


def _edge_index(g: nx.Graph) -> dict[tuple[int, int], int]:
    edges = sorted(tuple(sorted(e)) for e in g.edges())
    return {e: i + 1 for i, e in enumerate(edges)}


def _incident_vars(g: nx.Graph, e_index: dict[tuple[int, int], int]) -> list[list[int]]:
    n = g.number_of_nodes()
    out: list[list[int]] = [[] for _ in range(n)]
    for v in range(n):
        out[v] = [e_index[tuple(sorted((v, u)))] for u in g.neighbors(v)]
    return out


def bit_axioms_fast(
    incident: list[list[int]], charges: tuple[int, ...]
) -> list[tuple[int, int]]:
    axs: list[tuple[int, int]] = []
    for v, lits in enumerate(incident):
        for cl in xor_cnf(lits, charges[v] % 2):
            b = clause_to_bits(cl)
            if b is None:
                raise ValueError("cannot bit-encode clause")
            axs.append(b)
    return axs


def status_to_label(code: int) -> str:
    if code == 1:
        return "eq"
    if code == 0:
        return "gt"
    return "inconclusive"


def run(
    n_lo: int,
    n_hi: int,
    max_charges: int | None,
    out: Path | None = None,
    gpu_chunk: int = 16,
    max_c: int = 4096,
    max_c_cap: int = 16384,
) -> dict:
    out_path = out or OUT
    reset_cl_runtime()
    t0 = time.perf_counter()
    checked = 0
    mismatches: list[dict] = []
    inconclusive: list[dict] = []
    by_n: dict[str, dict] = {}

    for n in range(n_lo, n_hi + 1):
        cap = max_charges
        if cap is None and n >= 9:
            cap = 64
        charges_list = odd_charges(n, cap)
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        eq = gt = inc = bad = 0
        graphs = 0
        t_n = time.perf_counter()

        for chords in combinations(non, 2):
            g = base.copy()
            g.add_edges_from(chords)
            if g.number_of_edges() != n + 2:
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            if len({*chords[0], *chords[1]}) < 4:
                continue
            graphs += 1
            cross = chords_cross_on_cycle(n, chords[0], chords[1])
            pred = "gt" if cross else "eq"
            incident = _incident_vars(g, _edge_index(g))

            for start in range(0, len(charges_list), gpu_chunk):
                batch_ch = charges_list[start : start + gpu_chunk]
                bits_list = [bit_axioms_fast(incident, ch) for ch in batch_ch]
                deltas = [delta] * len(bits_list)
                codes = list(
                    batch_width_status_gpu(
                        bits_list,
                        deltas,
                        max_c=max_c,
                        chunk=len(bits_list),
                    )
                )
                # Escalate GPU clause budget before expensive CPU fallback.
                if any(status_to_label(c) == "inconclusive" for c in codes):
                    for esc in sorted({min(max_c * 2, max_c_cap), max_c_cap}):
                        if esc <= max_c:
                            continue
                        need_idx = [
                            i
                            for i, c in enumerate(codes)
                            if status_to_label(c) == "inconclusive"
                        ]
                        if not need_idx:
                            break
                        sub = list(
                            batch_width_status_gpu(
                                [bits_list[i] for i in need_idx],
                                [delta] * len(need_idx),
                                max_c=esc,
                                chunk=min(len(need_idx), 8),
                            )
                        )
                        for j, i in enumerate(need_idx):
                            codes[i] = sub[j]
                # Parallel CPU fallback for remaining GPU-inconclusive.
                if any(status_to_label(c) == "inconclusive" for c in codes):
                    from concurrent.futures import ThreadPoolExecutor

                    from backend.proof_complexity.chord_law_search import _bitsat_complete

                    need = [
                        (i, bits_list[i])
                        for i, c in enumerate(codes)
                        if status_to_label(c) == "inconclusive"
                    ]

                    def _resolve(item: tuple[int, list]) -> tuple[int, int]:
                        i, bits = item
                        ok, complete = _bitsat_complete(
                            bits, delta, max_c=max(50_000, max_c_cap)
                        )
                        if ok:
                            return i, 1
                        if complete:
                            return i, 0
                        return i, 2

                    workers = min(4, max(1, len(need)))
                    with ThreadPoolExecutor(max_workers=workers) as pool:
                        for i, code in pool.map(_resolve, need):
                            codes[i] = code
                del bits_list

                for charges, code in zip(batch_ch, codes):
                    lab = status_to_label(code)
                    checked += 1
                    meta = {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "charges": list(charges),
                        "delta": delta,
                        "pred": pred,
                        "crossing": cross,
                        "gpu_code": code,
                    }
                    if lab == "inconclusive":
                        inc += 1
                        if len(inconclusive) < 20:
                            inconclusive.append({**meta, "label": lab})
                        continue
                    if lab == "eq":
                        eq += 1
                    else:
                        gt += 1
                    if lab != pred:
                        bad += 1
                        if len(mismatches) < 50:
                            mismatches.append({**meta, "label": lab})

            if graphs % 10 == 0 or graphs == 1:
                print(
                    f"  n={n} graph {graphs} "
                    f"eq={eq} gt={gt} inc={inc} bad={bad} "
                    f"elapsed={time.perf_counter()-t_n:.1f}s",
                    flush=True,
                )

        by_n[str(n)] = {
            "graphs": graphs,
            "charges_per_graph": len(charges_list),
            "checked": graphs * len(charges_list),
            "eq": eq,
            "gt": gt,
            "inconclusive": inc,
            "mismatches": bad,
            "gpu_chunk": gpu_chunk,
            "max_c": max_c,
            "max_c_cap": max_c_cap,
            "elapsed_s": round(time.perf_counter() - t_n, 2),
        }
        print(f"n={n} {by_n[str(n)]}", flush=True)

    report = {
        "family": "C_n+2 chords, Delta<=3, all (or capped) odd charges",
        "checked": checked,
        "by_n": by_n,
        "mismatches": mismatches,
        "inconclusive": inconclusive,
        "law_holds": len(mismatches) == 0
        and all(v["inconclusive"] == 0 for v in by_n.values()),
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "engine": "gpu_width_status_streamed_adaptive",
        "max_c": max_c,
        "max_c_cap": max_c_cap,
        "statement": (
            "crossing ⇒ Width>Δ and non-crossing ⇒ Width=Δ "
            "for odd charges in the enumerated range"
        ),
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "law_holds": report["law_holds"],
                "checked": checked,
                "mismatches": len(mismatches),
                "inconclusive": len(inconclusive),
                "elapsed_s": report["elapsed_s"],
            },
            indent=2,
        ),
        flush=True,
    )
    print(f"wrote {out_path}", flush=True)
    return report


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--n-lo", type=int, default=5)
    p.add_argument("--n-hi", type=int, default=8)
    p.add_argument("--max-charges", type=int, default=None)
    p.add_argument("--out", type=str, default=None)
    p.add_argument("--gpu-chunk", type=int, default=16)
    p.add_argument("--max-c", type=int, default=4096, help="GPU clause buffer size")
    p.add_argument(
        "--max-c-cap",
        type=int,
        default=16384,
        help="Escalate inconclusive batches up to this max_c",
    )
    args = p.parse_args()
    out = Path(args.out) if args.out else None
    report = run(
        args.n_lo,
        args.n_hi,
        args.max_charges,
        out,
        args.gpu_chunk,
        args.max_c,
        args.max_c_cap,
    )
    return 0 if report["law_holds"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
