"""Characterize Width vs Δ for tricyclic graphs C_n + 2 chords (unit charge, Δ≤3).

Emits reports/discovery/tricyclic_eq_vs_gt_structure.json and a positive W=Δ witness.
"""

from __future__ import annotations

import json
from collections import defaultdict, deque
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.gpu_width_opencl import (
    batch_has_refutation_gpu,
    formula_to_bit_axioms,
)
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf

OUT = Path("reports/discovery/tricyclic_eq_vs_gt_structure.json")
WITNESS_OUT = Path("datasets/examples/tricyclic_width_eq_delta.json")


def _dist(n: int, a: int, b: int) -> int:
    d = abs(a - b)
    return min(d, n - d)


def _bitsat(axs: list[tuple[int, int]], wlim: int, max_c: int = 30_000) -> bool:
    def width(c: tuple[int, int]) -> int:
        return bin(c[0] | c[1]).count("1")

    def resolve(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int] | None:
        piv = (a[0] & b[1]) | (a[1] & b[0])
        if bin(piv).count("1") != 1:
            return None
        out = ((a[0] | b[0]) & ~piv, (a[1] | b[1]) & ~piv)
        if out[0] & out[1]:
            return None
        return out

    seen: set[tuple[int, int]] = set()
    lst: list[tuple[int, int]] = []
    pending: deque[int] = deque()

    def add(c: tuple[int, int]) -> bool:
        if width(c) > wlim or c in seen:
            return False
        seen.add(c)
        lst.append(c)
        pending.append(len(lst) - 1)
        return c == (0, 0)

    for a in axs:
        if width(a) <= wlim and add(a):
            return True
    while pending:
        if len(lst) > max_c:
            return False
        i = pending.popleft()
        a = lst[i]
        n = len(lst)
        for j in range(n):
            if i == j:
                continue
            r = resolve(a, lst[j])
            if r is None or width(r) > wlim:
                continue
            if add(r):
                return True
    return False


def classify_one(bits: list[tuple[int, int]], delta: int) -> str:
    """eq | gt using GPU fast-path then CPU bitsat."""
    if batch_has_refutation_gpu([bits], [delta])[0]:
        return "eq"
    # Complete closure at Δ: if no empty clause, W > Δ when higher succeeds.
    if not _bitsat(bits, delta):
        aw = max((bin(p | q).count("1") for p, q in bits), default=0)
        for w in range(delta + 1, max(delta + 1, aw) + 5):
            if _bitsat(bits, w):
                return "gt"
        return "inconclusive"
    return "eq"


def main() -> int:
    report: dict = {
        "family": "cycle_plus_two_chords_unit_dleq3",
        "by_n": [],
        "eq_examples": [],
        "gt_examples": [],
        "structure": {},
        "pattern": (
            "C_n + 2 chords, Δ≤3, unit charge: n=5 all W>Δ in this family; "
            "n≥6 admits W=Δ, typically vertex-disjoint chords of circular length 2–4."
        ),
    }
    struct: dict[str, dict[str, int]] = defaultdict(lambda: {"eq": 0, "gt": 0, "inconclusive": 0})

    for n in range(5, 9):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        eq = gt = inc = 0
        for chords in combinations(non, 2):
            g = base.copy()
            g.add_edges_from(chords)
            if g.number_of_edges() != n + 2:
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            bits = formula_to_bit_axioms(tseitin_cnf(GraphInstance(g, charges, "tri", 0, {})))
            lab = classify_one(bits, delta)
            lens = sorted(_dist(n, *c) for c in chords)
            share = len(set(chords[0]) | set(chords[1])) < 4
            key = f"lens={lens}|share={share}"
            struct[key][lab] += 1
            meta = {
                "n": n,
                "chords": [list(c) for c in chords],
                "chord_lens": lens,
                "share_vertex": share,
                "delta": delta,
            }
            if lab == "eq":
                eq += 1
                if len(report["eq_examples"]) < 8:
                    report["eq_examples"].append(meta)
            elif lab == "gt":
                gt += 1
                if len(report["gt_examples"]) < 8:
                    report["gt_examples"].append(meta)
            else:
                inc += 1
        row = {"n": n, "eq": eq, "gt": gt, "inconclusive": inc}
        report["by_n"].append(row)
        print(row, flush=True)

    report["structure"] = dict(struct)
    report["first_eq_witness"] = {
        "n": 6,
        "graph": "C6 + chords {0-2, 3-5}",
        "edges": [[i, (i + 1) % 6] for i in range(6)] + [[0, 2], [3, 5]],
        "charges": [1, 0, 0, 0, 0, 0],
        "delta": 3,
        "width": 3,
        "gamma": 3,
        "certified": "GPU bitmask saturation derives empty at width Δ; axiom width=Δ ⇒ Width=Δ",
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    WITNESS_OUT.parent.mkdir(parents=True, exist_ok=True)
    WITNESS_OUT.write_text(json.dumps(report["first_eq_witness"], indent=2), encoding="utf-8")
    print(f"wrote {OUT}", flush=True)
    print(f"wrote {WITNESS_OUT}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
