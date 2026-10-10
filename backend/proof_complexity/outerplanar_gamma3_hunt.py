"""Outerplanar Δ≤3, γ≥3 ⇒ Width=Δ? (relevant test for C-OUTERPLANAR-WIDTH-EQ-DELTA)

Enumerates C_n + 3 noncrossing chords with Δ≤3 (disjoint length-2 ears on n≥9).
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/outerplanar_width_eq_delta_gamma3.json")
OUT_MERGED = Path("reports/discovery/outerplanar_width_eq_delta.json")


def is_outerplanar(g: nx.Graph) -> bool:
    h = g.copy()
    apex = "__apex__"
    h.add_node(apex)
    for v in list(g.nodes()):
        h.add_edge(apex, v)
    return nx.check_planarity(h)[0]


def classify(g: nx.Graph, charges: tuple[int, ...], delta: int) -> str:
    form = tseitin_cnf(GraphInstance(g, charges, "op", 0, {}))
    if has_width_refutation(form, delta)[0]:
        return "eq"
    if has_width_refutation(form, delta + 1)[0]:
        return "gt"
    return "inc"


def gamma(g: nx.Graph) -> int:
    return g.number_of_edges() - g.number_of_nodes() + 1


def noncrossing_pair(n: int, a: tuple[int, int], b: tuple[int, int]) -> bool:
    if len({*a, *b}) < 4:
        return True  # share a vertex: cannot cross as proper chords
    return not chords_cross_on_cycle(n, a, b)


def run(n_lo: int = 9, n_hi: int = 12) -> dict:
    buckets: Counter[str] = Counter()
    op_gt: list[dict] = []
    op_eq: list[dict] = []
    checked = 0

    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        # all undirected length-2 chords
        ears = [tuple(sorted((i, (i + 2) % n))) for i in range(n)]
        ears = sorted(set(ears))
        for chords in combinations(ears, 3):
            # pairwise noncrossing
            ok_nc = True
            for a, b in combinations(chords, 2):
                if not noncrossing_pair(n, a, b):
                    ok_nc = False
                    break
            if not ok_nc:
                continue
            # prefer endpoint-disjoint so Δ≤3 automatically
            ends = [x for ch in chords for x in ch]
            if len(set(ends)) < 6:
                # may still be Δ≤3 if no vertex in >1 chord... already <6 means share
                pass
            g = base.copy()
            g.add_edges_from(chords)
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            if not is_outerplanar(g):
                continue
            if gamma(g) < 3:
                continue
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            lab = classify(g, charges, delta)
            buckets[lab] += 1
            checked += 1
            rec = {
                "n": n,
                "gamma": gamma(g),
                "delta": delta,
                "chords": [list(c) for c in chords],
                "lab": lab,
            }
            if lab == "gt" and len(op_gt) < 15:
                op_gt.append(rec)
            if lab == "eq" and len(op_eq) < 8:
                op_eq.append(rec)

        # also: 4 noncrossing disjoint ears when possible (γ=4), Δ≤3
        for chords in combinations(ears, 4):
            if any(
                not noncrossing_pair(n, a, b) for a, b in combinations(chords, 2)
            ):
                continue
            g = base.copy()
            g.add_edges_from(chords)
            delta = max(d for _, d in g.degree())
            if delta > 3 or not is_outerplanar(g):
                continue
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            lab = classify(g, charges, delta)
            buckets[f"g4_{lab}"] += 1
            checked += 1
            if lab == "gt" and len(op_gt) < 15:
                op_gt.append(
                    {
                        "n": n,
                        "gamma": gamma(g),
                        "delta": delta,
                        "chords": [list(c) for c in chords],
                        "lab": lab,
                    }
                )

    return {
        "family": "C_n + 3..4 noncrossing length-2 ears, Delta<=3, outerplanar, unit",
        "n_range": [n_lo, n_hi],
        "checked": checked,
        "counts": dict(buckets),
        "outerplanar_gt_delta": op_gt,
        "outerplanar_eq_examples": op_eq,
        "conjecture": "C-OUTERPLANAR-WIDTH-EQ-DELTA",
        "status": "supported" if not op_gt else "refuted_by_examples",
    }


def main() -> int:
    report = run(9, 11)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    merged = {
        "gamma_ge_3": report,
        "conjecture_C_OUTERPLANAR_WIDTH_EQ_DELTA": (
            "For connected outerplanar G with Delta<=3 and odd charge, "
            "Width(T(G,c))=Delta(G)."
        ),
        "status": report["status"],
        "note": "γ≥3 noncrossing ear family is the relevant test (Δ≤3).",
    }
    if OUT_MERGED.exists():
        try:
            prev = json.loads(OUT_MERGED.read_text(encoding="utf-8"))
            if "counts" in prev and "gamma_le_2" not in prev:
                merged["gamma_le_2_tree_plus_chords"] = prev
            else:
                merged["previous"] = {
                    k: prev[k] for k in prev if k not in ("gamma_ge_3",)
                }
        except json.JSONDecodeError:
            pass
    OUT_MERGED.write_text(json.dumps(merged, indent=2), encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("checked", "counts", "status")}, indent=2))
    print(f"wrote {OUT}")
    return 0 if report["status"] == "supported" else 1


if __name__ == "__main__":
    raise SystemExit(main())
