"""Hunt: outerplanar Δ≤3 odd-charge Tseitin ⇒ Width=Δ?

Uses CPU width saturation only (avoids OpenCL hangs). Enumerates tree + k≤2
chords with Prufer stride for larger n.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, product
from pathlib import Path

import networkx as nx

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/outerplanar_width_eq_delta.json")


def is_outerplanar(g: nx.Graph) -> bool:
    h = g.copy()
    apex = "__apex__"
    h.add_node(apex)
    for v in list(g.nodes()):
        h.add_edge(apex, v)
    return nx.check_planarity(h)[0]


def classify(g: nx.Graph, charges: tuple[int, ...], delta: int) -> str:
    form = tseitin_cnf(GraphInstance(g, charges, "op", 0, {}))
    ok_d, _, _ = has_width_refutation(form, delta)
    if ok_d:
        return "eq"
    ok_up, _, size = has_width_refutation(form, delta + 1)
    if ok_up:
        return "gt"
    if size >= 200_000:
        return "inc"
    return "gt"  # closed without empty at Δ, empty at Δ+1 failed but rare


def run(
    n_lo: int = 3,
    n_hi: int = 6,
    *,
    prufer_stride: int = 1,
) -> dict:
    buckets: Counter[tuple[str, str]] = Counter()
    counterexamples_op_gt: list[dict] = []
    examples_nonop_eq: list[dict] = []

    for n in range(n_lo, n_hi + 1):
        stride = prufer_stride if n <= 5 else max(prufer_stride, 2)
        for k in (0, 1, 2):
            codes = [()] if n <= 2 else product(range(n), repeat=n - 2)
            for ti, code in enumerate(codes):
                if n > 2 and stride > 1 and (ti % stride):
                    continue
                tree = nx.path_graph(n) if n <= 2 else nx.from_prufer_sequence(list(code))
                if max((d for _, d in tree.degree()), default=0) > 3:
                    continue
                edges = {tuple(sorted(e)) for e in tree.edges()}
                non = [
                    (u, v)
                    for u in range(n)
                    for v in range(u + 1, n)
                    if (u, v) not in edges
                ]
                for chords in combinations(non, k):
                    g = tree.copy()
                    g.add_edges_from(chords)
                    if not nx.is_connected(g):
                        continue
                    delta = max(d for _, d in g.degree())
                    if delta > 3:
                        continue
                    op = is_outerplanar(g)
                    charges = tuple(1 if i == 0 else 0 for i in range(n))
                    lab = classify(g, charges, delta)
                    buckets[("op" if op else "nonop", lab)] += 1
                    if op and lab == "gt" and len(counterexamples_op_gt) < 20:
                        counterexamples_op_gt.append(
                            {
                                "n": n,
                                "k": k,
                                "delta": delta,
                                "edges": [list(e) for e in g.edges()],
                            }
                        )
                    if (not op) and lab == "eq" and len(examples_nonop_eq) < 10:
                        examples_nonop_eq.append(
                            {
                                "n": n,
                                "k": k,
                                "delta": delta,
                                "edges": [list(e) for e in g.edges()],
                            }
                        )

    report = {
        "family": f"tree+k chords, k<=2, n={n_lo}..{n_hi}, Delta<=3, unit charge, CPU",
        "prufer_stride": prufer_stride,
        "counts": {f"{a}|{b}": v for (a, b), v in sorted(buckets.items())},
        "outerplanar_gt_delta": counterexamples_op_gt,
        "non_outerplanar_eq_delta": examples_nonop_eq,
        "conjecture_C_OUTERPLANAR_WIDTH_EQ_DELTA": (
            "For connected outerplanar G with Delta<=3 and odd charge, "
            "Width(T(G,c))=Delta(G)."
        ),
        "status": (
            "supported" if not counterexamples_op_gt else "refuted_by_examples"
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


def main() -> int:
    report = run(3, 6, prufer_stride=1)
    print(
        json.dumps(
            {
                "counts": report["counts"],
                "status": report["status"],
                "op_gt": len(report["outerplanar_gt_delta"]),
                "nonop_eq": len(report["non_outerplanar_eq_delta"]),
            },
            indent=2,
        )
    )
    print(f"wrote {OUT}")
    return 0 if report["status"] == "supported" else 1


if __name__ == "__main__":
    raise SystemExit(main())
