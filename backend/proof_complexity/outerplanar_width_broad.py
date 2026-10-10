"""Broader outerplanar Δ≤3 Width=Δ hunt: series of fans + nested ears + mop-strips."""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/outerplanar_width_eq_delta_broad.json")


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


def nested_ears(n: int, depth: int) -> nx.Graph | None:
    """Cycle + nested length-2 chords from a common apex path."""
    if depth < 1 or 2 * depth + 2 > n:
        return None
    g = nx.cycle_graph(n)
    # nested: (0,2), (0,4), ... limited by Δ≤3 → apex 0 can take at most 1 extra
    # so use a path of nested ears with distinct apices
    for i in range(depth):
        a = 2 * i
        b = 2 * i + 2
        if b >= n:
            return None
        g.add_edge(a, b)
    if max(d for _, d in g.degree()) > 3:
        return None
    return g


def run() -> dict:
    buckets: Counter[str] = Counter()
    op_gt: list[dict] = []
    checked = 0

    # 1) C_n + any noncrossing set of ≤4 length-2 ears, Δ≤3
    for n in range(6, 12):
        base = nx.cycle_graph(n)
        ears = sorted({tuple(sorted((i, (i + 2) % n))) for i in range(n)})
        for k in range(0, 5):
            for chords in combinations(ears, k):
                if any(
                    len({*a, *b}) == 4 and chords_cross_on_cycle(n, a, b)
                    for a, b in combinations(chords, 2)
                ):
                    continue
                g = base.copy()
                g.add_edges_from(chords)
                delta = max(d for _, d in g.degree())
                if delta > 3 or not is_outerplanar(g):
                    continue
                charges = tuple(1 if i == 0 else 0 for i in range(n))
                lab = classify(g, charges, delta)
                buckets[f"ears_k{k}_{lab}"] += 1
                checked += 1
                if lab == "gt" and len(op_gt) < 15:
                    op_gt.append(
                        {
                            "family": "ears",
                            "n": n,
                            "k": k,
                            "chords": [list(c) for c in chords],
                            "delta": delta,
                        }
                    )

    # 2) Nested chains
    for n in range(8, 13):
        for depth in range(1, 5):
            g = nested_ears(n, depth)
            if g is None or not is_outerplanar(g):
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            lab = classify(g, charges, delta)
            buckets[f"nested_d{depth}_{lab}"] += 1
            checked += 1
            if lab == "gt" and len(op_gt) < 15:
                op_gt.append(
                    {
                        "family": "nested",
                        "n": n,
                        "depth": depth,
                        "delta": delta,
                        "edges": [list(e) for e in g.edges()],
                    }
                )

    # 3) Path + pending outerplanar attachments (cactus of triangles)
    for t in range(1, 5):
        # chain of t triangles sharing vertices: 0-1-2-0, 2-3-4-2, ...
        nodes = 2 * t + 1
        g = nx.Graph()
        g.add_nodes_from(range(nodes))
        for i in range(t):
            a, b, c = 2 * i, 2 * i + 1, 2 * i + 2
            g.add_edges_from([(a, b), (b, c), (c, a)])
        if max(d for _, d in g.degree()) > 3:
            continue
        if not is_outerplanar(g):
            continue
        charges = tuple(1 if i == 0 else 0 for i in range(nodes))
        delta = max(d for _, d in g.degree())
        lab = classify(g, charges, delta)
        buckets[f"triangle_chain_t{t}_{lab}"] += 1
        checked += 1
        if lab == "gt" and len(op_gt) < 15:
            op_gt.append({"family": "triangle_chain", "t": t, "delta": delta})

    return {
        "checked": checked,
        "counts": dict(buckets),
        "outerplanar_gt_delta": op_gt,
        "conjecture": "C-OUTERPLANAR-WIDTH-EQ-DELTA",
        "status": "supported" if not op_gt else "refuted_by_examples",
    }


def main() -> int:
    report = run()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "checked": report["checked"],
                "status": report["status"],
                "op_gt": len(report["outerplanar_gt_delta"]),
                "counts": report["counts"],
            },
            indent=2,
        )
    )
    print(f"wrote {OUT}")
    return 0 if report["status"] == "supported" else 1


if __name__ == "__main__":
    raise SystemExit(main())
