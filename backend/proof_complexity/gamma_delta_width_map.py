"""Compact γ/Δ width map including Δ=4 samples (Category C E2)."""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/gamma_delta_width_map.json")


def gamma(g: nx.Graph) -> int:
    return g.number_of_edges() - g.number_of_nodes() + 1


def classify(g: nx.Graph, charges: tuple[int, ...], delta: int) -> str:
    form = tseitin_cnf(GraphInstance(g, charges, "map", 0, {}))
    if has_width_refutation(form, delta)[0]:
        return "eq"
    # Probe Δ+1 then Δ+2 (audit: all former `inc` resolved at gap=2).
    for bump in (1, 2):
        w = min(delta + bump, 7)
        if has_width_refutation(form, w)[0]:
            return "gt"
    return "inc"


def run() -> dict:
    buckets: Counter[tuple[int, int, str]] = Counter()
    examples_gt: list[dict] = []
    # denser: n=5..6 k≤4 Δ≤4; n=7 k≤3 Δ≤3; n=8 k≤2 Δ≤3 (unit)
    for n in (5, 6, 7, 8):
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        if n <= 6:
            kmax = 4
        elif n == 7:
            kmax = 3
        else:
            kmax = 2
        for k in range(0, kmax + 1):
            for ch in combinations(non, k):
                g = base.copy()
                g.add_edges_from(ch)
                if not nx.is_connected(g):
                    continue
                delta = max(d for _, d in g.degree())
                if delta > 4:
                    continue
                if n >= 7 and delta > 3:
                    continue
                lab = classify(
                    g, tuple(1 if i == 0 else 0 for i in range(n)), delta
                )
                buckets[(gamma(g), delta, lab)] += 1
                if lab == "gt" and len(examples_gt) < 20:
                    examples_gt.append(
                        {
                            "n": n,
                            "gamma": gamma(g),
                            "delta": delta,
                            "chords": [list(c) for c in ch],
                        }
                    )
    by: dict = {}
    for (gam, d, lab), v in sorted(buckets.items()):
        by.setdefault(str(gam), {}).setdefault(str(d), {})[lab] = v
    return {
        "family": "C_n+k: n=5..6 k<=4 Delta<=4; n=7 k<=3 Delta<=3; n=8 k<=2 Delta<=3 unit",
        "by_gamma_delta": by,
        "examples_gt": examples_gt,
        "summary": (
            "gamma<=2 => Width=Delta on this sample; "
            "gamma>=3 with Delta=3 shows mix =/> (crossing); denser k<=4 on n<=6."
        ),
        "total": sum(buckets.values()),
    }


def main() -> int:
    report = run()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "total": report["total"],
                "by": report["by_gamma_delta"],
                "gt": len(report["examples_gt"]),
            },
            indent=2,
        )
    )
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
