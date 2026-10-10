"""Incremental γ/Δ map: add n=8 k≤2 onto existing report (faster than full rebuild)."""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.gamma_delta_width_map import classify, gamma

BASE = Path("reports/discovery/gamma_delta_width_map.json")
OUT = Path("reports/discovery/gamma_delta_width_map_n8.json")


def main() -> int:
    base = json.loads(BASE.read_text(encoding="utf-8")) if BASE.exists() else {}
    buckets: Counter[tuple[int, int, str]] = Counter()
    for gam, dmap in (base.get("by_gamma_delta") or {}).items():
        for d, labs in dmap.items():
            for lab, v in labs.items():
                buckets[(int(gam), int(d), lab)] += int(v)

    examples_gt = list(base.get("examples_gt") or [])
    added = 0
    n = 8
    base_g = nx.cycle_graph(n)
    non = [
        (u, v)
        for u in range(n)
        for v in range(u + 1, n)
        if not base_g.has_edge(u, v)
    ]
    for k in range(0, 3):
        for ch in combinations(non, k):
            g = base_g.copy()
            g.add_edges_from(ch)
            if not nx.is_connected(g):
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            lab = classify(g, tuple(1 if i == 0 else 0 for i in range(n)), delta)
            buckets[(gamma(g), delta, lab)] += 1
            added += 1
            if lab == "gt" and len(examples_gt) < 40:
                examples_gt.append(
                    {
                        "n": n,
                        "gamma": gamma(g),
                        "delta": delta,
                        "chords": [list(c) for c in ch],
                    }
                )
            if added % 50 == 0:
                print(f"n8 progress {added}", flush=True)

    by: dict = {}
    for (gam, d, lab), v in sorted(buckets.items()):
        by.setdefault(str(gam), {}).setdefault(str(d), {})[lab] = v
    report = {
        "family": "merged base + n=8 k<=2 Delta<=3 unit",
        "by_gamma_delta": by,
        "examples_gt": examples_gt,
        "n8_added": added,
        "total": sum(buckets.values()),
        "summary": (
            "gamma<=2 => Width=Delta; gamma>=3 Delta=3 mix =/>; "
            f"n=8 k<=2 added {added} samples."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    BASE.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} and {BASE} total={report['total']} n8_added={added}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
