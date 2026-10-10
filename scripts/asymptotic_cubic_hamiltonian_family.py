#!/usr/bin/env python3
"""Asymptotic candidate: cubic Hamiltonian cycle + chord matching family D_n.

Documents tw(line graph) growth numerically — NOT a Lean theorem.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from treewidth import compute_treewidth  # noqa: E402


def cubic_hamiltonian_chord_graph(n: int, offset: int = 0) -> nx.Graph:
    """C_n with chord (i, i + n//2) for even n (perfect matching style)."""
    g = nx.cycle_graph(n)
    half = n // 2
    for i in range(n):
        j = (i + half + offset) % n
        if i != j and not g.has_edge(i, j):
            g.add_edge(i, j)
    return g


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n-lo", type=int, default=6)
    parser.add_argument("--n-hi", type=int, default=40)
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    rows = []
    for n in range(args.n_lo, args.n_hi + 1, args.step):
        g = cubic_hamiltonian_chord_graph(n)
        lg = nx.line_graph(g)
        tw_g, mg = compute_treewidth(g, exact_max_nodes=14, memory_safe=True)
        tw_l, ml = compute_treewidth(lg, exact_max_nodes=14, memory_safe=True)
        rows.append({
            "n": n,
            "|V|": n,
            "|E|": g.number_of_edges(),
            "|V(L)|": lg.number_of_nodes(),
            "tw_G": tw_g,
            "tw_L": tw_l,
            "method_L": ml,
            "max_degree": max(dict(g.degree()).values()),
        })
    out = ROOT / "experiments" / "asymptotic_cubic_hamiltonian_tw.csv"
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print(f"Wrote {out}")
    for r in rows:
        print(r)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
