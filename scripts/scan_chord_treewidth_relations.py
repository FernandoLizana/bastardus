#!/usr/bin/env python3
"""Scan tw(I(D)), tw(L(D)), tw(G) relations on small k-chord diagrams.

Outputs:
  experiments/chord_treewidth_relation.csv
  reports/CHORD_TREEWIDTH_RELATION_SCAN.md

Does NOT emit Lean axioms.
"""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle  # noqa: E402
from treewidth import compute_treewidth  # noqa: E402

CSV_OUT = ROOT / "experiments" / "chord_treewidth_relation.csv"
MD_OUT = ROOT / "reports" / "CHORD_TREEWIDTH_RELATION_SCAN.md"


@dataclass(frozen=True)
class Diagram2:
    n: int
    p0: int
    p1: int
    p2: int
    p3: int
    pairing: str

    def chord1(self) -> tuple[int, int]:
        if self.pairing == "crossing":
            return (self.p0, self.p2)
        if self.pairing == "nested":
            return (self.p0, self.p3)
        return (self.p0, self.p1)

    def chord2(self) -> tuple[int, int]:
        if self.pairing == "crossing":
            return (self.p1, self.p3)
        if self.pairing == "nested":
            return (self.p1, self.p2)
        return (self.p2, self.p3)


def underlying_graph(d: Diagram2) -> nx.Graph:
    g = nx.cycle_graph(d.n)
    c1, c2 = d.chord1(), d.chord2()
    g.add_edge(*c1)
    g.add_edge(*c2)
    return g


def line_graph(g: nx.Graph) -> nx.Graph:
    return nx.line_graph(g)


def intersection_graph(d: Diagram2) -> nx.Graph:
    c1 = d.chord1()
    c2 = d.chord2()
    cross = chords_cross_on_cycle(d.n, c1, c2)
    ig = nx.Graph()
    ig.add_node(0)
    ig.add_node(1)
    if cross:
        ig.add_edge(0, 1)
    return ig


def iter_diagrams(n_lo: int, n_hi: int):
    for n in range(n_lo, n_hi + 1):
        for p0, p1, p2, p3 in combinations(range(n), 4):
            if not (p0 < p1 < p2 < p3):
                continue
            for pairing in ("crossing", "nested", "disjoint"):
                yield Diagram2(n, p0, p1, p2, p3, pairing)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-lo", type=int, default=5)
    ap.add_argument("--n-hi", type=int, default=10)
    ap.add_argument("--exact-max-nodes", type=int, default=14)
    args = ap.parse_args()

    CSV_OUT.parent.mkdir(parents=True, exist_ok=True)

    rows: list[dict] = []
    counterexamples: list[dict] = []

    for d in iter_diagrams(args.n_lo, args.n_hi):
        ug = underlying_graph(d)
        lg = line_graph(ug)
        ig = intersection_graph(d)
        tw_u, mu = compute_treewidth(ug, exact_max_nodes=args.exact_max_nodes, memory_safe=True)
        tw_l, ml = compute_treewidth(lg, exact_max_nodes=args.exact_max_nodes, memory_safe=True)
        tw_i, mi = compute_treewidth(ig, exact_max_nodes=args.exact_max_nodes, memory_safe=True)
        row = {
            "n": d.n,
            "p0": d.p0,
            "p1": d.p1,
            "p2": d.p2,
            "p3": d.p3,
            "pairing": d.pairing,
            "tw_underlying": tw_u,
            "tw_line": tw_l,
            "tw_intersection": tw_i,
            "method_underlying": mu,
            "method_line": ml,
            "method_intersection": mi,
        }
        rows.append(row)
        if d.pairing == "crossing" and tw_l != 4:
            counterexamples.append({**row, "expected": "tw_line=4"})
        if d.pairing != "crossing" and tw_l != 3:
            counterexamples.append({**row, "expected": "tw_line=3"})

    with CSV_OUT.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else [])
        if rows:
            w.writeheader()
            w.writerows(rows)

    with MD_OUT.open("w", encoding="utf-8") as f:
        f.write("# Chord treewidth relation scan\n\n")
        f.write(f"Range n={args.n_lo}..{args.n_hi}, diagrams={len(rows)}\n\n")
        f.write(f"CSV: `{CSV_OUT.relative_to(ROOT)}`\n\n")
        f.write("## Counterexamples to two-chord tw(L(G)) pattern\n\n")
        if not counterexamples:
            f.write("None in scanned range.\n")
        else:
            for c in counterexamples[:20]:
                f.write(f"- n={c['n']} {c['pairing']} tw_line={c['tw_line']} ({c['expected']})\n")
            if len(counterexamples) > 20:
                f.write(f"\n... and {len(counterexamples) - 20} more\n")
        f.write("\n## Relation samples (first 10)\n\n")
        f.write("| n | pairing | tw(G) | tw(L) | tw(I) |\n")
        f.write("|---|---------|-------|-------|-------|\n")
        for r in rows[:10]:
            f.write(
                f"| {r['n']} | {r['pairing']} | {r['tw_underlying']} | "
                f"{r['tw_line']} | {r['tw_intersection']} |\n"
            )
        f.write("\n**Nota:** datos experimentales; no teoremas Lean.\n")

    print(f"Wrote {len(rows)} rows to {CSV_OUT}")
    print(f"Counterexamples: {len(counterexamples)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
