"""Selective outerplanar Closure_Δ mass for n=11 (span-2 ears only, Δ≤3).

Full C_11+2 noncrossing is huge; this samples noncrossing span-2 ear pairs.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.bicyclic_full_closure_mass import (
    full_width_closure,
    lean_sound_closed,
)
from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.outerplanar_pathfold_certs import is_outerplanar
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf

OUT = Path("reports/discovery/outerplanar_full_closure_mass_n11.json")


def main() -> int:
    n = 11
    ok = fail = 0
    rows: list[dict] = []
    ears = sorted({tuple(sorted((i, (i + 2) % n))) for i in range(n)})
    for c1, c2 in combinations(ears, 2):
        if len(set(c1) | set(c2)) < 4:
            continue
        if chords_cross_on_cycle(n, c1, c2):
            continue
        g = nx.cycle_graph(n)
        g.add_edges_from([c1, c2])
        if max(d for _, d in g.degree()) > 3:
            continue
        if not is_outerplanar(g):
            continue
        delta = max(d for _, d in g.degree())
        form = tseitin_cnf(
            GraphInstance(
                g, tuple(1 if i == 0 else 0 for i in range(n)), "O11", 0, {}
            )
        )
        cl = full_width_closure(form, delta)
        has_empty = () in cl
        closed_ok = lean_sound_closed(cl, delta) if len(cl) <= 400 else None
        row = {
            "n": n,
            "chords": [list(c1), list(c2)],
            "delta": delta,
            "closure_size": len(cl),
            "has_empty": has_empty,
            "lean_sound_closed": closed_ok,
            "ok": has_empty,
        }
        rows.append(row)
        if row["ok"]:
            ok += 1
        else:
            fail += 1
        if (ok + fail) % 10 == 0:
            print(f"n11 progress {ok + fail}", flush=True)
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "rows": rows,
        "family": "C_11 + 2 noncrossing span-2 ears, Delta<=3, unit",
        "claim": (
            "Selective n=11 outerplanar noncrossing ear pairs: full Closure_Δ ∋ □."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
