"""Mass: full Closure_Δ ∋ □ for noncrossing C_n+2 chords (outerplanar Δ≤3)."""

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
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf

OUT = Path("reports/discovery/outerplanar_full_closure_mass.json")


def main() -> int:
    ok = fail = 0
    rows = []
    for n in range(5, 11):
        chords = [
            c
            for c in combinations(range(n), 2)
            if (c[1] - c[0]) % n not in (1, n - 1)
        ]
        for c1, c2 in combinations(chords, 2):
            if len(set(c1) | set(c2)) < 4:
                continue
            if chords_cross_on_cycle(n, c1, c2):
                continue
            g = nx.cycle_graph(n)
            g.add_edges_from([c1, c2])
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            form = tseitin_cnf(
                GraphInstance(
                    g, tuple(1 if i == 0 else 0 for i in range(n)), "O", 0, {}
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
            if (ok + fail) % 25 == 0:
                print(f"progress {ok + fail}", flush=True)
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "rows": rows,
        "max_n": 10,
        "claim": (
            "Noncrossing C_n+2 (Δ≤3, n≤10) full Closure_Δ contains □ "
            "(outerplanar upper bound E2; large |Cl| skip Lean-sound check)."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
