"""Mass noncrossing pathfold certificates for C_n+2 chords, n≤10."""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import prove_noncrossing_pathfold_lemma

OUT = Path("reports/discovery/noncrossing_pathfold_n10.json")


def main() -> int:
    ok = fail = 0
    errs: list[dict] = []
    for n in range(5, 10):  # include n=9; abort early reporting if fail
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        for ch in combinations(non, 2):
            if len({*ch[0], *ch[1]}) < 4:
                continue
            g = base.copy()
            g.add_edges_from(ch)
            if max(d for _, d in g.degree()) > 3:
                continue
            if chords_cross_on_cycle(n, ch[0], ch[1]):
                continue
            try:
                prove_noncrossing_pathfold_lemma(
                    g, {i: int(i == 0) for i in range(n)}
                )
                ok += 1
            except Exception as e:  # noqa: BLE001
                fail += 1
                if len(errs) < 8:
                    errs.append(
                        {
                            "n": n,
                            "chords": [list(c) for c in ch],
                            "err": str(e),
                        }
                    )
    report = {"ok": ok, "fail": fail, "errs": errs, "n_range": [5, 9]}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"wrote {OUT}")
    return 0 if fail == 0 and ok > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
