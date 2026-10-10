"""Mass certificates for prove_outerplanar_pathfold_lemma."""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import prove_outerplanar_pathfold_lemma

OUT = Path("reports/discovery/outerplanar_pathfold_certificates.json")


def is_outerplanar(g: nx.Graph) -> bool:
    h = g.copy()
    apex = "__apex__"
    h.add_node(apex)
    for v in list(g.nodes()):
        h.add_edge(apex, v)
    return nx.check_planarity(h)[0]


def main() -> int:
    ok = 0
    fail = 0
    errs: list[dict] = []

    # triangle chains
    for t in range(1, 6):
        nodes = 2 * t + 1
        g = nx.Graph()
        g.add_nodes_from(range(nodes))
        for i in range(t):
            a, b, c = 2 * i, 2 * i + 1, 2 * i + 2
            g.add_edges_from([(a, b), (b, c), (c, a)])
        if max(d for _, d in g.degree()) > 3:
            continue
        try:
            prove_outerplanar_pathfold_lemma(g, {i: int(i == 0) for i in range(nodes)})
            ok += 1
        except Exception as e:  # noqa: BLE001
            fail += 1
            if len(errs) < 8:
                errs.append({"family": "tri_chain", "t": t, "err": str(e)})

    # C_n + noncrossing ears
    for n in range(5, 11):
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
                if max(d for _, d in g.degree()) > 3:
                    continue
                if not is_outerplanar(g):
                    continue
                try:
                    prove_outerplanar_pathfold_lemma(
                        g, {i: int(i == 0) for i in range(n)}
                    )
                    ok += 1
                except Exception as e:  # noqa: BLE001
                    fail += 1
                    if len(errs) < 8:
                        errs.append(
                            {
                                "family": "ears",
                                "n": n,
                                "k": k,
                                "chords": [list(c) for c in chords],
                                "err": str(e),
                            }
                        )

    report = {"ok": ok, "fail": fail, "errs": errs}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"wrote {OUT}")
    return 0 if fail == 0 and ok > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
