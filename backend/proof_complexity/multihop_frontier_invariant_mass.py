"""E2: frontier invariant on crossing open arcs during multihop fold.

For every tip in the left-to-right schedule:
  - tip deg == 2
  - left frontier neighbor has deg >= 3 (or becomes so via prior folds)
  - tip neighbors are not adjacent (shortcut, not triangle)

Matches Lean OpenArcPath.hasFrontierTip / crossingOpenArc.
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.multihop_projection_mass import chord_pairs
from backend.proof_complexity.path_fold import fold_deg2_tip

OUT = Path("reports/discovery/multihop_frontier_invariant_mass.json")


def check_frontier(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    ends, arcs = crossing_branch_sets(n, c1, c2)
    e_index = _edge_var_map(g0)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)

    hops = 0
    fails: list[dict] = []

    for arc_i, arc in enumerate(arcs):
        path = list(arc)
        # left frontier starts at branch endpoint ends[arc_i]
        left = ends[arc_i]
        while path:
            tip = path[0]
            nbrs = list(work.neighbors(tip))
            deg_tip = work.degree(tip)
            adj = work.has_edge(nbrs[0], nbrs[1]) if len(nbrs) == 2 else True
            # frontier: tip adjacent to current left endpoint
            frontier_ok = left in nbrs and work.degree(left) >= 3
            other = nbrs[0] if nbrs[1] == left else nbrs[1] if len(nbrs) == 2 else None
            ok = (
                deg_tip == 2
                and not adj
                and frontier_ok
            )
            hops += 1
            if not ok:
                fails.append(
                    {
                        "hop": hops,
                        "arc": arc_i,
                        "tip": tip,
                        "left": left,
                        "deg_tip": deg_tip,
                        "deg_left": work.degree(left) if left in work else None,
                        "adjacent_nbrs": adj,
                        "frontier_ok": frontier_ok,
                    }
                )
            fold_deg2_tip(builder, work, charges, e_index, tip, fold_into=left)
            path.pop(0)
            # after fold into left, left stays the frontier endpoint

    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "hops": hops,
        "fails": len(fails),
        "fail_sample": fails[:3],
        "ok": len(fails) == 0,
    }


def main() -> int:
    ok = fail = 0
    hop_total = 0
    by_n: dict[str, dict] = {}
    samples: list[dict] = []

    for n in range(5, 11):
        n_ok = n_fail = 0
        for c1, c2 in chord_pairs(n):
            cert = check_frontier(n, c1, c2)
            hop_total += cert["hops"]
            if cert["ok"]:
                ok += 1
                n_ok += 1
            else:
                fail += 1
                n_fail += 1
                if len(samples) < 5:
                    samples.append(cert)
        by_n[str(n)] = {"ok": n_ok, "fail": n_fail}

    report = {
        "total_ok": ok,
        "total_fail": fail,
        "tip_hops_total": hop_total,
        "by_n": by_n,
        "fail_samples": samples,
        "claim": (
            "Every multihop tip is deg-2, neighbors non-adjacent, and adjacent "
            "to a deg≥3 left frontier endpoint (OpenArcPath.hasFrontierTip)."
        ),
        "lean": "lean/PNPLab/OpenArcPath.lean",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail} hops={hop_total}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
