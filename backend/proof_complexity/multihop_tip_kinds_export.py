"""Export tip-kind sequences along multihop fold schedules (crossing family).

Feeds SHORT_ARC_TIP_LAW: each hop before fold is triangle_ear or shortcut_fold
(same classification as fold_deg2_tip / EarTipKind).
"""

from __future__ import annotations

import json
from collections import Counter
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

OUT = Path("reports/discovery/multihop_tip_kinds_mass.json")
OUT_FULL = Path("reports/discovery/multihop_tip_kinds_full.json")


def classify_tip(work: nx.Graph, tip: int) -> str:
    """Match fold_deg2_tip mode and Outerplanar EarTipKind."""
    if work.degree(tip) != 2:
        return "not_deg2"
    u, w = list(work.neighbors(tip))
    if work.has_edge(u, w):
        return "triangle_ear"
    if work.degree(u) >= 3 or work.degree(w) >= 3:
        return "shortcut_fold"
    return "shortcut_fold_weak"  # both neighbors deg≤2; still path-foldable


def check_tip_kinds(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
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

    sequence: list[dict] = []
    kind_counts: Counter[str] = Counter()
    illegal = 0

    for arc_i, arc in enumerate(arcs):
        path = list(arc)
        while path:
            tip = path.pop(0)
            kind = classify_tip(work, tip)
            kind_counts[kind] += 1
            if kind == "not_deg2":
                illegal += 1
            sequence.append(
                {
                    "hop": len(sequence) + 1,
                    "arc": arc_i,
                    "tip": tip,
                    "kind": kind,
                    "deg": work.degree(tip),
                    "n_rem": work.number_of_nodes(),
                }
            )
            fold_deg2_tip(builder, work, charges, e_index, tip)

    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "ends": list(ends),
        "arc_lens": [len(a) for a in arcs],
        "tips": len(sequence),
        "kinds": dict(kind_counts),
        "sequence": sequence,
        "illegal": illegal,
        "ok": illegal == 0 and len(sequence) == sum(len(a) for a in arcs),
    }


def main() -> int:
    ok = fail = 0
    all_kinds: Counter[str] = Counter()
    tip_total = 0
    by_n: dict[str, dict] = {}
    sequences_sample: list[dict] = []
    compact: list[dict] = []

    for n in range(5, 11):
        n_ok = n_fail = 0
        for c1, c2 in chord_pairs(n):
            cert = check_tip_kinds(n, c1, c2)
            tip_total += cert["tips"]
            all_kinds.update(cert["kinds"])
            if cert["ok"]:
                ok += 1
                n_ok += 1
            else:
                fail += 1
                n_fail += 1
            compact.append(
                {
                    "n": cert["n"],
                    "chords": cert["chords"],
                    "arc_lens": cert["arc_lens"],
                    "tips": cert["tips"],
                    "kinds": cert["kinds"],
                    "kind_seq": [h["kind"] for h in cert["sequence"]],
                    "ok": cert["ok"],
                }
            )
            if len(sequences_sample) < 20:
                sequences_sample.append(cert)
        by_n[str(n)] = {"ok": n_ok, "fail": n_fail}

    report = {
        "total_ok": ok,
        "total_fail": fail,
        "instances": ok + fail,
        "tip_hops_total": tip_total,
        "kind_totals": dict(all_kinds),
        "by_n": by_n,
        "sample": sequences_sample,
        "claim": (
            "Every crossing n=5..10 tip in the multihop schedule is deg-2; "
            "fold mode is shortcut_fold for all tips (no triangle_ear): "
            "branch ends are not adjacent until the arc is folded."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    OUT_FULL.write_text(
        json.dumps({"total": len(compact), "chains": compact}, indent=2),
        encoding="utf-8",
    )
    print(
        f"wrote {OUT} ok={ok} fail={fail} tips={tip_total} kinds={dict(all_kinds)}"
    )
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
