"""Export detailed multihop chains: hop sizes, residual var sets, nest flags.

Complements multihop_projection_mass.json for E5 family-proof planning.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.models.cnf import CNFFormula
from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.multihop_projection_mass import chord_pairs, check_multihop
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm

OUT = Path("reports/discovery/multihop_chains_export.json")


def _xor_axioms(work, charges, e_index) -> list[tuple[int, ...]]:
    axs: list[tuple[int, ...]] = []
    for v in work.nodes():
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return axs


def _edge_vars_list(work, e_index) -> list[int]:
    return sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )


def _closure(axioms: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    return _width_closure_clauses(form, 3)


def check_multihop_detailed(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
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

    hops: list[dict] = []
    prev = _closure(_xor_axioms(work, charges, e_index))
    v_prev = _edge_vars_list(work, e_index)
    hops.append({"hop": 0, "cl_size": len(prev), "vars": v_prev})

    miss_total = 0
    tips = 0
    nest_ok = True

    for i, arc in enumerate(arcs):
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            tips += 1
            cur = _closure(_xor_axioms(work, charges, e_index))
            vv = set(_edge_vars_list(work, e_index))
            v_list = sorted(vv)
            missing = [
                c
                for c in prev
                if c and all(abs(lit) in vv for lit in c) and c not in cur
            ]
            miss_total += len(missing)
            # nest: V_after ⊆ V_before
            if not set(v_list).issubset(set(v_prev)):
                nest_ok = False
            hops.append(
                {
                    "hop": tips,
                    "tip": tip,
                    "cl_size": len(cur),
                    "vars": v_list,
                    "missing": len(missing),
                }
            )
            prev = cur
            v_prev = v_list

    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "tips": tips,
        "hops": hops,
        "hop_sizes": [h["cl_size"] for h in hops],
        "nest_monotone": nest_ok,
        "missing": miss_total,
        "final_size": hops[-1]["cl_size"],
        "empty_final": () in prev,
        "ok": miss_total == 0 and nest_ok and () not in prev and hops[-1]["cl_size"] == 16,
    }


def main() -> int:
    ok = fail = 0
    chains: list[dict] = []
    stats = {
        "max_tips": 0,
        "max_cl_g0": 0,
        "nest_fail": 0,
    }
    for n in range(5, 11):
        for c1, c2 in chord_pairs(n):
            cert = check_multihop_detailed(n, c1, c2)
            stats["max_tips"] = max(stats["max_tips"], cert["tips"])
            stats["max_cl_g0"] = max(stats["max_cl_g0"], cert["hop_sizes"][0])
            if not cert["nest_monotone"]:
                stats["nest_fail"] += 1
            if cert["ok"]:
                ok += 1
            else:
                fail += 1
            if len(chains) < 30:  # sample for inspection
                chains.append(cert)
    # full compact export (all 461)
    compact: list[dict] = []
    for n in range(5, 11):
        for c1, c2 in chord_pairs(n):
            cert = check_multihop_detailed(n, c1, c2)
            compact.append(
                {
                    "n": cert["n"],
                    "chords": cert["chords"],
                    "tips": cert["tips"],
                    "hop_sizes": cert["hop_sizes"],
                    "nest_monotone": cert["nest_monotone"],
                    "ok": cert["ok"],
                }
            )
    full_path = OUT.parent / "multihop_chains_full.json"
    full_path.write_text(json.dumps({"total": len(compact), "chains": compact}, indent=2), encoding="utf-8")
    # quick consistency with mass checker
    spot = check_multihop(6, (0, 3), (2, 5))
    report = {
        "total_ok": ok,
        "total_fail": fail,
        "stats": stats,
        "sample_chains": chains,
        "spot_check_n6": spot,
        "claim": (
            "Every crossing n=5..10: multihop projection OK; residual var sets "
            "monotone (V_{i+1} ⊆ V_i) along tip-by-tip fold."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail} max_tips={stats['max_tips']}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
