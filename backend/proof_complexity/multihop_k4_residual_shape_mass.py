"""E2: final multihop residual always has K₄ shape — 6 edge vars, Closure₃ size 16.

Feeds Lean `ResidualK4Shape` / `K4ResidualID` (G3 identification up to rename).
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.multihop_projection_mass import chord_pairs
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm
from backend.models.cnf import CNFFormula

OUT = Path("reports/discovery/multihop_k4_residual_shape_mass.json")


def _xor_axioms(work, charges, e_index) -> list[tuple[int, ...]]:
    axs: list[tuple[int, ...]] = []
    for v in work.nodes():
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return axs


def _edge_vars(work, e_index) -> list[int]:
    return sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )


def check_shape(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
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
    tips = 0
    for arc in arcs:
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            tips += 1
    axioms = _xor_axioms(work, charges, e_index)
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    closed = _width_closure_clauses(form, 3)
    vars_ = _edge_vars(work, e_index)
    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "tips": tips,
        "n_nodes": work.number_of_nodes(),
        "n_edges": work.number_of_edges(),
        "n_vars": len(vars_),
        "vars": vars_,
        "axiom_size": len(axioms),
        "closed_size": len(closed),
        "has_empty": () in closed,
        "ok": (
            work.number_of_nodes() == 4
            and work.number_of_edges() == 6
            and len(vars_) == 6
            and len(closed) == 16
            and () not in closed
            and len(axioms) == 16
        ),
    }


def main() -> int:
    ok = fail = 0
    by_n: dict[str, dict] = {}
    samples: list[dict] = []
    for n in range(5, 11):
        n_ok = n_fail = 0
        for c1, c2 in chord_pairs(n):
            cert = check_shape(n, c1, c2)
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
        "by_n": by_n,
        "fail_samples": samples,
        "claim": (
            "Every crossing n=5..10 after multihop fold: residual is K₄ "
            "(4 nodes, 6 edges/vars), Closure₃ size 16 without □ "
            "(ResidualK4Shape / K4ResidualID)."
        ),
        "lean": "lean/PNPLab/K4ResidualID.lean",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} ok={ok} fail={fail}")
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
