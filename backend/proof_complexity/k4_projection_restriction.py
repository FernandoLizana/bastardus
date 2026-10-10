"""Machine support for the projection/restriction lemma G → residual K₄.

Claim (analytic): if every width-3 resolvent of G whose variables lie in the
residual K₄ edge-set also lies in the width-3 closure of the residual K₄
Tseitin instance, then □ ∈ Closure₃(G) ⇒ □ ∈ Closure₃(K₄).

This module checks that inclusion on the crossing family after path-fold
identifies residual edge variables.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import (
    contract_charges_to_endpoints,
    crossing_branch_sets,
)
from backend.proof_complexity.k4_path_contraction_derivation import (
    _odd_charge_for_crossing,
    derive_k4_via_path_fold,
)
from backend.proof_complexity.path_fold import fold_open_arc_internals
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import has_width_refutation

OUT = Path("reports/discovery/k4_projection_restriction.json")


def _width_closure_clauses(formula, width: int) -> set[tuple[int, ...]]:
    """Return the set of clauses in a width-bounded saturation (not only empty)."""
    from collections import defaultdict
    from backend.proof_complexity.width import _norm, resolve

    clauses: set[tuple[int, ...]] = set()
    by_lit: dict[int, set[tuple[int, ...]]] = defaultdict(set)

    def add(c: tuple[int, ...]) -> None:
        if c in clauses:
            return
        clauses.add(c)
        for lit in c:
            by_lit[lit].add(c)

    for clause in formula.clauses:
        n = _norm(clause.literals)
        if n is None:
            continue
        if len(n) <= width:
            add(n)

    pending = list(clauses)
    while pending:
        if len(clauses) > 200_000:
            break
        a = pending.pop()
        partners: set[tuple[int, ...]] = set()
        for lit in a:
            partners |= by_lit.get(-lit, set())
        for b in partners:
            if a == b:
                continue
            r = resolve(a, b)
            if r is None or len(r) > width or r in clauses:
                continue
            add(r)
            pending.append(r)
            if len(r) == 0:
                return clauses
    return clauses


def residual_vars_after_fold(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> tuple[set[int], tuple[int, ...], list[int]]:
    """Fold arcs; return residual edge-var set, residual charges, ends."""
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    ends, arcs = crossing_branch_sets(n, c1, c2)
    e_index = _edge_var_map(g0)
    delta = max(d for _, d in g0.degree())
    builder = _ProofBuilder(_all_axioms(g0, charges0, e_index), delta=delta)
    work = g0.copy()
    charges = dict(charges0)
    for i, arc in enumerate(arcs):
        if not arc:
            continue
        left = ends[i]
        right = ends[(i + 1) % 4]
        fold_open_arc_internals(
            builder, work, charges, e_index, left, list(arc), right
        )
    res_vars = {
        e_index[tuple(sorted(e))]
        for e in work.edges()
        if tuple(sorted(e)) in e_index
    }
    residual_chi = tuple(charges[e] for e in ends)
    return res_vars, residual_chi, list(ends)


def check_projection_instance(
    n: int, c1: tuple[int, int], c2: tuple[int, int]
) -> dict:
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    form_g = tseitin_cnf(
        GraphInstance(g0, tuple(charges0[v] for v in range(n)), "G", 0, {})
    )
    res_vars, residual_chi, ends = residual_vars_after_fold(n, c1, c2)

    # Residual abstract K4 on ends with remapped edge vars 1..6
    k4 = nx.complete_graph(4)
    # Map ends → 0..3
    rename = {ends[i]: i for i in range(4)}
    form_k4 = tseitin_cnf(
        GraphInstance(k4, residual_chi, "K4", 0, {})
    )

    cl_g = _width_closure_clauses(form_g, 3)
    cl_k4 = _width_closure_clauses(form_k4, 3)

    # Project G-closure onto residual *original* edge vars of G
    proj = {c for c in cl_g if c and all(abs(lit) in res_vars for lit in c)}
    # Compare shape counts: inclusion into abstract K4 needs a var bijection.
    # Check combinatorial proxy: |proj| ≤ |cl_k4| and neither has empty;
    # and every residual XOR axiom of folded G appears in Cl₃(G).
    _, contracted = contract_charges_to_endpoints(n, c1, c2, charges0)
    fold_cert = derive_k4_via_path_fold(n, c1, c2)

    empty_g = () in cl_g
    empty_k4 = () in cl_k4

    # Sufficient proxy for the lemma on this instance:
    # (i) K4 has no □ at width 3; (ii) G has no □ at width 3;
    # (iii) residual K4 XORs derived at ≤Δ from G (forward fold);
    # (iv) every clause in Cl₃(G) supported on res_vars is a consequence of
    #     residual vertex XORs — checked by sat: those clauses alone don't
    #     yield □ at width 3 beyond K4 (count match of unit/binary stubs).
    #
    # Stronger check: rebuild residual XOR axioms in original vars; their
    # width-3 closure must contain proj.
    e_index = _edge_var_map(g0)
    # Rebuild residual multigraph vars after fold for axiom list — use fold state
    # From fold_cert residual charges + ends; residual edges among ends in
    # *folded* sense are the K₄'s edges, but vars are original e_index labels.
    # Recover by re-folding briefly for XOR axioms only.
    ends2, arcs = crossing_branch_sets(n, c1, c2)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)
    for i, arc in enumerate(arcs):
        if not arc:
            continue
        fold_open_arc_internals(
            builder,
            work,
            charges,
            e_index,
            ends2[i],
            list(arc),
            ends2[(i + 1) % 4],
        )
    residual_axioms: list[tuple[int, ...]] = []
    for v in ends2:
        residual_axioms.extend(_xor_clauses_for_vertex(work, e_index, v, charges[v]))
    # Width-3 closure of residual axioms only
    from backend.models.cnf import CNFFormula

    form_res = CNFFormula.from_clauses(
        [list(c) for c in residual_axioms],
        num_variables=max((abs(lit) for c in residual_axioms for lit in c), default=1),
    )
    cl_res = _width_closure_clauses(form_res, 3)
    missing = [c for c in proj if c not in cl_res]
    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "ends": ends,
        "res_var_count": len(res_vars),
        "cl_g_size": len(cl_g),
        "cl_res_size": len(cl_res),
        "cl_k4_size": len(cl_k4),
        "proj_size": len(proj),
        "proj_subseteq_residual_closure": len(missing) == 0,
        "missing_from_residual": len(missing),
        "empty_g_at_3": empty_g,
        "empty_k4_at_3": empty_k4,
        "forward_fold_ok": fold_cert.get("derived_residual_xor_at_delta", False),
        "charges_match": list(residual_chi) == list(contracted)
        or fold_cert.get("charges_match_contracted", False),
        "projection_support": (
            (not empty_g)
            and (not empty_k4)
            and len(missing) == 0
            and fold_cert.get("derived_residual_xor_at_delta", False)
        ),
    }


def verify_family(n_lo: int = 5, n_hi: int = 8, *, max_per_n: int = 20) -> dict:
    ok = 0
    fails: list[dict] = []
    examples: list[dict] = []
    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [
            (u, v)
            for u in range(n)
            for v in range(u + 1, n)
            if not base.has_edge(u, v)
        ]
        count = 0
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            if not chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            try:
                cert = check_projection_instance(n, chords[0], chords[1])
            except Exception as exc:  # noqa: BLE001
                fails.append(
                    {
                        "n": n,
                        "chords": [list(c) for c in chords],
                        "error": str(exc),
                    }
                )
                continue
            if cert["projection_support"]:
                ok += 1
            else:
                fails.append(cert)
            if len(examples) < 5:
                examples.append(cert)
            count += 1
            if max_per_n is not None and count >= max_per_n:
                break
    return {
        "ok": ok,
        "fails": fails,
        "examples": examples,
        "lemma_statement": (
            "If Proj₃(G)|_{V_res} ⊆ Closure₃(residual K4 XORs), then "
            "□∈Closure₃(G) ⇒ □∈Closure₃(K4). Checked on sampled crossings."
        ),
        "note": (
            "This is machine support for the restriction step, not a Lean proof. "
            "Together with Width(K4)=4 it yields Width(G)≥4 without saturating G "
            "to decide emptiness — provided the inclusion holds."
        ),
    }


def main() -> int:
    report = verify_family(5, 8, max_per_n=15)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "fails": len(report["fails"]),
                "first_fail": report["fails"][:1],
            },
            indent=2,
        )
    )
    print(f"wrote {OUT}")
    return 0 if report["ok"] > 0 and not report["fails"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
