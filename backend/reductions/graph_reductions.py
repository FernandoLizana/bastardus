"""3-SAT → Independent Set and 3-SAT → Vertex Cover (Karp; textbook).

Construction (Garey & Johnson / standard course notes):
  Same vertex set as the Clique reduction (one vertex per literal occurrence).
  Independent Set asks for an independent set of size m (#clauses) in the
  *complement* of the Clique graph used by 3-SAT→Clique — equivalently,
  connect vertices that conflict (same clause or complementary literals) and
  ask for an independent set of size m.

  Vertex Cover: G has an independent set of size m iff G has a vertex cover
  of size |V|−m (classic identity).
"""

from __future__ import annotations

import itertools
import time
from typing import Any

from backend.models.cnf import CNFFormula, ThreeCNF
from backend.reductions.base import GraphDecisionInstance, ReductionResult
from backend.reductions.sat_to_clique import three_sat_to_clique


def three_sat_to_independent_set(formula: CNFFormula | ThreeCNF) -> ReductionResult:
    """Build conflict graph: edge if same clause or complementary literals; k=m."""
    t0 = time.perf_counter()
    if not all(1 <= len(c) <= 3 for c in formula.clauses):
        raise ValueError("expects clause width in 1..3")

    vertices: list[tuple[int, int, int]] = []
    for c_idx, clause in enumerate(formula.clauses):
        for lit in clause.literals:
            vertices.append((len(vertices), c_idx, lit))

    edges: set[tuple[int, int]] = set()
    for i, (vi, ci, li) in enumerate(vertices):
        for j in range(i + 1, len(vertices)):
            vj, cj, lj = vertices[j]
            conflict = ci == cj or li == -lj
            if conflict:
                a, b = (vi, vj) if vi < vj else (vj, vi)
                edges.add((a, b))

    k = formula.num_clauses
    inst = GraphDecisionInstance(
        num_vertices=len(vertices),
        edges=frozenset(edges),
        k=k,
        problem="independent_set",
        metadata={
            "vertex_map": [
                {"id": vid, "clause": c, "literal": lit} for vid, c, lit in vertices
            ],
            "reduction": "3sat_to_independent_set",
            "source_hash": formula.content_hash(),
            "references": [
                "Karp, R. M. (1972). Reducibility among combinatorial problems.",
                "Garey, M. R., & Johnson, D. S. (1979).",
            ],
        },
    )
    elapsed = time.perf_counter() - t0
    return ReductionResult(
        source_problem="3sat",
        target_problem="independent_set",
        source_size={
            "variables": formula.num_variables,
            "clauses": formula.num_clauses,
        },
        target_size={
            "vertices": inst.num_vertices,
            "edges": len(inst.edges),
            "k": inst.k,
        },
        transformation_time=elapsed,
        expected_answer=None,
        verified_answer=None,
        mapping_metadata={
            "instance": inst,
            "poly_size_check_local": inst.num_vertices <= 3 * max(formula.num_clauses, 1) + 3,
        },
        certificate_mapping={"vertex_to_literal": {vid: lit for vid, _c, lit in vertices}},
        validation_status="constructed",
    )


def three_sat_to_vertex_cover(formula: CNFFormula | ThreeCNF) -> ReductionResult:
    """IS instance from 3-SAT, then VC with k_vc = |V| - m."""
    is_red = three_sat_to_independent_set(formula)
    is_inst: GraphDecisionInstance = is_red.mapping_metadata["instance"]
    k_vc = is_inst.num_vertices - is_inst.k
    vc_inst = GraphDecisionInstance(
        num_vertices=is_inst.num_vertices,
        edges=is_inst.edges,
        k=k_vc,
        problem="vertex_cover",
        metadata={
            **is_inst.metadata,
            "reduction": "3sat_to_vertex_cover_via_is",
            "independent_set_k": is_inst.k,
        },
    )
    return ReductionResult(
        source_problem="3sat",
        target_problem="vertex_cover",
        source_size=is_red.source_size,
        target_size={
            "vertices": vc_inst.num_vertices,
            "edges": len(vc_inst.edges),
            "k": vc_inst.k,
        },
        transformation_time=is_red.transformation_time,
        expected_answer=None,
        verified_answer=None,
        mapping_metadata={
            "instance": vc_inst,
            "poly_size_check_local": is_red.mapping_metadata["poly_size_check_local"],
            "via": "independent_set",
        },
        certificate_mapping=is_red.certificate_mapping,
        validation_status="constructed",
    )


def verify_independent_set(inst: GraphDecisionInstance, verts: list[int]) -> bool:
    if len(verts) != inst.k or len(set(verts)) != len(verts):
        return False
    if any(v < 0 or v >= inst.num_vertices for v in verts):
        return False
    for i, u in enumerate(verts):
        for v in verts[i + 1 :]:
            if inst.has_edge(u, v):
                return False
    return True


def verify_vertex_cover(inst: GraphDecisionInstance, verts: list[int]) -> bool:
    if len(verts) != inst.k or len(set(verts)) != len(verts):
        return False
    cover = set(verts)
    if any(v < 0 or v >= inst.num_vertices for v in cover):
        return False
    for u, v in inst.edges:
        if u not in cover and v not in cover:
            return False
    return True


def solve_independent_set_bruteforce(
    inst: GraphDecisionInstance, timeout_seconds: float | None = 5.0
) -> bool | None:
    import time

    n, k = inst.num_vertices, inst.k
    if k == 0:
        return True
    if k > n:
        return False
    if n > 20:
        return None
    deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
    for combo in itertools.combinations(range(n), k):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        if verify_independent_set(inst, list(combo)):
            return True
    return False


def solve_vertex_cover_bruteforce(
    inst: GraphDecisionInstance, timeout_seconds: float | None = 5.0
) -> bool | None:
    import time

    n, k = inst.num_vertices, inst.k
    if k < 0:
        return False
    if k >= n:
        return True
    if n > 20:
        return None
    deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
    for combo in itertools.combinations(range(n), k):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        if verify_vertex_cover(inst, list(combo)):
            return True
    return False


def cross_check_clique_vs_is(formula: CNFFormula) -> dict[str, Any]:
    """Sanity: Clique answer on Clique-graph ≡ IS answer on conflict-graph."""
    clique_red = three_sat_to_clique(formula)
    is_red = three_sat_to_independent_set(formula)
    return {
        "clique_vertices": clique_red.target_size["vertices"],
        "is_vertices": is_red.target_size["vertices"],
        "note": "Same |V|; edges are complements w.r.t. cross-clause non-conflicts.",
        "evidence_level": "E2",
    }
