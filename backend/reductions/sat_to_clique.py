"""Polynomial-time reductions between NP-complete problems.

Each reduction returns a ReductionResult suitable for empirical validation.
Mathematical correctness proofs live in docs/; Lean stubs in lean/.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Any

from backend.models.cnf import CNFFormula, ThreeCNF
from backend.reductions.base import ReductionResult

# Back-compat alias
__all__ = [
    "CliqueInstance",
    "ReductionResult",
    "solve_clique_bruteforce",
    "three_sat_to_clique",
    "verify_clique",
]


@dataclass
class CliqueInstance:
    """Undirected graph G and integer k: does G contain a k-clique?"""

    num_vertices: int
    edges: frozenset[tuple[int, int]]
    k: int
    metadata: dict[str, Any] = field(default_factory=dict)

    def has_edge(self, u: int, v: int) -> bool:
        a, b = (u, v) if u < v else (v, u)
        return (a, b) in self.edges


def three_sat_to_clique(formula: CNFFormula | ThreeCNF) -> ReductionResult:
    """Classical Karp reduction 3-SAT → Clique (Garey & Johnson / Karp 1972).

    Formal status: algorithm + empiric validation (E2). Lean: pending.
    Manual proof: textbook known_result (not novel).
    """
    t0 = time.perf_counter()
    if not all(1 <= len(c) <= 3 for c in formula.clauses):
        raise ValueError("three_sat_to_clique expects clauses of width at most 3")

    vertices: list[tuple[int, int, int]] = []
    for c_idx, clause in enumerate(formula.clauses):
        for lit in clause.literals:
            vertices.append((len(vertices), c_idx, lit))

    edges: set[tuple[int, int]] = set()
    for i, (vi, ci, li) in enumerate(vertices):
        for j in range(i + 1, len(vertices)):
            vj, cj, lj = vertices[j]
            if ci == cj:
                continue
            if li == -lj:
                continue
            a, b = (vi, vj) if vi < vj else (vj, vi)
            edges.add((a, b))

    k = formula.num_clauses
    instance = CliqueInstance(
        num_vertices=len(vertices),
        edges=frozenset(edges),
        k=k,
        metadata={
            "vertex_map": [
                {"id": vid, "clause": c, "literal": lit} for vid, c, lit in vertices
            ],
            "source_hash": formula.content_hash(),
            "reduction": "3sat_to_clique_karp",
            "references": [
                "Karp, R. M. (1972). Reducibility among combinatorial problems.",
                "Garey, M. R., & Johnson, D. S. (1979). Computers and Intractability.",
            ],
        },
    )
    elapsed = time.perf_counter() - t0
    return ReductionResult(
        source_problem="3sat",
        target_problem="clique",
        source_size={
            "variables": formula.num_variables,
            "clauses": formula.num_clauses,
            "bits_estimate": formula.num_variables
            + sum(len(c) for c in formula.clauses) * 8,
        },
        target_size={
            "vertices": instance.num_vertices,
            "edges": len(instance.edges),
            "k": instance.k,
        },
        transformation_time=elapsed,
        expected_answer=None,
        verified_answer=None,
        mapping_metadata={
            "instance": instance,
            "poly_size_check_local": instance.num_vertices
            <= 3 * max(formula.num_clauses, 1) + 3,
        },
        certificate_mapping={"vertex_to_literal": {vid: lit for vid, _c, lit in vertices}},
        validation_status="constructed",
    )


def verify_clique(instance: CliqueInstance, vertices: list[int]) -> bool:
    """Polynomial-time Clique certificate verifier."""
    if len(vertices) != instance.k:
        return False
    if len(set(vertices)) != len(vertices):
        return False
    if any(v < 0 or v >= instance.num_vertices for v in vertices):
        return False
    for i, u in enumerate(vertices):
        for v in vertices[i + 1 :]:
            if not instance.has_edge(u, v):
                return False
    return True


def solve_clique_bruteforce(
    instance: CliqueInstance, timeout_seconds: float | None = 5.0
) -> bool | None:
    """Exact Clique via combinatorial enumeration (tiny instances only)."""
    import itertools
    import time as time_mod

    n, k = instance.num_vertices, instance.k
    if k == 0:
        return True
    if k > n:
        return False
    if n > 20:
        return None
    deadline = None if timeout_seconds is None else time_mod.perf_counter() + timeout_seconds
    for combo in itertools.combinations(range(n), k):
        if deadline is not None and time_mod.perf_counter() > deadline:
            return None
        if verify_clique(instance, list(combo)):
            return True
    return False
