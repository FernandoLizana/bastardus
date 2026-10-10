"""Hamiltonian Cycle → TSP (decision) reduction (Karp / Garey–Johnson).

Construction (undirected):
  From G=(V,E) with n=|V|, build complete graph K_n with weights
    w(u,v) = 1 if {u,v}∈E else 2.
  Ask whether there is a tour of total cost ≤ n.

  Correctness (known textbook result): a tour of cost ≤ n uses only weight-1
  edges and is a Hamiltonian cycle of G; conversely any Hamiltonian cycle
  yields a tour of cost n.

  Evidence: algorithm + empirical checks = E2. Novelty: none (known_result).
  Lean formalization: pending beyond certificate stubs.
"""

from __future__ import annotations

import itertools
import time
from dataclasses import dataclass, field
from typing import Any

from backend.reductions.base import ReductionResult


@dataclass(frozen=True)
class HamiltonianInstance:
    num_vertices: int
    edges: frozenset[tuple[int, int]]
    metadata: dict[str, Any] = field(default_factory=dict)

    def has_edge(self, u: int, v: int) -> bool:
        a, b = (u, v) if u < v else (v, u)
        return (a, b) in self.edges


@dataclass(frozen=True)
class TSPDecisionInstance:
    """Complete graph with integer weights; accept iff tour cost ≤ budget."""

    num_cities: int
    weights: dict[tuple[int, int], int]
    budget: int
    metadata: dict[str, Any] = field(default_factory=dict)

    def weight(self, u: int, v: int) -> int:
        a, b = (u, v) if u < v else (v, u)
        return self.weights[(a, b)]


def hamiltonian_to_tsp(instance: HamiltonianInstance) -> ReductionResult:
    t0 = time.perf_counter()
    n = instance.num_vertices
    weights: dict[tuple[int, int], int] = {}
    for i in range(n):
        for j in range(i + 1, n):
            weights[(i, j)] = 1 if instance.has_edge(i, j) else 2
    tsp = TSPDecisionInstance(
        num_cities=n,
        weights=weights,
        budget=n,
        metadata={
            "reduction": "hamiltonian_to_tsp_decision",
            "weight_rule": "1 if edge else 2; budget = n",
            "references": [
                "Karp, R. M. (1972). Reducibility among combinatorial problems.",
                "Garey, M. R., & Johnson, D. S. (1979). Computers and Intractability.",
            ],
            "source": instance.metadata,
        },
    )
    elapsed = time.perf_counter() - t0
    return ReductionResult(
        source_problem="hamiltonian_cycle",
        target_problem="tsp_decision",
        source_size={"vertices": n, "edges": len(instance.edges)},
        target_size={"cities": n, "budget": n, "weighted_pairs": len(weights)},
        transformation_time=elapsed,
        expected_answer=None,
        verified_answer=None,
        mapping_metadata={
            "instance": tsp,
            "poly_size_check_local": len(weights) == n * (n - 1) // 2,
        },
        certificate_mapping={"identity_vertices": list(range(n))},
        validation_status="constructed",
    )


def verify_hamiltonian_cycle(inst: HamiltonianInstance, cycle: list[int]) -> bool:
    n = inst.num_vertices
    if len(cycle) != n or len(set(cycle)) != n:
        return False
    if any(v < 0 or v >= n for v in cycle):
        return False
    for i in range(n):
        u, v = cycle[i], cycle[(i + 1) % n]
        if not inst.has_edge(u, v):
            return False
    return True


def tour_cost(tsp: TSPDecisionInstance, tour: list[int]) -> int:
    n = tsp.num_cities
    return sum(tsp.weight(tour[i], tour[(i + 1) % n]) for i in range(n))


def verify_tsp_tour(tsp: TSPDecisionInstance, tour: list[int]) -> bool:
    n = tsp.num_cities
    if len(tour) != n or len(set(tour)) != n:
        return False
    if any(v < 0 or v >= n for v in tour):
        return False
    return tour_cost(tsp, tour) <= tsp.budget


def solve_hamiltonian_bruteforce(
    inst: HamiltonianInstance, timeout_seconds: float | None = 5.0
) -> bool | None:
    n = inst.num_vertices
    if n == 0:
        return True
    if n == 1:
        return True
    if n > 10:
        return None
    deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
    # Fix start at 0 to remove rotation symmetry
    for perm in itertools.permutations(range(1, n)):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        cycle = [0, *perm]
        if verify_hamiltonian_cycle(inst, cycle):
            return True
    return False


def solve_tsp_decision_bruteforce(
    tsp: TSPDecisionInstance, timeout_seconds: float | None = 5.0
) -> bool | None:
    n = tsp.num_cities
    if n == 0:
        return True
    if n > 10:
        return None
    deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
    for perm in itertools.permutations(range(1, n)):
        if deadline is not None and time.perf_counter() > deadline:
            return None
        tour = [0, *perm]
        if verify_tsp_tour(tsp, tour):
            return True
    return False
