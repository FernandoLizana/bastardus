from backend.reductions.base import GraphDecisionInstance, ReductionResult
from backend.reductions.graph_reductions import (
    solve_independent_set_bruteforce,
    solve_vertex_cover_bruteforce,
    three_sat_to_independent_set,
    three_sat_to_vertex_cover,
    verify_independent_set,
    verify_vertex_cover,
)
from backend.reductions.hamiltonian_tsp import (
    HamiltonianInstance,
    TSPDecisionInstance,
    hamiltonian_to_tsp,
    solve_hamiltonian_bruteforce,
    solve_tsp_decision_bruteforce,
    verify_hamiltonian_cycle,
    verify_tsp_tour,
)
from backend.reductions.sat_to_3sat import sat_to_3sat
from backend.reductions.sat_to_clique import (
    CliqueInstance,
    solve_clique_bruteforce,
    three_sat_to_clique,
    verify_clique,
)

__all__ = [
    "CliqueInstance",
    "GraphDecisionInstance",
    "HamiltonianInstance",
    "ReductionResult",
    "TSPDecisionInstance",
    "hamiltonian_to_tsp",
    "sat_to_3sat",
    "solve_clique_bruteforce",
    "solve_hamiltonian_bruteforce",
    "solve_independent_set_bruteforce",
    "solve_tsp_decision_bruteforce",
    "solve_vertex_cover_bruteforce",
    "three_sat_to_clique",
    "three_sat_to_independent_set",
    "three_sat_to_vertex_cover",
    "verify_clique",
    "verify_hamiltonian_cycle",
    "verify_independent_set",
    "verify_tsp_tour",
    "verify_vertex_cover",
]
