"""Reduction validation tests."""

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import CNFFormula
from backend.reductions.sat_to_clique import (
    solve_clique_bruteforce,
    three_sat_to_clique,
)
from backend.solvers.pysat_adapter import PySATSolver


def test_reduction_size_polynomial_bound() -> None:
    f = CNFFormula.from_clauses([[1, 2, 3], [-1, -2, 3], [1, -2, -3]], num_variables=3)
    red = three_sat_to_clique(f)
    assert red.mapping_metadata["poly_size_check_local"] is True
    assert red.target_size["vertices"] == 9
    assert red.target_size["k"] == 3


@given(seed=st.integers(0, 2000))
@settings(max_examples=40, deadline=None)
def test_3sat_clique_answer_agreement(seed: int) -> None:
    """Thousands of small instances: SAT answer coincides with Clique answer."""
    formula = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=4, num_clauses=6, k=3, seed=seed)
    )
    sat = PySATSolver().solve(formula).satisfiable
    red = three_sat_to_clique(formula)
    clique_inst = red.mapping_metadata["instance"]
    clique_ans = solve_clique_bruteforce(clique_inst, timeout_seconds=10.0)
    assert clique_ans is not None
    assert sat == clique_ans
