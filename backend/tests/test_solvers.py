"""Solver correctness and cross-validation tests."""

from __future__ import annotations

import pytest
from hypothesis import given, settings, strategies as st

from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import CNFFormula, verify_assignment
from backend.solvers.brute_force import BruteForceSAT
from backend.solvers.dpll import BranchingHeuristic, DPLLSolver
from backend.solvers.pysat_adapter import PySATSolver


@pytest.fixture
def tiny_sat() -> CNFFormula:
    return CNFFormula.from_clauses([[1, 2], [-1, 3], [-2, -3]], num_variables=3)


@pytest.fixture
def tiny_unsat() -> CNFFormula:
    return CNFFormula.from_clauses(
        [[1], [-1], [1, 2], [-2]],
        num_variables=2,
    )


def test_bruteforce_sat(tiny_sat: CNFFormula) -> None:
    r = BruteForceSAT().solve(tiny_sat)
    assert r.satisfiable is True
    assert r.assignment is not None
    assert verify_assignment(tiny_sat, r.assignment)


def test_bruteforce_unsat(tiny_unsat: CNFFormula) -> None:
    r = BruteForceSAT().solve(tiny_unsat)
    assert r.satisfiable is False


@pytest.mark.parametrize(
    "branching",
    [BranchingHeuristic.FIRST, BranchingHeuristic.DLIS, BranchingHeuristic.RANDOM],
)
def test_dpll_matches_bruteforce(
    tiny_sat: CNFFormula, tiny_unsat: CNFFormula, branching: BranchingHeuristic
) -> None:
    for formula in (tiny_sat, tiny_unsat):
        bf = BruteForceSAT().solve(formula)
        dp = DPLLSolver(branching=branching).solve(formula)
        assert bf.satisfiable == dp.satisfiable
        if dp.satisfiable:
            assert dp.assignment is not None
            assert verify_assignment(formula, dp.assignment)


def test_dpll_unit_prop_and_pure() -> None:
    # x1 forced true by unit; x2 pure positive
    f = CNFFormula.from_clauses([[1], [1, 2], [2, 3], [-3, 2]], num_variables=3)
    r = DPLLSolver(use_unit_propagation=True, use_pure_literal=True).solve(f)
    assert r.satisfiable is True
    assert r.assignment is not None
    assert verify_assignment(f, r.assignment)
    assert r.metrics.unit_propagations >= 1


def test_pysat_cross_check(tiny_sat: CNFFormula, tiny_unsat: CNFFormula) -> None:
    pysat = PySATSolver()
    for formula, expected in ((tiny_sat, True), (tiny_unsat, False)):
        r = pysat.solve(formula)
        assert r.satisfiable is expected
        if expected:
            assert r.assignment is not None
            assert verify_assignment(formula, r.assignment)


@given(seed=st.integers(0, 10_000), n=st.integers(3, 8), ratio=st.floats(1.0, 5.0))
@settings(max_examples=25, deadline=None)
def test_solvers_agree_on_random_3sat(seed: int, n: int, ratio: float) -> None:
    formula = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=n, clause_variable_ratio=ratio, k=3, seed=seed)
    )
    bf = BruteForceSAT().solve(formula)
    dpll = DPLLSolver().solve(formula)
    pysat = PySATSolver().solve(formula)
    assert bf.satisfiable == dpll.satisfiable == pysat.satisfiable
    if dpll.satisfiable:
        assert dpll.assignment is not None
        assert verify_assignment(formula, dpll.assignment)
    if pysat.satisfiable:
        assert pysat.assignment is not None
        assert verify_assignment(formula, pysat.assignment)


def test_generator_reproducible() -> None:
    g = RandomKSatGenerator()
    p = RandomKSatParams(num_variables=10, num_clauses=40, k=3, seed=99)
    a = g.generate(p)
    b = g.generate(p)
    assert a.content_hash() == b.content_hash()
    assert a.is_3cnf
