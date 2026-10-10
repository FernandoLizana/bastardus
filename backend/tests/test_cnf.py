"""Unit and property-based tests for CNF models."""

from __future__ import annotations

import pytest
from hypothesis import given, settings, strategies as st

from backend.models.cnf import CNFFormula, Clause, ThreeCNF, verify_assignment


def test_empty_formula_is_sat() -> None:
    f = CNFFormula((), num_variables=0)
    assert verify_assignment(f, {})


def test_empty_clause_unsat() -> None:
    f = CNFFormula((Clause(()),), num_variables=1)
    assert f.contains_empty_clause()
    assert not verify_assignment(f, {1: True})


def test_simple_sat() -> None:
    f = CNFFormula.from_clauses([[1, 2], [-1, 2]], num_variables=2)
    assert verify_assignment(f, {1: True, 2: True})
    assert not verify_assignment(f, {1: True, 2: False})


def test_three_cnf_rejects_wrong_width() -> None:
    with pytest.raises(ValueError):
        ThreeCNF((Clause((1, 2)),), num_variables=2)


def test_dimacs_roundtrip() -> None:
    f = CNFFormula.from_clauses([[1, -2, 3], [-1, 2, -3]], num_variables=3)
    text = f.to_dimacs()
    g = CNFFormula.from_dimacs(text)
    assert g.num_variables == 3
    assert g.num_clauses == 2
    assert g.content_hash() == f.content_hash()


def test_tautology_detection() -> None:
    c = Clause((1, -1, 2))
    assert c.is_tautology()


@given(
    n=st.integers(min_value=1, max_value=6),
    data=st.data(),
)
@settings(max_examples=40, deadline=None)
def test_verify_assignment_consistent_with_bruteforce_definition(n: int, data: st.DataObject) -> None:
    """Property: verify_assignment matches exhaustive clause evaluation."""
    from backend.solvers.brute_force import BruteForceSAT

    m = data.draw(st.integers(min_value=0, max_value=8))
    clauses = []
    for _ in range(m):
        k = data.draw(st.integers(min_value=1, max_value=min(3, n)))
        vars_ = data.draw(
            st.lists(st.integers(1, n), min_size=k, max_size=k, unique=True)
        )
        lits = []
        for v in vars_:
            sign = data.draw(st.sampled_from([1, -1]))
            lits.append(sign * v)
        clauses.append(lits)
    formula = CNFFormula.from_clauses(clauses, num_variables=n)
    # brute force finds sat iff some assignment verifies
    result = BruteForceSAT().solve(formula)
    if result.satisfiable:
        assert result.assignment is not None
        assert verify_assignment(formula, result.assignment)
    else:
        # every assignment fails
        total = 1 << n
        for mask in range(total):
            asg = {i + 1: bool(mask & (1 << i)) for i in range(n)}
            assert not verify_assignment(formula, asg)
