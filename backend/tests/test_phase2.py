"""Tests for new reductions, meta-solver, and refutation search."""

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from backend.conjectures.refute import (
    refute_all_random_3sat_always_sat,
    refute_solvers_always_agree,
)
from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import CNFFormula, verify_assignment
from backend.reductions import (
    sat_to_3sat,
    solve_independent_set_bruteforce,
    solve_vertex_cover_bruteforce,
    three_sat_to_independent_set,
    three_sat_to_vertex_cover,
)
from backend.solvers.meta import MetaSolver, extract_features
from backend.solvers.pysat_adapter import PySATSolver


def test_sat_to_3sat_equisatisfiable_width4() -> None:
    f = CNFFormula.from_clauses([[1, 2, 3, 4], [-1, -2, 3]], num_variables=4)
    red = sat_to_3sat(f)
    g = red.mapping_metadata["instance"]
    assert all(len(c) == 3 for c in g.clauses)
    assert red.mapping_metadata["poly_size_check_local"]
    sat_f = PySATSolver().solve(f).satisfiable
    sat_g = PySATSolver().solve(g).satisfiable
    assert sat_f == sat_g


@given(seed=st.integers(0, 300))
@settings(max_examples=25, deadline=None)
def test_sat_to_3sat_random_agreement(seed: int) -> None:
    # Build a mixed-width CNF from random 3-sat by merging two clauses sometimes
    base = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=5, num_clauses=4, k=3, seed=seed)
    )
    clauses = [list(c.literals) for c in base.clauses]
    if len(clauses) >= 2:
        clauses[0] = list(dict.fromkeys(clauses[0] + clauses[1][:1]))
    f = CNFFormula.from_clauses(clauses, num_variables=5)
    red = sat_to_3sat(f)
    g = red.mapping_metadata["instance"]
    assert PySATSolver().solve(f).satisfiable == PySATSolver().solve(g).satisfiable


@given(seed=st.integers(0, 400))
@settings(max_examples=20, deadline=None)
def test_3sat_to_is_agreement(seed: int) -> None:
    formula = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=4, num_clauses=5, k=3, seed=seed)
    )
    sat = PySATSolver().solve(formula).satisfiable
    red = three_sat_to_independent_set(formula)
    ans = solve_independent_set_bruteforce(red.mapping_metadata["instance"])
    assert ans is not None
    assert sat == ans


@given(seed=st.integers(0, 400))
@settings(max_examples=20, deadline=None)
def test_3sat_to_vc_agreement(seed: int) -> None:
    formula = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=4, num_clauses=5, k=3, seed=seed)
    )
    sat = PySATSolver().solve(formula).satisfiable
    red = three_sat_to_vertex_cover(formula)
    ans = solve_vertex_cover_bruteforce(red.mapping_metadata["instance"])
    assert ans is not None
    assert sat == ans


def test_sat_to_3sat_narrow_widths() -> None:
    f = CNFFormula.from_clauses([[1], [2, 3], [1, 2, 3, 4, 5]], num_variables=5)
    red = sat_to_3sat(f)
    g = red.mapping_metadata["instance"]
    assert all(len(c) == 3 for c in g.clauses if len(c) > 0)
    assert PySATSolver().solve(f).satisfiable == PySATSolver().solve(g).satisfiable


def test_meta_strategies_cover_branches() -> None:
    meta = MetaSolver()
    small = CNFFormula.from_clauses([[1, -2]], num_variables=2)
    assert meta.choose(small)[1].name == "bruteforce"
    mid = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=20, clause_variable_ratio=4.2, k=3, seed=1)
    )
    assert meta.choose(mid)[1].name in {"dpll-dlis", "dpll-first", "pysat"}
    big = RandomKSatGenerator().generate(
        RandomKSatParams(num_variables=80, clause_variable_ratio=6.0, k=3, seed=2)
    )
    assert meta.choose(big)[1].name == "pysat"
    cmp = meta.compare_all(small, timeout_seconds=1.0)
    assert "rows" in cmp



def test_refute_always_sat_finds_counterexample() -> None:
    report = refute_all_random_3sat_always_sat(
        n_values=(4, 5, 6, 8), seeds_per_n=40
    )
    assert report.found is True
    assert report.minimal is not None
    assert report.evidence_level.name.startswith("E2")


def test_solvers_agree_search() -> None:
    report = refute_solvers_always_agree(n_values=(3, 4, 5), seeds_per_n=15)
    assert report.found is False
