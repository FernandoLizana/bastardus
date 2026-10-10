"""Tests for Hamiltonian→TSP and adversarial generators."""

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from backend.formalization import status_report
from backend.generators import (
    CraftedHamiltonianParams,
    PigeonholeParams,
    SubsetSumParams,
    TseitinParams,
    generate_crafted_hamiltonian,
    generate_hard_subset_sum,
    generate_pigeonhole,
    generate_tseitin,
    subset_sum_dp_solvable,
    verify_subset_sum,
)
from backend.reductions import (
    hamiltonian_to_tsp,
    solve_hamiltonian_bruteforce,
    solve_tsp_decision_bruteforce,
)
from backend.solvers.pysat_adapter import PySATSolver


def test_pigeonhole_unsat() -> None:
    f = generate_pigeonhole(PigeonholeParams(holes=3, seed=0))
    assert f.metadata["known_answer"] is False
    assert PySATSolver().solve(f).satisfiable is False


def test_tseitin_odd_charge_unsat() -> None:
    f = generate_tseitin(TseitinParams(num_vertices=6, seed=1, charge_odd=True))
    assert PySATSolver().solve(f).satisfiable is False


def test_subset_sum_planted_and_dp() -> None:
    inst = generate_hard_subset_sum(SubsetSumParams(num_items=12, seed=3, bits=10))
    assert subset_sum_dp_solvable(inst) is True
    planted = inst.metadata["planted_indices"]
    assert verify_subset_sum(inst, planted)


@given(seed=st.integers(0, 50), n=st.integers(3, 7))
@settings(max_examples=15, deadline=None)
def test_hamiltonian_tsp_agreement(seed: int, n: int) -> None:
    ham = generate_crafted_hamiltonian(
        CraftedHamiltonianParams(num_vertices=n, seed=seed, make_nonhamiltonian=False)
    )
    ham_ans = solve_hamiltonian_bruteforce(ham)
    tsp_red = hamiltonian_to_tsp(ham)
    tsp_ans = solve_tsp_decision_bruteforce(tsp_red.mapping_metadata["instance"])
    assert ham_ans is True
    assert tsp_ans is True
    assert tsp_red.mapping_metadata["poly_size_check_local"]


def test_nonhamiltonian_crafted() -> None:
    ham = generate_crafted_hamiltonian(
        CraftedHamiltonianParams(num_vertices=5, seed=0, make_nonhamiltonian=True)
    )
    assert solve_hamiltonian_bruteforce(ham) is False
    tsp = hamiltonian_to_tsp(ham).mapping_metadata["instance"]
    assert solve_tsp_decision_bruteforce(tsp) is False


def test_formalization_status() -> None:
    report = status_report()
    assert report["e5_partial"] >= 1
    assert "caveat" in report
