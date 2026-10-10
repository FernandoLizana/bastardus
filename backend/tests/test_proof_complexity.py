"""Tests for exact width oracle and tree/cycle width conjecture survivors."""

from backend.proof_complexity.tseitin_family import (
    make_cycle,
    make_path,
    make_random_regular,
    make_tree_random,
    tseitin_cnf,
)
from backend.proof_complexity.width import min_resolution_width
from backend.solvers.pysat_adapter import PySATSolver


def test_cycle_width_equals_two() -> None:
    for n in range(3, 8):
        f = tseitin_cnf(make_cycle(n))
        assert PySATSolver().solve(f).satisfiable is False
        assert min_resolution_width(f).claimed_min_width == 2


def test_path_width_equals_delta() -> None:
    for n in range(2, 8):
        inst = make_path(n)
        f = tseitin_cnf(inst)
        delta = max(d for _, d in inst.graph.degree())
        assert min_resolution_width(f).claimed_min_width == delta


def test_trees_width_equals_delta_sample() -> None:
    for n in range(3, 8):
        for seed in range(3):
            inst = make_tree_random(n, seed=seed)
            f = tseitin_cnf(inst)
            delta = max(d for _, d in inst.graph.degree())
            assert min_resolution_width(f).claimed_min_width == delta


def test_regular_can_exceed_delta() -> None:
    f = tseitin_cnf(make_random_regular(6, 3, seed=0))
    w = min_resolution_width(f).claimed_min_width
    assert w >= 4
