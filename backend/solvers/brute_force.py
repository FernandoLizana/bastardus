"""Naive exponential brute-force SAT solver.

Enumerates all 2^n assignments. Used as an independent correctness oracle
for tiny instances and as a baseline for empirical scaling studies (E2 only).
"""

from __future__ import annotations

import time

from backend.core.metrics import SolverMetrics, measure_resources
from backend.models.cnf import Assignment, CNFFormula, verify_assignment
from backend.solvers.base import SATSolver, SolverResult

_DEFAULT_CAVEATS = [
    "Finite solver runs do not establish asymptotic complexity class membership.",
    "A satisfying assignment is an NP certificate; unsatisfiability claims depend "
    "on solver completeness.",
]


class BruteForceSAT(SATSolver):
    """Exhaustive search over Boolean assignments."""

    name = "bruteforce"

    def solve(self, formula: CNFFormula, timeout_seconds: float | None = None) -> SolverResult:
        metrics = SolverMetrics(solver_name=self.name)
        n = formula.num_variables
        if formula.contains_empty_clause():
            metrics.conflicts = 1
            return SolverResult(False, None, metrics)

        if n == 0:
            return SolverResult(True, {}, metrics)

        if n > 24:
            metrics.notes.append(
                f"Refusing brute force for n={n} (>24); use DPLL/CDCL. "
                "This safeguard is an engineering limit, not a complexity theorem."
            )
            metrics.timed_out = True
            return SolverResult(
                None,
                None,
                metrics,
                caveats=[
                    "Brute force aborted by safety limit — no complexity claim.",
                    *_DEFAULT_CAVEATS,
                ],
            )

        deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
        found: Assignment | None = None
        sat = False

        def _search() -> None:
            nonlocal found, sat
            total = 1 << n
            for mask in range(total):
                if deadline is not None and time.perf_counter() > deadline:
                    metrics.timed_out = True
                    return
                metrics.record_decision(depth=n)
                assignment = {i + 1: bool(mask & (1 << i)) for i in range(n)}
                if verify_assignment(formula, assignment):
                    found = assignment
                    sat = True
                    return
            metrics.conflicts = total

        with measure_resources(metrics):
            _search()

        if metrics.timed_out and not sat:
            return SolverResult(None, None, metrics)

        return SolverResult(sat, found, metrics)
