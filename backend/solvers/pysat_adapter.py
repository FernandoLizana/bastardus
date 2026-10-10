"""Independent SAT check via PySAT (MiniSat / Glucose backends).

Used as a cross-validator for our educational solvers — not as a proof
of asymptotic complexity.
"""

from __future__ import annotations

from backend.core.metrics import SolverMetrics, measure_resources
from backend.models.cnf import Assignment, CNFFormula
from backend.solvers.base import SATSolver, SolverResult


class PySATSolver(SATSolver):
    """Adapter around python-sat."""

    name = "pysat"

    def __init__(self, solver_name: str = "minisat22") -> None:
        self.solver_name = solver_name

    def solve(self, formula: CNFFormula, timeout_seconds: float | None = None) -> SolverResult:
        metrics = SolverMetrics(solver_name=f"{self.name}:{self.solver_name}")
        if timeout_seconds is not None:
            metrics.notes.append(
                "PySAT adapter ignores timeout_seconds in MVP; use wrapper in experiments."
            )

        try:
            from pysat.solvers import Solver
        except ImportError as exc:  # pragma: no cover
            metrics.notes.append(f"PySAT not installed: {exc}")
            metrics.timed_out = True
            return SolverResult(
                None,
                None,
                metrics,
                caveats=["PySAT unavailable — install python-sat."],
            )

        clauses = [list(c.literals) for c in formula.clauses if not c.is_tautology()]
        sat: bool | None = None
        assignment: Assignment | None = None

        def _run() -> None:
            nonlocal sat, assignment
            with Solver(name=self.solver_name, bootstrap_with=clauses) as solver:
                sat = bool(solver.solve())
                try:
                    stats = solver.accum_stats() if hasattr(solver, "accum_stats") else {}
                    if isinstance(stats, dict):
                        metrics.decisions = int(stats.get("decisions", 0) or 0)
                        metrics.conflicts = int(stats.get("conflicts", 0) or 0)
                except Exception:  # noqa: BLE001
                    metrics.notes.append("PySAT accum_stats unavailable")
                if sat:
                    model = solver.get_model() or []
                    assignment = {}
                    for lit in model:
                        if lit == 0:
                            continue
                        assignment[abs(lit)] = lit > 0
                    for v in range(1, formula.num_variables + 1):
                        assignment.setdefault(v, False)

        with measure_resources(metrics):
            _run()

        return SolverResult(
            sat,
            assignment,
            metrics,
            metadata={"backend": self.solver_name},
        )
