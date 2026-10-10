"""Adaptive meta-solver: choose a strategy from cheap instance features.

IMPORTANT: Adaptive selection improving *practical* runtime is Category A/B
engineering / experimental evidence (≤ E2). It never implies a worst-case
polynomial algorithm or P = NP.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from backend.models.cnf import CNFFormula
from backend.solvers.base import SATSolver, SolverResult
from backend.solvers.brute_force import BruteForceSAT
from backend.solvers.dpll import BranchingHeuristic, DPLLSolver
from backend.solvers.pysat_adapter import PySATSolver


@dataclass(frozen=True)
class InstanceFeatures:
    num_variables: int
    num_clauses: int
    ratio: float
    max_clause_width: int
    has_unit: bool
    evidence_level: str = "E2_feature_extraction"


def extract_features(formula: CNFFormula) -> InstanceFeatures:
    widths = [len(c) for c in formula.clauses] or [0]
    return InstanceFeatures(
        num_variables=formula.num_variables,
        num_clauses=formula.num_clauses,
        ratio=formula.ratio,
        max_clause_width=max(widths),
        has_unit=any(len(c) == 1 for c in formula.clauses),
    )


@dataclass
class StrategyChoice:
    name: str
    reason: str
    caveats: list[str]


class MetaSolver(SATSolver):
    """Select among brute force / DPLL variants / PySAT from features."""

    name = "meta"

    def choose(self, formula: CNFFormula) -> tuple[SATSolver, StrategyChoice]:
        f = extract_features(formula)
        caveats = [
            "Strategy choice is heuristic for practical performance only.",
            "Does not claim worst-case polynomial time.",
        ]
        if f.num_variables <= 12:
            return (
                BruteForceSAT(),
                StrategyChoice(
                    "bruteforce",
                    f"n={f.num_variables}≤12 — exhaustive search feasible as oracle",
                    caveats,
                ),
            )
        if f.has_unit or f.ratio < 3.0:
            return (
                DPLLSolver(branching=BranchingHeuristic.FIRST),
                StrategyChoice(
                    "dpll-first",
                    "Units / low ratio — DPLL with simple branching often enough",
                    caveats,
                ),
            )
        if 3.5 <= f.ratio <= 5.0 and f.num_variables <= 60:
            return (
                DPLLSolver(branching=BranchingHeuristic.DLIS),
                StrategyChoice(
                    "dpll-dlis",
                    "Near literature phase-transition band — stronger branching",
                    caveats
                    + ["α band is a literature cue, not a proved universal constant."],
                ),
            )
        return (
            PySATSolver(),
            StrategyChoice(
                "pysat",
                "Larger / denser instance — delegate to CDCL backend",
                caveats,
            ),
        )

    def solve(self, formula: CNFFormula, timeout_seconds: float | None = None) -> SolverResult:
        solver, choice = self.choose(formula)
        result = solver.solve(formula, timeout_seconds=timeout_seconds)
        result.metadata = {
            **result.metadata,
            "meta_strategy": choice.name,
            "meta_reason": choice.reason,
            "features": extract_features(formula).__dict__,
            "evidence_level": "E2_reproducible_computational",
            "claim_type": "observation_experimental",
        }
        result.caveats = list(dict.fromkeys([*result.caveats, *choice.caveats]))
        result.metrics.solver_name = f"meta:{choice.name}"
        result.metrics.notes.append(f"Selected {choice.name}: {choice.reason}")
        return result

    def compare_all(
        self, formula: CNFFormula, timeout_seconds: float | None = 2.0
    ) -> dict[str, Any]:
        """Run several solvers for benchmarking; never claim asymptotic superiority."""
        solvers: list[SATSolver] = [
            DPLLSolver(branching=BranchingHeuristic.DLIS),
            PySATSolver(),
            self,
        ]
        if formula.num_variables <= 12:
            solvers.insert(0, BruteForceSAT())
        rows = []
        for s in solvers:
            r = s.solve(formula, timeout_seconds=timeout_seconds)
            rows.append(
                {
                    "solver": r.metrics.solver_name or s.name,
                    "satisfiable": r.satisfiable,
                    "wall_time_seconds": r.metrics.wall_time_seconds,
                    "decisions": r.metrics.decisions,
                    "timed_out": r.metrics.timed_out,
                }
            )
        return {
            "rows": rows,
            "evidence_level": "E2",
            "caveat": "Finite comparison only; no complexity-class claim.",
        }
