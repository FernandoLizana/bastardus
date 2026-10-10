"""Common solver interfaces and result types."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any

from backend.core.evidence import EvidenceLevel
from backend.core.metrics import SolverMetrics
from backend.models.cnf import Assignment, CNFFormula


@dataclass
class SolverResult:
    """Outcome of a SAT (or related) solver run.

    claim_type is always observation_experimental for solver outputs.
    evidence_level is at most E2.
    """

    satisfiable: bool | None
    assignment: Assignment | None
    metrics: SolverMetrics
    evidence_level: EvidenceLevel = EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL
    claim_type: str = "observation_experimental"
    caveats: list[str] = field(
        default_factory=lambda: [
            "Finite solver runs do not establish asymptotic complexity class membership.",
            "A satisfying assignment is an NP certificate; unsatisfiability claims depend "
            "on solver completeness.",
        ]
    )
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "satisfiable": self.satisfiable,
            "assignment": self.assignment,
            "metrics": self.metrics.to_dict(),
            "evidence_level": self.evidence_level.name,
            "claim_type": self.claim_type,
            "caveats": self.caveats,
            "metadata": self.metadata,
        }


class SATSolver(ABC):
    """Abstract SAT solver over CNFFormula."""

    name: str = "abstract"

    @abstractmethod
    def solve(self, formula: CNFFormula, timeout_seconds: float | None = None) -> SolverResult:
        """Return a solver result. If timeout, satisfiable may be None."""
