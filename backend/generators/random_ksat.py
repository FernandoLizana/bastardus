"""Reproducible random k-SAT generator.

Uniform random k-SAT is the classic model for phase-transition studies
(e.g. Mitchell, Selman, Levesque 1992; Mézard & Zecchina 2002).

This generator does NOT assume a universal critical ratio. The often-cited
≈4.26 value for random 3-SAT is an empirical / conjectural threshold in the
large-n limit — we treat it as a literature hint for where to look, not as
a theorem proved by this laboratory (evidence for threshold location is E2/E3,
not a resolution of P vs NP).
"""

from __future__ import annotations

import hashlib
import platform
import socket
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from typing import Any

import numpy as np

from backend import __version__
from backend.models.cnf import CNFFormula, ThreeCNF


@dataclass(frozen=True)
class RandomKSatParams:
    num_variables: int
    num_clauses: int | None = None
    clause_variable_ratio: float | None = None
    k: int = 3
    seed: int = 0
    allow_duplicate_clauses: bool = True
    forbid_tautological_clauses: bool = True

    def resolved_num_clauses(self) -> int:
        if self.num_clauses is not None:
            return self.num_clauses
        if self.clause_variable_ratio is None:
            raise ValueError("Provide num_clauses or clause_variable_ratio")
        return max(0, int(round(self.clause_variable_ratio * self.num_variables)))


class RandomKSatGenerator:
    """Generate random k-CNF instances with provenance tags."""

    name = "random-k-sat"

    def generate(self, params: RandomKSatParams) -> CNFFormula:
        if params.num_variables < 0:
            raise ValueError("num_variables must be >= 0")
        if params.k < 1:
            raise ValueError("k must be >= 1")
        if params.num_variables > 0 and params.k > params.num_variables:
            raise ValueError("k cannot exceed num_variables")

        m = params.resolved_num_clauses()
        rng = np.random.default_rng(params.seed)
        clauses: list[tuple[int, ...]] = []
        seen: set[tuple[int, ...]] = set()

        attempts = 0
        max_attempts = max(m * 50, 1)
        while len(clauses) < m and attempts < max_attempts:
            attempts += 1
            vars_chosen = rng.choice(params.num_variables, size=params.k, replace=False)
            signs = rng.choice([-1, 1], size=params.k)
            lits = tuple(sorted(int(signs[i] * (int(vars_chosen[i]) + 1)) for i in range(params.k)))
            if params.forbid_tautological_clauses:
                abs_vals = [abs(x) for x in lits]
                if len(set(abs_vals)) < params.k:
                    continue
                if any(-lit in lits for lit in lits):
                    continue
            if not params.allow_duplicate_clauses and lits in seen:
                continue
            seen.add(lits)
            clauses.append(lits)

        if len(clauses) < m:
            raise RuntimeError(
                f"Could only generate {len(clauses)}/{m} clauses; "
                "relax constraints or increase variable count."
            )

        meta = self._provenance(params, m, clauses)
        formula = CNFFormula.from_clauses(
            clauses, num_variables=params.num_variables, metadata=meta
        )
        if params.k == 3:
            # Re-wrap as ThreeCNF when applicable
            return ThreeCNF(formula.clauses, formula.num_variables, dict(formula.metadata))
        return formula

    def _provenance(
        self, params: RandomKSatParams, m: int, clauses: list[tuple[int, ...]]
    ) -> dict[str, Any]:
        payload = {
            "generator": self.name,
            "parameters": asdict(params),
            "resolved_num_clauses": m,
            "created_at": datetime.now(timezone.utc).isoformat(),
            "host": socket.gethostname(),
            "platform": platform.platform(),
            "python": platform.python_version(),
            "code_version": __version__,
            "known_answer": None,
            "confirming_solver": None,
            "evidence_level": "E2_instance_provenance",
            "warnings": [
                "Random generation does not imply hardness.",
                "No asymptotic claims follow from finite samples.",
            ],
        }
        blob = repr(sorted(clauses)).encode() + repr(asdict(params)).encode()
        payload["instance_hash"] = hashlib.sha256(blob).hexdigest()
        return payload
