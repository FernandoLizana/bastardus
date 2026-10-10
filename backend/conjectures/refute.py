"""Automatic search for minimal counterexamples to structured conjectures.

Refutation-first: prefer smallest (n, seed) that breaks a claim.
Evidence of a counterexample is E2; absence of one is NOT a proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

from backend.core.evidence import EvidenceLevel
from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.solvers.dpll import DPLLSolver
from backend.solvers.pysat_adapter import PySATSolver


@dataclass
class CounterexampleReport:
    conjecture_id: str
    found: bool
    minimal: dict[str, Any] | None
    trials: int
    evidence_level: EvidenceLevel
    claim_type: str
    caveats: list[str]

    def to_dict(self) -> dict[str, Any]:
        return {
            "conjecture_id": self.conjecture_id,
            "found": self.found,
            "minimal": self.minimal,
            "trials": self.trials,
            "evidence_level": self.evidence_level.name,
            "claim_type": self.claim_type,
            "caveats": self.caveats,
        }


def search_minimal_counterexample(
    conjecture_id: str,
    predicate: Callable[[dict[str, Any]], bool],
    *,
    n_values: tuple[int, ...] = (3, 4, 5, 6, 8, 10),
    seeds_per_n: int = 40,
    ratio: float = 4.2,
) -> CounterexampleReport:
    """Search random 3-SAT instances for a violation of *predicate*.

    *predicate* receives a dict with keys:
      formula, sat (bool|None), n, seed, ratio, features
    and should return True if the conjecture HOLDS on that instance.
    A counterexample is the first instance where predicate returns False.
    """
    gen = RandomKSatGenerator()
    pysat = PySATSolver()
    trials = 0
    for n in n_values:
        for i in range(seeds_per_n):
            seed = 1000 * n + i
            trials += 1
            formula = gen.generate(
                RandomKSatParams(
                    num_variables=n, clause_variable_ratio=ratio, k=3, seed=seed
                )
            )
            sat = pysat.solve(formula).satisfiable
            payload = {
                "formula": formula,
                "sat": sat,
                "n": n,
                "seed": seed,
                "ratio": ratio,
                "num_clauses": formula.num_clauses,
            }
            if not predicate(payload):
                return CounterexampleReport(
                    conjecture_id=conjecture_id,
                    found=True,
                    minimal={
                        "n": n,
                        "seed": seed,
                        "ratio": ratio,
                        "num_clauses": formula.num_clauses,
                        "sat": sat,
                        "hash": formula.content_hash(),
                    },
                    trials=trials,
                    evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
                    claim_type="observation_experimental",
                    caveats=[
                        "Counterexample refutes the tested finite-domain claim only.",
                        "Absence of counterexamples would not prove the conjecture.",
                    ],
                )
    return CounterexampleReport(
        conjecture_id=conjecture_id,
        found=False,
        minimal=None,
        trials=trials,
        evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
        claim_type="error_or_inconclusive",
        caveats=[
            "No counterexample in search budget — NOT a proof.",
            "Increase n_values / seeds_per_n or reformulate the conjecture.",
        ],
    )


def refute_all_random_3sat_always_sat(
    *, n_values: tuple[int, ...] = (3, 4, 5, 6), seeds_per_n: int = 30
) -> CounterexampleReport:
    """Example refutation target: 'every random 3-SAT at α=4.2 is satisfiable'."""

    def holds(payload: dict[str, Any]) -> bool:
        return payload["sat"] is True

    return search_minimal_counterexample(
        "C-always-sat-at-4.2",
        holds,
        n_values=n_values,
        seeds_per_n=seeds_per_n,
        ratio=4.2,
    )


def refute_solvers_always_agree(
    *, n_values: tuple[int, ...] = (3, 4, 5, 6, 8), seeds_per_n: int = 20
) -> CounterexampleReport:
    """Should NOT find disagreements if implementations are correct.

    Finding one is a bug report (engineering), not a complexity theorem.
    """
    dpll = DPLLSolver()
    pysat = PySATSolver()
    gen = RandomKSatGenerator()
    trials = 0
    for n in n_values:
        for i in range(seeds_per_n):
            seed = 5000 * n + i
            trials += 1
            formula = gen.generate(
                RandomKSatParams(num_variables=n, clause_variable_ratio=4.0, k=3, seed=seed)
            )
            a = dpll.solve(formula).satisfiable
            b = pysat.solve(formula).satisfiable
            if a is not None and b is not None and a != b:
                return CounterexampleReport(
                    conjecture_id="C-solvers-agree",
                    found=True,
                    minimal={"n": n, "seed": seed, "dpll": a, "pysat": b},
                    trials=trials,
                    evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
                    claim_type="error_or_inconclusive",
                    caveats=["Solver disagreement indicates an implementation bug."],
                )
    return CounterexampleReport(
        conjecture_id="C-solvers-agree",
        found=False,
        minimal=None,
        trials=trials,
        evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
        claim_type="observation_experimental",
        caveats=["No disagreement in budget — does not prove full equivalence."],
    )
