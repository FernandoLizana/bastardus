"""Formal models for SAT / CNF / 3-CNF.

Definitions follow standard references (see docs/MATHEMATICAL_FOUNDATIONS.md):
  - Arora & Barak, Computational Complexity: A Modern Approach (2009)
  - Sipser, Introduction to the Theory of Computation (3rd ed.)
  - Cook, The Complexity of Theorem-Proving Procedures (1971)

This module implements finite CNF formulae as mathematical objects with
certificate verification — the defining NP membership check for SAT.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

# A literal is a non-zero integer: positive = x_i, negative = ¬x_|i|.
Literal = int
Variable = int
Assignment = dict[Variable, bool]


@dataclass(frozen=True, slots=True)
class Clause:
    """A disjunction of literals. Empty clause is unsatisfiable."""

    literals: tuple[Literal, ...]

    def __post_init__(self) -> None:
        if any(lit == 0 for lit in self.literals):
            raise ValueError("Literal 0 is forbidden (DIMACS convention)")
        # Detect complementary pairs later; duplicates allowed but normalized out.
        object.__setattr__(self, "literals", tuple(dict.fromkeys(self.literals)))

    def __iter__(self) -> Iterator[Literal]:
        return iter(self.literals)

    def __len__(self) -> int:
        return len(self.literals)

    @property
    def variables(self) -> frozenset[Variable]:
        return frozenset(abs(lit) for lit in self.literals)

    def is_tautology(self) -> bool:
        positives = {lit for lit in self.literals if lit > 0}
        negatives = {-lit for lit in self.literals if lit < 0}
        return bool(positives & negatives)

    def satisfied_by(self, assignment: Mapping[Variable, bool]) -> bool | None:
        """Return True if sat, False if all literals false, None if undetermined."""
        unknown = False
        for lit in self.literals:
            var = abs(lit)
            if var not in assignment:
                unknown = True
                continue
            value = assignment[var]
            if (lit > 0 and value) or (lit < 0 and not value):
                return True
        return None if unknown else False

    def simplifies(self, assignment: Mapping[Variable, bool]) -> Clause | None:
        """Return simplified clause, or None if already satisfied."""
        remaining: list[Literal] = []
        for lit in self.literals:
            var = abs(lit)
            if var not in assignment:
                remaining.append(lit)
                continue
            value = assignment[var]
            if (lit > 0 and value) or (lit < 0 and not value):
                return None  # clause satisfied
        return Clause(tuple(remaining))


@dataclass(frozen=True)
class CNFFormula:
    """Conjunctive normal form: conjunction of clauses over positive integer variables.

    An empty formula (no clauses) is satisfiable.
    A formula containing the empty clause is unsatisfiable.
    """

    clauses: tuple[Clause, ...]
    num_variables: int = 0
    metadata: dict[str, Any] = field(default_factory=dict, compare=False, hash=False)

    def __post_init__(self) -> None:
        max_var = 0
        for clause in self.clauses:
            for lit in clause:
                max_var = max(max_var, abs(lit))
        n = max(self.num_variables, max_var)
        object.__setattr__(self, "num_variables", n)
        # Drop tautologies for a canonical representation in metadata hash only;
        # keep them in clauses to preserve exact generator output.
        if any(c.is_tautology() for c in self.clauses):
            meta = dict(self.metadata)
            meta["contains_tautology"] = True
            object.__setattr__(self, "metadata", meta)

    def __len__(self) -> int:
        return len(self.clauses)

    @property
    def num_clauses(self) -> int:
        return len(self.clauses)

    @property
    def ratio(self) -> float:
        if self.num_variables == 0:
            return 0.0
        return self.num_clauses / self.num_variables

    @property
    def is_3cnf(self) -> bool:
        return all(len(c) == 3 for c in self.clauses)

    @property
    def is_at_most_3cnf(self) -> bool:
        return all(len(c) <= 3 for c in self.clauses)

    def variables(self) -> frozenset[Variable]:
        vs: set[Variable] = set()
        for clause in self.clauses:
            vs |= set(clause.variables)
        return frozenset(vs)

    def contains_empty_clause(self) -> bool:
        return any(len(c) == 0 for c in self.clauses)

    def content_hash(self) -> str:
        payload = {
            "num_variables": self.num_variables,
            "clauses": [list(c.literals) for c in self.clauses],
        }
        raw = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(raw.encode()).hexdigest()

    def to_dimacs(self) -> str:
        lines = [f"p cnf {self.num_variables} {self.num_clauses}"]
        for clause in self.clauses:
            lines.append(" ".join(str(lit) for lit in clause.literals) + " 0")
        return "\n".join(lines) + "\n"

    @classmethod
    def from_dimacs(cls, text: str, metadata: dict[str, Any] | None = None) -> CNFFormula:
        clauses: list[Clause] = []
        n_vars = 0
        for raw in text.splitlines():
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                if len(parts) >= 4 and parts[1] == "cnf":
                    n_vars = int(parts[2])
                continue
            nums = [int(x) for x in line.split()]
            if nums and nums[-1] == 0:
                nums = nums[:-1]
            if nums:
                clauses.append(Clause(tuple(nums)))
        return cls(tuple(clauses), num_variables=n_vars, metadata=metadata or {})

    @classmethod
    def from_clauses(
        cls,
        clauses: Iterable[Sequence[Literal]],
        num_variables: int = 0,
        metadata: dict[str, Any] | None = None,
    ) -> CNFFormula:
        built = tuple(Clause(tuple(c)) for c in clauses)
        return cls(built, num_variables=num_variables, metadata=metadata or {})

    def as_3cnf_view(self) -> ThreeCNF:
        if not self.is_3cnf:
            raise ValueError("Formula is not a 3-CNF (every clause must have exactly 3 literals)")
        return ThreeCNF(self.clauses, self.num_variables, dict(self.metadata))


@dataclass(frozen=True)
class ThreeCNF(CNFFormula):
    """3-CNF: every clause has exactly three literals.

    Classic NP-complete problem (Cook–Levin; Garey & Johnson).
    """

    def __post_init__(self) -> None:
        super().__post_init__()
        if not all(len(c) == 3 for c in self.clauses):
            bad = [c for c in self.clauses if len(c) != 3]
            raise ValueError(f"3-CNF requires clause width 3; found: {bad[:3]}")


def verify_assignment(formula: CNFFormula, assignment: Mapping[Variable, bool]) -> bool:
    """Polynomial-time certificate verifier for SAT (NP membership witness check).

    Returns True iff every clause is satisfied under *assignment*.
    Variables not appearing in the formula may be omitted; missing variables
    needed by a clause cause that clause to fail if no remaining literal saves it.
    """
    for clause in formula.clauses:
        result = clause.satisfied_by(assignment)
        if result is not True:
            return False
    return True


def assignment_from_list(values: Sequence[bool]) -> Assignment:
    """Map 0-indexed Boolean list to 1-indexed variables."""
    return {i + 1: bool(v) for i, v in enumerate(values)}


def complete_assignment(
    formula: CNFFormula, partial: Mapping[Variable, bool], default: bool = False
) -> Assignment:
    """Extend a partial assignment to all variables of the formula."""
    full = {v: default for v in range(1, formula.num_variables + 1)}
    full.update(dict(partial))
    return full
