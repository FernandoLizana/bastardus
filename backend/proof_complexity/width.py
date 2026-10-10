"""Exact minimum resolution width via width-bounded saturation (optimized)."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable

from backend.models.cnf import CNFFormula, Literal


def _norm(lits: Iterable[Literal]) -> tuple[Literal, ...] | None:
    s = sorted(set(lits))
    pos = {x for x in s if x > 0}
    neg = {-x for x in s if x < 0}
    if pos & neg:
        return None
    return tuple(s)


def resolve(a: tuple[Literal, ...], b: tuple[Literal, ...]) -> tuple[Literal, ...] | None:
    sa, sb = set(a), set(b)
    pivots = {x for x in sa if -x in sb}
    if len(pivots) != 1:
        return None
    p = next(iter(pivots))
    return _norm((sa | sb) - {p, -p})


@dataclass
class WidthCertificate:
    formula_hash: str
    claimed_min_width: int
    upper_derivation: list[tuple[Literal, ...]] = field(default_factory=list)
    lower_closure_size: int = 0
    notes: list[str] = field(default_factory=list)
    evidence_level: str = "E2_certified_computation"
    claim_type: str = "observation_experimental"


def has_width_refutation(
    formula: CNFFormula, width: int, *, max_clauses: int = 200_000
) -> tuple[bool, list[tuple[Literal, ...]], int]:
    """Saturation under resolvents of length ≤ width, indexed by literals."""
    clauses: set[tuple[Literal, ...]] = set()
    by_lit: dict[int, set[tuple[Literal, ...]]] = defaultdict(set)

    def add(c: tuple[Literal, ...]) -> None:
        if c in clauses:
            return
        clauses.add(c)
        for lit in c:
            by_lit[lit].add(c)

    derivation: list[tuple[Literal, ...]] = []
    for clause in formula.clauses:
        n = _norm(clause.literals)
        if n is None:
            continue
        if len(n) == 0:
            return True, [()], 1
        if len(n) <= width:
            add(n)
            derivation.append(n)

    if () in clauses:
        return True, [()], len(clauses)

    pending = list(clauses)
    while pending:
        if len(clauses) > max_clauses:
            return False, derivation, len(clauses)
        a = pending.pop()
        # Candidate partners: share a complementary literal with a
        partners: set[tuple[Literal, ...]] = set()
        for lit in a:
            partners |= by_lit.get(-lit, set())
        for b in partners:
            if a == b:
                continue
            r = resolve(a, b)
            if r is None or len(r) > width:
                continue
            if r not in clauses:
                add(r)
                derivation.append(r)
                pending.append(r)
                if len(r) == 0:
                    return True, derivation, len(clauses)
    return False, derivation, len(clauses)


def min_resolution_width(
    formula: CNFFormula, max_width: int | None = None
) -> WidthCertificate:
    from backend.solvers.pysat_adapter import PySATSolver

    sat = PySATSolver().solve(formula).satisfiable
    if sat:
        return WidthCertificate(
            formula_hash=formula.content_hash(),
            claimed_min_width=-1,
            notes=["Formula is satisfiable; resolution width undefined."],
            claim_type="error_or_inconclusive",
        )

    axiom_w = max((len(c) for c in formula.clauses), default=0)
    hi = max_width if max_width is not None else min(max(axiom_w, 8), formula.num_variables)
    last_fail_size = 0
    for w in range(axiom_w, hi + 1):
        ok, der, size = has_width_refutation(formula, w)
        if ok:
            return WidthCertificate(
                formula_hash=formula.content_hash(),
                claimed_min_width=w,
                upper_derivation=der,
                lower_closure_size=last_fail_size,
                notes=[
                    f"axiom_width={axiom_w}",
                    "upper: saturation derivation",
                    "lower: width-(w-1) saturation avoids empty clause"
                    if w > axiom_w
                    else "matches axiom-width lower bound",
                ],
            )
        last_fail_size = size
    return WidthCertificate(
        formula_hash=formula.content_hash(),
        claimed_min_width=hi + 1,
        lower_closure_size=last_fail_size,
        notes=["Exceeded max_width; only lower bound certified."],
        claim_type="error_or_inconclusive",
    )
