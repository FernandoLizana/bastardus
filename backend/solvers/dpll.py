"""DPLL SAT solver with unit propagation and pure literal elimination.

Classic Davis–Putnam–Logemann–Loveland procedure
(Davis, Logemann, Loveland, 1962). Completeness holds for classical
propositional CNF; runtime remains exponential in the worst case.
"""

from __future__ import annotations

import time
from collections.abc import Callable
from enum import Enum

from backend.core.metrics import SolverMetrics, measure_resources
from backend.models.cnf import Assignment, CNFFormula, Clause, Literal, Variable
from backend.solvers.base import SATSolver, SolverResult


class BranchingHeuristic(str, Enum):
    FIRST = "first"
    DLIS = "dlis"  # Dynamic Largest Individual Sum (occurrence count)
    RANDOM = "random"


BranchFn = Callable[[list[Clause], set[Variable], int], Literal]


class DPLLSolver(SATSolver):
    """Configurable DPLL with unit prop + pure literal elimination."""

    name = "dpll"

    def __init__(
        self,
        branching: BranchingHeuristic = BranchingHeuristic.DLIS,
        use_unit_propagation: bool = True,
        use_pure_literal: bool = True,
        rng_seed: int = 0,
    ) -> None:
        self.branching = branching
        self.use_unit_propagation = use_unit_propagation
        self.use_pure_literal = use_pure_literal
        self._rng_seed = rng_seed

    def solve(self, formula: CNFFormula, timeout_seconds: float | None = None) -> SolverResult:
        metrics = SolverMetrics(solver_name=self.name)
        deadline = None if timeout_seconds is None else time.perf_counter() + timeout_seconds
        assignment: Assignment = {}
        clauses = [Clause(c.literals) for c in formula.clauses if not c.is_tautology()]
        remaining_vars = set(range(1, formula.num_variables + 1))

        result_sat: bool | None = None
        result_asg: Assignment | None = None

        def branch_literal(cls: list[Clause], vars_left: set[Variable], depth: int) -> Literal:
            if self.branching == BranchingHeuristic.FIRST:
                # Pick first remaining variable positively
                v = min(vars_left)
                return v
            if self.branching == BranchingHeuristic.RANDOM:
                # Deterministic pseudo-random from seed + depth
                ordered = sorted(vars_left)
                idx = (self._rng_seed + depth * 2654435761) % len(ordered)
                return ordered[idx]
            # DLIS: choose literal with most occurrences
            pos_count: dict[Variable, int] = {v: 0 for v in vars_left}
            neg_count: dict[Variable, int] = {v: 0 for v in vars_left}
            for clause in cls:
                for lit in clause:
                    v = abs(lit)
                    if v not in vars_left:
                        continue
                    if lit > 0:
                        pos_count[v] += 1
                    else:
                        neg_count[v] += 1
            best_lit = min(vars_left)
            best_score = -1
            for v in vars_left:
                if pos_count[v] >= best_score:
                    best_score = pos_count[v]
                    best_lit = v
                if neg_count[v] > best_score:
                    best_score = neg_count[v]
                    best_lit = -v
            return best_lit

        def simplify(
            cls: list[Clause], asg: Assignment
        ) -> list[Clause] | None:
            """Apply assignment; return None if conflict (empty clause)."""
            new_cls: list[Clause] = []
            for clause in cls:
                simplified = clause.simplifies(asg)
                if simplified is None:
                    continue
                if len(simplified) == 0:
                    metrics.conflicts += 1
                    return None
                new_cls.append(simplified)
            return new_cls

        def unit_propagate(
            cls: list[Clause], asg: Assignment, vars_left: set[Variable]
        ) -> tuple[list[Clause] | None, Assignment]:
            asg = dict(asg)
            changed = True
            while changed and self.use_unit_propagation:
                changed = False
                units = [c.literals[0] for c in cls if len(c) == 1]
                if not units:
                    break
                for lit in units:
                    v = abs(lit)
                    val = lit > 0
                    if v in asg:
                        if asg[v] != val:
                            metrics.conflicts += 1
                            return None, asg
                        continue
                    asg[v] = val
                    vars_left.discard(v)
                    metrics.unit_propagations += 1
                    metrics.propagations += 1
                    changed = True
                simplified = simplify(cls, asg)
                if simplified is None:
                    return None, asg
                cls = simplified
            return cls, asg

        def pure_literal_elim(
            cls: list[Clause], asg: Assignment, vars_left: set[Variable]
        ) -> tuple[list[Clause] | None, Assignment]:
            if not self.use_pure_literal:
                return cls, asg
            asg = dict(asg)
            appeared_pos: set[Variable] = set()
            appeared_neg: set[Variable] = set()
            for clause in cls:
                for lit in clause:
                    v = abs(lit)
                    if v not in vars_left:
                        continue
                    if lit > 0:
                        appeared_pos.add(v)
                    else:
                        appeared_neg.add(v)
            pure: list[Literal] = []
            for v in list(vars_left):
                in_pos = v in appeared_pos
                in_neg = v in appeared_neg
                if in_pos and not in_neg:
                    pure.append(v)
                elif in_neg and not in_pos:
                    pure.append(-v)
            if not pure:
                return cls, asg
            for lit in pure:
                v = abs(lit)
                if v not in vars_left:
                    continue
                asg[v] = lit > 0
                vars_left.discard(v)
                metrics.pure_literal_eliminations += 1
            simplified = simplify(cls, asg)
            if simplified is None:
                return None, asg
            return simplified, asg

        def dpll(cls: list[Clause], asg: Assignment, vars_left: set[Variable], depth: int) -> bool:
            nonlocal result_sat, result_asg
            if deadline is not None and time.perf_counter() > deadline:
                metrics.timed_out = True
                return False

            cls2, asg2 = unit_propagate(cls, asg, vars_left)
            if cls2 is None:
                return False
            cls2, asg2 = pure_literal_elim(cls2, asg2, vars_left)
            if cls2 is None:
                return False

            if not cls2:
                result_sat = True
                result_asg = dict(asg2)
                for v in vars_left:
                    result_asg.setdefault(v, False)
                return True

            if not vars_left:
                metrics.conflicts += 1
                return False

            lit = branch_literal(cls2, vars_left, depth)
            metrics.record_decision(depth)
            v = abs(lit)
            preferred = lit > 0

            for val in (preferred, not preferred):
                new_asg = dict(asg2)
                new_vars = set(vars_left)
                new_asg[v] = val
                new_vars.discard(v)
                simplified = simplify(cls2, new_asg)
                if simplified is None:
                    metrics.record_backtrack()
                    continue
                if dpll(simplified, new_asg, new_vars, depth + 1):
                    return True
                metrics.record_backtrack()
                if metrics.timed_out:
                    return False
            return False

        with measure_resources(metrics):
            if formula.contains_empty_clause():
                result_sat = False
            elif formula.num_variables == 0 and not formula.clauses:
                result_sat = True
                result_asg = {}
            else:
                ok = dpll(clauses, assignment, remaining_vars, 0)
                if metrics.timed_out:
                    result_sat = None
                elif ok:
                    result_sat = True
                else:
                    result_sat = False

        return SolverResult(result_sat, result_asg, metrics)
