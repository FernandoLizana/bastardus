"""Emit Lean `BicyclicWidth3.lean`: C₄+chord UpperBound Width≤3 (□ ∈ Closure₃).

Uses full width-3 saturation (continues after empty) so the enumerated set
is closed under sound Lean `resolveOriented`.
"""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path

import networkx as nx

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm, resolve

OUT = Path("lean/PNPLab/BicyclicWidth3.lean")


def lean_clause(c: tuple[int, ...] | list[int]) -> str:
    if not c:
        return "[]"
    return "[" + ", ".join(f"({lit} : Lit)" for lit in c) + "]"


def list_lit(name: str, clauses: list[tuple[int, ...]]) -> str:
    lines = [f"def {name} : List Clause :="]
    for i, c in enumerate(clauses):
        pref = "  [ " if i == 0 else "  , "
        lines.append(pref + lean_clause(c))
    lines.append("  ]")
    return "\n".join(lines)


def full_width_closure(formula, width: int) -> set[tuple[int, ...]]:
    clauses: set[tuple[int, ...]] = set()
    by_lit: dict[int, set[tuple[int, ...]]] = defaultdict(set)

    def add(c: tuple[int, ...]) -> None:
        if c in clauses:
            return
        clauses.add(c)
        for lit in c:
            by_lit[lit].add(c)

    for clause in formula.clauses:
        n = _norm(clause.literals)
        if n is not None and len(n) <= width:
            add(n)

    pending = list(clauses)
    while pending:
        a = pending.pop()
        partners: set[tuple[int, ...]] = set()
        for lit in a:
            partners |= by_lit.get(-lit, set())
        for b in partners:
            if a == b:
                continue
            r = resolve(a, b)
            if r is None or len(r) > width or r in clauses:
                continue
            add(r)
            pending.append(r)
    return clauses


def main() -> int:
    g = nx.cycle_graph(4)
    g.add_edge(0, 2)
    form = tseitin_cnf(
        GraphInstance(g, (1, 0, 0, 0), "BicyclicC4", 0, {})
    )
    axioms: list[tuple[int, ...]] = []
    for cl in form.clauses:
        n = _norm(list(cl.literals))
        if n is not None and n not in axioms:
            axioms.append(n)
    axioms = sorted(axioms, key=lambda c: (len(c), c))
    closed = sorted(full_width_closure(form, 3), key=lambda c: (len(c), c))
    assert () in closed
    assert len(closed) == 131

    pivots = "[-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]"
    body = f"""/-
  Bicyclic upper bound: C₄ + chord (0,2), odd charge, Width ≤ 3 = Δ.

  Machine: full Closure₃ (continue after □) has size {len(closed)} and
  contains □; axioms size {len(axioms)}. Packaged as WidthClosure with
  `mem []` — dual of K₄ / crossing lower-bound packs.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit("biAxioms", axioms)}

{list_lit("biClosed", closed)}

def biPivots : List Lit := {pivots}

def biClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem bi_closed_bool : biClosedUnder biClosed 3 biPivots = true := by
  native_decide

theorem bi_lits_in_pivots :
    (biClosed.all fun C => C.all fun lit => decide (lit ∈ biPivots)) = true := by
  native_decide

theorem bi_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ biClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ biPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp bi_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem bi_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : biClosedUnder S w pivots = true)
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ S) (hD : D ∈ S)
    (hRes : resolveOriented C D p = some R)
    (hw : clauseWidth R ≤ w)
    (hp : p ∈ pivots) :
    R ∈ S := by
  have hpall := (List.all_eq_true.mp hbool) p hp
  have hCall := (List.all_eq_true.mp hpall) C hC
  have hDall := (List.all_eq_true.mp hCall) D hD
  simp only [hRes] at hDall
  have hnotlt : ¬ w < clauseWidth R := Nat.not_lt.mpr hw
  cases hwidth : decide (w < clauseWidth R) with
  | false =>
    simp only [hwidth, Bool.false_or] at hDall
    exact (List.contains_iff_mem).mp hDall
  | true =>
    exact absurd (of_decide_eq_true hwidth) hnotlt

def biClosure : WidthClosure 3 where
  axioms := biAxioms
  mem := fun C => C ∈ biClosed
  axiom_mem := by
    intro C hC _
    have h : (biAxioms.all fun A => biClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact bi_mem_of_closed bi_closed_bool hC hD hRes hw (bi_pivot hC hRes)

theorem bi_has_empty : biClosure.mem [] := by
  simp [biClosure]
  native_decide

/-- Upper bound: empty at width 3 for this θ-graph (Width ≤ Δ = 3). -/
theorem bi_width_le_delta : biClosure.mem [] := bi_has_empty

def biSelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 biClosure [1, 2, 3, 4, 5]

def biEliminationChain : EliminationChain 3 where
  steps := [identityElimination 3 biClosure [1, 2, 3, 4, 5]]
  certDoc := "lean/PNPLab/BicyclicWidth3.lean"

def biDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} |Closed|={len(closed)} axioms={len(axioms)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
