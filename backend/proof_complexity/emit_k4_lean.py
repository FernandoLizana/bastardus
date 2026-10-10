"""Emit Lean `K4Width3.lean` for odd-charge K₄ WidthClosure at w=3."""

from __future__ import annotations

from pathlib import Path

import networkx as nx

from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/K4Width3.lean")


def lean_clause(c: tuple[int, ...]) -> str:
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


def odd_k4_axioms() -> list[tuple[int, ...]]:
    g = nx.complete_graph(4)
    form = tseitin_cnf(
        GraphInstance(g, tuple(1 if i == 0 else 0 for i in range(4)), "K4", 0, {})
    )
    axioms: list[tuple[int, ...]] = []
    for cl in form.clauses:
        n = _norm(list(cl.literals))
        if n is not None and n not in axioms:
            axioms.append(n)
    return axioms


def main() -> int:
    axioms = odd_k4_axioms()
    assert len(axioms) == 16
    pre = "k4"
    pivots = "[-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]"
    body = f"""/-
  Odd-charge K₄ Tseitin as a width-3 closure (Category C).

  Machine fact: Closure₃(T(K₄, odd)) has size 16 = #axioms and excludes □;
  Width = 4 (empty appears only at width 4). Packaged for ProjectionInclusion.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit(pre + "Axioms", axioms)}

/-- At width 3 the saturated set equals the axiom list (no □). -/
abbrev {pre}Closed : List Clause := {pre}Axioms

def {pre}Pivots : List Lit := {pivots}

def {pre}ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem {pre}_closed_bool : {pre}ClosedUnder {pre}Closed 3 {pre}Pivots = true := by
  native_decide

theorem {pre}_lits_in_pivots :
    ({pre}Closed.all fun C => C.all fun lit => decide (lit ∈ {pre}Pivots)) = true := by
  native_decide

theorem {pre}_pivot_in
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {pre}Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ {pre}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {pre}_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem {pre}_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : {pre}ClosedUnder S w pivots = true)
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

def {pre}Closure : WidthClosure 3 where
  axioms := {pre}Axioms
  mem := fun C => C ∈ {pre}Closed
  axiom_mem := by
    intro C hC _
    -- axioms ≡ closed
    simpa [{pre}Closed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact {pre}_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot_in hC hRes)

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure, {pre}Closed, {pre}Axioms]

/-- Self-projection of the K₄ width-3 closure (restriction lemma instance). -/
def {pre}SelfProjection : ProjectionInclusion 3 :=
  selfProjection 3 {pre}Closure [1, 2, 3, 4, 5, 6]

theorem {pre}_no_empty_of_self_projection :
    ¬ {pre}SelfProjection.gClosure.mem [] :=
  no_empty_of_projection {pre}SelfProjection {pre}_no_empty

def {pre}EliminationChain : EliminationChain 3 where
  steps := [identityElimination 3 {pre}Closure [1, 2, 3, 4, 5, 6]]
  certDoc := "lean/PNPLab/K4Width3.lean"

def {pre}LowerBoundDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/LIFT_K4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} axioms={len(axioms)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
