"""Emit Lean `BicyclicC5Width3.lean`: C₅+chord (0,2), Width ≤ 3 = Δ."""

from __future__ import annotations

from pathlib import Path

import networkx as nx

from backend.proof_complexity.bicyclic_full_closure_mass import full_width_closure
from backend.proof_complexity.emit_bicyclic_lean import lean_clause, list_lit
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/BicyclicC5Width3.lean")


def main() -> int:
    g = nx.cycle_graph(5)
    g.add_edge(0, 2)
    form = tseitin_cnf(
        GraphInstance(g, (1, 0, 0, 0, 0), "BicyclicC5", 0, {})
    )
    axioms = []
    for cl in form.clauses:
        n = _norm(list(cl.literals))
        if n is not None and n not in axioms:
            axioms.append(n)
    axioms = sorted(axioms, key=lambda c: (len(c), c))
    closed = sorted(full_width_closure(form, 3), key=lambda c: (len(c), c))
    assert () in closed
    pivots = "[-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7]"
    pre = "bi5"
    body = f"""/-
  Bicyclic upper bound: C₅ + chord (0,2), odd charge, Width ≤ 3 = Δ.
  Full Closure₃ size {len(closed)} contains □.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit(pre + "Axioms", axioms)}

{list_lit(pre + "Closed", closed)}

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

theorem {pre}_pivot
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
    have h : ({pre}Axioms.all fun A => {pre}Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact {pre}_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot hC hRes)

theorem {pre}_has_empty : {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide

theorem {pre}_width_le_delta : {pre}Closure.mem [] := {pre}_has_empty

def {pre}Doc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} |Closed|={len(closed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
