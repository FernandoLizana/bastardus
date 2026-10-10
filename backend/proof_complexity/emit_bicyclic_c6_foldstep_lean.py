"""Emit Lean `BicyclicC6FoldStep.lean`.

Concrete θ hop: C6 + chord (0,2), fold triangle tip 1.
Uses width-3 saturation that **stops at □** (same as projection packs),
not full post-□ upper-bound saturation.
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

from backend.models.cnf import CNFFormula
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.emit_bicyclic_lean import list_lit
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/BicyclicC6FoldStep.lean")
REPORT = Path("reports/discovery/bicyclic_c6_foldstep_projection_check.json")
PRE = "bi6f"


def xor_axioms(work: nx.Graph, charges: dict[int, int], e_index: dict[tuple[int, int], int]):
    axs: list[tuple[int, ...]] = []
    for v in sorted(work.nodes()):
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return sorted(axs, key=lambda c: (len(c), c))


def proj_closure(axioms: list[tuple[int, ...]], width: int = 3) -> list[tuple[int, ...]]:
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    return sorted(_width_closure_clauses(form, width), key=lambda c: (len(c), c))


def main() -> int:
    g0 = nx.cycle_graph(6)
    g0.add_edge(0, 2)
    charges0 = {i: int(i == 0) for i in range(6)}
    e_index = _edge_var_map(g0)

    before_axioms = xor_axioms(g0, charges0, e_index)
    before_closed = proj_closure(before_axioms, 3)

    builder = _ProofBuilder(_all_axioms(g0, charges0, e_index), delta=3)
    work = g0.copy()
    charges = dict(charges0)
    fold_deg2_tip(builder, work, charges, e_index, 1)

    after_axioms = xor_axioms(work, charges, e_index)
    after_closed = proj_closure(after_axioms, 3)
    v_after = sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )

    missing = [
        c
        for c in before_closed
        if all(abs(lit) in set(v_after) for lit in c) and c not in after_closed
    ]
    report = {
        "mode": "stop_at_empty_projection_closures",
        "before_size": len(before_closed),
        "after_size": len(after_closed),
        "before_has_empty": () in before_closed,
        "after_has_empty": () in after_closed,
        "v_after": v_after,
        "missing_count": len(missing),
        "missing_sample": [list(c) for c in missing[:20]],
        "ok": len(missing) == 0,
    }
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        f"wrote {REPORT} ok={report['ok']} missing={len(missing)} "
        f"before={len(before_closed)} after={len(after_closed)} "
        f"empty_b={report['before_has_empty']} empty_a={report['after_has_empty']}"
    )
    if missing:
        return 1

    max_var = max(
        (abs(lit) for c in before_closed + after_closed for lit in c),
        default=1,
    )
    pivots = "[" + ", ".join(str(i) for i in range(-max_var - 1, max_var + 2)) + "]"
    v_list = "[" + ", ".join(str(v) for v in v_after) + "]"

    body = f"""/-
  Concrete θ fold step: C₆ + chord (0,2), fold triangle tip 1.

  Closures use stop-at-□ saturation (projection style), not full post-□
  upper-bound packs. See `bicyclic_c6_foldstep_projection_check.json`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit(PRE + "BeforeAxioms", before_axioms)}

{list_lit(PRE + "BeforeClosed", before_closed)}

{list_lit(PRE + "AfterAxioms", after_axioms)}

{list_lit(PRE + "AfterClosed", after_closed)}

def {PRE}Vafter : List Nat := {v_list}

def {PRE}Pivots : List Lit := {pivots}

def {PRE}ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem {PRE}_before_closed_bool :
    {PRE}ClosedUnder {PRE}BeforeClosed 3 {PRE}Pivots = true := by
  native_decide

theorem {PRE}_after_closed_bool :
    {PRE}ClosedUnder {PRE}AfterClosed 3 {PRE}Pivots = true := by
  native_decide

theorem {PRE}_before_lits_in_pivots :
    ({PRE}BeforeClosed.all fun C => C.all fun lit => decide (lit ∈ {PRE}Pivots)) = true := by
  native_decide

theorem {PRE}_after_lits_in_pivots :
    ({PRE}AfterClosed.all fun C => C.all fun lit => decide (lit ∈ {PRE}Pivots)) = true := by
  native_decide

theorem {PRE}_before_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {PRE}BeforeClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ {PRE}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {PRE}_before_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem {PRE}_after_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {PRE}AfterClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ {PRE}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {PRE}_after_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem {PRE}_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : {PRE}ClosedUnder S w pivots = true)
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

def {PRE}BeforeClosure : WidthClosure 3 where
  axioms := {PRE}BeforeAxioms
  mem := fun C => C ∈ {PRE}BeforeClosed
  axiom_mem := by
    intro C hC _
    have h : ({PRE}BeforeAxioms.all fun A => {PRE}BeforeClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact {PRE}_mem_of_closed {PRE}_before_closed_bool hC hD hRes hw
      ({PRE}_before_pivot hC hRes)

def {PRE}AfterClosure : WidthClosure 3 where
  axioms := {PRE}AfterAxioms
  mem := fun C => C ∈ {PRE}AfterClosed
  axiom_mem := by
    intro C hC _
    have h : ({PRE}AfterAxioms.all fun A => {PRE}AfterClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact {PRE}_mem_of_closed {PRE}_after_closed_bool hC hD hRes hw
      ({PRE}_after_pivot hC hRes)

def {PRE}ProjectionOK : Bool :=
  {PRE}BeforeClosed.all fun C =>
    !(supportedOn C {PRE}Vafter) || {PRE}AfterClosed.contains C

theorem {PRE}ProjectionOK_true : {PRE}ProjectionOK = true := by
  native_decide

theorem {PRE}_supported
    {{C : Clause}} (hG : C ∈ {PRE}BeforeClosed)
    (hsup : supportedOn C {PRE}Vafter = true) :
    C ∈ {PRE}AfterClosed := by
  have hall := (List.all_eq_true.mp {PRE}ProjectionOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def {PRE}Step : EliminationStep 3 where
  before := {PRE}BeforeClosure
  after := {PRE}AfterClosure
  V_after := {PRE}Vafter
  preserves := fun _ hB hsup => {PRE}_supported hB hsup

def {PRE}Projection : ProjectionInclusion 3 := {PRE}Step.toProjection

def {PRE}Doc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/INDUCTION_WIDTH_EQ_DELTA.md"

end PNPLab.Resolution
"""

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} before={len(before_closed)} after={len(after_closed)} V={v_after}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
