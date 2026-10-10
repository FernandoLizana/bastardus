"""Emit Lean `OneFoldProjection.lean` for n=5 crossing one-fold G→residual K₄.

Instance: C_5 + chords (0,2),(1,3). Uses width-3 normalized closures
(G: 42 clauses, R: 16 = residual XOR axioms) after `resolveOriented` normalizes
and rejects tautological resolvents.
"""

from __future__ import annotations

from pathlib import Path

import networkx as nx

from backend.models.cnf import CNFFormula
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.path_fold import fold_open_arc_internals
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/OneFoldProjection.lean")

# Fixed small instance (one open arc of length 1 on an otherwise K₄ skeleton).
N = 5
C1 = (0, 2)
C2 = (1, 3)


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


def ofold_payload() -> tuple[
    list[tuple[int, ...]], list[tuple[int, ...]], list[tuple[int, ...]], list[int]
]:
    charges0 = _odd_charge_for_crossing(N, C1, C2)
    g0 = nx.cycle_graph(N)
    g0.add_edges_from([C1, C2])
    form_g = tseitin_cnf(
        GraphInstance(g0, tuple(charges0[v] for v in range(N)), "G", 0, {})
    )
    cl_g = sorted(_width_closure_clauses(form_g, 3), key=lambda c: (len(c), c))

    e_index = _edge_var_map(g0)
    ends, arcs = crossing_branch_sets(N, C1, C2)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)
    for i, arc in enumerate(arcs):
        if not arc:
            continue
        fold_open_arc_internals(
            builder,
            work,
            charges,
            e_index,
            ends[i],
            list(arc),
            ends[(i + 1) % 4],
        )
    residual_axioms: list[tuple[int, ...]] = []
    for v in ends:
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in residual_axioms:
                residual_axioms.append(n)
    form_res = CNFFormula.from_clauses(
        [list(c) for c in residual_axioms],
        num_variables=max((abs(lit) for c in residual_axioms for lit in c), default=1),
    )
    cl_res = sorted(_width_closure_clauses(form_res, 3), key=lambda c: (len(c), c))
    res_vars = sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )

    axioms_g: list[tuple[int, ...]] = []
    for cl in form_g.clauses:
        n = _norm(list(cl.literals))
        if n is not None and n not in axioms_g:
            axioms_g.append(n)
    axioms_g = sorted(axioms_g, key=lambda c: (len(c), c))

    assert () not in cl_g and () not in cl_res
    assert len(cl_res) == 16
    proj = {c for c in cl_g if c and all(abs(lit) in res_vars for lit in c)}
    assert proj <= set(cl_res)
    return axioms_g, cl_g, cl_res, res_vars


def main() -> int:
    axioms_g, cl_g, cl_res, res_vars = ofold_payload()
    pre = "ofold"
    pivots = "[-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]"
    vres = "[" + ", ".join(str(v) for v in res_vars) + "]"
    body = f"""/-
  One-fold crossing projection: C_5 + chords (0,2),(1,3) → residual K₄.

  Machine fact: Closure₃(G) has size {len(cl_g)} and excludes □; residual XOR
  Closure₃(R) has size {len(cl_res)} (= axioms) and excludes □; every Closure₃(G)
  clause supported on residual edge vars lies in Closure₃(R).

  Relies on `resolveOriented` rejecting tautological resolvents and normalizing
  survivors (same as Python `_norm` / width saturation).
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit(pre + "GAxioms", axioms_g)}

{list_lit(pre + "GClosed", cl_g)}

{list_lit(pre + "RAxioms", cl_res)}

/-- Residual width-3 closure equals residual XOR axioms. -/
abbrev {pre}RClosed : List Clause := {pre}RAxioms

def {pre}Pivots : List Lit := {pivots}

def {pre}Vres : List Nat := {vres}

def {pre}ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem {pre}G_closed_bool : {pre}ClosedUnder {pre}GClosed 3 {pre}Pivots = true := by
  native_decide

theorem {pre}R_closed_bool : {pre}ClosedUnder {pre}RClosed 3 {pre}Pivots = true := by
  native_decide

theorem {pre}G_lits_in_pivots :
    ({pre}GClosed.all fun C => C.all fun lit => decide (lit ∈ {pre}Pivots)) = true := by
  native_decide

theorem {pre}R_lits_in_pivots :
    ({pre}RClosed.all fun C => C.all fun lit => decide (lit ∈ {pre}Pivots)) = true := by
  native_decide

theorem {pre}_pivot_G
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {pre}GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ {pre}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {pre}G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem {pre}_pivot_R
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {pre}RClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ {pre}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {pre}R_lits_in_pivots) C hC
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

def {pre}GClosure : WidthClosure 3 where
  axioms := {pre}GAxioms
  mem := fun C => C ∈ {pre}GClosed
  axiom_mem := by
    intro C hC _
    -- every axiom is present in the enumerated Closure₃
    have h : ({pre}GAxioms.all fun A => {pre}GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact {pre}_mem_of_closed {pre}G_closed_bool hC hD hRes hw ({pre}_pivot_G hC hRes)

def {pre}RClosure : WidthClosure 3 where
  axioms := {pre}RAxioms
  mem := fun C => C ∈ {pre}RClosed
  axiom_mem := by
    intro C hC _
    simpa [{pre}RClosed] using hC
  closed := by
    intro C D R p hC hD hRes hw
    exact {pre}_mem_of_closed {pre}R_closed_bool hC hD hRes hw ({pre}_pivot_R hC hRes)

theorem {pre}G_no_empty : ¬ {pre}GClosure.mem [] := by
  simp [{pre}GClosure]
  native_decide

theorem {pre}R_no_empty : ¬ {pre}RClosure.mem [] := by
  simp [{pre}RClosure, {pre}RClosed]
  native_decide

def {pre}ProjOK : Bool :=
  {pre}GClosed.all fun C =>
    !(supportedOn C {pre}Vres) || {pre}RClosed.contains C

theorem {pre}ProjOK_true : {pre}ProjOK = true := by native_decide

theorem {pre}_supported_in_R
    {{C : Clause}} (hG : C ∈ {pre}GClosed) (hsup : supportedOn C {pre}Vres = true) :
    C ∈ {pre}RClosed := by
  have hall := (List.all_eq_true.mp {pre}ProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def {pre}Projection : ProjectionInclusion 3 where
  gClosure := {pre}GClosure
  rClosure := {pre}RClosure
  Vres := {pre}Vres
  holds := fun _ hG hsup => {pre}_supported_in_R hG hsup

def {pre}EliminationStep : EliminationStep 3 where
  before := {pre}GClosure
  after := {pre}RClosure
  V_after := {pre}Vres
  preserves := fun _ hB hsup => {pre}_supported_in_R hB hsup

def {pre}EliminationChain : EliminationChain 3 where
  steps := [{pre}EliminationStep]
  certDoc := "lean/PNPLab/OneFoldProjection.lean"

theorem {pre}_no_empty_of_projection :
    ¬ {pre}Projection.gClosure.mem [] :=
  no_empty_of_projection {pre}Projection {pre}R_no_empty

def {pre}Doc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} |G|={len(cl_g)} |R|={len(cl_res)} axioms_g={len(axioms_g)} Vres={res_vars}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
