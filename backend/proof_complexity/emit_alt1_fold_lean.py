"""Emit Lean `Alt1FoldProjection.lean`: fresh G₀→R for non-pack alt1.

Instance: C_5 + chords (0,2),(1,4) — same hop-1 shape as ofold (42→16)
but distinct chords / global edge vars. Residual `alt1R*` already lives in
`AltResidualWitnesses.lean`; this emitter only packages Closure₃(G₀) + projection.
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
from backend.proof_complexity.emit_crossing_residual_catalog import residual_of
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.path_fold import fold_open_arc_internals
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/Alt1FoldProjection.lean")

N = 5
C1 = (0, 2)
C2 = (1, 4)
PRE = "alt1G"


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


def alt1g_payload() -> tuple[
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
    assert len(cl_g) == 42 and len(cl_res) == 16
    proj = {c for c in cl_g if c and all(abs(lit) in res_vars for lit in c)}
    assert proj <= set(cl_res)

    # Must match AltResidualWitnesses residual_of labeling.
    cat = residual_of(N, C1, C2)
    assert set(map(tuple, cat["RAxioms"])) == set(cl_res)
    assert list(cat["Vres"]) == res_vars
    return axioms_g, cl_g, cl_res, res_vars


def main() -> int:
    axioms_g, cl_g, _cl_res, res_vars = alt1g_payload()
    pivots = "[-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"
    vres = "[" + ", ".join(str(v) for v in res_vars) + "]"
    body = f"""/-
  Fresh G₀→R for non-pack alt1: C_5 + chords (0,2),(1,4).

  Machine fact: Closure₃(G) has size {len(cl_g)} and excludes □; residual
  `alt1RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `alt1RClosed`.

  Beyond pack-canonical ofold (chords (0,2),(1,3)): same |G|→|R| shape,
  distinct global `_edge_var_map` labeling.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.AltResidualClosures

namespace PNPLab.Resolution

{list_lit(PRE + "Axioms", axioms_g)}

{list_lit(PRE + "Closed", cl_g)}

/-- Pivot range covering all alt1 G₀ literals. -/
def {PRE}Pivots : List Lit := {pivots}

/-- Residual vars (must match `alt1Vres`). -/
def {PRE}Vres : List Nat := {vres}

theorem {PRE}Vres_eq_alt1 : {PRE}Vres = alt1Vres := by native_decide

def {PRE}ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem {PRE}_closed_bool : {PRE}ClosedUnder {PRE}Closed 3 {PRE}Pivots = true := by
  native_decide

theorem {PRE}_lits_in_pivots :
    ({PRE}Closed.all fun C => C.all fun lit => decide (lit ∈ {PRE}Pivots)) = true := by
  native_decide

theorem {PRE}_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {PRE}Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ {PRE}Pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {PRE}_lits_in_pivots) C hC
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

def {PRE}Closure : WidthClosure 3 where
  axioms := {PRE}Axioms
  mem := fun C => C ∈ {PRE}Closed
  axiom_mem := by
    intro C hC _
    have h : ({PRE}Axioms.all fun A => {PRE}Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact {PRE}_mem_of_closed {PRE}_closed_bool hC hD hRes hw ({PRE}_pivot hC hRes)

theorem {PRE}_no_empty : ¬ {PRE}Closure.mem [] := by
  simp [{PRE}Closure]
  native_decide

def {PRE}ProjOK : Bool :=
  {PRE}Closed.all fun C =>
    !(supportedOn C alt1Vres) || alt1RClosed.contains C

theorem {PRE}ProjOK_true : {PRE}ProjOK = true := by native_decide

theorem {PRE}_supported_in_R
    {{C : Clause}} (hG : C ∈ {PRE}Closed) (hsup : supportedOn C alt1Vres = true) :
    C ∈ alt1RClosed := by
  have hall := (List.all_eq_true.mp {PRE}ProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

/-- Fresh instance G₀ → residual R (beyond pack routing / R→R self-proj). -/
def {PRE}Projection : ProjectionInclusion 3 where
  gClosure := {PRE}Closure
  rClosure := alt1RClosure
  Vres := alt1Vres
  holds := fun _ hG hsup => {PRE}_supported_in_R hG hsup

def {PRE}EliminationStep : EliminationStep 3 where
  before := {PRE}Closure
  after := alt1RClosure
  V_after := alt1Vres
  preserves := fun _ hB hsup => {PRE}_supported_in_R hB hsup

theorem {PRE}_no_empty_of_projection :
    ¬ {PRE}Projection.gClosure.mem [] :=
  no_empty_of_projection {PRE}Projection alt1R_closure_no_empty

/-- Fresh G₀→R beyond packs, with residual ≅ template residualAxioms. -/
theorem alt1_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt1TopologyRename alt1RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt1GProjection.gClosure.mem [] :=
  ⟨(alt1_global_edge_iso_to_residualAxioms e).1,
    (alt1_global_edge_iso_to_residualAxioms e).2,
    alt1G_no_empty_of_projection⟩

def {PRE}Doc : String :=
  "fresh G₀ Closure₃ for alt1; ProjectionInclusion beyond packs"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} |G|={len(cl_g)} axioms_g={len(axioms_g)} Vres={res_vars}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
