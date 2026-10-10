"""Emit Lean `MultiFoldProjection.lean` for n=6 two-arc path-fold chain.

Instance: C_6 + chords (0,3),(2,5). Fold sequence:
  G0 (Closure₃ size 68) → G1 (42) → R (16 residual K₄ XORs).

Each step has ProjectionInclusion / EliminationStep; chain has both steps.
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

OUT = Path("lean/PNPLab/MultiFoldProjection.lean")

N = 6
C1 = (0, 3)
C2 = (2, 5)


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


def xor_axioms(work, charges, e_index) -> list[tuple[int, ...]]:
    axs: list[tuple[int, ...]] = []
    for v in sorted(work.nodes()):
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return sorted(axs, key=lambda c: (len(c), c))


def edge_vars(work, e_index) -> list[int]:
    return sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )


def closure_of(axioms: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    return sorted(_width_closure_clauses(form, 3), key=lambda c: (len(c), c))


def multifold_payload() -> dict:
    charges0 = _odd_charge_for_crossing(N, C1, C2)
    g0 = nx.cycle_graph(N)
    g0.add_edges_from([C1, C2])
    ends, arcs = crossing_branch_sets(N, C1, C2)
    e_index = _edge_var_map(g0)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)

    ax0 = xor_axioms(work, charges, e_index)
    cl0 = closure_of(ax0)
    v0 = edge_vars(work, e_index)

    # First nonempty arc
    folded = 0
    v_after_steps: list[list[int]] = []
    stages_ax = [ax0]
    stages_cl = [cl0]
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
        ax = xor_axioms(work, charges, e_index)
        cl = closure_of(ax)
        vv = edge_vars(work, e_index)
        v_after_steps.append(vv)
        stages_ax.append(ax)
        stages_cl.append(cl)
        folded += 1

    assert folded == 2
    assert len(stages_cl[0]) == 68
    assert len(stages_cl[1]) == 42
    assert len(stages_cl[2]) == 16
    assert () not in stages_cl[0] and () not in stages_cl[1] and () not in stages_cl[2]

    # Projection checks
    for i in range(2):
        v_next = set(v_after_steps[i])
        missing = [
            c
            for c in stages_cl[i]
            if c and all(abs(lit) in v_next for lit in c) and c not in stages_cl[i + 1]
        ]
        assert not missing, (i, missing[:3])

    return {
        "ax0": stages_ax[0],
        "cl0": stages_cl[0],
        "ax1": stages_ax[1],
        "cl1": stages_cl[1],
        "axR": stages_ax[2],
        "clR": stages_cl[2],
        "v1": v_after_steps[0],
        "vR": v_after_steps[1],
        "v0": v0,
        "ends": ends,
        "arcs": arcs,
    }


def pack_closure_block(pre: str, axioms_name: str, closed_name: str) -> str:
    """Shared WidthClosure boilerplate for a stage."""
    return f"""
theorem {pre}_closed_bool : mfClosedUnder {closed_name} 3 mfPivots = true := by
  native_decide

theorem {pre}_lits_in_pivots :
    ({closed_name}.all fun C => C.all fun lit => decide (lit ∈ mfPivots)) = true := by
  native_decide

theorem {pre}_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {closed_name}) (hRes : resolveOriented C D p = some R) :
    p ∈ mfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp {pre}_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def {pre}Closure : WidthClosure 3 where
  axioms := {axioms_name}
  mem := fun C => C ∈ {closed_name}
  axiom_mem := by
    intro C hC _
    have h : ({axioms_name}.all fun A => {closed_name}.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact mf_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot hC hRes)

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide
"""


def main() -> int:
    d = multifold_payload()
    pivots = (
        "[-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"
    )
    v1 = "[" + ", ".join(str(v) for v in d["v1"]) + "]"
    vR = "[" + ", ".join(str(v) for v in d["vR"]) + "]"

    body = f"""/-
  Two-arc path-fold projection chain (n=6 crossing).

  Instance: C_6 + chords (0,3),(2,5). Open arcs fold tip-by-tip:
    G0 Closure₃ size {len(d['cl0'])}
    → G1 Closure₃ size {len(d['cl1'])}
    → R  Closure₃ size {len(d['clR'])} (residual K₄ XOR axioms).

  Each hop is a ProjectionInclusion / EliminationStep; the chain is the
  first multi-arc EliminationChain instance in the lab.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit("mfG0Axioms", d["ax0"])}

{list_lit("mfG0Closed", d["cl0"])}

{list_lit("mfG1Axioms", d["ax1"])}

{list_lit("mfG1Closed", d["cl1"])}

{list_lit("mfRAxioms", d["axR"])}

abbrev mfRClosed : List Clause := mfRAxioms

def mfPivots : List Lit := {pivots}

def mfV1 : List Nat := {v1}

def mfVres : List Nat := {vR}

def mfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem mf_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : mfClosedUnder S w pivots = true)
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
{pack_closure_block("mfG0", "mfG0Axioms", "mfG0Closed")}
{pack_closure_block("mfG1", "mfG1Axioms", "mfG1Closed")}
{pack_closure_block("mfR", "mfRAxioms", "mfRClosed")}

def mfProj01OK : Bool :=
  mfG0Closed.all fun C =>
    !(supportedOn C mfV1) || mfG1Closed.contains C

def mfProj1ROK : Bool :=
  mfG1Closed.all fun C =>
    !(supportedOn C mfVres) || mfRClosed.contains C

def mfProj0ROK : Bool :=
  mfG0Closed.all fun C =>
    !(supportedOn C mfVres) || mfRClosed.contains C

theorem mfProj01OK_true : mfProj01OK = true := by native_decide
theorem mfProj1ROK_true : mfProj1ROK = true := by native_decide
theorem mfProj0ROK_true : mfProj0ROK = true := by native_decide

theorem mf_supported_01
    {{C : Clause}} (hG : C ∈ mfG0Closed) (hsup : supportedOn C mfV1 = true) :
    C ∈ mfG1Closed := by
  have hall := (List.all_eq_true.mp mfProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem mf_supported_1R
    {{C : Clause}} (hG : C ∈ mfG1Closed) (hsup : supportedOn C mfVres = true) :
    C ∈ mfRClosed := by
  have hall := (List.all_eq_true.mp mfProj1ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem mf_supported_0R
    {{C : Clause}} (hG : C ∈ mfG0Closed) (hsup : supportedOn C mfVres = true) :
    C ∈ mfRClosed := by
  have hall := (List.all_eq_true.mp mfProj0ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def mfStep01 : EliminationStep 3 where
  before := mfG0Closure
  after := mfG1Closure
  V_after := mfV1
  preserves := fun _ hB hsup => mf_supported_01 hB hsup

def mfStep1R : EliminationStep 3 where
  before := mfG1Closure
  after := mfRClosure
  V_after := mfVres
  preserves := fun _ hB hsup => mf_supported_1R hB hsup

def mfEliminationChain : EliminationChain 3 where
  steps := [mfStep01, mfStep1R]
  certDoc := "lean/PNPLab/MultiFoldProjection.lean"

theorem mfNest : varsSubset mfVres mfV1 = true := by native_decide

/-- G0 → R via composeElimination (Vres ⊆ V1). -/
def mfProjection : ProjectionInclusion 3 :=
  composeProjection mfStep01 mfStep1R rfl mfNest

theorem mf_no_empty_of_projection :
    ¬ mfProjection.gClosure.mem [] :=
  no_empty_of_projection mfProjection mfR_no_empty

def mfDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(
        f"wrote {OUT} |G0|={len(d['cl0'])} |G1|={len(d['cl1'])} |R|={len(d['clR'])} "
        f"V1={d['v1']} Vres={d['vR']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
