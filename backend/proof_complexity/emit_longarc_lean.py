"""Emit Lean `LongArcProjection.lean` for n=6 length-2 arc tip-by-tip fold.

Instance: C_6 + chords (0,2),(1,3). Arc [4,5] folds tip-by-tip:
  G0 Closure₃ size 92 → G1 size 42 → R size 16.
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
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm

OUT = Path("lean/PNPLab/LongArcProjection.lean")

N = 6
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


def payload() -> dict:
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

    stages_ax: list[list[tuple[int, ...]]] = []
    stages_cl: list[list[tuple[int, ...]]] = []
    stages_v: list[list[int]] = []

    ax = xor_axioms(work, charges, e_index)
    stages_ax.append(ax)
    stages_cl.append(closure_of(ax))
    stages_v.append(edge_vars(work, e_index))

    for i, arc in enumerate(arcs):
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            ax = xor_axioms(work, charges, e_index)
            stages_ax.append(ax)
            stages_cl.append(closure_of(ax))
            stages_v.append(edge_vars(work, e_index))

    assert len(stages_cl) == 3
    assert [len(c) for c in stages_cl] == [92, 42, 16]
    for i in range(2):
        vv = set(stages_v[i + 1])
        missing = [
            c
            for c in stages_cl[i]
            if c and all(abs(lit) in vv for lit in c) and c not in stages_cl[i + 1]
        ]
        assert not missing
    return {
        "ax0": stages_ax[0],
        "cl0": stages_cl[0],
        "ax1": stages_ax[1],
        "cl1": stages_cl[1],
        "axR": stages_ax[2],
        "clR": stages_cl[2],
        "v1": stages_v[1],
        "vR": stages_v[2],
    }


def pack_block(pre: str, axioms_name: str, closed_name: str) -> str:
    return f"""
theorem {pre}_closed_bool : laClosedUnder {closed_name} 3 laPivots = true := by
  native_decide

theorem {pre}_lits_in_pivots :
    ({closed_name}.all fun C => C.all fun lit => decide (lit ∈ laPivots)) = true := by
  native_decide

theorem {pre}_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {closed_name}) (hRes : resolveOriented C D p = some R) :
    p ∈ laPivots := by
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
    exact la_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot hC hRes)

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide
"""


def main() -> int:
    d = payload()
    pivots = (
        "[-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]"
    )
    v1 = "[" + ", ".join(str(v) for v in d["v1"]) + "]"
    vR = "[" + ", ".join(str(v) for v in d["vR"]) + "]"
    body = f"""/-
  Length-2 arc tip-by-tip projection chain (n=6 crossing).

  Instance: C_6 + chords (0,2),(1,3). Open arc [4,5]:
    G0 Closure₃ size {len(d['cl0'])}
    → G1 Closure₃ size {len(d['cl1'])} (after tip 4)
    → R  Closure₃ size {len(d['clR'])} (after tip 5 = residual K₄).
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit("laG0Axioms", d["ax0"])}

{list_lit("laG0Closed", d["cl0"])}

{list_lit("laG1Axioms", d["ax1"])}

{list_lit("laG1Closed", d["cl1"])}

{list_lit("laRAxioms", d["axR"])}

abbrev laRClosed : List Clause := laRAxioms

def laPivots : List Lit := {pivots}

def laV1 : List Nat := {v1}

def laVres : List Nat := {vR}

def laClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem la_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : laClosedUnder S w pivots = true)
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
{pack_block("laG0", "laG0Axioms", "laG0Closed")}
{pack_block("laG1", "laG1Axioms", "laG1Closed")}
{pack_block("laR", "laRAxioms", "laRClosed")}

def laProj01OK : Bool :=
  laG0Closed.all fun C =>
    !(supportedOn C laV1) || laG1Closed.contains C

def laProj1ROK : Bool :=
  laG1Closed.all fun C =>
    !(supportedOn C laVres) || laRClosed.contains C

def laProj0ROK : Bool :=
  laG0Closed.all fun C =>
    !(supportedOn C laVres) || laRClosed.contains C

theorem laProj01OK_true : laProj01OK = true := by native_decide
theorem laProj1ROK_true : laProj1ROK = true := by native_decide
theorem laProj0ROK_true : laProj0ROK = true := by native_decide

theorem la_supported_01
    {{C : Clause}} (hG : C ∈ laG0Closed) (hsup : supportedOn C laV1 = true) :
    C ∈ laG1Closed := by
  have hall := (List.all_eq_true.mp laProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem la_supported_1R
    {{C : Clause}} (hG : C ∈ laG1Closed) (hsup : supportedOn C laVres = true) :
    C ∈ laRClosed := by
  have hall := (List.all_eq_true.mp laProj1ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem la_supported_0R
    {{C : Clause}} (hG : C ∈ laG0Closed) (hsup : supportedOn C laVres = true) :
    C ∈ laRClosed := by
  have hall := (List.all_eq_true.mp laProj0ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def laStep01 : EliminationStep 3 where
  before := laG0Closure
  after := laG1Closure
  V_after := laV1
  preserves := fun _ hB hsup => la_supported_01 hB hsup

def laStep1R : EliminationStep 3 where
  before := laG1Closure
  after := laRClosure
  V_after := laVres
  preserves := fun _ hB hsup => la_supported_1R hB hsup

def laEliminationChain : EliminationChain 3 where
  steps := [laStep01, laStep1R]
  certDoc := "lean/PNPLab/LongArcProjection.lean"

theorem laNest : varsSubset laVres laV1 = true := by native_decide

/-- G0 → R via composeElimination (Vres ⊆ V1). -/
def laProjection : ProjectionInclusion 3 :=
  composeProjection laStep01 laStep1R rfl laNest

theorem la_no_empty_of_projection :
    ¬ laProjection.gClosure.mem [] :=
  no_empty_of_projection laProjection laR_no_empty

def laDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(
        f"wrote {OUT} |G0|={len(d['cl0'])} |G1|={len(d['cl1'])} |R|={len(d['clR'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
