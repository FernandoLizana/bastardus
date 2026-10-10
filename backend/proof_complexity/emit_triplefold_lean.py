"""Emit Lean `TripleFoldProjection.lean` for n=7 three-tip path-fold chain.

Instance: C_7 + chords (0,4),(1,5). Tip-by-tip:
  G0 118 → G1 68 → G2 42 → R 16.
Uses composeProjection3.
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

OUT = Path("lean/PNPLab/TripleFoldProjection.lean")

N = 7
C1 = (0, 4)
C2 = (1, 5)


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

    assert [len(c) for c in stages_cl] == [118, 68, 42, 16], [len(c) for c in stages_cl]
    for i in range(3):
        vv = set(stages_v[i + 1])
        missing = [
            c
            for c in stages_cl[i]
            if c and all(abs(lit) in vv for lit in c) and c not in stages_cl[i + 1]
        ]
        assert not missing
    return {
        "axs": stages_ax,
        "cls": stages_cl,
        "vs": stages_v,
    }


def pack_block(pre: str, axioms_name: str, closed_name: str) -> str:
    return f"""
theorem {pre}_closed_bool : tfClosedUnder {closed_name} 3 tfPivots = true := by
  native_decide

theorem {pre}_lits_in_pivots :
    ({closed_name}.all fun C => C.all fun lit => decide (lit ∈ tfPivots)) = true := by
  native_decide

theorem {pre}_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {closed_name}) (hRes : resolveOriented C D p = some R) :
    p ∈ tfPivots := by
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
    exact tf_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot hC hRes)

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide
"""


def hop_proofs() -> str:
    """Projection Bool + supported lemmas for hops 0→1, 1→2, 2→R."""
    hops = [
        ("01", "tfG0Closed", "tfG1Closed", "tfV1"),
        ("12", "tfG1Closed", "tfG2Closed", "tfV2"),
        ("2R", "tfG2Closed", "tfRClosed", "tfVres"),
    ]
    parts: list[str] = []
    for tag, src, dst, v in hops:
        parts.append(
            f"""
def tfProj{tag}OK : Bool :=
  {src}.all fun C =>
    !(supportedOn C {v}) || {dst}.contains C

theorem tfProj{tag}OK_true : tfProj{tag}OK = true := by native_decide

theorem tf_supported_{tag}
    {{C : Clause}} (hG : C ∈ {src}) (hsup : supportedOn C {v} = true) :
    C ∈ {dst} := by
  have hall := (List.all_eq_true.mp tfProj{tag}OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h
"""
        )
    return "\n".join(parts)


def main() -> int:
    d = payload()
    max_var = max(d["vs"][0]) if d["vs"][0] else 9
    piv = ", ".join(str(i) for i in range(-max_var - 1, max_var + 2))
    pivots = f"[{piv}]"
    v1 = "[" + ", ".join(str(v) for v in d["vs"][1]) + "]"
    v2 = "[" + ", ".join(str(v) for v in d["vs"][2]) + "]"
    vR = "[" + ", ".join(str(v) for v in d["vs"][3]) + "]"

    body = f"""/-
  Three-tip path-fold projection chain (n=7 crossing).

  Instance: C_7 + chords (0,4),(1,5):
    G0 Closure₃ size {len(d['cls'][0])}
    → G1 size {len(d['cls'][1])}
    → G2 size {len(d['cls'][2])}
    → R  size {len(d['cls'][3])} (residual K₄).

  Projection G0→R via `composeProjection3`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{list_lit("tfG0Axioms", d["axs"][0])}

{list_lit("tfG0Closed", d["cls"][0])}

{list_lit("tfG1Axioms", d["axs"][1])}

{list_lit("tfG1Closed", d["cls"][1])}

{list_lit("tfG2Axioms", d["axs"][2])}

{list_lit("tfG2Closed", d["cls"][2])}

{list_lit("tfRAxioms", d["axs"][3])}

abbrev tfRClosed : List Clause := tfRAxioms

def tfPivots : List Lit := {pivots}

def tfV1 : List Nat := {v1}

def tfV2 : List Nat := {v2}

def tfVres : List Nat := {vR}

def tfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem tf_mem_of_closed
    {{S : List Clause}} {{w : Nat}} {{pivots : List Lit}}
    (hbool : tfClosedUnder S w pivots = true)
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
{pack_block("tfG0", "tfG0Axioms", "tfG0Closed")}
{pack_block("tfG1", "tfG1Axioms", "tfG1Closed")}
{pack_block("tfG2", "tfG2Axioms", "tfG2Closed")}
{pack_block("tfR", "tfRAxioms", "tfRClosed")}
{hop_proofs()}

def tfStep01 : EliminationStep 3 where
  before := tfG0Closure
  after := tfG1Closure
  V_after := tfV1
  preserves := fun _ hB hsup => tf_supported_01 hB hsup

def tfStep12 : EliminationStep 3 where
  before := tfG1Closure
  after := tfG2Closure
  V_after := tfV2
  preserves := fun _ hB hsup => tf_supported_12 hB hsup

def tfStep2R : EliminationStep 3 where
  before := tfG2Closure
  after := tfRClosure
  V_after := tfVres
  preserves := fun _ hB hsup => tf_supported_2R hB hsup

def tfEliminationChain : EliminationChain 3 where
  steps := [tfStep01, tfStep12, tfStep2R]
  certDoc := "lean/PNPLab/TripleFoldProjection.lean"

theorem tfNest12 : varsSubset tfV2 tfV1 = true := by native_decide
theorem tfNest2R : varsSubset tfVres tfV2 = true := by native_decide

def tfProjection : ProjectionInclusion 3 :=
  composeProjection3 tfStep01 tfStep12 tfStep2R rfl rfl tfNest12 tfNest2R

theorem tf_no_empty_of_projection :
    ¬ tfProjection.gClosure.mem [] :=
  no_empty_of_projection tfProjection tfR_no_empty

def tfDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(
        f"wrote {OUT} sizes={[len(c) for c in d['cls']]} "
        f"V1={d['vs'][1]} V2={d['vs'][2]} Vres={d['vs'][3]}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
