"""Emit Lean `FourFoldProjection.lean` for n=8 four-tip path-fold chain.

Instance: C_8 + chords (0,4),(1,5):
  G0 168 → G1 118 → G2 92 → G3 42 → R 16.
Uses composeProjection4.
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

OUT = Path("lean/PNPLab/FourFoldProjection.lean")
N, C1, C2 = 8, (0, 4), (1, 5)
EXPECTED = [168, 118, 92, 42, 16]
PRE = "ff"


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
    axs, cls, vs = [], [], []
    ax = xor_axioms(work, charges, e_index)
    axs.append(ax)
    cls.append(closure_of(ax))
    vs.append(edge_vars(work, e_index))
    for i, arc in enumerate(arcs):
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            ax = xor_axioms(work, charges, e_index)
            axs.append(ax)
            cls.append(closure_of(ax))
            vs.append(edge_vars(work, e_index))
    assert [len(c) for c in cls] == EXPECTED, [len(c) for c in cls]
    for i in range(4):
        vv = set(vs[i + 1])
        assert not [
            c
            for c in cls[i]
            if c and all(abs(lit) in vv for lit in c) and c not in cls[i + 1]
        ]
    return {"axs": axs, "cls": cls, "vs": vs}


def pack_block(pre: str, axioms_name: str, closed_name: str) -> str:
    return f"""
theorem {pre}_closed_bool : {PRE}ClosedUnder {closed_name} 3 {PRE}Pivots = true := by
  native_decide

theorem {pre}_lits_in_pivots :
    ({closed_name}.all fun C => C.all fun lit => decide (lit ∈ {PRE}Pivots)) = true := by
  native_decide

theorem {pre}_pivot
    {{C D R : Clause}} {{p : Lit}}
    (hC : C ∈ {closed_name}) (hRes : resolveOriented C D p = some R) :
    p ∈ {PRE}Pivots := by
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
    exact {PRE}_mem_of_closed {pre}_closed_bool hC hD hRes hw ({pre}_pivot hC hRes)

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide
"""


def hop(tag: str, src: str, dst: str, v: str) -> str:
    return f"""
def {PRE}Proj{tag}OK : Bool :=
  {src}.all fun C =>
    !(supportedOn C {v}) || {dst}.contains C

theorem {PRE}Proj{tag}OK_true : {PRE}Proj{tag}OK = true := by native_decide

theorem {PRE}_supported_{tag}
    {{C : Clause}} (hG : C ∈ {src}) (hsup : supportedOn C {v} = true) :
    C ∈ {dst} := by
  have hall := (List.all_eq_true.mp {PRE}Proj{tag}OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h
"""


def main() -> int:
    d = payload()
    max_var = max(d["vs"][0]) if d["vs"][0] else 12
    pivots = "[" + ", ".join(str(i) for i in range(-max_var - 1, max_var + 2)) + "]"
    vlists = [
        "[" + ", ".join(str(v) for v in d["vs"][i]) + "]" for i in range(1, 5)
    ]
    names = [
        ("G0", d["axs"][0], d["cls"][0]),
        ("G1", d["axs"][1], d["cls"][1]),
        ("G2", d["axs"][2], d["cls"][2]),
        ("G3", d["axs"][3], d["cls"][3]),
        ("R", d["axs"][4], d["cls"][4]),
    ]
    lists = "\n\n".join(
        list_lit(f"{PRE}{n}Axioms", ax) + "\n\n" + list_lit(f"{PRE}{n}Closed", cl)
        if n != "R"
        else list_lit(f"{PRE}RAxioms", ax)
        for n, ax, cl in names
    )
    # R closed: rewrite last - cleaner
    lists = "\n\n".join(
        [
            list_lit(f"{PRE}G0Axioms", d["axs"][0]),
            list_lit(f"{PRE}G0Closed", d["cls"][0]),
            list_lit(f"{PRE}G1Axioms", d["axs"][1]),
            list_lit(f"{PRE}G1Closed", d["cls"][1]),
            list_lit(f"{PRE}G2Axioms", d["axs"][2]),
            list_lit(f"{PRE}G2Closed", d["cls"][2]),
            list_lit(f"{PRE}G3Axioms", d["axs"][3]),
            list_lit(f"{PRE}G3Closed", d["cls"][3]),
            list_lit(f"{PRE}RAxioms", d["axs"][4]),
        ]
    )
    body = f"""/-
  Four-tip path-fold projection chain (n=8 crossing).

  Instance: C_8 + chords (0,4),(1,5):
    {' → '.join(str(s) for s in EXPECTED)} (Closure₃ sizes).

  Projection G0→R via `composeProjection4`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{lists}

abbrev {PRE}RClosed : List Clause := {PRE}RAxioms

def {PRE}Pivots : List Lit := {pivots}

def {PRE}V1 : List Nat := {vlists[0]}

def {PRE}V2 : List Nat := {vlists[1]}

def {PRE}V3 : List Nat := {vlists[2]}

def {PRE}Vres : List Nat := {vlists[3]}

def {PRE}ClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

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
{pack_block(f"{PRE}G0", f"{PRE}G0Axioms", f"{PRE}G0Closed")}
{pack_block(f"{PRE}G1", f"{PRE}G1Axioms", f"{PRE}G1Closed")}
{pack_block(f"{PRE}G2", f"{PRE}G2Axioms", f"{PRE}G2Closed")}
{pack_block(f"{PRE}G3", f"{PRE}G3Axioms", f"{PRE}G3Closed")}
{pack_block(f"{PRE}R", f"{PRE}RAxioms", f"{PRE}RClosed")}
{hop("01", f"{PRE}G0Closed", f"{PRE}G1Closed", f"{PRE}V1")}
{hop("12", f"{PRE}G1Closed", f"{PRE}G2Closed", f"{PRE}V2")}
{hop("23", f"{PRE}G2Closed", f"{PRE}G3Closed", f"{PRE}V3")}
{hop("3R", f"{PRE}G3Closed", f"{PRE}RClosed", f"{PRE}Vres")}

def {PRE}Step01 : EliminationStep 3 where
  before := {PRE}G0Closure
  after := {PRE}G1Closure
  V_after := {PRE}V1
  preserves := fun _ hB hsup => {PRE}_supported_01 hB hsup

def {PRE}Step12 : EliminationStep 3 where
  before := {PRE}G1Closure
  after := {PRE}G2Closure
  V_after := {PRE}V2
  preserves := fun _ hB hsup => {PRE}_supported_12 hB hsup

def {PRE}Step23 : EliminationStep 3 where
  before := {PRE}G2Closure
  after := {PRE}G3Closure
  V_after := {PRE}V3
  preserves := fun _ hB hsup => {PRE}_supported_23 hB hsup

def {PRE}Step3R : EliminationStep 3 where
  before := {PRE}G3Closure
  after := {PRE}RClosure
  V_after := {PRE}Vres
  preserves := fun _ hB hsup => {PRE}_supported_3R hB hsup

def {PRE}EliminationChain : EliminationChain 3 where
  steps := [{PRE}Step01, {PRE}Step12, {PRE}Step23, {PRE}Step3R]
  certDoc := "lean/PNPLab/FourFoldProjection.lean"

theorem {PRE}Nest12 : varsSubset {PRE}V2 {PRE}V1 = true := by native_decide
theorem {PRE}Nest23 : varsSubset {PRE}V3 {PRE}V2 = true := by native_decide
theorem {PRE}Nest3R : varsSubset {PRE}Vres {PRE}V3 = true := by native_decide

def {PRE}Projection : ProjectionInclusion 3 :=
  composeProjection4 {PRE}Step01 {PRE}Step12 {PRE}Step23 {PRE}Step3R
    rfl rfl rfl {PRE}Nest12 {PRE}Nest23 {PRE}Nest3R

theorem {PRE}_no_empty_of_projection :
    ¬ {PRE}Projection.gClosure.mem [] :=
  no_empty_of_projection {PRE}Projection {PRE}R_no_empty

def {PRE}Doc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} sizes={[len(c) for c in d['cls']]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
