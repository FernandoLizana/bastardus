"""Emit Lean `TenFoldProjection.lean` for n=14 Ten-tip path-fold chain.

Instance: C_14 + chords (0,2),(1,3):
  912 → 652 → 446 → 288 → 172 → 92 → 42 → 16.
Uses `projectionOfLinkedChain` (same pattern as SixFold).
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

OUT = Path("lean/PNPLab/TenFoldProjection.lean")
N, C1, C2 = 14, (0, 2), (1, 3)
EXPECTED = [2076, 1618, 1232, 912, 652, 446, 288, 172, 92, 42, 16]
PRE = "zf"
NUM_HOPS = 10


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


def xor_axioms(work, charges, e_index):
    axs = []
    for v in sorted(work.nodes()):
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return sorted(axs, key=lambda c: (len(c), c))


def edge_vars(work, e_index):
    return sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )


def closure_of(axioms):
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    return sorted(_width_closure_clauses(form, 3), key=lambda c: (len(c), c))


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
    charges0 = _odd_charge_for_crossing(N, C1, C2)
    g0 = nx.cycle_graph(N)
    g0.add_edges_from([C1, C2])
    _ends, arcs = crossing_branch_sets(N, C1, C2)
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
    for arc in arcs:
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            ax = xor_axioms(work, charges, e_index)
            axs.append(ax)
            cls.append(closure_of(ax))
            vs.append(edge_vars(work, e_index))
    assert [len(c) for c in cls] == EXPECTED, [len(c) for c in cls]
    assert len(axs) == NUM_HOPS + 1

    max_var = max(vs[0])
    pivots = "[" + ", ".join(str(i) for i in range(-max_var - 1, max_var + 2)) + "]"
    vlists = ["[" + ", ".join(str(v) for v in vs[i]) + "]" for i in range(1, NUM_HOPS + 1)]

    list_parts = []
    for i in range(NUM_HOPS):
        list_parts.append(list_lit(f"{PRE}G{i}Axioms", axs[i]))
        list_parts.append(list_lit(f"{PRE}G{i}Closed", cls[i]))
    list_parts.append(list_lit(f"{PRE}RAxioms", axs[NUM_HOPS]))
    lists = "\n\n".join(list_parts)

    packs = "\n".join(
        pack_block(f"{PRE}G{i}", f"{PRE}G{i}Axioms", f"{PRE}G{i}Closed")
        for i in range(NUM_HOPS)
    )
    packs += pack_block(f"{PRE}R", f"{PRE}RAxioms", f"{PRE}RAxioms")

    last_tag = f"{NUM_HOPS - 1}R"
    hop_tags = [f"{i}{i + 1}" for i in range(NUM_HOPS - 1)] + [last_tag]
    hop_src = [f"{PRE}G{i}Closed" for i in range(NUM_HOPS - 1)] + [
        f"{PRE}G{NUM_HOPS - 1}Closed"
    ]
    hop_dst = [f"{PRE}G{i + 1}Closed" for i in range(NUM_HOPS - 1)] + [f"{PRE}RClosed"]
    hop_vs = [f"{PRE}V{i + 1}" for i in range(NUM_HOPS - 1)] + [f"{PRE}Vres"]
    hops = "\n".join(
        hop(t, s, d, v) for t, s, d, v in zip(hop_tags, hop_src, hop_dst, hop_vs)
    )

    vdefs = "\n".join(
        f"def {PRE}V{i + 1} : List Nat := {vlists[i]}" for i in range(NUM_HOPS - 1)
    )
    vdefs += f"\ndef {PRE}Vres : List Nat := {vlists[NUM_HOPS - 1]}"

    steps = []
    for i in range(NUM_HOPS - 1):
        steps.append(
            f"""def {PRE}Step{i}{i + 1} : EliminationStep 3 where
  before := {PRE}G{i}Closure
  after := {PRE}G{i + 1}Closure
  V_after := {PRE}V{i + 1}
  preserves := fun _ hB hsup => {PRE}_supported_{i}{i + 1} hB hsup"""
        )
    steps.append(
        f"""def {PRE}Step{last_tag} : EliminationStep 3 where
  before := {PRE}G{NUM_HOPS - 1}Closure
  after := {PRE}RClosure
  V_after := {PRE}Vres
  preserves := fun _ hB hsup => {PRE}_supported_{last_tag} hB hsup"""
    )
    steps_block = "\n\n".join(steps)

    nests = []
    for i in range(NUM_HOPS - 2):
        nests.append(
            f"theorem {PRE}Nest{i + 1}{i + 2} : "
            f"varsSubset {PRE}V{i + 2} {PRE}V{i + 1} = true := by native_decide"
        )
    nests.append(
        f"theorem {PRE}Nest{last_tag} : "
        f"varsSubset {PRE}Vres {PRE}V{NUM_HOPS - 1} = true := by native_decide"
    )
    nests_block = "\n".join(nests)

    step_names = [f"{PRE}Step{i}{i + 1}" for i in range(NUM_HOPS - 1)] + [
        f"{PRE}Step{last_tag}"
    ]
    links = []
    for i in range(NUM_HOPS - 2):
        links.append(
            f"""theorem {PRE}Link{i + 1}{i + 2} : StepLink 3 {PRE}Step{i}{i + 1} {PRE}Step{i + 1}{i + 2} where
  bridge := rfl
  nest := {PRE}Nest{i + 1}{i + 2}"""
        )
    links.append(
        f"""theorem {PRE}Link{last_tag} : StepLink 3 {PRE}Step{NUM_HOPS - 2}{NUM_HOPS - 1} {PRE}Step{last_tag} where
  bridge := rfl
  nest := {PRE}Nest{last_tag}"""
    )
    links_block = "\n\n".join(links)

    # nested linkedChainCons … singleton
    chain = f"LinkedChain.singleton {PRE}Step{last_tag}"
    for i in range(NUM_HOPS - 2, -1, -1):
        if i == NUM_HOPS - 2:
            link_name = f"{PRE}Link{last_tag}"
        else:
            link_name = f"{PRE}Link{i + 1}{i + 2}"
        chain = f"linkedChainCons {link_name}\n    ({chain})"

    sizes_str = " → ".join(str(s) for s in EXPECTED)
    body = f"""/-
  Ten-tip path-fold projection chain (n=14 crossing).

  Instance: C_14 + chords (0,2),(1,3):
    {sizes_str}.

  Projection G0→R via `projectionOfLinkedChain`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

{lists}

abbrev {PRE}RClosed : List Clause := {PRE}RAxioms

def {PRE}Pivots : List Lit := {pivots}

{vdefs}

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
{packs}
{hops}

{steps_block}

def {PRE}EliminationChain : EliminationChain 3 where
  steps := [{", ".join(step_names)}]
  certDoc := "lean/PNPLab/TenFoldProjection.lean"

{nests_block}

{links_block}

def {PRE}Linked : LinkedChain 3
    [{", ".join(step_names)}] :=
  {chain}

/-- G0 → R via generic `projectionOfLinkedChain` fold over `{PRE}Linked`. -/
def {PRE}Projection : ProjectionInclusion 3 :=
  projectionOfLinkedChain {PRE}Linked

theorem {PRE}_no_empty_of_projection :
    ¬ {PRE}Projection.gClosure.mem [] :=
  no_empty_of_projection {PRE}Projection {PRE}R_no_empty

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} sizes={[len(c) for c in cls]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
