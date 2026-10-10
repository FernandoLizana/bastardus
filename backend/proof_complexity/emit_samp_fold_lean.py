"""Emit Lean Samp{N}FoldProjection.lean: fresh G₀→R for sample residuals.

Chords are loaded from `lean/PNPLab/ResidualSampleCatalog.lean` comments so
indices always match the catalog (avoids hop/index mismatches).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import networkx as nx

from backend.proof_complexity.emit_crossing_residual_catalog import residual_of
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
from backend.proof_complexity.width import _norm

CATALOG = Path("lean/PNPLab/ResidualSampleCatalog.lean")


def load_samps_from_catalog(path: Path = CATALOG) -> dict[int, tuple]:
    """samp_id -> (n, c1, c2, 'sampN', 'SampNFoldProjection')."""
    text = path.read_text(encoding="utf-8")
    pat = re.compile(
        r"/-- Sample hop-(\d+): C_(\d+) \+ \[(\d+), (\d+)\],\[(\d+), (\d+)\]\. -/\n"
        r"def samp(\d+)Vres"
    )
    out: dict[int, tuple] = {}
    for m in pat.finditer(text):
        _hop, n, a, b, c, d, i = m.groups()
        i = int(i)
        n = int(n)
        c1 = (int(a), int(b))
        c2 = (int(c), int(d))
        pre = f"samp{i}"
        out[i] = (n, c1, c2, pre, f"Samp{i}FoldProjection")
    return out


SAMPS = load_samps_from_catalog()


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


def g0_payload(n: int, c1: tuple[int, int], c2: tuple[int, int]):
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    form_g = tseitin_cnf(
        GraphInstance(g0, tuple(charges0[v] for v in range(n)), "G", 0, {})
    )
    cl_g = sorted(_width_closure_clauses(form_g, 3), key=lambda c: (len(c), c))
    axioms_g: list[tuple[int, ...]] = []
    for cl in form_g.clauses:
        nn = _norm(list(cl.literals))
        if nn is not None and nn not in axioms_g:
            axioms_g.append(nn)
    axioms_g = sorted(axioms_g, key=lambda c: (len(c), c))
    cat = residual_of(n, c1, c2)
    vres = list(cat["Vres"])
    rset = set(map(tuple, cat["RAxioms"]))
    proj = {c for c in cl_g if c and all(abs(lit) in set(vres) for lit in c)}
    assert () not in cl_g
    assert proj <= rset and len(proj) == 16
    max_var = max((abs(lit) for c in cl_g for lit in c), default=max(vres))
    return axioms_g, cl_g, vres, max_var


def emit_one(k: int) -> Path:
    n, c1, c2, rpre, fname = SAMPS[k]
    axioms_g, cl_g, vres, max_var = g0_payload(n, c1, c2)
    pre = f"{rpre}G"
    out = Path(f"lean/PNPLab/{fname}.lean")
    piv_hi = max(max_var + 2, 10)
    pivots = "[" + ", ".join(str(x) for x in range(-piv_hi, piv_hi + 1)) + "]"
    vres_lit = "[" + ", ".join(str(v) for v in vres) + "]"
    hop = n - 4
    # Prefer catalog hop comment if available via residual tips.
    iso_block = ""
    if k != 1:
        iso_block = f"""
theorem {rpre}_global_edge_iso_to_residualAxioms (e : Bicyclic.CrossingEndpoints) :
    topologySetEq {rpre}TopologyRename {rpre}RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := {rpre}TopologySetEq_true
  simpa [topologySetEq, {rpre}TopologySetEq] using h
"""
    body = f"""/-
  Fresh G₀→R for hop-{hop} sample {rpre}: C_{n} + chords {list(c1)},{list(c2)}.

  Machine fact: Closure₃(G) has size {len(cl_g)} and excludes □; residual
  `{rpre}RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `{rpre}RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.SampleResidualClosures

namespace PNPLab.Resolution

{list_lit(pre + "Axioms", axioms_g)}

{list_lit(pre + "Closed", cl_g)}

def {pre}Pivots : List Lit := {pivots}

def {pre}Vres : List Nat := {vres_lit}

theorem {pre}Vres_eq_samp : {pre}Vres = {rpre}Vres := by native_decide

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

theorem {pre}_no_empty : ¬ {pre}Closure.mem [] := by
  simp [{pre}Closure]
  native_decide

def {pre}ProjOK : Bool :=
  {pre}Closed.all fun C =>
    !(supportedOn C {rpre}Vres) || {rpre}RClosed.contains C

theorem {pre}ProjOK_true : {pre}ProjOK = true := by native_decide

theorem {pre}_supported_in_R
    {{C : Clause}} (hG : C ∈ {pre}Closed) (hsup : supportedOn C {rpre}Vres = true) :
    C ∈ {rpre}RClosed := by
  have hall := (List.all_eq_true.mp {pre}ProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def {pre}Projection : ProjectionInclusion 3 where
  gClosure := {pre}Closure
  rClosure := {rpre}RClosure
  Vres := {rpre}Vres
  holds := fun _ hG hsup => {pre}_supported_in_R hG hsup

def {pre}EliminationStep : EliminationStep 3 where
  before := {pre}Closure
  after := {rpre}RClosure
  V_after := {rpre}Vres
  preserves := fun _ hB hsup => {pre}_supported_in_R hB hsup

theorem {pre}_no_empty_of_projection :
    ¬ {pre}Projection.gClosure.mem [] :=
  no_empty_of_projection {pre}Projection {rpre}_closure_no_empty
{iso_block}
theorem {rpre}_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq {rpre}TopologyRename {rpre}RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ {pre}Projection.gClosure.mem [] :=
  ⟨({rpre}_global_edge_iso_to_residualAxioms e).1,
    ({rpre}_global_edge_iso_to_residualAxioms e).2,
    {pre}_no_empty_of_projection⟩

def {pre}Doc : String :=
  "fresh G₀ Closure₃ for {rpre}; ProjectionInclusion beyond packs/alts"

end PNPLab.Resolution
"""
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body, encoding="utf-8")
    print(f"wrote {out} |G|={len(cl_g)} axioms={len(axioms_g)} Vres={vres}")
    return out


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument(
        "samps",
        nargs="*",
        type=int,
        default=[25, 26, 27, 28, 29, 30, 31, 32, 37, 38],
        help="sample indices to emit (default: finish hop-3 + smallest hop-4)",
    )
    args = p.parse_args(argv)
    global SAMPS
    SAMPS = load_samps_from_catalog()
    for k in args.samps:
        if k not in SAMPS:
            print(f"unknown samp {k}; catalog has {sorted(SAMPS)[:5]}...", file=sys.stderr)
            return 2
        emit_one(k)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
