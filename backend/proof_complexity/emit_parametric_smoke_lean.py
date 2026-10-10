"""Emit Lean parametric smoke endpoints + rename dst + projection for n=5..10 canonical seeds."""

from __future__ import annotations

from pathlib import Path

from backend.proof_complexity.emit_crossing_residual_catalog import (
    _extract_k4_axioms,
    _find_signed_iso,
    residual_of,
)

OUT = Path("lean/PNPLab/CrossingEndpointsSmokeMass.lean")

# Sorted cycle endpoints p0<p1<p2<p3 from chords (c0,c2) and (c1,c3).
SEEDS = [
    ("c5OfoldEndpoints", 5, (0, 2), (1, 3)),
    ("c5Alt1Endpoints", 5, (0, 2), (1, 4)),
    ("c6Endpoints0123", 6, (0, 2), (1, 3)),
    ("c7Endpoints0123", 7, (0, 2), (1, 3)),
    ("c8Endpoints0123", 8, (0, 2), (1, 3)),
    ("c9Endpoints0123", 9, (0, 2), (1, 3)),
    ("c10Endpoints024", 10, (0, 2), (1, 4)),
]


def endpoints_fields(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> tuple[int, int, int, int]:
    pts = sorted({*c1, *c2})
    assert len(pts) == 4
    return pts[0], pts[1], pts[2], pts[3]


def short_seed(name: str) -> str:
    return name.split("Endpoints")[0]


def cap_seed(short: str) -> str:
    return short[0].upper() + short[1:]


def emit_projection_block(name: str) -> str:
    short = short_seed(name)
    cap = cap_seed(short)
    return f"""
theorem {short}_parametricProjOK : parametricProjOK {name} = true := by native_decide

theorem {short}_closure3_closed :
    closedUnder (closure3 {name}) 3 (parametricGPivots {name}) = true := by native_decide

theorem {short}_parametricG_lits_in_pivots :
    ((closure3 {name}).all fun C =>
      C.all fun lit => decide (lit ∈ parametricGPivots {name})) = true := by native_decide

theorem {short}_parametricG_axioms_subset :
    ({name}.tseitinAxioms.all fun A => (closure3 {name}).contains A) = true := by native_decide

theorem {short}_residual_closed_under :
    k4ClosedUnder (residualGlobalAxioms {name}) 3 (parametricRPivots {name}) = true := by native_decide

theorem {short}_parametricR_lits_in_pivots :
    ((residualGlobalClosed {name}).all fun C =>
      C.all fun lit => decide (lit ∈ parametricRPivots {name})) = true := by native_decide

theorem {short}_parametricR_axioms_subset :
    ((residualGlobalAxioms {name}).all fun A =>
      (residualGlobalClosed {name}).contains A) = true := by native_decide

theorem {short}_closure3_no_empty :
    ¬ (closure3 {name}).contains [] := by native_decide

theorem {short}_residual_axioms_no_empty :
    ¬ ([] ∈ residualGlobalAxioms {name}) := by native_decide

def parametric{cap}GClosure : WidthClosure 3 :=
  parametricGClosureOf {name} {short}_closure3_closed {short}_parametricG_lits_in_pivots
    {short}_parametricG_axioms_subset

def parametric{cap}RClosure : WidthClosure 3 :=
  parametricRClosureOf {name} {short}_residual_closed_under {short}_parametricR_lits_in_pivots
    {short}_parametricR_axioms_subset

def parametric{cap}Projection : ProjectionInclusion 3 :=
  parametricProjectionOf {name} {short}_parametricProjOK {short}_closure3_closed
    {short}_parametricG_lits_in_pivots {short}_parametricG_axioms_subset {short}_residual_closed_under
    {short}_parametricR_lits_in_pivots {short}_parametricR_axioms_subset

theorem {short}_parametricR_no_empty :
    ¬ parametric{cap}RClosure.mem [] := fun h =>
  {short}_residual_axioms_no_empty h

def freshG0_parametric_{short} : FreshG0Obligation :=
  freshG0_of_projection parametric{cap}Projection {short}_parametricR_no_empty
"""


def main() -> int:
    target = frozenset(tuple(sorted(c)) for c in _extract_k4_axioms())
    blocks: list[str] = []
    rename_lines: list[str] = []
    proj_blocks: list[str] = []
    topo_lines: list[str] = []
    topo_props: list[str] = []
    proj_ok_lines: list[str] = []
    proj_ok_props: list[str] = []
    fresh_no_empty_lines: list[str] = []
    fresh_no_empty_props: list[str] = []
    fresh_theorem_names: list[str] = []

    for name, n, c1, c2 in SEEDS:
        if name in ("c5OfoldEndpoints", "c5Alt1Endpoints", "c6Endpoints0123"):
            continue  # already in CrossingEndpointsGraph / CrossingChordsToArcs
        p0, p1, p2, p3 = endpoints_fields(n, c1, c2)
        res = residual_of(n, c1, c2)
        wit = _find_signed_iso(res["RAxioms"], res["Vres"], target)
        assert wit is not None and not wit["needs_flips"], (name, n)
        perm = wit["permutation"]
        blocks.append(
            f"""
def {name} : CrossingEndpoints where
  n := {n}
  p0 := {p0}
  p1 := {p1}
  p2 := {p2}
  p3 := {p3}
  ordered := by decide
"""
        )
        pre = name.replace("Endpoints", "")
        short = short_seed(name)
        rename_lines.append(f"def {pre}RenameDst : List Nat := canonicalTopologyRenameDst")
        rename_lines.append(
            f"theorem {pre}Rename_topology :\n"
            f"    topologySetEq (globalTopologyRenameCanonical {name} (by native_decide))\n"
            f"      (residualGlobalAxioms {name}) = true := by\n"
            f"  native_decide"
        )
        topo_lines.append(f"{pre}Rename_topology")
        topo_props.append(
            f"(topologySetEq (globalTopologyRenameCanonical {name} (by native_decide)) "
            f"(residualGlobalAxioms {name}) = true)"
        )
        proj_blocks.append(emit_projection_block(name))
        proj_ok_lines.append(f"{short}_parametricProjOK")
        proj_ok_props.append(f"parametricProjOK {name} = true")
        fresh_no_empty_lines.append(
            f"theorem {short}_fresh_g0_no_empty :\n"
            f"    ¬ freshG0_parametric_{short}.projection.gClosure.mem [] :=\n"
            f"  freshG0_parametric_{short}.g_no_empty"
        )
        fresh_no_empty_props.append(
            f"¬ freshG0_parametric_{short}.projection.gClosure.mem []"
        )
        fresh_theorem_names.append(f"{short}_fresh_g0_no_empty")

    blocks_join = "".join(blocks)
    rename_join = "\n".join(rename_lines)
    proj_join = "".join(proj_blocks)
    fresh_lines_join = "\n".join(fresh_no_empty_lines)
    topo_conj = " ∧\n      ".join(topo_props)
    topo_thms = ", ".join(topo_lines)
    proj_ok_conj = " ∧ ".join(proj_ok_props)
    proj_ok_thms = ", ".join(proj_ok_lines)
    fresh_conj = " ∧\n      ".join(fresh_no_empty_props)
    fresh_thms = ", ".join(fresh_theorem_names)

    body = f"""/-
  Mass-window parametric smoke endpoints (n=7..10) + projection + E2 catalog mass link.
  Generated by `backend/proof_complexity/emit_parametric_smoke_lean.py`.
-/

import PNPLab.CrossingEndpointsParametricProjection
import PNPLab.CrossingEndpointsGlobalRename
import PNPLab.CrossingResidualCatalog
import PNPLab.FreshG0Obligation

namespace PNPLab.Bicyclic

open PNPLab.Resolution
{blocks_join}
{rename_join}

theorem mass_smoke_topology_flags :
    {topo_conj} :=
  ⟨{topo_thms}⟩

{proj_join}

theorem mass_smoke_projection_flags :
    {proj_ok_conj} :=
  ⟨{proj_ok_thms}⟩

{fresh_lines_join}

theorem mass_smoke_fresh_g0_no_empty :
    {fresh_conj} :=
  ⟨{fresh_thms}⟩

def parametricSmokeMassDoc : String :=
  "Topology + ProjectionInclusion smoke on canonical n=7..10 seeds; Python mass verified"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem parametric_mass_iso_link :
    crossingResidualCatalogMass.isoOk = 461 ∧
      crossingResidualCatalogMass.flipNeeded = 0 := by
  native_decide

end PNPLab.Resolution
"""
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(body, encoding="utf-8")
    print(f"wrote {OUT} new_seeds={len(blocks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
