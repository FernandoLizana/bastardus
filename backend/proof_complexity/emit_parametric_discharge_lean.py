"""Emit Lean parametric discharge witnesses for all 461 E2 catalog instances (E5).

Reads `crossing_residual_catalog.json`, derives `CrossingEndpoints` from n + chord
endpoints, emits `ParametricEndpointsDischarge` + topology per instance via
`native_decide` (same pattern as `emit_parametric_smoke_lean.py`).

Streams three part files (~154 instances each) plus `ParametricDischargeAll.lean`.
"""

from __future__ import annotations

import argparse
import json
import textwrap
from pathlib import Path
from typing import TextIO

from backend.proof_complexity.emit_crossing_residual_catalog import (
    _extract_k4_axioms,
    _find_signed_iso,
    residual_of,
)

ROOT = Path(__file__).resolve().parents[2]
CATALOG = ROOT / "reports" / "discovery" / "crossing_residual_catalog.json"
LEAN_DIR = ROOT / "lean" / "PNPLab"
CHUNK = 154
EMIT_SCRIPT = "backend/proof_complexity/emit_parametric_discharge_lean.py"


def endpoints_fields(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> tuple[int, int, int, int]:
    pts = sorted({*c1, *c2})
    assert len(pts) == 4
    return pts[0], pts[1], pts[2], pts[3]


def cap_prefix(pre: str) -> str:
    return pre[0].upper() + pre[1:]


def _emit_projection_block(name: str, pre: str) -> str:
    cap = cap_prefix(pre)
    return textwrap.dedent(
        f"""
        theorem {pre}_parametricProjOK : parametricProjOK {name} = true := by native_decide

        theorem {pre}_closure3_closed :
            closedUnder (closure3 {name}) 3 (parametricGPivots {name}) = true := by native_decide

        theorem {pre}_parametricG_lits_in_pivots :
            ((closure3 {name}).all fun C =>
              C.all fun lit => decide (lit ∈ parametricGPivots {name})) = true := by native_decide

        theorem {pre}_parametricG_axioms_subset :
            ({name}.tseitinAxioms.all fun A => (closure3 {name}).contains A) = true := by native_decide

        theorem {pre}_residual_closed_under :
            k4ClosedUnder (residualGlobalAxioms {name}) 3 (parametricRPivots {name}) = true := by native_decide

        theorem {pre}_parametricR_lits_in_pivots :
            ((residualGlobalClosed {name}).all fun C =>
              C.all fun lit => decide (lit ∈ parametricRPivots {name})) = true := by native_decide

        theorem {pre}_parametricR_axioms_subset :
            ((residualGlobalAxioms {name}).all fun A =>
              (residualGlobalClosed {name}).contains A) = true := by native_decide

        theorem {pre}_closure3_no_empty :
            ¬ (closure3 {name}).contains [] := by native_decide

        theorem {pre}_residual_axioms_no_empty :
            ¬ ([] ∈ residualGlobalAxioms {name}) := by native_decide

        def parametric{cap}GClosure : WidthClosure 3 :=
          parametricGClosureOf {name} {pre}_closure3_closed {pre}_parametricG_lits_in_pivots
            {pre}_parametricG_axioms_subset

        def parametric{cap}RClosure : WidthClosure 3 :=
          parametricRClosureOf {name} {pre}_residual_closed_under {pre}_parametricR_lits_in_pivots
            {pre}_parametricR_axioms_subset

        def parametric{cap}Projection : ProjectionInclusion 3 :=
          parametricProjectionOf {name} {pre}_parametricProjOK {pre}_closure3_closed
            {pre}_parametricG_lits_in_pivots {pre}_parametricG_axioms_subset {pre}_residual_closed_under
            {pre}_parametricR_lits_in_pivots {pre}_parametricR_axioms_subset

        theorem {pre}_parametricR_no_empty :
            ¬ parametric{cap}RClosure.mem [] := fun h =>
          {pre}_residual_axioms_no_empty h

        def freshG0_parametric_{pre} : FreshG0Obligation :=
          freshG0_of_projection parametric{cap}Projection {pre}_parametricR_no_empty
        """
    ).strip("\n") + "\n\n"


def _emit_instance_block(global_idx: int, inst: dict, perm: list[int]) -> str:
    n = inst["n"]
    c1, c2 = inst["chords"]
    tips = inst["tips"]
    p0, p1, p2, p3 = endpoints_fields(n, tuple(c1), tuple(c2))
    pre = f"pd{global_idx}"
    name = f"{pre}Endpoints"
    perm_s = "[" + ", ".join(str(v) for v in perm) + "]"

    block = textwrap.dedent(
        f"""
        /- Hop-{tips}: C_{n} + {c1},{c2}. -/
        def {name} : CrossingEndpoints where
          n := {n}
          p0 := {p0}
          p1 := {p1}
          p2 := {p2}
          p3 := {p3}
          ordered := by decide

        theorem {pre}_topology :
            topologySetEq
                (globalTopologyRenameFromPerm {name} {perm_s} (by native_decide) (by native_decide))
                (residualGlobalAxioms {name}) = true := by
          native_decide
        """
    ).strip("\n") + "\n\n"

    block += _emit_projection_block(name, pre)

    block += textwrap.dedent(
        f"""
        theorem {pre}ParametricDischarge : ParametricEndpointsDischarge {name} where
          proj_ok := {pre}_parametricProjOK
          g_closed := {pre}_closure3_closed
          g_lits := {pre}_parametricG_lits_in_pivots
          g_axioms := {pre}_parametricG_axioms_subset
          r_closed := {pre}_residual_closed_under
          r_lits := {pre}_parametricR_lits_in_pivots
          r_axioms := {pre}_parametricR_axioms_subset
          r_no_empty := {pre}_residual_axioms_no_empty

        def {pre}ParametricGoal : ParametricEndpointsGoal {name} where
          discharge := {pre}ParametricDischarge
          topology :=
            ⟨globalTopologyRenameFromPerm {name} {perm_s} (by native_decide) (by native_decide),
              {pre}_topology⟩
        """
    ).strip("\n") + "\n\n"

    return block


def _write_part_header(f: TextIO, part_idx: int, count: int, start_idx: int) -> None:
    f.write(
        textwrap.dedent(
            f"""\
            /-
              Parametric discharge witnesses part {part_idx} (Category C / E5).
              {count} instances (pd{start_idx}..pd{start_idx + count - 1}): CrossingEndpoints,
              ParametricEndpointsDischarge + topology via native_decide.

              Generated by `{EMIT_SCRIPT}`.
              E2 parent: `crossing_residual_catalog.json` (461/461 iso).
            -/

            import PNPLab.CrossingEndpointsParametricProjection
            import PNPLab.CrossingEndpointsGlobalRename
            import PNPLab.CrossingEndpointsParametricGoal
            import PNPLab.FreshG0Obligation

            namespace PNPLab.Bicyclic

            open PNPLab.Resolution

            """
        )
    )


def _write_part_footer(
    f: TextIO,
    part_idx: int,
    entries: list[tuple[str, list[int]]],
    start_idx: int,
    count: int,
) -> None:
    proj_flags = ", ".join(f"parametricProjOK {pre}Endpoints" for pre, _ in entries)
    topo_flags = ", ".join(
        "topologySetEq "
        f"(globalTopologyRenameFromPerm {pre}Endpoints "
        f"[{', '.join(str(v) for v in perm)}] (by native_decide) (by native_decide)) "
        f"(residualGlobalAxioms {pre}Endpoints)"
        for pre, perm in entries
    )
    f.write(
        textwrap.dedent(
            f"""\
            def parametricDischargeProjOkFlagsPart{part_idx} : List Bool :=
              [{proj_flags}]

            def parametricDischargeTopologyFlagsPart{part_idx} : List Bool :=
              [{topo_flags}]

            theorem all_parametric_discharge_proj_ok_part{part_idx} :
                parametricDischargeProjOkFlagsPart{part_idx}.all (· = true) := by
              native_decide

            theorem all_parametric_discharge_topology_part{part_idx} :
                parametricDischargeTopologyFlagsPart{part_idx}.all (· = true) := by
              native_decide

            theorem parametric_discharge_part{part_idx}_count :
                parametricDischargeProjOkFlagsPart{part_idx}.length = {count} := by
              native_decide

            def parametricDischargePart{part_idx}Doc : String :=
              "pd{start_idx}..pd{start_idx + count - 1}"

            end PNPLab.Bicyclic
            """
        )
    )


def _emit_part(
    part_idx: int,
    chunk: list[dict],
    global_start: int,
    target: frozenset[tuple[int, ...]],
) -> list[str]:
    count = len(chunk)
    start_idx = global_start
    out = LEAN_DIR / f"ParametricDischargePart{part_idx}.lean"
    entries: list[tuple[str, list[int]]] = []

    with out.open("w", encoding="utf-8", newline="\n") as f:
        _write_part_header(f, part_idx, count, start_idx)
        for local_i, inst in enumerate(chunk):
            global_idx = global_start + local_i
            pre = f"pd{global_idx}"
            n = inst["n"]
            c1, c2 = inst["chords"]
            c1t, c2t = tuple(c1), tuple(c2)

            res = residual_of(n, c1t, c2t)
            assert res["shape_ok"], (global_idx, n, c1, c2)
            assert res["tips"] == inst["tips"], (global_idx, res["tips"], inst["tips"])
            assert res["Vres"] == inst["Vres"], (global_idx, res["Vres"], inst["Vres"])

            wit = inst.get("witness")
            assert wit is not None and inst["iso_found"]
            assert not wit.get("needs_flips", False), (global_idx, n, c1, c2)
            perm = list(wit["permutation"])

            check = _find_signed_iso(res["RAxioms"], res["Vres"], target)
            assert check is not None and not check["needs_flips"], (
                global_idx,
                n,
                c1,
                c2,
            )

            entries.append((pre, perm))
            f.write(_emit_instance_block(global_idx, inst, perm))

        _write_part_footer(f, part_idx, entries, start_idx, count)

    print(f"wrote {out} entries={count} bytes={out.stat().st_size}")
    return [pre for pre, _ in entries]


def _emit_all(total: int, part_sizes: list[int]) -> None:
    out = LEAN_DIR / "ParametricDischargeAll.lean"
    n_parts = len(part_sizes)
    imports = "\n".join(
        f"import PNPLab.ParametricDischargePart{i}" for i in range(1, n_parts + 1)
    )
    proj_parts = " ++ ".join(
        f"parametricDischargeProjOkFlagsPart{i}" for i in range(1, n_parts + 1)
    )
    topo_parts = " ++ ".join(
        f"parametricDischargeTopologyFlagsPart{i}" for i in range(1, n_parts + 1)
    )
    part_proj_refs = ", ".join(
        f"all_parametric_discharge_proj_ok_part{i}" for i in range(1, n_parts + 1)
    )
    part_topo_refs = ", ".join(
        f"all_parametric_discharge_topology_part{i}" for i in range(1, n_parts + 1)
    )
    part_count_refs = ", ".join(
        f"parametric_discharge_part{i}_count" for i in range(1, n_parts + 1)
    )
    body = f"""/-
  Aggregated parametric discharge (461/461 catalog).

  Generated by `{EMIT_SCRIPT}`. Composes part-level witnesses — no giant
  `native_decide` over all {total} flags.
-/

{imports}
import PNPLab.CrossingResidualCatalog
import PNPLab.ParametricProjectionMass

namespace PNPLab.Bicyclic

theorem List.all_append {{α}} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil => simp [List.all]
  | cons x xs ih =>
    simp [List.all, ih, Bool.and_left_comm, Bool.and_comm]

def allParametricDischargeProjOkFlags : List Bool :=
  {proj_parts}

def allParametricDischargeTopologyFlags : List Bool :=
  {topo_parts}

theorem all_parametric_discharges_proj_ok_parts :
    {" ∧\n      ".join(f"parametricDischargeProjOkFlagsPart{i}.all (· = true)" for i in range(1, n_parts + 1))} :=
  ⟨{part_proj_refs}⟩

theorem all_parametric_discharges_topology_parts :
    {" ∧\n      ".join(f"parametricDischargeTopologyFlagsPart{i}.all (· = true)" for i in range(1, n_parts + 1))} :=
  ⟨{part_topo_refs}⟩

theorem all_parametric_discharges_proj_ok :
    allParametricDischargeProjOkFlags.all (· = true) := by
  unfold allParametricDischargeProjOkFlags
  rcases all_parametric_discharges_proj_ok_parts with ⟨h1, h2, h3⟩
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨And.intro h1 h2, h3⟩

theorem all_parametric_discharges_topology :
    allParametricDischargeTopologyFlags.all (· = true) := by
  unfold allParametricDischargeTopologyFlags
  rcases all_parametric_discharges_topology_parts with ⟨h1, h2, h3⟩
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨And.intro h1 h2, h3⟩

theorem all_parametric_discharges_count :
    allParametricDischargeProjOkFlags.length = {total} := by
  unfold allParametricDischargeProjOkFlags
  simp only [List.length_append, {part_count_refs}]

def parametricDischargeAllDoc : String :=
  "reports/discovery/crossing_residual_catalog.json"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem all_parametric_discharges_mass :
    allParametricDischargeProjOkFlags.length = parametricProjectionMass.projOk ∧
      parametricProjectionMass.projOk = crossingResidualCatalogMass.isoOk := by
  rw [all_parametric_discharges_count]
  exact ⟨rfl, parametric_projection_mass_matches_catalog.1⟩

theorem parametric_discharge_mass_link :
    allParametricDischargeProjOkFlags.length = 461 ∧
      parametricProjectionMass.projOk = 461 ∧
      crossingResidualCatalogMass.isoOk = 461 := by
  rw [all_parametric_discharges_count]
  exact ⟨rfl, (parametricProjectionMass_ok).2.1, parametric_projection_mass_matches_catalog.2⟩

end PNPLab.Resolution
"""
    out.write_text(body, encoding="utf-8")
    print(f"wrote {out} bytes={out.stat().st_size}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-parts",
        type=int,
        default=3,
        help="Emit only the first N part files (default 3 = all)",
    )
    args = parser.parse_args()

    catalog = json.loads(CATALOG.read_text(encoding="utf-8"))
    instances = catalog["instances"]
    total = len(instances)
    assert total == catalog["iso_ok"] == 461, (total, catalog["iso_ok"])

    k4 = _extract_k4_axioms()
    target = frozenset(tuple(sorted(c)) for c in k4)

    chunks: list[list[dict]] = []
    for i in range(0, total, CHUNK):
        chunks.append(instances[i : i + CHUNK])
    chunks = chunks[: args.max_parts]
    part_sizes = [len(c) for c in chunks]
    emitted_total = sum(part_sizes)

    global_start = 1
    all_names: list[str] = []
    LEAN_DIR.mkdir(parents=True, exist_ok=True)
    for part_idx, chunk in enumerate(chunks, start=1):
        names = _emit_part(part_idx, chunk, global_start, target)
        all_names.extend(names)
        global_start += len(chunk)

    assert len(all_names) == emitted_total, len(all_names)
    if args.max_parts >= 3 and emitted_total == total:
        _emit_all(total, part_sizes)
    elif emitted_total < total:
        print(f"partial emit: {emitted_total}/{total} parts={part_sizes} (no aggregator)")
    print(f"total={emitted_total}/{total} parts={part_sizes}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
