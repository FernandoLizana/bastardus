/-
  Aggregated parametric discharge (461/461 catalog).

  Composes part-level `native_decide` witnesses — avoids re-evaluating 461
  `parametricProjOK` calls in one giant `native_decide`.
-/

import PNPLab.ParametricDischargePart1
import PNPLab.ParametricDischargePart2
import PNPLab.ParametricDischargePart3
import PNPLab.CrossingResidualCatalog
import PNPLab.ParametricProjectionMass

namespace PNPLab.Bicyclic

theorem List.all_append {α} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil => simp [List.all]
  | cons x xs ih => simp [List.all, ih, Bool.and_left_comm, Bool.and_comm]

def allParametricDischargeProjOkFlags : List Bool :=
  parametricDischargeProjOkFlagsPart1 ++ parametricDischargeProjOkFlagsPart2 ++
    parametricDischargeProjOkFlagsPart3

def allParametricDischargeTopologyFlags : List Bool :=
  parametricDischargeTopologyFlagsPart1 ++ parametricDischargeTopologyFlagsPart2 ++
    parametricDischargeTopologyFlagsPart3

theorem all_parametric_discharges_proj_ok_parts :
    parametricDischargeProjOkFlagsPart1.all (· = true) ∧
      parametricDischargeProjOkFlagsPart2.all (· = true) ∧
      parametricDischargeProjOkFlagsPart3.all (· = true) :=
  ⟨all_parametric_discharge_proj_ok_part1, all_parametric_discharge_proj_ok_part2,
    all_parametric_discharge_proj_ok_part3⟩

theorem all_parametric_discharges_topology_parts :
    parametricDischargeTopologyFlagsPart1.all (· = true) ∧
      parametricDischargeTopologyFlagsPart2.all (· = true) ∧
      parametricDischargeTopologyFlagsPart3.all (· = true) :=
  ⟨all_parametric_discharge_topology_part1, all_parametric_discharge_topology_part2,
    all_parametric_discharge_topology_part3⟩

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
    allParametricDischargeProjOkFlags.length = 461 := by
  unfold allParametricDischargeProjOkFlags
  simp only [List.length_append, parametric_discharge_part1_count,
    parametric_discharge_part2_count, parametric_discharge_part3_count]

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
