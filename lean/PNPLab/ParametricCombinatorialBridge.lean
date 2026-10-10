/-
  Prop-level combinatorial bridge (E5): saturate → WidthClosure, discharge ⇒ FreshG0,
  and honest mass-window links to the 461/461 emit catalog.

  Does **not** prove `∀ e, ParametricEndpointsDischarge e` — see
  `parametricCombinatorialOpenDoc` in `CrossingEndpointsParametricGoal.lean`.
-/

import PNPLab.CrossingEndpointsParametricGoal
import PNPLab.ParametricCombinatorialDischarge
import PNPLab.ParametricDischargeAll
import PNPLab.ClosureFromList
import PNPLab.CrossingEndpointsClosure3

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-- Discharge witnesses imply Prop-level projection inclusion. -/
theorem parametric_discharge_fresh_g0 {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  parametric_fresh_g0_of_discharge d

/-- Mass-window specialization (5 ≤ n ≤ 14): same conclusion with window hyps. -/
theorem parametric_mass_window_discharge_fresh_g0
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14)
    (d : ParametricEndpointsDischarge e) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  parametric_fresh_g0_of_mass_window e h5 h14 d

theorem parametric_discharge_proj_holds {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : parametricProjHolds e :=
  parametricProjHolds_of_discharge d

def parametric_discharge_projection {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : ProjectionInclusion 3 :=
  parametricProjectionFromDischarge d

theorem parametric_witnesses_fresh_g0 {e : CrossingEndpoints}
    (w : ParametricDischargeWitnesses e) :
    ∃ fw : FreshG0Obligation, ¬ fw.projection.gClosure.mem [] :=
  parametric_discharge_witnesses_fresh_g0 w

theorem parametric_canonical_discharges :
    ParametricEndpointsDischarge c5OfoldEndpoints ∧
      ParametricEndpointsDischarge c5Alt1Endpoints ∧
      ParametricEndpointsDischarge c6Endpoints0123 ∧
      ParametricEndpointsDischarge c7Endpoints0123 ∧
      ParametricEndpointsDischarge c8Endpoints0123 ∧
      ParametricEndpointsDischarge c9Endpoints0123 ∧
      ParametricEndpointsDischarge c10Endpoints024 :=
  canonical_parametric_discharges

/-- Emit catalog 461/461 (not combinatorial synthesis); contrast with open `parametricDischargeCombinatorialForAll`. -/
theorem parametric_discharge_emit_catalog_ok :
    allParametricDischargeProjOkFlags.length = 461 ∧
      allParametricDischargeProjOkFlags.all (· = true) :=
  ⟨all_parametric_discharges_count, all_parametric_discharges_proj_ok⟩

def parametricCombinatorialBridgeDoc : String :=
  "Witnesses⇒Discharge; saturate→WidthClosure; discharge→FreshG0; " ++
  "canonical 7/461 partial; 461 emit flags; see ParametricCombinatorialDischarge"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem parametric_catalog_discharge_mass :
    allParametricDischargeProjOkFlags.length = 461 ∧
      allParametricDischargeProjOkFlags.all (· = true) ∧
      parametricProjectionMass.projOk = 461 ∧
      parametricProjectionMass.allOk = true ∧
      crossingResidualCatalogMass.isoOk = 461 := by
  refine ⟨all_parametric_discharges_count, all_parametric_discharges_proj_ok, ?_, ?_, ?_⟩
  · exact (parametricProjectionMass_ok).2.1
  · exact (parametricProjectionMass_ok).2.2.2
  · exact parametric_projection_mass_matches_catalog.2

theorem parametric_emit_mass_link :
    allParametricDischargeProjOkFlags.length = parametricProjectionMass.projOk ∧
      parametricProjectionMass.projOk = crossingResidualCatalogMass.isoOk := by
  rw [all_parametric_discharges_count]
  exact ⟨rfl, parametric_projection_mass_matches_catalog.1⟩

theorem parametric_discharge_topology_mass :
    allParametricDischargeTopologyFlags.length = 461 ∧
      allParametricDischargeTopologyFlags.all (· = true) := by
  refine ⟨?_, all_parametric_discharges_topology⟩
  native_decide

end PNPLab.Resolution
