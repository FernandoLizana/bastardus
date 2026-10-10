/-
  Parametric endpoints goal bundle (Category C / E5).

  Discharges FreshG0 + topology from `closure3` + `residualGlobal` witnesses
  (non-pack track).  Per-seed Bool checks still come from emit / `native_decide`;
  this module lifts them into a single `ParametricEndpointsGoal` API and a
  generic implication: discharge ⇒ ProjectionInclusion + FreshG0.
-/

import PNPLab.CrossingEndpointsParametricProjection
import PNPLab.CrossingEndpointsGlobalRename
import PNPLab.CrossingEndpointsSmokeMass
import PNPLab.FreshG0Obligation
import PNPLab.ParametricProjectionMass

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-- Bool witnesses for non-pack parametric G₀→R (Python `parametricProjOK` parity). -/
structure ParametricEndpointsDischarge (e : CrossingEndpoints) where
  proj_ok : parametricProjOK e = true
  g_closed : closedUnder (closure3 e) 3 (parametricGPivots e) = true
  g_lits :
    ((closure3 e).all fun C => C.all fun lit => decide (lit ∈ parametricGPivots e)) = true
  g_axioms : (e.tseitinAxioms.all fun A => (closure3 e).contains A) = true
  r_closed : k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true
  r_lits :
    ((residualGlobalClosed e).all fun C =>
      C.all fun lit => decide (lit ∈ parametricRPivots e)) = true
  r_axioms :
    ((residualGlobalAxioms e).all fun A => (residualGlobalClosed e).contains A) = true
  r_no_empty : ¬ ([] ∈ residualGlobalAxioms e)

/-- Signed topology rename onto K₄ template (E2 permutation or index map). -/
structure ParametricTopologyDischarge (e : CrossingEndpoints) where
  rename : VarRename
  topology_ok : topologySetEq rename (residualGlobalAxioms e) = true

/-- Full non-pack parametric checklist for one crossing seed. -/
structure ParametricEndpointsGoal (e : CrossingEndpoints) where
  discharge : ParametricEndpointsDischarge e
  topology : ParametricTopologyDischarge e

def parametricProjectionFromDischarge {e : CrossingEndpoints}
    (h : ParametricEndpointsDischarge e) : ProjectionInclusion 3 :=
  parametricProjectionOf e h.proj_ok h.g_closed h.g_lits h.g_axioms h.r_closed h.r_lits h.r_axioms

theorem parametricProjHolds_of_discharge {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : parametricProjHolds e :=
  parametricProjHolds_of_projOK d.proj_ok

theorem parametricProjHolds_of_discharge_projection {e : CrossingEndpoints}
    (d : ParametricEndpointsDischarge e) : parametricProjHolds e :=
  parametricProjHolds_of_projection (parametricProjectionFromDischarge d)
    (parametricGClosureOf_mem e d.g_closed d.g_lits d.g_axioms)
    (parametricRClosureOf_mem e d.r_closed d.r_lits d.r_axioms) rfl

theorem parametricR_no_empty_of_discharge {e : CrossingEndpoints}
    (h : ParametricEndpointsDischarge e) :
    ¬ (parametricRClosureOf e h.r_closed h.r_lits h.r_axioms).mem [] := fun hmem =>
  h.r_no_empty hmem

def parametricFreshG0FromDischarge {e : CrossingEndpoints}
    (h : ParametricEndpointsDischarge e) : FreshG0Obligation :=
  freshG0_of_projection (parametricProjectionFromDischarge h)
    (parametricR_no_empty_of_discharge h)

theorem parametric_fresh_g0_of_discharge {e : CrossingEndpoints}
    (h : ParametricEndpointsDischarge e) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  ⟨parametricFreshG0FromDischarge h, (parametricFreshG0FromDischarge h).g_no_empty⟩

theorem parametric_goal_fresh_g0 {e : CrossingEndpoints}
    (g : ParametricEndpointsGoal e) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  parametric_fresh_g0_of_discharge g.discharge

/-- Mass window: discharge ⇒ non-pack FreshG0 (Prop-level ∀e step). -/
theorem parametric_fresh_g0_of_mass_window
    (e : CrossingEndpoints) (_h5 : 5 ≤ e.n) (_h14 : e.n ≤ 14)
    (d : ParametricEndpointsDischarge e) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] :=
  parametric_fresh_g0_of_discharge d

def parametric_projection_of_mass_window_discharge
    (e : CrossingEndpoints) (d : ParametricEndpointsDischarge e) : ProjectionInclusion 3 :=
  parametricProjectionFromDischarge d

def parametric_goal_projection
    {e : CrossingEndpoints} (g : ParametricEndpointsGoal e) : ProjectionInclusion 3 :=
  parametricProjectionFromDischarge g.discharge

theorem c5OfoldParametricDischarge : ParametricEndpointsDischarge c5OfoldEndpoints where
  proj_ok := c5Ofold_parametricProjOK
  g_closed := c5Ofold_closure3_closed
  g_lits := c5Ofold_parametricG_lits_in_pivots
  g_axioms := c5Ofold_parametricG_axioms_subset
  r_closed := by native_decide
  r_lits := by native_decide
  r_axioms := c5Ofold_parametricR_axioms_subset
  r_no_empty := c5Ofold_residual_axioms_no_empty

theorem c5Alt1ParametricDischarge : ParametricEndpointsDischarge c5Alt1Endpoints where
  proj_ok := c5Alt1_parametricProjOK
  g_closed := c5Alt1_closure3_closed
  g_lits := c5Alt1_parametricG_lits_in_pivots
  g_axioms := c5Alt1_parametricG_axioms_subset
  r_closed := by native_decide
  r_lits := by native_decide
  r_axioms := c5Alt1_parametricR_axioms_subset
  r_no_empty := c5Alt1_residual_axioms_no_empty

theorem c6ParametricDischarge : ParametricEndpointsDischarge c6Endpoints0123 where
  proj_ok := c6_parametricProjOK
  g_closed := c6_closure3_closed
  g_lits := c6_parametricG_lits_in_pivots
  g_axioms := c6_parametricG_axioms_subset
  r_closed := by native_decide
  r_lits := by native_decide
  r_axioms := c6_parametricR_axioms_subset
  r_no_empty := c6_residual_axioms_no_empty

theorem c7ParametricDischarge : ParametricEndpointsDischarge c7Endpoints0123 where
  proj_ok := c7_parametricProjOK
  g_closed := c7_closure3_closed
  g_lits := c7_parametricG_lits_in_pivots
  g_axioms := c7_parametricG_axioms_subset
  r_closed := c7_residual_closed_under
  r_lits := c7_parametricR_lits_in_pivots
  r_axioms := c7_parametricR_axioms_subset
  r_no_empty := c7_residual_axioms_no_empty

theorem c8ParametricDischarge : ParametricEndpointsDischarge c8Endpoints0123 where
  proj_ok := c8_parametricProjOK
  g_closed := c8_closure3_closed
  g_lits := c8_parametricG_lits_in_pivots
  g_axioms := c8_parametricG_axioms_subset
  r_closed := c8_residual_closed_under
  r_lits := c8_parametricR_lits_in_pivots
  r_axioms := c8_parametricR_axioms_subset
  r_no_empty := c8_residual_axioms_no_empty

theorem c9ParametricDischarge : ParametricEndpointsDischarge c9Endpoints0123 where
  proj_ok := c9_parametricProjOK
  g_closed := c9_closure3_closed
  g_lits := c9_parametricG_lits_in_pivots
  g_axioms := c9_parametricG_axioms_subset
  r_closed := c9_residual_closed_under
  r_lits := c9_parametricR_lits_in_pivots
  r_axioms := c9_parametricR_axioms_subset
  r_no_empty := c9_residual_axioms_no_empty

theorem c10ParametricDischarge : ParametricEndpointsDischarge c10Endpoints024 where
  proj_ok := c10_parametricProjOK
  g_closed := c10_closure3_closed
  g_lits := c10_parametricG_lits_in_pivots
  g_axioms := c10_parametricG_axioms_subset
  r_closed := c10_residual_closed_under
  r_lits := c10_parametricR_lits_in_pivots
  r_axioms := c10_parametricR_axioms_subset
  r_no_empty := c10_residual_axioms_no_empty

def c5OfoldParametricGoal : ParametricEndpointsGoal c5OfoldEndpoints where
  discharge := c5OfoldParametricDischarge
  topology := ⟨ofoldGlobalTopologyRename, ofoldGlobalTopologySetEq⟩

def c5Alt1ParametricGoal : ParametricEndpointsGoal c5Alt1Endpoints where
  discharge := c5Alt1ParametricDischarge
  topology :=
    ⟨globalRenameFromEndpoints c5Alt1Endpoints (by native_decide), c5Alt1_globalRename_topology⟩

def c6ParametricGoal : ParametricEndpointsGoal c6Endpoints0123 where
  discharge := c6ParametricDischarge
  topology := ⟨alt2TopologyRename, c6_globalTopologySetEq⟩

def c7ParametricGoal : ParametricEndpointsGoal c7Endpoints0123 where
  discharge := c7ParametricDischarge
  topology :=
    ⟨globalTopologyRenameCanonical c7Endpoints0123 (by native_decide), c70123Rename_topology⟩

def c8ParametricGoal : ParametricEndpointsGoal c8Endpoints0123 where
  discharge := c8ParametricDischarge
  topology :=
    ⟨globalTopologyRenameCanonical c8Endpoints0123 (by native_decide), c80123Rename_topology⟩

def c9ParametricGoal : ParametricEndpointsGoal c9Endpoints0123 where
  discharge := c9ParametricDischarge
  topology :=
    ⟨globalTopologyRenameCanonical c9Endpoints0123 (by native_decide), c90123Rename_topology⟩

def c10ParametricGoal : ParametricEndpointsGoal c10Endpoints024 where
  discharge := c10ParametricDischarge
  topology :=
    ⟨globalTopologyRenameCanonical c10Endpoints024 (by native_decide), c10024Rename_topology⟩

theorem canonical_parametric_goals_fresh_g0 :
    (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) :=
  ⟨parametric_fresh_g0_of_discharge c5OfoldParametricDischarge,
    parametric_fresh_g0_of_discharge c5Alt1ParametricDischarge,
    parametric_fresh_g0_of_discharge c6ParametricDischarge,
    parametric_fresh_g0_of_discharge c7ParametricDischarge,
    parametric_fresh_g0_of_discharge c8ParametricDischarge,
    parametric_fresh_g0_of_discharge c9ParametricDischarge,
    parametric_fresh_g0_of_discharge c10ParametricDischarge⟩

def crossingEndpointsParametricGoalOpenDoc : String :=
  "ParametricEndpointsGoal; canonical n=5..10 + E2 mass 461/461 proj; " ++
  "Prop discharge⇒FreshG0 OK; open: combinatorial ∀e (no emit/table)"

def parametricCombinatorialOpenDoc : String :=
  "BLOCKER: combinatorial ∀e = parametricDischargeCombinatorialWitnessesForAll " ++
  "(per-instance saturate on closure3/residualGlobal + proj Bool); topology perm closed " ++
  "461/461 via (n,toArcs,p0) tabulation — not the gap. Provable subclasses from ForAll: " ++
  "fixedN, fixedNRange, massWindow, arcP0Catalog, arcUniqueCatalog. Sufficient per instance: " ++
  "ParametricCombinatorialGoalSufficient (witnesses + topologySetEq); reduces to " ++
  "ParametricArcP0GoalSufficient when parametricDischargeReducesToArcP0; to " ++
  "ParametricArcUniqueGoalSufficient when parametricDischargeReducesToArcUnique (83/461). " ++
  "Mass window 5≤n≤14 ⇒ hop 1..10 necessary not sufficient (c8EndpointsEven vs c8Endpoints0123: same hop, projOK, discharge only canonical). " ++
  "461/461 discharge + topology via emit only. See parametricCombinatorialDischargeCeilingDoc."

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem parametric_projection_mass_link :
    parametricProjectionMass.projOk = 461 ∧
      parametricProjectionMass.allOk = true ∧
      parametricProjectionMass.projOk = crossingResidualCatalogMass.isoOk := by
  native_decide

theorem canonical_parametric_topology_flags :
    (topologySetEq ofoldGlobalTopologyRename (residualGlobalAxioms c5OfoldEndpoints) = true) ∧
      (topologySetEq (globalRenameFromEndpoints c5Alt1Endpoints (by native_decide))
          (residualGlobalAxioms c5Alt1Endpoints) = true) ∧
      (topologySetEq alt2TopologyRename (residualGlobalAxioms c6Endpoints0123) = true) ∧
      (topologySetEq (globalTopologyRenameCanonical c7Endpoints0123 (by native_decide))
          (residualGlobalAxioms c7Endpoints0123) = true) ∧
      (topologySetEq (globalTopologyRenameCanonical c8Endpoints0123 (by native_decide))
          (residualGlobalAxioms c8Endpoints0123) = true) ∧
      (topologySetEq (globalTopologyRenameCanonical c9Endpoints0123 (by native_decide))
          (residualGlobalAxioms c9Endpoints0123) = true) ∧
      (topologySetEq (globalTopologyRenameCanonical c10Endpoints024 (by native_decide))
          (residualGlobalAxioms c10Endpoints024) = true) :=
  ⟨ofoldGlobalTopologySetEq, c5Alt1_globalRename_topology, c6_globalTopologySetEq,
    c70123Rename_topology, c80123Rename_topology, c90123Rename_topology, c10024Rename_topology⟩

end PNPLab.Resolution
