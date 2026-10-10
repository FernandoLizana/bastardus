/-
  Parametric global `_edge_var_map` iso checklist (Category C / G5).

  E2 mass (461 catalog + 96 samples + alts) discharges topology set-eq
  per instance via `native_decide`.  A true parametric map would build
  residual + VarRename from `CrossingEndpoints` without a table lookup.
-/

import PNPLab.ResidualAxiomsFromEndpoints
import PNPLab.AltResidualClosures
import PNPLab.SampleResidualClosures
import PNPLab.ResidualClosureAll
import PNPLab.CrossingEndpointsGraph
import PNPLab.CrossingEndpointsGlobalRename
import PNPLab.CrossingEndpointsGlobalResidual
import PNPLab.CrossingEndpointsGlobalResidualXor

namespace PNPLab.Resolution

/--
  What a global-edge residual iso witness must discharge.
  Honest gap: `residual` / `rename` are not yet functions of endpoints.
-/
structure ParametricGlobalEdgeIso where
  residual : List Clause
  Vres : List Nat
  rename : VarRename
  vars_ok : Vres.length = 6
  size_ok : residual.length = 16
  rename_src : rename.src = Vres
  topology : topologySetEq rename residual = true
  no_empty : ¬ ([] ∈ residual)

theorem ParametricGlobalEdgeIso.no_empty_of_topology (w : ParametricGlobalEdgeIso) :
    ¬ ([] ∈ w.residual) :=
  topology_set_eq_no_empty w.rename w.residual w.topology

def alt1_as_global_edge_iso : ParametricGlobalEdgeIso where
  residual := alt1RClosed
  Vres := alt1Vres
  rename := alt1TopologyRename
  vars_ok := alt1Vres_len
  size_ok := alt1R_size
  rename_src := rfl
  topology := by
    have h := alt1TopologySetEq_true
    simpa [topologySetEq, alt1TopologySetEq] using h
  no_empty := by
    have h := alt1R_no_empty
    simpa [alt1RClosed] using h

def samp1_as_global_edge_iso : ParametricGlobalEdgeIso where
  residual := samp1RClosed
  Vres := samp1Vres
  rename := samp1TopologyRename
  vars_ok := samp1Vres_len
  size_ok := samp1R_size
  rename_src := rfl
  topology := by
    have h := samp1TopologySetEq_true
    simpa [topologySetEq, samp1TopologySetEq] using h
  no_empty := by
    have h := samp1R_no_empty
    simpa [samp1RClosed] using h

def rc1_as_global_edge_iso : ParametricGlobalEdgeIso where
  residual := rc1RClosed
  Vres := rc1Vres
  rename := rc1TopologyRename
  vars_ok := rc1Vres_len
  size_ok := rc1R_size
  rename_src := rfl
  topology := by
    have h := rc1TopologySetEq_true
    simpa [topologySetEq, rc1TopologySetEq] using h
  no_empty := by
    have h := rc1R_no_empty
    simpa [rc1RClosed] using h

def alt2_as_global_edge_iso : ParametricGlobalEdgeIso where
  residual := alt2RClosed
  Vres := alt2Vres
  rename := alt2TopologyRename
  vars_ok := alt2Vres_len
  size_ok := alt2R_size
  rename_src := rfl
  topology := by
    have h := alt2TopologySetEq_true
    simpa [topologySetEq, alt2TopologySetEq] using h
  no_empty := by
    have h := alt2R_no_empty
    simpa [alt2RClosed] using h

def samp6_as_global_edge_iso : ParametricGlobalEdgeIso where
  residual := samp6RClosed
  Vres := samp6Vres
  rename := samp6TopologyRename
  vars_ok := samp6Vres_len
  size_ok := samp6R_size
  rename_src := rfl
  topology := by
    have h := samp6TopologySetEq_true
    simpa [topologySetEq, samp6TopologySetEq] using h
  no_empty := by
    have h := samp6R_no_empty
    simpa [samp6RClosed] using h

/-- Mass form: all catalog topology flags + template residualAxioms. -/
theorem catalog_mass_global_edge_iso (e : Bicyclic.CrossingEndpoints) :
    allResidualClosureTopologyFlags.all (· = true) ∧
      residualAxioms e = k4Axioms :=
  all_catalog_iso_to_residualAxioms e

/-- Samples mass endpoints + template (full 96 topology via `all_sample_topology_set_eq`). -/
theorem samples_mass_global_edge_iso (e : Bicyclic.CrossingEndpoints) :
    residualAxioms e = k4Axioms ∧
      samp1TopologySetEq = true ∧ samp96TopologySetEq = true :=
  ⟨residualAxioms_eq_k4 e, samp1TopologySetEq_true, samp96TopologySetEq_true⟩

theorem all_alt_global_edge_iso_flags :
    alt1TopologySetEq = true ∧ alt2TopologySetEq = true ∧ alt3TopologySetEq = true ∧
      alt4TopologySetEq = true ∧ alt5TopologySetEq = true ∧ alt6TopologySetEq = true :=
  all_alt_topology_set_eq

theorem global_edge_iso_seeds_ok :
    topologySetEq alt1TopologyRename alt1RClosed = true ∧
      topologySetEq samp1TopologyRename samp1RClosed = true ∧
      topologySetEq rc1TopologyRename rc1RClosed = true ∧
      topologySetEq alt2TopologyRename alt2RClosed = true ∧
      topologySetEq samp6TopologyRename samp6RClosed = true :=
  ⟨alt1_as_global_edge_iso.topology, samp1_as_global_edge_iso.topology,
    rc1_as_global_edge_iso.topology, alt2_as_global_edge_iso.topology,
    samp6_as_global_edge_iso.topology⟩

def parametricGlobalEdgeIsoSeedCount : Nat := 5

theorem parametricGlobalEdgeIsoSeedCount_eq :
    parametricGlobalEdgeIsoSeedCount = 5 := rfl

/-- `edgeVar` is now a function of `CrossingEndpoints` (Python `_edge_var_map`). -/
theorem global_edge_var_map_from_endpoints :
    Bicyclic.c5OfoldEndpoints.edgeVar 0 1 = some 1 ∧
      Bicyclic.c5Alt1Endpoints.edgeVar 1 4 = some 5 ∧
      Bicyclic.c5OfoldEndpoints.edgeList.length = 7 :=
  ⟨by native_decide, by native_decide, by native_decide⟩

def parametricGlobalEdgeIsoDoc : String :=
  "ParametricGlobalEdgeIso seeds + edgeVar + residualGlobalVres (Python residual_of)"

def parametricGlobalEdgeIsoOpenDoc : String :=
  "edgeVar + residualGlobal + parametric ProjectionInclusion (c5); open: ∀e + signed VarRename"

/-- Smoke: parametric global `Vres` matches Python on canonical C₅ seeds. -/
theorem global_edge_vres_from_endpoints :
    Bicyclic.residualGlobalVres Bicyclic.c5OfoldEndpoints = [1, 2, 4, 5, 6, 7] ∧
      Bicyclic.residualGlobalVres Bicyclic.c5Alt1Endpoints = alt1Vres := by
  native_decide

/-- Smoke: residual XOR under global labels matches Python `residual_of` RAxioms. -/
theorem global_edge_residual_xor_from_endpoints :
    Bicyclic.residualGlobalClosed Bicyclic.c5Alt1Endpoints = alt1RClosed ∧
      Bicyclic.residualGlobalClosed Bicyclic.c5OfoldEndpoints = Bicyclic.ofoldGlobalRAxioms ∧
      topologySetEq alt1TopologyRename (Bicyclic.residualGlobalAxioms Bicyclic.c5Alt1Endpoints) = true ∧
      topologySetEq Bicyclic.ofoldGlobalTopologyRename
        (Bicyclic.residualGlobalAxioms Bicyclic.c5OfoldEndpoints) = true := by
  native_decide

end PNPLab.Resolution
