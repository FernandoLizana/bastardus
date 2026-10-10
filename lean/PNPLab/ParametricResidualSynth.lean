/-
  Parametric residual Closure₃ synthesis checklist (Category C / G5).

  Pack routing (`ParametricClosure3Goal`, OneFold…TenFold) discharges the
  all-odd window n≤14 by lookup.  True parametric synthesis must instead
  produce, for an arbitrary crossing, a residual axiom list + topology
  rename to `k4Closed` without consulting the pack table.

  This module records the obligation shape and shows every pack residual
  already meets it (infrastructure for a future `residualAxioms` emitter).
-/

import PNPLab.CrossingChordsToArcs
import PNPLab.CrossingPackCatalog
import PNPLab.CatalogIsoTransport
import PNPLab.ResidualAxiomsFromEndpoints

namespace PNPLab.Resolution

open Bicyclic

/--
  What a fresh residual synthesis for one crossing must discharge.
  Independent of which pack family (if any) covers the hop budget.
-/
structure ResidualSynthWitness where
  residual : List Clause
  Vres : List Nat
  rename : VarRename
  vars_ok : Vres.length = 6
  size_ok : residual.length = 16
  rename_src : rename.src = Vres
  rename_dst_template :
    rename.dst.all (fun v => k4TemplateVars.contains v) = true
  topology : topologySetEq rename residual = true
  no_empty : ¬ ([] ∈ residual)

/-- Topology set-eq alone already forbids □. -/
theorem ResidualSynthWitness.no_empty_of_topology (w : ResidualSynthWitness) :
    ¬ ([] ∈ w.residual) :=
  topology_set_eq_no_empty w.rename w.residual w.topology

/--
  Residual synthesis from endpoints via contracted-endpoint `residualAxioms`
  (no `packFamilyOfHops`).
-/
def residualSynthFromEndpoints (e : CrossingEndpoints) : ResidualSynthWitness where
  residual := residualAxioms e
  Vres := residualVres e
  rename := residualRename e
  vars_ok := residualVres_length e
  size_ok := residualAxioms_length e
  rename_src := residual_rename_src e
  rename_dst_template := residual_rename_dst_template e
  topology := residual_topology e
  no_empty := residualAxioms_no_empty_list e

theorem residualSynthFromEndpoints_eq_k4 (e : CrossingEndpoints) :
    (residualSynthFromEndpoints e).residual = k4Axioms ∧
      (residualSynthFromEndpoints e).Vres = k4TemplateVars :=
  ⟨rfl, rfl⟩

/-- Every crossing has a pack-free residual synthesis witness. -/
theorem residual_synth_from_endpoints_ok (e : CrossingEndpoints) :
    topologySetEq (residualSynthFromEndpoints e).rename
        (residualSynthFromEndpoints e).residual = true ∧
      ¬ ([] ∈ (residualSynthFromEndpoints e).residual) ∧
      (residualSynthFromEndpoints e).residual.length = 16 ∧
      e.toArcs.foldIter e.toArcs.total = K4Skeleton :=
  ⟨(residualSynthFromEndpoints e).topology, (residualSynthFromEndpoints e).no_empty,
    (residualSynthFromEndpoints e).size_ok, reaches_k4_skeleton e.toArcs⟩

/-- Mass window: pack-free residual synth for every endpoints config. -/
theorem mass_window_residual_synth_from_endpoints
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ w : ResidualSynthWitness,
      w.residual = k4Axioms ∧
        e.toArcs.total ≤ 10 ∧
        e.toArcs.foldIter e.toArcs.total = K4Skeleton :=
  ⟨residualSynthFromEndpoints e, rfl,
    crossing_hop_budget_le_pack_window e h5 h14,
    reaches_k4_skeleton e.toArcs⟩

private def packResidual : CrossingPackFamily → List Clause
  | .oneFold => ofoldRClosed
  | .multiFold => mfRClosed
  | .tripleFold => tfRClosed
  | .fourFold => ffRClosed
  | .fiveFold => xfRClosed
  | .sixFold => sfRClosed
  | .sevenFold => vfRClosed
  | .eightFold => efRClosed
  | .nineFold => nfRClosed
  | .tenFold => zfRClosed

private def packResidualRename : CrossingPackFamily → VarRename
  | .oneFold => identityRename
  | .multiFold => mfTopologyRename
  | .tripleFold => tfTopologyRename
  | .fourFold => ffTopologyRename
  | .fiveFold => xfTopologyRename
  | .sixFold => sfTopologyRename
  | .sevenFold => vfTopologyRename
  | .eightFold => efTopologyRename
  | .nineFold => nfTopologyRename
  | .tenFold => zfTopologyRename

private def packVres : CrossingPackFamily → List Nat
  | .oneFold => ofoldVres
  | .multiFold => mfVres
  | .tripleFold => tfVres
  | .fourFold => ffVres
  | .fiveFold => xfVres
  | .sixFold => sfVres
  | .sevenFold => vfVres
  | .eightFold => efVres
  | .nineFold => nfVres
  | .tenFold => zfVres

private theorem pack_topology_as_topologySetEq (f : CrossingPackFamily) :
    topologySetEq (packResidualRename f) (packResidual f) = true := by
  cases f <;> native_decide

/-- Pack residuals as synthesis witnesses (lookup path, not fresh synthesis). -/
def packResidualSynth (f : CrossingPackFamily) : ResidualSynthWitness where
  residual := packResidual f
  Vres := packVres f
  rename := packResidualRename f
  vars_ok := by cases f <;> native_decide
  size_ok := by cases f <;> native_decide
  rename_src := by cases f <;> rfl
  rename_dst_template := by cases f <;> native_decide
  topology := pack_topology_as_topologySetEq f
  no_empty := by
    cases f with
    | oneFold => exact ofoldR_no_empty
    | multiFold => exact mfR_no_empty
    | tripleFold => exact tfR_no_empty
    | fourFold => exact ffR_no_empty
    | fiveFold => exact xfR_no_empty
    | sixFold => exact sfR_no_empty
    | sevenFold => exact vfR_no_empty
    | eightFold => exact efR_no_empty
    | nineFold => exact nfR_no_empty
    | tenFold => exact zfR_no_empty

/-- Every pack family supplies a residual synthesis witness. -/
theorem pack_residual_synth_ok (f : CrossingPackFamily) :
    topologySetEq (packResidualSynth f).rename (packResidualSynth f).residual = true ∧
      ¬ ([] ∈ (packResidualSynth f).residual) ∧
      (packResidualSynth f).residual.length = 16 ∧
      (packResidualSynth f).Vres.length = 6 :=
  ⟨(packResidualSynth f).topology, (packResidualSynth f).no_empty,
    (packResidualSynth f).size_ok, (packResidualSynth f).vars_ok⟩

/-- Window routing + pack residual synth (still not ∀-instance synthesis). -/
theorem mass_window_has_pack_residual_synth
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ f : CrossingPackFamily,
      packFamilyOfHops e.toArcs.total = some f ∧
        topologySetEq (packResidualSynth f).rename (packResidualSynth f).residual = true ∧
        ¬ ([] ∈ (packResidualSynth f).residual) := by
  have hLo : 1 ≤ e.toArcs.total := by
    rw [CrossingEndpoints.toArcs_total]
    omega
  have hHi : e.toArcs.total ≤ 10 :=
    crossing_hop_budget_le_pack_window e h5 h14
  obtain ⟨f, hf, _, _⟩ := crossing_pack_route hLo hHi
  exact ⟨f, hf, (packResidualSynth f).topology, (packResidualSynth f).no_empty⟩

/-- Every pack family residual is topology-set-eq to template `residualAxioms`. -/
theorem pack_family_iso_to_residualAxioms
    (f : CrossingPackFamily) (e : CrossingEndpoints) :
    topologySetEq (packResidualSynth f).rename (packResidualSynth f).residual = true ∧
      residualAxioms e = k4Axioms :=
  ⟨(packResidualSynth f).topology, residualAxioms_eq_k4 e⟩

theorem all_packs_iso_to_residualAxioms (e : CrossingEndpoints) :
    (∀ f : CrossingPackFamily,
      topologySetEq (packResidualSynth f).rename (packResidualSynth f).residual = true) ∧
      residualAxioms e = k4Axioms :=
  ⟨fun f => (packResidualSynth f).topology, residualAxioms_eq_k4 e⟩

/-- Mass window: pack route + pack residual ≅ residualAxioms. -/
theorem mass_window_pack_iso_to_residualAxioms
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ f : CrossingPackFamily,
      packFamilyOfHops e.toArcs.total = some f ∧
        topologySetEq (packResidualSynth f).rename (packResidualSynth f).residual = true ∧
        residualAxioms e = k4Axioms := by
  obtain ⟨f, hf, htop, _⟩ := mass_window_has_pack_residual_synth e h5 h14
  exact ⟨f, hf, htop, residualAxioms_eq_k4 e⟩

def parametricResidualSynthOpenDoc : String :=
  "FreshG0Obligation seeds (alt1..6+samp1..3); ParametricGlobalEdgeIso seeds; " ++
  "open: Closure₃(G_e) / global-edge map ∀e."

def parametricResidualSynthDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

end PNPLab.Resolution
