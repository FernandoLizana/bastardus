/-
  Residual axioms from crossing endpoints (Category C / G5).

  After the combinatorial fold schedule reaches `K4Skeleton`, the residual
  Tseitin system is a K₄ XOR CNF.  In **contracted-endpoint coordinates**
  (template vars `{1,…,6}`), that residual is exactly `k4Axioms`.

  This is *not* the Python `residual_of` labeling under global `_edge_var_map`
  (those differ by a permutation iso — E2 461/461, 0 flips).  It *is*
  `residualAxioms` without `packFamilyOfHops` lookup.
-/

import PNPLab.CrossingChordsToArcs
import PNPLab.K4ResidualCatalog
import PNPLab.CatalogIsoTransport
import PNPLab.VarRenameTransport
import PNPLab.RenameClosedTransport
import PNPLab.OneFoldProjection
import PNPLab.ResidualClosureAll

namespace PNPLab.Resolution

open Bicyclic

/--
  Contracted-endpoint residual axioms for any crossing.
  Independent of `n`, hop budget, and pack family.
-/
def residualAxioms (_e : CrossingEndpoints) : List Clause :=
  k4Axioms

/-- Template residual edge variables. -/
def residualVres (_e : CrossingEndpoints) : List Nat :=
  k4TemplateVars

/-- Identity rename on the K₄ template. -/
def residualRename (_e : CrossingEndpoints) : VarRename :=
  identityRename

theorem residualAxioms_eq_k4 (e : CrossingEndpoints) :
    residualAxioms e = k4Axioms :=
  rfl

/-- OneFold residual is a permutation of contracted-endpoint `residualAxioms`. -/
theorem residualAxioms_perm_ofoldR (e : CrossingEndpoints) :
    List.Perm ofoldRClosed (residualAxioms e) := by
  simpa [residualAxioms_eq_k4 e] using ofoldRClosed_perm_k4

theorem residualVres_length (e : CrossingEndpoints) :
    (residualVres e).length = 6 :=
  k4TemplateVars_length

theorem residualAxioms_length (e : CrossingEndpoints) :
    (residualAxioms e).length = 16 := by
  simp [residualAxioms]
  native_decide

theorem residualAxioms_no_empty_list (e : CrossingEndpoints) :
    ¬ ([] ∈ residualAxioms e) := by
  simp [residualAxioms]
  native_decide

theorem residual_topology (e : CrossingEndpoints) :
    topologySetEq (residualRename e) (residualAxioms e) = true := by
  simp [residualRename, residualAxioms, topologySetEq]
  native_decide

/-- Template residual is the iso codomain for topology transport. -/
theorem residualAxioms_is_iso_codomain (e : CrossingEndpoints) :
    residualAxioms e = k4Closed ∧
      topologySetEq (residualRename e) (residualAxioms e) = true :=
  ⟨by simpa [k4Closed] using residualAxioms_eq_k4 e, residual_topology e⟩

/--
  Canonical catalog residual `rc1` (Python `residual_of` global edge vars)
  is topology-set-eq to the template, hence ≅ `residualAxioms`.
-/
theorem rc1_global_edge_iso_to_residualAxioms (e : CrossingEndpoints) :
    topologySetEq rc1TopologyRename rc1RClosed = true ∧
      residualAxioms e = k4Axioms := by
  refine ⟨?_, residualAxioms_eq_k4 e⟩
  have h := rc1TopologySetEq_true
  simpa [topologySetEq, rc1TopologySetEq] using h

theorem residual_rename_src (e : CrossingEndpoints) :
    (residualRename e).src = residualVres e :=
  rfl

theorem residual_rename_dst_template (e : CrossingEndpoints) :
    (residualRename e).dst.all (fun v => k4TemplateVars.contains v) = true := by
  simp [residualRename]
  native_decide

/--
  Schedule lands on K₄ skeleton; residual axioms are the template Closure₃.
  No pack-family lookup.
-/
theorem residual_synth_schedule (e : CrossingEndpoints) :
    residualAxioms e = k4Axioms ∧
      e.toArcs.foldIter e.toArcs.total = K4Skeleton ∧
      topologySetEq (residualRename e) (residualAxioms e) = true ∧
      ¬ ([] ∈ residualAxioms e) :=
  ⟨residualAxioms_eq_k4 e, reaches_k4_skeleton e.toArcs,
    residual_topology e, residualAxioms_no_empty_list e⟩

/-- Every mass-window crossing has pack-free residual axioms (= K₄ template). -/
theorem mass_window_residual_axioms
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    residualAxioms e = k4Axioms ∧
      e.toArcs.total ≤ 10 ∧
      1 ≤ e.toArcs.total ∧
      e.toArcs.foldIter e.toArcs.total = K4Skeleton ∧
      topologySetEq (residualRename e) (residualAxioms e) = true :=
  ⟨residualAxioms_eq_k4 e,
    crossing_hop_budget_le_pack_window e h5 h14,
    by rw [CrossingEndpoints.toArcs_total]; omega,
    reaches_k4_skeleton e.toArcs,
    residual_topology e⟩

def residualAxiomsFromEndpointsDoc : String :=
  "Contracted-endpoint residualAxioms = k4Axioms; " ++
  "global _edge_var_map labeling remains a permutation iso (E2)."

/-- Full catalog (461) topology flags ⇒ global-edge ≅ template residualAxioms. -/
theorem all_catalog_iso_to_residualAxioms (e : CrossingEndpoints) :
    allResidualClosureTopologyFlags.all (· = true) ∧
      residualAxioms e = k4Axioms :=
  ⟨all_residual_closures_topology_set_eq, residualAxioms_eq_k4 e⟩

def residualAxiomsOpenDoc : String :=
  "residualAxioms ≅ ofoldR (Perm); catalog 461/461 topology ≅ residualAxioms; " ++
  "open: parametric global _edge_var_map ∀e + fresh G₀ ∀e."

end PNPLab.Resolution
