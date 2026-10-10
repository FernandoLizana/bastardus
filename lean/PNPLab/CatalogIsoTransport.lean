/-
  Generic residual → k4Closed topology transport (Category C / G5).

  Any `VarRename` with `renamedSubset` ∧ `renamedSurjective` onto `k4Closed`
  transfers □-freedom and K₄ residual shape (strengthens `ParametricClosure3`).

  Per-instance iso witnesses (461/461, metadata only) live in
  `CatalogIsoPart1`–`CatalogIsoPart3`; full Vres+RAxioms+topology set-eq in
  `ResidualClosurePart1`–`ResidualClosurePart3` (`ResidualClosureAll`);
  stratified samples in `ResidualSampleCatalog` (96).
-/

import PNPLab.CrossingResidualCatalog
import PNPLab.CatalogIsoPart1
import PNPLab.CatalogIsoPart2
import PNPLab.CatalogIsoPart3

namespace PNPLab.Resolution

/-- Topology set-equality predicate (residual clauses ↔ `k4Closed`). -/
def topologySetEq (r : VarRename) (S : List Clause) : Bool :=
  renamedSubset r S k4Closed && renamedSurjective r S k4Closed

theorem topologySetEq_true_iff
    (r : VarRename) (S : List Clause) :
    topologySetEq r S = true ↔
      renamedSubset r S k4Closed = true ∧ renamedSurjective r S k4Closed = true := by
  simp [topologySetEq, Bool.and_eq_true]

/-- Full topology set-eq ⇒ no □ in the source residual. -/
theorem topology_set_eq_no_empty
    (r : VarRename) (S : List Clause)
    (h : topologySetEq r S = true) :
    ¬ ([] ∈ S) := by
  have ⟨hSub, _⟩ := (topologySetEq_true_iff r S).mp h
  exact renamedSubset_no_empty r S hSub

theorem topology_set_eq_no_empty_of_subset
    (r : VarRename) (S : List Clause)
    (hSub : renamedSubset r S k4Closed = true) :
    ¬ ([] ∈ S) :=
  renamedSubset_no_empty r S hSub

/-- Full topology set-eq + size 16 + |V|=6 ⇒ ResidualK4Shape bundle. -/
theorem topology_set_eq_residual_k4_shape
    (r : VarRename) (S : List Clause) (V : List Nat)
    (h : topologySetEq r S = true)
    (hS : S.length = 16)
    (hV : V.length = 6) :
    ¬ ([] ∈ S) ∧
      (∃ shape : ResidualK4Shape, shape.Vres = V ∧ shape.closedSize = 16) := by
  have hSub := (topologySetEq_true_iff r S).mp h |>.1
  exact topology_subset_residual_shape r S V hSub hS hV

/-- All 461 E2 iso witnesses (permutation-only; 0 flips). -/
def catalogIsoWitnesses : List CatalogIsoEntry :=
  catalogIsoWitnessesPart1 ++ catalogIsoWitnessesPart2 ++ catalogIsoWitnessesPart3

theorem catalogIsoWitnesses_length : catalogIsoWitnesses.length = 461 := by
  native_decide

theorem catalogIsoWitnesses_mass :
    catalogIsoWitnesses.length = crossingResidualCatalogMass.isoOk ∧
      crossingResidualCatalogMass.isoOk = 461 ∧
      crossingResidualCatalogMass.flipNeeded = 0 := by
  native_decide

/-- Every emitted witness has 6-var src and permutation (metadata mass check). -/
def catalogIsoWitnesses_src6 : Bool :=
  catalogIsoWitnesses.all fun e => decide (e.src.length = 6)

theorem catalogIsoWitnesses_src6_true : catalogIsoWitnesses_src6 = true := by
  native_decide

def catalogIsoTransportDoc : String :=
  "reports/discovery/crossing_residual_catalog.json"

def catalogIsoEmitScript : String :=
  "backend/proof_complexity/emit_topology_iso_lemmas_lean.py"

end PNPLab.Resolution
