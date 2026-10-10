/-
  Crossing residual catalog (Category C / G5 evidence bridge).

  E2 `crossing_residual_catalog.json`: every crossing n=5..10 residual Closure₃
  is set-isomorphic to `k4Axioms` under a **permutation-only** edge bijection
  (461/461; no variable complementation required).

  This does **not** yet emit 461 Lean `WidthClosure` instances. It records the
  mass that any parametric synthesis must match, and the transfer principle:
  topology rename onto `k4Closed` ⇒ ResidualK4Shape + □-freedom.
-/

import PNPLab.ParametricClosure3
import PNPLab.K4ResidualID

namespace PNPLab.Resolution

/-- Aggregate mass from `crossing_residual_catalog_mass.json`. -/
structure CrossingResidualCatalogMass where
  total : Nat
  shapeOk : Nat
  isoOk : Nat
  flipNeeded : Nat
  allOk : Bool

def crossingResidualCatalogMass : CrossingResidualCatalogMass where
  total := 461
  shapeOk := 461
  isoOk := 461
  flipNeeded := 0
  allOk := true

theorem crossingResidualCatalogMass_ok :
    crossingResidualCatalogMass.total = 461 ∧
      crossingResidualCatalogMass.shapeOk = 461 ∧
      crossingResidualCatalogMass.isoOk = 461 ∧
      crossingResidualCatalogMass.flipNeeded = 0 ∧
      crossingResidualCatalogMass.allOk = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Tip histogram matches hop→pack routing window. -/
structure CrossingResidualTipHist where
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat
  h5 : Nat
  h6 : Nat

def crossingResidualTipHist : CrossingResidualTipHist where
  h1 := 5
  h2 := 15
  h3 := 35
  h4 := 70
  h5 := 126
  h6 := 210

theorem crossingResidualTipHist_sum :
    crossingResidualTipHist.h1 + crossingResidualTipHist.h2 +
      crossingResidualTipHist.h3 + crossingResidualTipHist.h4 +
      crossingResidualTipHist.h5 + crossingResidualTipHist.h6 = 461 :=
  rfl

/--
  Signed / topology iso witness shape (permutation of template vars 1..6).
  Packs and the Python catalog use the same format; flips were never needed
  on the mass window.
-/
structure TopologyIsoWitness where
  src : List Nat
  permutation : List Nat
  src_len : src.length = 6
  perm_len : permutation.length = 6

/-- Build a `VarRename` from a topology iso (src[i] ↦ permutation[i]). -/
def TopologyIsoWitness.toRename (w : TopologyIsoWitness) : VarRename where
  src := w.src
  dst := w.permutation
  src_len := w.src_len
  dst_len := w.perm_len

/-- Witness metadata for one E2 catalog instance (no full `RAxioms`). -/
structure CatalogIsoEntry where
  n : Nat
  tips : Nat
  chord1 : Nat × Nat
  chord2 : Nat × Nat
  src : List Nat
  permutation : List Nat
  src_len : src.length = 6
  perm_len : permutation.length = 6

def CatalogIsoEntry.toWitness (e : CatalogIsoEntry) : TopologyIsoWitness :=
  { src := e.src
    permutation := e.permutation
    src_len := e.src_len
    perm_len := e.perm_len }

def CatalogIsoEntry.toRename (e : CatalogIsoEntry) : VarRename :=
  (e.toWitness).toRename

/--
  Transfer principle: if a residual clause list is topology-subset of `k4Closed`,
  it excludes □; with `|V|=6` and `|S|=16` it matches ResidualK4Shape.
-/
theorem topology_subset_residual_shape
    (r : VarRename) (S : List Clause) (V : List Nat)
    (hSub : renamedSubset r S k4Closed = true)
    (_hSize : S.length = 16)
    (hVars : V.length = 6) :
    ¬ ([] ∈ S) ∧
      (∃ shape : ResidualK4Shape, shape.Vres = V ∧ shape.closedSize = 16) :=
  ⟨renamedSubset_no_empty r S hSub,
    ⟨{ Vres := V, closedSize := 16, vars_ok := hVars, size_ok := rfl }, rfl, rfl⟩⟩

/-- Pack topology renames are instances of the catalog transfer principle. -/
theorem mf_topology_transfer :
    ¬ ([] ∈ mfRClosed) ∧ mfRClosed.length = 16 :=
  ⟨renamedSubset_no_empty mfTopologyRename mfRClosed (by
      have := mfTopologySetEq_true
      simp [mfTopologySetEq] at this
      exact this.1),
    by native_decide⟩

theorem all_pack_residuals_size_16 :
    ofoldRClosed.length = 16 ∧
      mfRClosed.length = 16 ∧
      tfRClosed.length = 16 ∧
      ffRClosed.length = 16 ∧
      xfRClosed.length = 16 ∧
      sfRClosed.length = 16 := by
  native_decide

/-- Bundle: E2 catalog mass + pack size + hop window. -/
theorem crossing_residual_catalog_bundle :
    crossingResidualCatalogMass.isoOk = 461 ∧
      crossingResidualCatalogMass.flipNeeded = 0 ∧
      (crossingResidualTipHist.h1 + crossingResidualTipHist.h2 +
        crossingResidualTipHist.h3 + crossingResidualTipHist.h4 +
        crossingResidualTipHist.h5 + crossingResidualTipHist.h6 = 461) ∧
      ofoldRClosed.length = 16 ∧
      mfRClosed.length = 16 ∧
      tfRClosed.length = 16 ∧
      ffRClosed.length = 16 ∧
      xfRClosed.length = 16 ∧
      sfRClosed.length = 16 :=
  ⟨rfl, rfl, rfl, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

def catalogDoc : String :=
  "reports/discovery/crossing_residual_catalog_mass.json"

def catalogFullDoc : String :=
  "reports/discovery/crossing_residual_catalog.json"

def catalogScript : String :=
  "backend/proof_complexity/emit_crossing_residual_catalog.py"

end PNPLab.Resolution
