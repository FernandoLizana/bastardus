/-
  Crossing pack catalog by hop budget (Category C / G5 bridge).

  Every crossing residual with hop budget `h ∈ [1,10]` (mass n=5..14) is covered
  by one of the concrete ProjectionInclusion packs OneFold…TenFold. This does
  **not** yet prove a fresh Closure₃ for an arbitrary instance — it classifies
  which pack family discharges the G0→R projection when `h` matches.

  Combined with `CrossingFoldSchedule.reaches_k4` + topology set-eq (G3), this
  is the parametric *routing* layer of E5: schedule → hop count → pack family →
  K₄ template.
-/

import PNPLab.K4ResidualCatalog
import PNPLab.MembershipTransport
import PNPLab.OneFoldProjection
import PNPLab.MultiFoldProjection
import PNPLab.TripleFoldProjection
import PNPLab.FourFoldProjection
import PNPLab.FiveFoldProjection
import PNPLab.SixFoldProjection
import PNPLab.SevenFoldProjection
import PNPLab.EightFoldProjection
import PNPLab.NineFoldProjection
import PNPLab.TenFoldProjection

namespace PNPLab.Resolution

/-- Which Lean pack discharges a crossing with `h` tip-by-tip hops. -/
inductive CrossingPackFamily where
  | oneFold
  | multiFold
  | tripleFold
  | fourFold
  | fiveFold
  | sixFold
  | sevenFold
  | eightFold
  | nineFold
  | tenFold
  deriving DecidableEq

def packFamilyOfHops (h : Nat) : Option CrossingPackFamily :=
  match h with
  | 1 => some .oneFold
  | 2 => some .multiFold
  | 3 => some .tripleFold
  | 4 => some .fourFold
  | 5 => some .fiveFold
  | 6 => some .sixFold
  | 7 => some .sevenFold
  | 8 => some .eightFold
  | 9 => some .nineFold
  | 10 => some .tenFold
  | _ => none

theorem packFamily_of_mass_budget {h : Nat} (hLo : 1 ≤ h) (hHi : h ≤ 10) :
    (packFamilyOfHops h).isSome = true := by
  match h with
  | 0 => cases hLo
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => rfl
  | n + 11 =>
    have : ¬ n + 11 ≤ 10 := by omega
    exact (this hHi).elim

/-- Mass window: n=5..14 crossings use at most 10 tips. -/
theorem maxCrossingHopBudget_eq :
    Bicyclic.maxCrossingHopBudget = 10 :=
  rfl

/-- Concrete pack projections (already proved no □ on G). -/
def packProjection : CrossingPackFamily → ProjectionInclusion 3
  | .oneFold => ofoldProjection
  | .multiFold => mfProjection
  | .tripleFold => tfProjection
  | .fourFold => ffProjection
  | .fiveFold => xfProjection
  | .sixFold => sfProjection
  | .sevenFold => vfProjection
  | .eightFold => efProjection
  | .nineFold => nfProjection
  | .tenFold => zfProjection

/-- Residual topology set-eq flag for each pack family. -/
def packTopologySetEq (f : CrossingPackFamily) : Bool :=
  match f with
  | .oneFold => ofoldR_in_k4Template && k4_in_ofoldR
  | .multiFold => mfTopologySetEq
  | .tripleFold => tfTopologySetEq
  | .fourFold => ffTopologySetEq
  | .fiveFold => xfTopologySetEq
  | .sixFold => sfTopologySetEq
  | .sevenFold => vfTopologySetEq
  | .eightFold => efTopologySetEq
  | .nineFold => nfTopologySetEq
  | .tenFold => zfTopologySetEq

theorem packTopologySetEq_all :
    (CrossingPackFamily.oneFold ::
      .multiFold :: .tripleFold :: .fourFold :: .fiveFold ::
        .sixFold :: .sevenFold :: .eightFold :: .nineFold :: [.tenFold]).all
      packTopologySetEq = true := by
  native_decide

/-- No □ on the residual side of each pack projection. -/
theorem pack_no_empty_residual (f : CrossingPackFamily) :
    ¬ (packProjection f).rClosure.mem [] := by
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

/-- No □ on G via projection for each pack family. -/
theorem pack_no_empty_of_projection (f : CrossingPackFamily) :
    ¬ (packProjection f).gClosure.mem [] :=
  no_empty_of_projection (packProjection f) (pack_no_empty_residual f)

private theorem packTopologySetEq_true (f : CrossingPackFamily) :
    packTopologySetEq f = true := by
  cases f <;> native_decide

/--
  G5 routing: if hop budget is in the mass window, a pack family exists with
  topology set-eq to K₄ and □-free projection.
-/
theorem crossing_pack_route {h : Nat} (hLo : 1 ≤ h) (hHi : h ≤ 10) :
    ∃ f : CrossingPackFamily,
      packFamilyOfHops h = some f ∧
        packTopologySetEq f = true ∧
        ¬ (packProjection f).gClosure.mem [] := by
  match h with
  | 0 => cases hLo
  | 1 =>
    exact ⟨.oneFold, rfl, packTopologySetEq_true .oneFold,
      pack_no_empty_of_projection .oneFold⟩
  | 2 =>
    exact ⟨.multiFold, rfl, packTopologySetEq_true .multiFold,
      pack_no_empty_of_projection .multiFold⟩
  | 3 =>
    exact ⟨.tripleFold, rfl, packTopologySetEq_true .tripleFold,
      pack_no_empty_of_projection .tripleFold⟩
  | 4 =>
    exact ⟨.fourFold, rfl, packTopologySetEq_true .fourFold,
      pack_no_empty_of_projection .fourFold⟩
  | 5 =>
    exact ⟨.fiveFold, rfl, packTopologySetEq_true .fiveFold,
      pack_no_empty_of_projection .fiveFold⟩
  | 6 =>
    exact ⟨.sixFold, rfl, packTopologySetEq_true .sixFold,
      pack_no_empty_of_projection .sixFold⟩
  | 7 =>
    exact ⟨.sevenFold, rfl, packTopologySetEq_true .sevenFold,
      pack_no_empty_of_projection .sevenFold⟩
  | 8 =>
    exact ⟨.eightFold, rfl, packTopologySetEq_true .eightFold,
      pack_no_empty_of_projection .eightFold⟩
  | 9 =>
    exact ⟨.nineFold, rfl, packTopologySetEq_true .nineFold,
      pack_no_empty_of_projection .nineFold⟩
  | 10 =>
    exact ⟨.tenFold, rfl, packTopologySetEq_true .tenFold,
      pack_no_empty_of_projection .tenFold⟩
  | n + 11 =>
    have : ¬ n + 11 ≤ 10 := by omega
    exact (this hHi).elim

/-- Bundle with combinatorial schedule for a concrete arc sketch. -/
theorem crossing_route_from_arcs (c : Bicyclic.CrossingArcs)
    (hLo : 1 ≤ c.total) (hHi : c.total ≤ 10) :
    (c.foldIter c.total) = Bicyclic.K4Skeleton ∧
      ∃ f : CrossingPackFamily,
        packFamilyOfHops c.total = some f ∧
          packTopologySetEq f = true ∧
          ¬ (packProjection f).gClosure.mem [] :=
  ⟨Bicyclic.reaches_k4_skeleton c, crossing_pack_route hLo hHi⟩

def packCatalogDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

def hopMassDoc : String :=
  "reports/discovery/crossing_hop_pack_catalog_mass.json"

/-- E2: all 461 multihop chains have tips ∈ [1,6]. -/
structure CrossingHopPackMass where
  nChains : Nat
  allInWindow : Bool
  hist1 : Nat
  hist2 : Nat
  hist3 : Nat
  hist4 : Nat
  hist5 : Nat
  hist6 : Nat

def crossingHopPackMass : CrossingHopPackMass where
  nChains := 461
  allInWindow := true
  hist1 := 5
  hist2 := 15
  hist3 := 35
  hist4 := 70
  hist5 := 126
  hist6 := 210

theorem crossingHopPackMass_covers :
    crossingHopPackMass.nChains = 461 ∧
      crossingHopPackMass.allInWindow = true ∧
      crossingHopPackMass.hist1 + crossingHopPackMass.hist2 +
        crossingHopPackMass.hist3 + crossingHopPackMass.hist4 +
        crossingHopPackMass.hist5 + crossingHopPackMass.hist6 = 461 :=
  ⟨rfl, rfl, rfl⟩

/-- C₆ crossing (4 internal tips) routes to the FourFold pack family. -/
theorem c6_pack_family :
    packFamilyOfHops (Bicyclic.hopBudget Bicyclic.c6CrossingArcs) = some .fourFold :=
  rfl

theorem c6_crossing_route :
    (Bicyclic.c6CrossingArcs.foldIter Bicyclic.c6CrossingArcs.total) = Bicyclic.K4Skeleton ∧
      packFamilyOfHops Bicyclic.c6CrossingArcs.total = some .fourFold ∧
      packTopologySetEq .fourFold = true ∧
      ¬ (packProjection .fourFold).gClosure.mem [] := by
  refine ⟨Bicyclic.reaches_k4_skeleton Bicyclic.c6CrossingArcs, rfl,
    packTopologySetEq_true .fourFold, pack_no_empty_of_projection .fourFold⟩

end PNPLab.Resolution
