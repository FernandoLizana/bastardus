/-
  Outerplanar upper-bound induction sketch (Category C / G6).

  This file packages the part that is already formal at the sketch level:

    non-cycle + earLaw + positive measure
      -> concrete tip kind
      -> strictly smaller vertex measure.

  It deliberately does not prove the graph-theoretic preservation facts
  (outerplanarity / Δ≤3 / charge parity after a fold). Those remain the
  Whitney / embedding gap documented in TERMINATION.md and EAR_LAW_OUTLINE.md.
-/

import PNPLab.OuterplanarFoldBridge

namespace PNPLab
namespace Outerplanar

/-- Measure-level upper-bound fold step. -/
structure UpperFoldStep where
  before : ResidualSketch
  tipKind : EarTipKind
  tipMatches : before.classify.tipKind = some tipKind
  afterMeasure : FoldMeasure
  drops : afterMeasure.nVertices < before.nVertices

/-- One legal upper-bound fold exists for every positive non-cycle sketch. -/
theorem upperFoldStep_exists
    (g : ResidualSketch) (hCyc : g.isCycle = false) (hPos : 0 < g.nVertices) :
    ∃ step : UpperFoldStep,
      step.before = g ∧
      step.afterMeasure = FoldMeasure.succFold (foldMeasureOf g) := by
  obtain ⟨tip, htip⟩ := foldTipWitness_of_not_cycle g hCyc
  refine ⟨{
    before := g
    tipKind := tip
    tipMatches := htip
    afterMeasure := FoldMeasure.succFold (foldMeasureOf g)
    drops := ?_
  }, rfl, rfl⟩
  exact fold_loop_decreases g.nVertices hPos

/-- If the residual is not a cycle, the classifier and measure drop agree. -/
theorem upperFoldStep_status
    (g : ResidualSketch) (hCyc : g.isCycle = false) (hPos : 0 < g.nVertices) :
    ∃ tip : EarTipKind,
      (g.classify).status = .needsFold ∧
      (g.classify).tipKind = some tip ∧
      (FoldMeasure.succFold (foldMeasureOf g)).nVertices < g.nVertices := by
  obtain ⟨step, hbefore, hafter⟩ := upperFoldStep_exists g hCyc hPos
  refine ⟨step.tipKind, ?_, ?_, ?_⟩
  · simpa [hbefore] using classify_needsFold g hCyc
  · simpa [hbefore] using step.tipMatches
  · simpa [hbefore, hafter] using step.drops

/-- Cycle sketches are the base case: no tip kind is selected. -/
theorem upperCycle_base (n : Nat) :
    (sketchCycle n).classify.status = .cycle ∧
      (sketchCycle n).classify.tipKind = none := by
  constructor
  · exact classify_cycle (sketchCycle n) rfl
  · simp [ResidualSketch.classify, sketchCycle]

/--
  Measure budget for any sketch-level fold induction.
  After `nVertices` strict vertex drops, no positive vertex measure remains.
-/
def upperFoldBudget (g : ResidualSketch) : Nat :=
  g.nVertices

theorem upperFoldBudget_zero_iff (g : ResidualSketch) :
    upperFoldBudget g = 0 ↔ g.nVertices = 0 := by
  rfl

/--
  A reusable induction principle over the vertex budget.

  To prove a property `P` for all residual sketches, it is enough to handle:
  * cycle sketches;
  * degenerate zero-vertex sketches;
  * a non-cycle step, assuming `P` for all strictly smaller measures.
-/
theorem outerplanar_measure_induction
    (P : ResidualSketch → Prop)
    (hZero : ∀ g, g.nVertices = 0 → P g)
    (hCycle : ∀ g, g.isCycle = true → P g)
    (hStep :
      ∀ g,
        g.isCycle = false →
        0 < g.nVertices →
        (∀ h : ResidualSketch, h.nVertices < g.nVertices → P h) →
        P g) :
    ∀ g, P g := by
  intro g
  have aux : ∀ m : Nat, ∀ g : ResidualSketch, g.nVertices ≤ m → P g := by
    intro m
    induction m with
    | zero =>
      intro g hg
      exact hZero g (Nat.eq_zero_of_le_zero hg)
    | succ m ih =>
      intro g hg
      by_cases hz : g.nVertices = 0
      · exact hZero g hz
      · have hPos : 0 < g.nVertices := Nat.pos_iff_ne_zero.mpr hz
        by_cases hc : g.isCycle = true
        · exact hCycle g hc
        · have hcf : g.isCycle = false := eq_false_of_ne_true hc
          apply hStep g hcf hPos
          intro h hlt
          apply ih h
          omega
  exact aux g.nVertices g (Nat.le_refl _)

def upperSketchDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

def earLawOutlineDocUpper : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

/--
  Combinatorial flags assumed preserved by `fold_deg2_tip` on outerplanar Δ≤3
  instances (E2 certificates; not a Mathlib graph proof).
-/
structure FoldPreservationSketch where
  outerplanar : Bool := true
  deltaLe3 : Bool := true
  oddCharge : Bool := true

def defaultPreservation : FoldPreservationSketch := {}

/-- After one upper fold, vertex measure drops; preservation flags unchanged at sketch level. -/
theorem upperFold_preservation_sketch
    (g : ResidualSketch) (hCyc : g.isCycle = false) (hPos : 0 < g.nVertices)
    (_pres : FoldPreservationSketch) :
    ∃ step : UpperFoldStep,
      step.before = g ∧
      step.afterMeasure.nVertices = g.nVertices - 1 ∧
      defaultPreservation.outerplanar = true ∧
      defaultPreservation.deltaLe3 = true := by
  obtain ⟨step, hbefore, hafter⟩ := upperFoldStep_exists g hCyc hPos
  refine ⟨step, hbefore, ?_, rfl, rfl⟩
  simp [hafter, FoldMeasure.succFold, foldMeasureOf]

end Outerplanar
end PNPLab
