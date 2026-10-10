/-
  Bicyclic (θ-graph) upper-bound induction sketch (Category C / G8).

  Parallel to OuterplanarUpperSketch:
    non-cycle + chordFoldLaw + positive measure
      -> tip kind
      -> strictly smaller vertex measure.

  Tip existence on θ-residues is already discharged by `ThetaResidue.chordFoldLaw`.
  Fold preservation of Closure_Δ / outer embedding stays classical (pathfold mass
  210/210; do **not** use ProjectionInclusion for upper packs).
-/

import PNPLab.Bicyclic
import PNPLab.ThetaChordFold
import PNPLab.ThetaFoldBridge

namespace PNPLab.Bicyclic

/-- Measure-level upper-bound chord-fold step. -/
structure UpperChordFoldStep where
  before : ThetaSketch
  tipKind : ChordTipKind
  tipMatches : before.classify.tipKind = some tipKind
  afterMeasure : FoldMeasure
  drops : afterMeasure.nVertices < before.nVertices

/-- Non-cycle θ-sketch with positive measure admits an upper fold step. -/
theorem upperChordFoldStep_exists
    (g : ThetaSketch) (hCyc : g.isCycle = false) (hPos : 0 < g.nVertices) :
    ∃ step : UpperChordFoldStep,
      step.before = g ∧
      step.afterMeasure = FoldMeasure.succFold (foldMeasureOf g) := by
  refine ⟨{
    before := g
    tipKind := .shortcutOnShorterArc
    tipMatches := by simp [ThetaSketch.classify, hCyc]
    afterMeasure := FoldMeasure.succFold (foldMeasureOf g)
    drops := fold_measure_lt hPos
  }, rfl, rfl⟩

/-- Status + tip + drop for a non-cycle θ-sketch. -/
theorem upperChordFoldStep_status
    (g : ThetaSketch) (hCyc : g.isCycle = false) (hPos : 0 < g.nVertices) :
    (g.classify).status = .needsChordFold ∧
      (g.classify).tipKind = some .shortcutOnShorterArc ∧
      (FoldMeasure.succFold (foldMeasureOf g)).nVertices < g.nVertices := by
  refine ⟨classify_needsFold g hCyc, ?_, fold_measure_lt hPos⟩
  simp [ThetaSketch.classify, hCyc]

/-- Cycle base case. -/
theorem upperCycle_theta (n : Nat) :
    let g : ThetaSketch := {
      nVertices := n
      isCycle := true
      hasFoldTip := false
      chordFoldLaw := Or.inl rfl
    }
    (g.classify).status = .cycle ∧ (g.classify).tipKind = none := by
  constructor
  · simp [ThetaSketch.classify]
  · simp [ThetaSketch.classify]

/-- Induction over vertex budget (parallel outerplanar). -/
theorem bicyclic_measure_induction
    (P : ThetaSketch → Prop)
    (hZero : ∀ g, g.nVertices = 0 → P g)
    (hCycle : ∀ g, g.isCycle = true → P g)
    (hStep :
      ∀ g,
        g.isCycle = false →
        0 < g.nVertices →
        (∀ h : ThetaSketch, h.nVertices < g.nVertices → P h) →
        P g) :
    ∀ g, P g := by
  intro g
  have aux : ∀ m : Nat, ∀ g : ThetaSketch, g.nVertices ≤ m → P g := by
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

/-- θ-residue tip law feeds the upper sketch. -/
theorem thetaResidue_feeds_upper (t : ThetaResidue) :
    t.hasTriangleEar = true ∨ t.hasShortcutTip = true :=
  t.chordFoldLaw

/-- Bridge: C₆ short chord is a triangle tip (ThetaFoldBridge). -/
theorem c6_upper_triangle_ready :
    c6chordShort.tipKind = ChordTipKind.triangleEar :=
  c6chordShort_triangle.2

def bicyclicUpperDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/INDUCTION_WIDTH_EQ_DELTA.md"

def pathfoldMassDoc : String :=
  "reports/discovery/bicyclic_pathfold_mass.json"

end PNPLab.Bicyclic
