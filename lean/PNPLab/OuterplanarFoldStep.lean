/-
  Unified facial triangle-fold step (Category C / G6 / E3).

  Packages every invariant already discharged for one fold on a facial
  cycle+chord with a triangle ear:

    * tip kind / `FoldTipWitness` (earLaw → classifier);
    * outerplanarity preserved (`OuterplanarEmbedCert.foldTriangle`);
    * odd charge preserved (`OddChargeVec.foldTip`);
    * vertex measure drops.

  This is the upper-bound half of the earLaw→EliminationStep bridge
  (`EAR_LAW_TO_ELIMINATION.md`).  Concrete `EliminationStep` packs remain the
  lower-bound / crossing side (`FoldTipElimination`).
-/

import PNPLab.OddChargeFold
import PNPLab.OuterplanarEmbedCert
import PNPLab.OuterplanarUpperSketch

namespace PNPLab.Outerplanar

/-- Residual sketch induced by a facial one-chord triangle ear. -/
def CycleChord.toTriangleSketch (c : CycleChord)
    (_htri : c.shorterInternals = 1) : ResidualSketch :=
  c.toEarPath.toSketch c.n c.shorter_pos (Or.inl rfl)

theorem CycleChord.toEarPath_triangle (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    c.toEarPath.hasTriangleEar = true := by
  simp [CycleChord.toEarPath, OuterplanarEarPath.hasTriangleEar, htri]

theorem CycleChord.toTriangleSketch_tip (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    (c.toTriangleSketch htri).classify.tipKind = some .triangleEar := by
  have hflag := c.toEarPath_triangle htri
  simp [CycleChord.toTriangleSketch, OuterplanarEarPath.toSketch,
    ResidualSketch.classify, hflag]

/--
  One complete facial triangle-fold step: tip witness + embed residual +
  odd-charge residual + strict measure drop.
-/
structure FacialTriangleFoldStep where
  chord : CycleChord
  triangle : chord.shorterInternals = 1
  nPos : 1 < chord.n
  /-- Odd charge on the `n` facial vertices. -/
  charges : OddChargeVec
  charges_len : charges.charges.length = chord.n
  /-- Tip index and fold-into neighbor in the charge vector. -/
  tip : Nat
  foldInto : Nat
  tip_lt : tip < charges.charges.length
  foldInto_lt : foldInto < charges.charges.length
  tip_ne : foldInto ≠ tip

namespace FacialTriangleFoldStep

def before (s : FacialTriangleFoldStep) : OuterplanarEmbedCert :=
  .oneChord s.chord

def after (s : FacialTriangleFoldStep) : OuterplanarEmbedCert :=
  OuterplanarEmbedCert.foldTriangle s.chord s.triangle

def sketch (s : FacialTriangleFoldStep) : ResidualSketch :=
  s.chord.toTriangleSketch s.triangle

def tipWitness (s : FacialTriangleFoldStep) : FoldTipWitness 3 where
  sketch := s.sketch
  tipKind := .triangleEar
  tipMatches := s.chord.toTriangleSketch_tip s.triangle

def chargesAfter (s : FacialTriangleFoldStep) : OddChargeVec :=
  s.charges.foldTip s.foldInto s.tip s.foldInto_lt s.tip_lt s.tip_ne

theorem before_not_cycle (s : FacialTriangleFoldStep) :
    s.before.isCycle = false :=
  rfl

theorem after_is_cycle (s : FacialTriangleFoldStep) :
    s.after.isCycle = true :=
  OuterplanarEmbedCert.foldTriangle_isCycle s.chord s.triangle

theorem measure_drops (s : FacialTriangleFoldStep) :
    s.after.nVertices < s.before.nVertices := by
  simpa [before, after, OuterplanarEmbedCert.nVertices] using
    OuterplanarEmbedCert.foldTriangle_lt s.chord s.triangle s.nPos

theorem charges_remain_odd (s : FacialTriangleFoldStep) :
    gf2Sum s.chargesAfter.charges = 1 :=
  s.chargesAfter.odd

theorem charges_length_drops (s : FacialTriangleFoldStep) :
    s.chargesAfter.charges.length = s.chord.n - 1 := by
  have := s.charges.foldTip_length s.foldInto s.tip s.foldInto_lt s.tip_lt s.tip_ne
  simpa [chargesAfter, s.charges_len] using this

theorem tipWitness_matches (s : FacialTriangleFoldStep) :
    s.tipWitness.sketch.classify.tipKind = some .triangleEar :=
  s.tipWitness.tipMatches

/-- Full upper-bound bundle for one facial triangle fold. -/
theorem bundle (s : FacialTriangleFoldStep) :
    s.before.isCycle = false ∧
      s.after.isCycle = true ∧
      s.after.nVertices < s.before.nVertices ∧
      gf2Sum s.chargesAfter.charges = 1 ∧
      s.chargesAfter.charges.length = s.chord.n - 1 ∧
      s.tipWitness.tipKind = .triangleEar ∧
      s.tipWitness.sketch.classify.tipKind = some .triangleEar :=
  ⟨s.before_not_cycle, s.after_is_cycle, s.measure_drops, s.charges_remain_odd,
    s.charges_length_drops, rfl, s.tipWitness_matches⟩

/-- Bridge into the sketch-level `UpperFoldStep`. -/
theorem upperFoldStep_of (s : FacialTriangleFoldStep) :
    ∃ step : UpperFoldStep,
      step.before = s.sketch ∧
      step.tipKind = .triangleEar ∧
      step.afterMeasure.nVertices < s.sketch.nVertices := by
  have hCyc : s.sketch.isCycle = false := by
    simp [sketch, CycleChord.toTriangleSketch, OuterplanarEarPath.toSketch]
  have hPos : 0 < s.sketch.nVertices := by
    simp [sketch, CycleChord.toTriangleSketch, OuterplanarEarPath.toSketch]
    exact Nat.zero_lt_of_lt s.nPos
  obtain ⟨step, hbefore, hafter⟩ := upperFoldStep_exists s.sketch hCyc hPos
  have htip := s.chord.toTriangleSketch_tip s.triangle
  refine ⟨step, hbefore, ?_, ?_⟩
  · have hm := step.tipMatches
    simp [hbefore, sketch] at hm
    -- hm : some step.tipKind = some .triangleEar  (or tipMatches vs htip)
    have : step.tipKind = .triangleEar := by
      simpa [htip] using hm.symm
    exact this
  · simpa [hbefore, hafter] using step.drops

end FacialTriangleFoldStep

/-- Concrete C₄ diagonal triangle-fold step with unit odd charge. -/
def c4FacialTriangleFold : FacialTriangleFoldStep where
  chord := c4Diagonal
  triangle := by native_decide
  nPos := by decide
  charges := unitOddCharge 4 (by decide)
  charges_len := by native_decide
  tip := 1
  foldInto := 0
  tip_lt := by native_decide
  foldInto_lt := by native_decide
  tip_ne := by decide

theorem c4FacialTriangleFold_bundle :
    c4FacialTriangleFold.after.isCycle = true ∧
      c4FacialTriangleFold.after.nVertices = 3 ∧
      gf2Sum c4FacialTriangleFold.chargesAfter.charges = 1 ∧
      c4FacialTriangleFold.tipWitness.tipKind = .triangleEar := by
  refine ⟨c4FacialTriangleFold.after_is_cycle, ?_,
    c4FacialTriangleFold.charges_remain_odd, rfl⟩
  rfl

/-- From any triangle `CycleChord`, a facial fold step exists (unit charge). -/
noncomputable def FacialTriangleFoldStep.ofTriangleChord (c : CycleChord)
    (htri : c.shorterInternals = 1) (hPos : 1 < c.n) :
    FacialTriangleFoldStep :=
  let charges := unitOddCharge c.n (Nat.zero_lt_of_lt hPos)
  have hlen : charges.charges.length = c.n := by
    simp [charges, unitOddCharge]
    have : 0 < c.n := Nat.zero_lt_of_lt hPos
    exact Nat.sub_add_cancel this
  have htip : 1 < charges.charges.length := by
    rw [hlen]; exact hPos
  have hfold : 0 < charges.charges.length := by
    rw [hlen]; exact Nat.zero_lt_of_lt hPos
  { chord := c
    triangle := htri
    nPos := hPos
    charges := charges
    charges_len := hlen
    tip := 1
    foldInto := 0
    tip_lt := htip
    foldInto_lt := hfold
    tip_ne := Ne.symm (Nat.succ_ne_zero 0) }

theorem ofTriangleChord_bundle (c : CycleChord)
    (htri : c.shorterInternals = 1) (hPos : 1 < c.n) :
    let s := FacialTriangleFoldStep.ofTriangleChord c htri hPos
    s.after.isCycle = true ∧
      s.after.nVertices < s.before.nVertices ∧
      gf2Sum s.chargesAfter.charges = 1 :=
  let s := FacialTriangleFoldStep.ofTriangleChord c htri hPos
  ⟨s.after_is_cycle, s.measure_drops, s.charges_remain_odd⟩

def foldStepDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

end PNPLab.Outerplanar
