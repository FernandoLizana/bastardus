/-
  Facial induction to cycle base (Category C / G6).

  One triangle fold on a facial cycle+chord certificate reaches the pure-cycle
  base with odd charge preserved.  Combined with `foldSteps_cycle`, the residual
  needs no further ear folds — this is the complete upper-bound induction step
  for the triangle-ear unicyclic / derived-ear family.
-/

import PNPLab.OuterplanarFoldStep
import PNPLab.OuterplanarFoldTermination
import PNPLab.ChordDiagramEar

namespace PNPLab.Outerplanar

/-- Result of one facial induction step to the cycle base. -/
structure FacialCycleBase where
  nBefore : Nat
  nAfter : Nat
  nAfter_lt : nAfter < nBefore
  nAfter_ge3 : 3 ≤ nAfter
  embedAfter : OuterplanarEmbedCert
  embed_cycle : embedAfter.isCycle = true
  embed_n : embedAfter.nVertices = nAfter
  chargesAfter : OddChargeVec
  charges_odd : gf2Sum chargesAfter.charges = 1
  charges_len : chargesAfter.charges.length = nAfter

/-- Sketch of the cycle base: no further folds. -/
def FacialCycleBase.baseSketch (b : FacialCycleBase) : ResidualSketch :=
  sketchCycle b.nAfter

theorem FacialCycleBase.base_foldSteps (b : FacialCycleBase) :
    foldSteps b.baseSketch = 0 :=
  foldSteps_cycle b.nAfter

/-- Extract the cycle-base residual from a completed facial triangle fold. -/
def FacialTriangleFoldStep.toCycleBase (s : FacialTriangleFoldStep) :
    FacialCycleBase where
  nBefore := s.chord.n
  nAfter := s.chord.n - 1
  nAfter_lt := Nat.sub_lt (Nat.zero_lt_of_lt s.nPos) Nat.zero_lt_one
  nAfter_ge3 := by
    have := s.chord.gap
    have := s.chord.b_lt_n
    have := s.chord.fwd_pos
    have := s.chord.bwd_pos
    omega
  embedAfter := s.after
  embed_cycle := s.after_is_cycle
  embed_n := by
    simp [FacialTriangleFoldStep.after, OuterplanarEmbedCert.foldTriangle,
      OuterplanarEmbedCert.nVertices]
  chargesAfter := s.chargesAfter
  charges_odd := s.charges_remain_odd
  charges_len := s.charges_length_drops

/-- One triangle fold reaches a cycle base with odd charge and zero remaining folds. -/
theorem FacialTriangleFoldStep.reaches_cycle_base (s : FacialTriangleFoldStep) :
    let b := s.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter < b.nBefore ∧
      3 ≤ b.nAfter :=
  let b := s.toCycleBase
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, b.nAfter_lt, b.nAfter_ge3⟩

/-- Full upper-bound story for a facial triangle fold. -/
theorem FacialTriangleFoldStep.induction_bundle (s : FacialTriangleFoldStep) :
    s.before.isCycle = false ∧
      s.after.isCycle = true ∧
      gf2Sum s.chargesAfter.charges = 1 ∧
      s.chargesAfter.charges.length = s.chord.n - 1 ∧
      s.tipWitness.tipKind = .triangleEar ∧
      foldSteps (sketchCycle (s.chord.n - 1)) = 0 :=
  ⟨s.before_not_cycle, s.after_is_cycle, s.charges_remain_odd,
    s.charges_length_drops, rfl, foldSteps_cycle (s.chord.n - 1)⟩

/-- Noncrossing diagram whose derived ear is a triangle → facial induction. -/
noncomputable def NoncrossingChordDiagram.toTriangleFoldStep
    (d : NoncrossingChordDiagram)
    (htri : d.toEar.shorterInternals = 1) (hPos : 1 < d.n) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord d.toEar htri (by
    simpa [NoncrossingChordDiagram.toEar] using hPos)

theorem NoncrossingChordDiagram.triangle_reaches_cycle
    (d : NoncrossingChordDiagram)
    (htri : d.toEar.shorterInternals = 1) (hPos : 1 < d.n) :
    let s := d.toTriangleFoldStep htri hPos
    s.after.isCycle = true ∧
      gf2Sum s.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle (d.n - 1)) = 0 :=
  let s := d.toTriangleFoldStep htri hPos
  ⟨s.after_is_cycle, s.charges_remain_odd, foldSteps_cycle (d.n - 1)⟩

/-- Concrete: C₄ diagonal reaches C₃ base with odd charge. -/
theorem c4_reaches_cycle_base :
    let b := c4FacialTriangleFold.toCycleBase
    b.embedAfter.isCycle = true ∧
      b.nAfter = 3 ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle 3) = 0 :=
  let b := c4FacialTriangleFold.toCycleBase
  ⟨b.embed_cycle, rfl, b.charges_odd, foldSteps_cycle 3⟩

/-- Concrete: C₈ nested — ear-only projection (see `NestedChordResidual` for
  the honest two-chord residual; folding only the derived ear as `oneChord`
  is the local tip witness, not the full multi-chord residual). -/
theorem c8Nested_earProjection_fold :
    let s := c8NestedDiagram.toTriangleFoldStep (by native_decide) (by decide)
    s.after.isCycle = true ∧
      gf2Sum s.chargesAfter.charges = 1 :=
  let s := c8NestedDiagram.toTriangleFoldStep (by native_decide) (by decide)
  ⟨s.after_is_cycle, s.charges_remain_odd⟩

def facialInductionDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
