/-
  Nested length-2 → cycle via residual one-chord totality (Category C / G6).

  Drops the `outerTri` restriction of `NestedTriangleInduction`: after the
  inner triangle fold, the outer residual is any `CycleChord`, and
  `CycleChord.toCycleBase` finishes the peel.
-/

import PNPLab.NestedChordResidual
import PNPLab.OuterplanarOneChordTotal

namespace PNPLab.Outerplanar

/-- Nested + length-2 inner ear; outer residual need not be a triangle. -/
structure NestedLen2Induction where
  diagram : NoncrossingChordDiagram
  nested : diagram.pairing = .nested
  innerLen2 : diagram.innerLen2
  outerBwd : 0 < diagram.n - (diagram.p3 - diagram.p0) - 1
  innerTri : diagram.toEar.shorterInternals = 1
  nPos : 1 < diagram.n
  outerNPos : 1 < (diagram.residualOuterChord nested innerLen2 outerBwd).n

noncomputable def NestedLen2Induction.step1 (s : NestedLen2Induction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord s.diagram.toEar s.innerTri (by
    simpa [NoncrossingChordDiagram.toEar] using s.nPos)

def NestedLen2Induction.midChord (s : NestedLen2Induction) : CycleChord :=
  s.diagram.residualOuterChord s.nested s.innerLen2 s.outerBwd

def NestedLen2Induction.midEmbed (s : NestedLen2Induction) : OuterplanarEmbedCert :=
  s.diagram.afterInnerTriangle s.nested s.innerLen2 s.outerBwd

noncomputable def NestedLen2Induction.toCycleBase (s : NestedLen2Induction) :
    FacialCycleBase :=
  (s.midChord).toCycleBase s.outerNPos

theorem NestedLen2Induction.mid_not_cycle (s : NestedLen2Induction) :
    s.midEmbed.isCycle = false :=
  s.diagram.afterInnerTriangle_not_cycle s.nested s.innerLen2 s.outerBwd

theorem NestedLen2Induction.reaches_cycle (s : NestedLen2Induction) :
    let b := s.toCycleBase
    s.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let h := (s.midChord).reaches_cycle s.outerNPos
  ⟨s.mid_not_cycle, h.1, h.2.1, h.2.2⟩

/-- Drop-in generalization when the outer residual happens to be a triangle. -/
noncomputable def NestedTriangleInduction.toLen2 (s : NestedTriangleInduction) :
    NestedLen2Induction where
  diagram := s.diagram
  nested := s.nested
  innerLen2 := s.innerLen2
  outerBwd := s.outerBwd
  innerTri := s.innerTri
  nPos := s.nPos
  outerNPos := s.outerNPos

theorem NestedTriangleInduction.reaches_cycle_via_total (s : NestedTriangleInduction) :
    let b := s.toLen2.toCycleBase
    s.toLen2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := s.toLen2.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- C₈ nested via total residual peel (outer residual is a triangle). -/
noncomputable def c8NestedLen2Induction : NestedLen2Induction :=
  c8NestedInduction.toLen2

theorem c8Nested_len2_reaches_cycle :
    let b := c8NestedLen2Induction.toCycleBase
    c8NestedLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c8NestedLen2Induction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/--
  C₁₂ nested length-2 with long outer chord: inner `{2,4}`, outer `{0,8}`.
  Residual after inner fold is `{0,7}` on 11 verts (shorterInternals = 3).
-/
def c12NestedLen2LongOuter : NoncrossingChordDiagram where
  n := 12
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 8
  pairing := .nested
  ordered := by decide
  earA := 2
  earB := 4
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c12NestedLen2LongOuter_residual_long :
    let c := c12NestedLen2LongOuter.residualOuterChord
      rfl (by native_decide) (by decide)
    c.n = 11 ∧ c.a = 0 ∧ c.b = 7 ∧ 2 ≤ c.shorterInternals := by
  native_decide

def c12NestedLen2Induction : NestedLen2Induction where
  diagram := c12NestedLen2LongOuter
  nested := rfl
  innerLen2 := by native_decide
  outerBwd := by decide
  innerTri := by native_decide
  nPos := by decide
  outerNPos := by native_decide

theorem c12NestedLen2_reaches_cycle :
    let b := c12NestedLen2Induction.toCycleBase
    c12NestedLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      2 ≤ c12NestedLen2Induction.midChord.shorterInternals :=
  let h := c12NestedLen2Induction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1, by native_decide⟩

def nestedLen2ToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
