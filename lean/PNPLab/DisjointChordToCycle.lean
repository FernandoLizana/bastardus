/-
  Disjoint length-2 → cycle via residual one-chord totality (Category C / G6).

  Drops the `secondTri` restriction of `DisjointTriangleInduction`: after the
  first triangle fold, the second residual is any `CycleChord`, and
  `CycleChord.toCycleBase` finishes the peel.
-/

import PNPLab.DisjointChordResidual
import PNPLab.OuterplanarOneChordTotal

namespace PNPLab.Outerplanar

/-- Disjoint + length-2 first ear; second residual need not be a triangle. -/
structure DisjointLen2Induction where
  diagram : NoncrossingChordDiagram
  disjoint : diagram.pairing = .disjoint
  firstLen2 : diagram.firstLen2
  secondGap : diagram.p2 + 2 ≤ diagram.p3
  secondBwd : 0 < (diagram.n - 1) - ((diagram.p3 - 1) - (diagram.p2 - 1)) - 1
  firstTri : diagram.toEar.shorterInternals = 1
  nPos : 1 < diagram.n
  secondNPos :
    1 < (diagram.residualSecondChord disjoint firstLen2 secondGap secondBwd).n

noncomputable def DisjointLen2Induction.step1 (s : DisjointLen2Induction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord s.diagram.toEar s.firstTri (by
    simpa [NoncrossingChordDiagram.toEar] using s.nPos)

def DisjointLen2Induction.midChord (s : DisjointLen2Induction) : CycleChord :=
  s.diagram.residualSecondChord s.disjoint s.firstLen2 s.secondGap s.secondBwd

def DisjointLen2Induction.midEmbed (s : DisjointLen2Induction) : OuterplanarEmbedCert :=
  s.diagram.afterFirstTriangle s.disjoint s.firstLen2 s.secondGap s.secondBwd

noncomputable def DisjointLen2Induction.toCycleBase (s : DisjointLen2Induction) :
    FacialCycleBase :=
  (s.midChord).toCycleBase s.secondNPos

theorem DisjointLen2Induction.mid_not_cycle (s : DisjointLen2Induction) :
    s.midEmbed.isCycle = false :=
  s.diagram.afterFirstTriangle_not_cycle s.disjoint s.firstLen2 s.secondGap s.secondBwd

theorem DisjointLen2Induction.reaches_cycle (s : DisjointLen2Induction) :
    let b := s.toCycleBase
    s.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let h := (s.midChord).reaches_cycle s.secondNPos
  ⟨s.mid_not_cycle, h.1, h.2.1, h.2.2⟩

/-- Drop-in generalization when the second residual happens to be a triangle. -/
noncomputable def DisjointTriangleInduction.toLen2 (s : DisjointTriangleInduction) :
    DisjointLen2Induction where
  diagram := s.diagram
  disjoint := s.disjoint
  firstLen2 := s.firstLen2
  secondGap := s.secondGap
  secondBwd := s.secondBwd
  firstTri := s.firstTri
  nPos := s.nPos
  secondNPos := s.secondNPos

theorem DisjointTriangleInduction.reaches_cycle_via_total (s : DisjointTriangleInduction) :
    let b := s.toLen2.toCycleBase
    s.toLen2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := s.toLen2.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- C₈ disjoint via total residual peel (second residual is a triangle). -/
noncomputable def c8DisjointLen2Induction : DisjointLen2Induction :=
  c8DisjointInduction.toLen2

theorem c8Disjoint_len2_reaches_cycle :
    let b := c8DisjointLen2Induction.toCycleBase
    c8DisjointLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c8DisjointLen2Induction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/--
  C₁₂ disjoint length-2 with long second chord: first `{0,2}`, second `{4,9}`.
  Residual after first fold is `{3,8}` on 11 verts (shorterInternals = 4).
-/
def c12DisjointLen2LongSecond : NoncrossingChordDiagram where
  n := 12
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 9
  pairing := .disjoint
  ordered := by decide
  earA := 0
  earB := 2
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c12DisjointLen2LongSecond_residual_long :
    let c := c12DisjointLen2LongSecond.residualSecondChord
      rfl (by native_decide) (by decide) (by decide)
    c.n = 11 ∧ c.a = 3 ∧ c.b = 8 ∧ 2 ≤ c.shorterInternals := by
  native_decide

def c12DisjointLen2Induction : DisjointLen2Induction where
  diagram := c12DisjointLen2LongSecond
  disjoint := rfl
  firstLen2 := by native_decide
  secondGap := by decide
  secondBwd := by decide
  firstTri := by native_decide
  nPos := by decide
  secondNPos := by native_decide

theorem c12DisjointLen2_reaches_cycle :
    let b := c12DisjointLen2Induction.toCycleBase
    c12DisjointLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      2 ≤ c12DisjointLen2Induction.midChord.shorterInternals :=
  let h := c12DisjointLen2Induction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1, by native_decide⟩

def disjointLen2ToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
