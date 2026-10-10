/-
  Multi-chord residual after first-block triangle fold (Category C / G6).

  Symmetric to `NestedChordResidual`: for disjoint pairings with a length-2
  first ear `{p0, p0+2}`, deleting the tip at `p0 + 1` leaves the second chord
  `{p2, p3}` on `n - 1` vertices (both endpoints shifted down by one).
-/

import PNPLab.OuterplanarFacialInduction
import PNPLab.OddChargeFold

namespace PNPLab.Outerplanar

/-- First (disjoint) ear endpoints form a length-2 chord. -/
abbrev NoncrossingChordDiagram.firstLen2 (d : NoncrossingChordDiagram) : Prop :=
  d.earB = d.earA + 2

/--
  Second-chord residual after deleting the unique internal of a disjoint
  length-2 first ear.  Tip index is `earA + 1 = p0 + 1`; both `p2` and `p3`
  lie strictly above the tip, so they shift: `p2 ↦ p2 - 1`, `p3 ↦ p3 - 1`.
-/
def NoncrossingChordDiagram.residualSecondChord (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen2 : d.firstLen2)
    (hSecondGap : d.p2 + 2 ≤ d.p3)
    (hSecondBwd : 0 < (d.n - 1) - ((d.p3 - 1) - (d.p2 - 1)) - 1) : CycleChord where
  n := d.n - 1
  a := d.p2 - 1
  b := d.p3 - 1
  gap := by
    have ord := d.ordered
    have em := d.ear_match
    simp [NoncrossingChordDiagram.firstLen2] at hlen2
    simp [hdisj] at em
    have : d.earA = d.p0 ∧ d.earB = d.p1 := em
    omega
  b_lt_n := by
    have := d.ordered
    omega
  bwd_pos := hSecondBwd

theorem NoncrossingChordDiagram.residualSecondChord_n
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen2 : d.firstLen2)
    (hSecondGap : d.p2 + 2 ≤ d.p3)
    (hSecondBwd : 0 < (d.n - 1) - ((d.p3 - 1) - (d.p2 - 1)) - 1) :
    (d.residualSecondChord hdisj hlen2 hSecondGap hSecondBwd).n = d.n - 1 :=
  rfl

/-- Embed cert after the first fold: still one chord (the second), not a cycle. -/
def NoncrossingChordDiagram.afterFirstTriangle (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen2 : d.firstLen2)
    (hSecondGap : d.p2 + 2 ≤ d.p3)
    (hSecondBwd : 0 < (d.n - 1) - ((d.p3 - 1) - (d.p2 - 1)) - 1) : OuterplanarEmbedCert :=
  .oneChord (d.residualSecondChord hdisj hlen2 hSecondGap hSecondBwd)

theorem NoncrossingChordDiagram.afterFirstTriangle_not_cycle
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen2 : d.firstLen2)
    (hSecondGap : d.p2 + 2 ≤ d.p3)
    (hSecondBwd : 0 < (d.n - 1) - ((d.p3 - 1) - (d.p2 - 1)) - 1) :
    (d.afterFirstTriangle hdisj hlen2 hSecondGap hSecondBwd).isCycle = false :=
  rfl

/-- Two-step disjoint induction when the second residual is also a triangle. -/
structure DisjointTriangleInduction where
  diagram : NoncrossingChordDiagram
  disjoint : diagram.pairing = .disjoint
  firstLen2 : diagram.firstLen2
  secondGap : diagram.p2 + 2 ≤ diagram.p3
  secondBwd : 0 < (diagram.n - 1) - ((diagram.p3 - 1) - (diagram.p2 - 1)) - 1
  firstTri : diagram.toEar.shorterInternals = 1
  nPos : 1 < diagram.n
  secondTri :
    (diagram.residualSecondChord disjoint firstLen2 secondGap secondBwd).shorterInternals = 1
  secondNPos :
    1 < (diagram.residualSecondChord disjoint firstLen2 secondGap secondBwd).n

noncomputable def DisjointTriangleInduction.step1 (s : DisjointTriangleInduction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord s.diagram.toEar s.firstTri (by
    simpa [NoncrossingChordDiagram.toEar] using s.nPos)

def DisjointTriangleInduction.midEmbed (s : DisjointTriangleInduction) :
    OuterplanarEmbedCert :=
  s.diagram.afterFirstTriangle s.disjoint s.firstLen2 s.secondGap s.secondBwd

noncomputable def DisjointTriangleInduction.step2 (s : DisjointTriangleInduction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord
    (s.diagram.residualSecondChord s.disjoint s.firstLen2 s.secondGap s.secondBwd)
    s.secondTri s.secondNPos

theorem DisjointTriangleInduction.mid_not_cycle (s : DisjointTriangleInduction) :
    s.midEmbed.isCycle = false :=
  s.diagram.afterFirstTriangle_not_cycle s.disjoint s.firstLen2 s.secondGap s.secondBwd

theorem DisjointTriangleInduction.final_is_cycle (s : DisjointTriangleInduction) :
    s.step2.after.isCycle = true :=
  s.step2.after_is_cycle

theorem DisjointTriangleInduction.bundle (s : DisjointTriangleInduction) :
    s.midEmbed.isCycle = false ∧
      s.step2.after.isCycle = true ∧
      gf2Sum s.step2.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle (s.step2.chord.n - 1)) = 0 :=
  ⟨s.mid_not_cycle, s.final_is_cycle, s.step2.charges_remain_odd,
    foldSteps_cycle (s.step2.chord.n - 1)⟩

/-- C₈ disjoint: first `{0,2}` then second residual `{3,5}` on 7 verts. -/
def c8DisjointInduction : DisjointTriangleInduction where
  diagram := c8DisjointDiagram
  disjoint := rfl
  firstLen2 := by native_decide
  secondGap := by decide
  secondBwd := by decide
  firstTri := by native_decide
  nPos := by decide
  secondTri := by native_decide
  secondNPos := by native_decide

theorem c8Disjoint_residual_second :
    (c8DisjointDiagram.residualSecondChord rfl (by native_decide) (by decide) (by decide)).a = 3 ∧
      (c8DisjointDiagram.residualSecondChord rfl (by native_decide) (by decide) (by decide)).b = 5 ∧
      (c8DisjointDiagram.residualSecondChord rfl (by native_decide) (by decide) (by decide)).n = 7 := by
  native_decide

theorem c8Disjoint_two_step_to_cycle :
    c8DisjointInduction.midEmbed.isCycle = false ∧
      c8DisjointInduction.step2.after.isCycle = true ∧
      gf2Sum c8DisjointInduction.step2.chargesAfter.charges = 1 :=
  ⟨c8DisjointInduction.mid_not_cycle, c8DisjointInduction.final_is_cycle,
    c8DisjointInduction.step2.charges_remain_odd⟩

def disjointResidualDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
