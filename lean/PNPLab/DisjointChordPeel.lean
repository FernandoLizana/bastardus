/-
  Disjoint long-ear peel: shorten the first ear by `firstFwd - 1` fwd
  shortcuts until it is length-2, leaving a disjoint diagram eligible for
  `DisjointTriangleInduction` (Category C / G6 honesty).
-/

import PNPLab.DisjointChordShortcut
import PNPLab.DisjointChordResidual

namespace PNPLab.Outerplanar

/-- First ear forward internals (`earB - earA - 1`). -/
def NoncrossingChordDiagram.firstFwd (d : NoncrossingChordDiagram) : Nat :=
  d.earB - d.earA - 1

/--
  After `firstFwd - 1` first-ear shortcuts: disjoint diagram with length-2
  first ear `{p0, p0+2}` and second `{p2 - k, p3 - k}` on `n - k`.
-/
def NoncrossingChordDiagram.peelFirstToLen2 (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - (d.firstFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (_hSecond : d.earA + 2 < d.p2 - (d.firstFwd - 1) ∧
      (d.p2 - (d.firstFwd - 1)) + 2 ≤ d.p3 - (d.firstFwd - 1)) :
    NoncrossingChordDiagram where
  n := d.n - (d.firstFwd - 1)
  p0 := d.p0
  p1 := d.earA + 2
  p2 := d.p2 - (d.firstFwd - 1)
  p3 := d.p3 - (d.firstFwd - 1)
  pairing := .disjoint
  ordered := by
    have := d.ordered
    have em := d.ear_match
    have hs := _hSecond
    simp [hdisj] at em
    have : d.earA = d.p0 ∧ d.earB = d.p1 := em
    simp [NoncrossingChordDiagram.firstLenGe3, NoncrossingChordDiagram.firstFwd] at hlen hs ⊢
    omega
  earA := d.earA
  earB := d.earA + 2
  ear_match := by
    have em := d.ear_match
    simp [hdisj] at em
    exact ⟨em.1, rfl⟩
  ear_gap := Nat.le_refl _
  ear_b_lt_n := by
    have := d.ordered
    have em := d.ear_match
    simp [hdisj] at em
    have : d.earA = d.p0 ∧ d.earB = d.p1 := em
    simp [NoncrossingChordDiagram.firstFwd] at *
    omega
  ear_bwd_pos := by
    simpa [NoncrossingChordDiagram.firstFwd] using hEarBwd

theorem NoncrossingChordDiagram.peelFirstToLen2_firstLen2
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - (d.firstFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (_hSecond : d.earA + 2 < d.p2 - (d.firstFwd - 1) ∧
      (d.p2 - (d.firstFwd - 1)) + 2 ≤ d.p3 - (d.firstFwd - 1)) :
    (d.peelFirstToLen2 hdisj hlen hEarBwd _hSecond).firstLen2 := by
  simp [NoncrossingChordDiagram.firstLen2, NoncrossingChordDiagram.peelFirstToLen2]

/-- Peeled first ear is a triangle (shorterInternals = 1). -/
theorem NoncrossingChordDiagram.peelFirstToLen2_toEar_triangle
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - (d.firstFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (_hSecond : d.earA + 2 < d.p2 - (d.firstFwd - 1) ∧
      (d.p2 - (d.firstFwd - 1)) + 2 ≤ d.p3 - (d.firstFwd - 1)) :
    (d.peelFirstToLen2 hdisj hlen hEarBwd _hSecond).toEar.shorterInternals = 1 := by
  simp only [NoncrossingChordDiagram.toEar, CycleChord.shorterInternals,
    CycleChord.fwdInternals, CycleChord.bwdInternals,
    NoncrossingChordDiagram.peelFirstToLen2]
  omega

theorem NoncrossingChordDiagram.peelFirstToLen2_nPos
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - (d.firstFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (_hSecond : d.earA + 2 < d.p2 - (d.firstFwd - 1) ∧
      (d.p2 - (d.firstFwd - 1)) + 2 ≤ d.p3 - (d.firstFwd - 1)) :
    1 < (d.peelFirstToLen2 hdisj hlen hEarBwd _hSecond).n := by
  have := d.ordered
  have em := d.ear_match
  simp [hdisj] at em
  have : d.earA = d.p0 ∧ d.earB = d.p1 := em
  simp only [NoncrossingChordDiagram.peelFirstToLen2, NoncrossingChordDiagram.firstLenGe3,
    NoncrossingChordDiagram.firstFwd] at hlen hEarBwd _hSecond ⊢
  omega

theorem NoncrossingChordDiagram.peelFirstToLen2_secondGap
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - (d.firstFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (_hSecond : d.earA + 2 < d.p2 - (d.firstFwd - 1) ∧
      (d.p2 - (d.firstFwd - 1)) + 2 ≤ d.p3 - (d.firstFwd - 1)) :
    (d.peelFirstToLen2 hdisj hlen hEarBwd _hSecond).p2 + 2 ≤
      (d.peelFirstToLen2 hdisj hlen hEarBwd _hSecond).p3 := by
  simpa [NoncrossingChordDiagram.peelFirstToLen2] using _hSecond.2

/-- C₁₀ disjoint peels to C₈-style `{0,2}` / `{4,6}`. -/
theorem c10Disjoint_peel_to_len2 :
    let d := c10DisjointDiagram.peelFirstToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 8 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 4 ∧ d.p3 = 6 ∧
      d.firstLen2 ∧ d.toEar.shorterInternals = 1 := by
  native_decide

/-- Peeled C₁₀ disjoint admits the two-step disjoint triangle induction. -/
def c10DisjointPeeledInduction : DisjointTriangleInduction where
  diagram := c10DisjointDiagram.peelFirstToLen2
    rfl (by native_decide) (by decide) (by decide)
  disjoint := rfl
  firstLen2 := by native_decide
  secondGap := by decide
  secondBwd := by decide
  firstTri := by native_decide
  nPos := by decide
  secondTri := by native_decide
  secondNPos := by native_decide

theorem c10Disjoint_peel_then_two_step_to_cycle :
    c10DisjointPeeledInduction.midEmbed.isCycle = false ∧
      c10DisjointPeeledInduction.step2.after.isCycle = true ∧
      gf2Sum c10DisjointPeeledInduction.step2.chargesAfter.charges = 1 :=
  ⟨c10DisjointPeeledInduction.mid_not_cycle, c10DisjointPeeledInduction.final_is_cycle,
    c10DisjointPeeledInduction.step2.charges_remain_odd⟩

def disjointPeelDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
