/-
  Nested long-ear peel: shorten the inner ear by `earInternals - 1` fwd
  shortcuts until it is length-2, leaving a nested diagram eligible for
  `NestedTriangleInduction` (Category C / G6 honesty).
-/

import PNPLab.NestedChordShortcut
import PNPLab.NestedChordResidual

namespace PNPLab.Outerplanar

/-- Inner ear forward internals (`earB - earA - 1`). -/
def NoncrossingChordDiagram.innerFwd (d : NoncrossingChordDiagram) : Nat :=
  d.earB - d.earA - 1

/--
  After `innerFwd - 1` inner shortcuts: nested diagram with length-2 ear
  `{p1, p1+2}` and outer `{p0, p3 - (innerFwd - 1)}` on `n - (innerFwd - 1)`.
-/
def NoncrossingChordDiagram.peelInnerToLen2 (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - (d.innerFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (hOuter : d.p0 < d.p1 ∧ d.earA + 2 < d.p3 - (d.innerFwd - 1) + 1) :
    NoncrossingChordDiagram where
  n := d.n - (d.innerFwd - 1)
  p0 := d.p0
  p1 := d.p1
  p2 := d.earA + 2
  p3 := d.p3 - (d.innerFwd - 1)
  pairing := .nested
  ordered := by
    have := d.ordered
    have em := d.ear_match
    simp [hnest] at em
    have : d.earA = d.p1 ∧ d.earB = d.p2 := em
    simp [NoncrossingChordDiagram.innerLenGe3, NoncrossingChordDiagram.innerFwd] at hlen ⊢
    omega
  earA := d.earA
  earB := d.earA + 2
  ear_match := by
    have em := d.ear_match
    simp [hnest] at em
    exact ⟨em.1, rfl⟩
  ear_gap := Nat.le_refl _
  ear_b_lt_n := by
    have := d.ordered
    have em := d.ear_match
    simp [hnest] at em
    have : d.earA = d.p1 ∧ d.earB = d.p2 := em
    simp [NoncrossingChordDiagram.innerFwd] at *
    omega
  ear_bwd_pos := by
    simpa [NoncrossingChordDiagram.innerFwd] using hEarBwd

theorem NoncrossingChordDiagram.peelInnerToLen2_innerLen2
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - (d.innerFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (hOuter : d.p0 < d.p1 ∧ d.earA + 2 < d.p3 - (d.innerFwd - 1) + 1) :
    (d.peelInnerToLen2 hnest hlen hEarBwd hOuter).innerLen2 := by
  simp [NoncrossingChordDiagram.innerLen2, NoncrossingChordDiagram.peelInnerToLen2]

theorem NoncrossingChordDiagram.peelInnerToLen2_n
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - (d.innerFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (hOuter : d.p0 < d.p1 ∧ d.earA + 2 < d.p3 - (d.innerFwd - 1) + 1) :
    (d.peelInnerToLen2 hnest hlen hEarBwd hOuter).n = d.n - (d.innerFwd - 1) :=
  rfl

/-- Peeled inner ear is a triangle (shorterInternals = 1). -/
theorem NoncrossingChordDiagram.peelInnerToLen2_toEar_triangle
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - (d.innerFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (hOuter : d.p0 < d.p1 ∧ d.earA + 2 < d.p3 - (d.innerFwd - 1) + 1) :
    (d.peelInnerToLen2 hnest hlen hEarBwd hOuter).toEar.shorterInternals = 1 := by
  simp only [NoncrossingChordDiagram.toEar, CycleChord.shorterInternals,
    CycleChord.fwdInternals, CycleChord.bwdInternals,
    NoncrossingChordDiagram.peelInnerToLen2]
  omega

theorem NoncrossingChordDiagram.peelInnerToLen2_nPos
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - (d.innerFwd - 1)) - ((d.earA + 2) - d.earA) - 1)
    (hOuter : d.p0 < d.p1 ∧ d.earA + 2 < d.p3 - (d.innerFwd - 1) + 1) :
    1 < (d.peelInnerToLen2 hnest hlen hEarBwd hOuter).n := by
  have := d.ordered
  have em := d.ear_match
  simp [hnest] at em
  have : d.earA = d.p1 ∧ d.earB = d.p2 := em
  simp only [NoncrossingChordDiagram.peelInnerToLen2, NoncrossingChordDiagram.innerLenGe3,
    NoncrossingChordDiagram.innerFwd] at hlen hEarBwd hOuter ⊢
  omega

/-- C₁₀ nested peels to C₈-style nested `{0,6}` / `{2,4}`. -/
theorem c10Nested_peel_to_len2 :
    let d := c10NestedDiagram.peelInnerToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 8 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 4 ∧ d.p3 = 6 ∧
      d.innerLen2 ∧ d.toEar.shorterInternals = 1 := by
  native_decide

/-- Peeled C₁₀ nested admits the two-step nested triangle induction. -/
def c10NestedPeeledInduction : NestedTriangleInduction where
  diagram := c10NestedDiagram.peelInnerToLen2
    rfl (by native_decide) (by decide) (by decide)
  nested := rfl
  innerLen2 := by native_decide
  outerBwd := by decide
  innerTri := by native_decide
  nPos := by decide
  outerTri := by native_decide
  outerNPos := by native_decide

theorem c10Nested_peel_then_two_step_to_cycle :
    c10NestedPeeledInduction.midEmbed.isCycle = false ∧
      c10NestedPeeledInduction.step2.after.isCycle = true ∧
      gf2Sum c10NestedPeeledInduction.step2.chargesAfter.charges = 1 :=
  ⟨c10NestedPeeledInduction.mid_not_cycle, c10NestedPeeledInduction.final_is_cycle,
    c10NestedPeeledInduction.step2.charges_remain_odd⟩

def nestedPeelDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
