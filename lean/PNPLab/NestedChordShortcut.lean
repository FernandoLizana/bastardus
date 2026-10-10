/-
  Nested two-chord residual after one **fwd shortcut** on a long inner ear
  (Category C / G6 honesty).

  When the derived nested ear has ≥ 2 internals, a shortcut tip shortens that
  ear but leaves the outer chord.  The residual is again a nested
  `NoncrossingChordDiagram` (not a cycle, not a pure outer one-chord).
-/

import PNPLab.NestedChordResidual
import PNPLab.OuterplanarShortcutFold

namespace PNPLab.Outerplanar

/-- Inner ear has ≥ 2 internals (`earB ≥ earA + 3`). -/
abbrev NoncrossingChordDiagram.innerLenGe3 (d : NoncrossingChordDiagram) : Prop :=
  d.earA + 3 ≤ d.earB

/--
  After deleting tip `earA + 1` on a nested long ear:
  outer `{p0, p3-1}`, inner `{p1, p2-1}` on `n - 1` vertices.
-/
def NoncrossingChordDiagram.residualAfterInnerShortcut (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hOuterOrd : d.p0 < d.p1 ∧ d.p2 ≤ d.p3) : NoncrossingChordDiagram where
  n := d.n - 1
  p0 := d.p0
  p1 := d.p1
  p2 := d.p2 - 1
  p3 := d.p3 - 1
  pairing := .nested
  ordered := by
    have := d.ordered
    have em := d.ear_match
    simp [hnest] at em
    have : d.earA = d.p1 ∧ d.earB = d.p2 := em
    simp [NoncrossingChordDiagram.innerLenGe3] at hlen
    omega
  earA := d.earA
  earB := d.earB - 1
  ear_match := by
    have em := d.ear_match
    simp [hnest] at em
    have : d.earA = d.p1 ∧ d.earB = d.p2 := em
    exact ⟨this.1, by omega⟩
  ear_gap := by
    have := d.ear_gap
    simp [NoncrossingChordDiagram.innerLenGe3] at hlen
    omega
  ear_b_lt_n := by
    have := d.ordered
    have := d.ear_b_lt_n
    omega
  ear_bwd_pos := hEarBwd

theorem NoncrossingChordDiagram.residualAfterInnerShortcut_ear_shortens
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hOuterOrd : d.p0 < d.p1 ∧ d.p2 ≤ d.p3) :
    (d.residualAfterInnerShortcut hnest hlen hEarBwd hOuterOrd).earB =
      d.earB - 1 ∧
      (d.residualAfterInnerShortcut hnest hlen hEarBwd hOuterOrd).n = d.n - 1 :=
  ⟨rfl, rfl⟩

theorem NoncrossingChordDiagram.afterInnerShortcut_embed_not_cycle
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen : d.innerLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hOuterOrd : d.p0 < d.p1 ∧ d.p2 ≤ d.p3) :
    (OuterplanarEmbedCert.oneChord
      (d.residualAfterInnerShortcut hnest hlen hEarBwd hOuterOrd).toEar).isCycle =
      false :=
  rfl

/-- C₁₀ nested: outer `{0,8}`, inner `{2,6}` (ear internals 3). -/
def c10NestedDiagram : NoncrossingChordDiagram where
  n := 10
  p0 := 0
  p1 := 2
  p2 := 6
  p3 := 8
  pairing := .nested
  ordered := by decide
  earA := 2
  earB := 6
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c10Nested_after_shortcut :
    let d := c10NestedDiagram.residualAfterInnerShortcut
      rfl (by native_decide) (by decide) (by decide)
    d.n = 9 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 5 ∧ d.p3 = 7 ∧
      d.earA = 2 ∧ d.earB = 5 ∧ d.pairing = .nested ∧
      d.toEar.shorterInternals = 2 := by
  native_decide

theorem c10Nested_shortcut_not_cycle :
    (OuterplanarEmbedCert.oneChord
      (c10NestedDiagram.residualAfterInnerShortcut
        rfl (by native_decide) (by decide) (by decide)).toEar).isCycle =
      false :=
  rfl

def nestedShortcutDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
