/-
  Disjoint two-chord residual after one **fwd shortcut** on a long first ear
  (Category C / G6 honesty).  Symmetric to `NestedChordShortcut`.
-/

import PNPLab.DisjointChordResidual
import PNPLab.OuterplanarShortcutFold

namespace PNPLab.Outerplanar

/-- First (disjoint) ear has ≥ 2 internals. -/
abbrev NoncrossingChordDiagram.firstLenGe3 (d : NoncrossingChordDiagram) : Prop :=
  d.earA + 3 ≤ d.earB

/--
  After deleting tip `earA + 1` on a disjoint long first ear:
  first `{p0, p1-1}`, second `{p2-1, p3-1}` on `n - 1` vertices.
-/
def NoncrossingChordDiagram.residualAfterFirstShortcut (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hSecond : d.p1 < d.p2 ∧ d.p2 + 1 < d.p3) : NoncrossingChordDiagram where
  n := d.n - 1
  p0 := d.p0
  p1 := d.p1 - 1
  p2 := d.p2 - 1
  p3 := d.p3 - 1
  pairing := .disjoint
  ordered := by
    have := d.ordered
    have em := d.ear_match
    simp [hdisj] at em
    have : d.earA = d.p0 ∧ d.earB = d.p1 := em
    simp [NoncrossingChordDiagram.firstLenGe3] at hlen
    omega
  earA := d.earA
  earB := d.earB - 1
  ear_match := by
    have em := d.ear_match
    simp [hdisj] at em
    have : d.earA = d.p0 ∧ d.earB = d.p1 := em
    exact ⟨this.1, by omega⟩
  ear_gap := by
    have := d.ear_gap
    simp [NoncrossingChordDiagram.firstLenGe3] at hlen
    omega
  ear_b_lt_n := by
    have := d.ordered
    have := d.ear_b_lt_n
    omega
  ear_bwd_pos := hEarBwd

theorem NoncrossingChordDiagram.residualAfterFirstShortcut_ear_shortens
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hSecond : d.p1 < d.p2 ∧ d.p2 + 1 < d.p3) :
    (d.residualAfterFirstShortcut hdisj hlen hEarBwd hSecond).earB = d.earB - 1 ∧
      (d.residualAfterFirstShortcut hdisj hlen hEarBwd hSecond).n = d.n - 1 ∧
      (d.residualAfterFirstShortcut hdisj hlen hEarBwd hSecond).pairing = .disjoint :=
  ⟨rfl, rfl, rfl⟩

theorem NoncrossingChordDiagram.afterFirstShortcut_embed_not_cycle
    (d : NoncrossingChordDiagram)
    (hdisj : d.pairing = .disjoint)
    (hlen : d.firstLenGe3)
    (hEarBwd : 0 < (d.n - 1) - ((d.earB - 1) - d.earA) - 1)
    (hSecond : d.p1 < d.p2 ∧ d.p2 + 1 < d.p3) :
    (OuterplanarEmbedCert.oneChord
      (d.residualAfterFirstShortcut hdisj hlen hEarBwd hSecond).toEar).isCycle =
      false :=
  rfl

/-- C₁₀ disjoint: `{0,4}` and `{6,8}` (first ear internals 3). -/
def c10DisjointDiagram : NoncrossingChordDiagram where
  n := 10
  p0 := 0
  p1 := 4
  p2 := 6
  p3 := 8
  pairing := .disjoint
  ordered := by decide
  earA := 0
  earB := 4
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c10Disjoint_after_shortcut :
    let d := c10DisjointDiagram.residualAfterFirstShortcut
      rfl (by native_decide) (by decide) (by decide)
    d.n = 9 ∧ d.p0 = 0 ∧ d.p1 = 3 ∧ d.p2 = 5 ∧ d.p3 = 7 ∧
      d.earA = 0 ∧ d.earB = 3 ∧ d.pairing = .disjoint ∧
      d.toEar.shorterInternals = 2 := by
  native_decide

theorem c10Disjoint_shortcut_not_cycle :
    (OuterplanarEmbedCert.oneChord
      (c10DisjointDiagram.residualAfterFirstShortcut
        rfl (by native_decide) (by decide) (by decide)).toEar).isCycle =
      false :=
  rfl

def disjointShortcutDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
