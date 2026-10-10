/-
  Nested-triple residual after innermost triangle fold (Category C / G6).

  Honesty: `NestedTripleChords.toSketch` packages only the innermost ear.
  Folding that ear does **not** yield a pure cycle — the middle and outer
  chords remain as a nested `NoncrossingChordDiagram` on `n - 1` vertices.
-/

import PNPLab.NestedTripleChordsEar
import PNPLab.ChordDiagramEar
import PNPLab.OuterplanarEmbedCert

namespace PNPLab.Outerplanar

/-- Innermost chord is length-2 (one internal tip). -/
abbrev NestedTripleChords.innerLen2 (c : NestedTripleChords) : Prop :=
  c.p3 = c.p2 + 2

/--
  After deleting tip `p2 + 1`, residual nested pair:
  outer `{p0, p5-1}`, inner `{p1, p4-1}` on `n - 1` vertices.
-/
def NestedTripleChords.residualNestedPair (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) : NoncrossingChordDiagram where
  n := c.n - 1
  p0 := c.p0
  p1 := c.p1
  p2 := c.p4 - 1
  p3 := c.p5 - 1
  pairing := .nested
  ordered := by
    have := c.ordered
    simp [NestedTripleChords.innerLen2] at hlen2
    omega
  earA := c.p1
  earB := c.p4 - 1
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by
    have := c.ordered
    simp [NestedTripleChords.innerLen2] at hlen2
    omega
  ear_b_lt_n := by
    have := c.ordered
    omega
  ear_bwd_pos := hEarBwd

theorem NestedTripleChords.residualNestedPair_n (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.residualNestedPair hlen2 hEarBwd).n = c.n - 1 :=
  rfl

/-- Embed cert after inner fold: still oneChord of the *derived mid ear*, not a cycle.
    Full two-chord residual is the `NoncrossingChordDiagram` above. -/
def NestedTripleChords.afterInnerTriangle (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) : OuterplanarEmbedCert :=
  .oneChord (c.residualNestedPair hlen2 hEarBwd).toEar

theorem NestedTripleChords.afterInnerTriangle_not_cycle (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.afterInnerTriangle hlen2 hEarBwd).isCycle = false :=
  rfl

theorem NestedTripleChords.residual_is_nested (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.residualNestedPair hlen2 hEarBwd).pairing = .nested :=
  rfl

/-- C₁₂ nested triple → residual nested pair `{0,9}` / `{2,7}` on 11 verts. -/
theorem c12NestedTriple_residual :
    let d := c12NestedTriple.residualNestedPair (by native_decide) (by decide)
    d.n = 11 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 7 ∧ d.p3 = 9 ∧
      d.pairing = .nested ∧ d.toEar.a = 2 ∧ d.toEar.b = 7 := by
  native_decide

theorem c12NestedTriple_after_not_cycle :
    (c12NestedTriple.afterInnerTriangle (by native_decide) (by decide)).isCycle =
      false :=
  rfl

def nestedTripleResidualDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
