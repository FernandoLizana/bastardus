/-
  Disjoint-triple residual after first triangle fold (Category C / G6).

  Honesty: `DisjointTripleChords.toSketch` packages only the first ear.
  Folding that ear does **not** yield a pure cycle — the other two chords
  remain as a disjoint `NoncrossingChordDiagram` on `n - 1` vertices.
-/

import PNPLab.DisjointTripleChordsEar
import PNPLab.ChordDiagramEar
import PNPLab.OuterplanarEmbedCert

namespace PNPLab.Outerplanar

/-- First chord is length-2 (one internal tip). -/
abbrev DisjointTripleChords.firstLen2 (c : DisjointTripleChords) : Prop :=
  c.p1 = c.p0 + 2

/--
  After deleting tip `p0 + 1`, residual disjoint pair:
  `{p2-1, p3-1}` and `{p4-1, p5-1}` on `n - 1` vertices.
-/
def DisjointTripleChords.residualDisjointPair (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    NoncrossingChordDiagram where
  n := c.n - 1
  p0 := c.p2 - 1
  p1 := c.p3 - 1
  p2 := c.p4 - 1
  p3 := c.p5 - 1
  pairing := .disjoint
  ordered := by
    have := c.ordered
    simp [DisjointTripleChords.firstLen2] at hlen2
    omega
  earA := c.p2 - 1
  earB := c.p3 - 1
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by
    have := c.ordered
    -- (p2 - 1) + 2 ≤ p3 - 1 ↔ p2 + 2 ≤ p3
    have h1 : 1 ≤ c.p2 := by omega
    have h3 : 1 ≤ c.p3 := by omega
    calc (c.p2 - 1) + 2
        = c.p2 + 1 := by omega
      _ ≤ c.p3 - 1 := by
          have : c.p2 + 2 ≤ c.p3 := hFirstGap
          omega
  ear_b_lt_n := by
    have ord := c.ordered
    have hp3 : c.p3 < c.n := by omega
    have h1 : 1 ≤ c.p3 := by omega
    exact Nat.sub_lt_sub_right h1 hp3
  ear_bwd_pos := hEarBwd

theorem DisjointTripleChords.residualDisjointPair_n (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    (c.residualDisjointPair hlen2 hFirstGap hEarBwd).n = c.n - 1 :=
  rfl

/-- Embed cert after first fold: still oneChord of the *derived first residual ear*. -/
def DisjointTripleChords.afterFirstTriangle (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) : OuterplanarEmbedCert :=
  .oneChord (c.residualDisjointPair hlen2 hFirstGap hEarBwd).toEar

theorem DisjointTripleChords.afterFirstTriangle_not_cycle (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    (c.afterFirstTriangle hlen2 hFirstGap hEarBwd).isCycle = false :=
  rfl

theorem DisjointTripleChords.residual_is_disjoint (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    (c.residualDisjointPair hlen2 hFirstGap hEarBwd).pairing = .disjoint :=
  rfl

/-- C₁₂ disjoint triple → residual `{3,5}` / `{7,9}` on 11 verts. -/
theorem c12DisjointTriple_residual :
    let d := c12DisjointTriple.residualDisjointPair
      (by native_decide) (by decide) (by decide)
    d.n = 11 ∧ d.p0 = 3 ∧ d.p1 = 5 ∧ d.p2 = 7 ∧ d.p3 = 9 ∧
      d.pairing = .disjoint ∧ d.toEar.a = 3 ∧ d.toEar.b = 5 := by
  native_decide

theorem c12DisjointTriple_after_not_cycle :
    (c12DisjointTriple.afterFirstTriangle
      (by native_decide) (by decide) (by decide)).isCycle = false :=
  rfl

def disjointTripleResidualDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
