/-
  Disjoint long-ear peel → cycle via auto-built `DisjointLen2Induction` (Category C / G6).

  Triangle/`nPos`/`secondGap` from peel lemmas; residual second bwd/NPos on peeled diagram.
-/

import PNPLab.DisjointChordPeel
import PNPLab.DisjointChordToCycle

namespace PNPLab.Outerplanar

/-- Long disjoint first ear → peel to len-2 → total second residual peel. -/
structure DisjointLongEarInduction where
  diagram : NoncrossingChordDiagram
  disjoint : diagram.pairing = .disjoint
  hlen : diagram.firstLenGe3
  hEarBwd : 0 < (diagram.n - (diagram.firstFwd - 1)) - ((diagram.earA + 2) - diagram.earA) - 1
  hSecond : diagram.earA + 2 < diagram.p2 - (diagram.firstFwd - 1) ∧
    (diagram.p2 - (diagram.firstFwd - 1)) + 2 ≤ diagram.p3 - (diagram.firstFwd - 1)
  hSecondBwd :
    let p := diagram.peelFirstToLen2 disjoint hlen hEarBwd hSecond
    0 < (p.n - 1) - ((p.p3 - 1) - (p.p2 - 1)) - 1
  hSecondNPos :
    let p := diagram.peelFirstToLen2 disjoint hlen hEarBwd hSecond
    let hg := NoncrossingChordDiagram.peelFirstToLen2_secondGap
      diagram disjoint hlen hEarBwd hSecond
    let hb : 0 < (p.n - 1) - ((p.p3 - 1) - (p.p2 - 1)) - 1 := hSecondBwd
    1 < (p.residualSecondChord rfl
      (NoncrossingChordDiagram.peelFirstToLen2_firstLen2 diagram disjoint hlen hEarBwd hSecond)
      hg hb).n

def DisjointLongEarInduction.peeled (s : DisjointLongEarInduction) : NoncrossingChordDiagram :=
  s.diagram.peelFirstToLen2 s.disjoint s.hlen s.hEarBwd s.hSecond

noncomputable def DisjointLongEarInduction.len2 (s : DisjointLongEarInduction) :
    DisjointLen2Induction where
  diagram := s.peeled
  disjoint := rfl
  firstLen2 := NoncrossingChordDiagram.peelFirstToLen2_firstLen2
    s.diagram s.disjoint s.hlen s.hEarBwd s.hSecond
  secondGap := NoncrossingChordDiagram.peelFirstToLen2_secondGap
    s.diagram s.disjoint s.hlen s.hEarBwd s.hSecond
  secondBwd := s.hSecondBwd
  firstTri := NoncrossingChordDiagram.peelFirstToLen2_toEar_triangle
    s.diagram s.disjoint s.hlen s.hEarBwd s.hSecond
  nPos := NoncrossingChordDiagram.peelFirstToLen2_nPos
    s.diagram s.disjoint s.hlen s.hEarBwd s.hSecond
  secondNPos := s.hSecondNPos

noncomputable def DisjointLongEarInduction.toCycleBase (s : DisjointLongEarInduction) :
    FacialCycleBase :=
  s.len2.toCycleBase

theorem DisjointLongEarInduction.reaches_cycle (s : DisjointLongEarInduction) :
    let b := s.toCycleBase
    s.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  s.len2.reaches_cycle

/-- C₁₀ disjoint long ear → peel → total (second residual is a triangle). -/
noncomputable def c10DisjointLongEarInduction : DisjointLongEarInduction where
  diagram := c10DisjointDiagram
  disjoint := rfl
  hlen := by native_decide
  hEarBwd := by decide
  hSecond := by decide
  hSecondBwd := by decide
  hSecondNPos := by native_decide

theorem c10Disjoint_long_ear_reaches_cycle :
    let b := c10DisjointLongEarInduction.toCycleBase
    c10DisjointLongEarInduction.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c10DisjointLongEarInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/--
  C₁₄ disjoint long first ear: `{0,4}` and `{6,12}`.
  Peel → C₁₂-style `{0,2}`/`{4,10}`; second residual `{3,9}` on 11 (shorter ≥ 2).
-/
def c14DisjointLongEar : NoncrossingChordDiagram where
  n := 14
  p0 := 0
  p1 := 4
  p2 := 6
  p3 := 12
  pairing := .disjoint
  ordered := by decide
  earA := 0
  earB := 4
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c14Disjoint_peel_shape :
    let d := c14DisjointLongEar.peelFirstToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 12 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 4 ∧ d.p3 = 10 ∧
      d.firstLen2 := by
  native_decide

theorem c14Disjoint_peel_residual_long :
    let d := c14DisjointLongEar.peelFirstToLen2
      rfl (by native_decide) (by decide) (by decide)
    let c := d.residualSecondChord rfl (by native_decide) (by decide) (by decide)
    c.n = 11 ∧ c.a = 3 ∧ c.b = 9 ∧ 2 ≤ c.shorterInternals := by
  native_decide

noncomputable def c14DisjointLongEarInduction : DisjointLongEarInduction where
  diagram := c14DisjointLongEar
  disjoint := rfl
  hlen := by native_decide
  hEarBwd := by decide
  hSecond := by decide
  hSecondBwd := by decide
  hSecondNPos := by native_decide

theorem c14Disjoint_long_ear_reaches_cycle :
    let b := c14DisjointLongEarInduction.toCycleBase
    c14DisjointLongEarInduction.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c14DisjointLongEarInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

def disjointLongEarToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
