/-
  Nested long-ear peel → cycle via auto-built `NestedLen2Induction` (Category C / G6).

  After `peelInnerToLen2`, finish with `CycleChord.toCycleBase`.  Triangle/`nPos`
  come from peel lemmas; residual outer bwd/NPos are stated on the peeled diagram.
-/

import PNPLab.NestedChordPeel
import PNPLab.NestedChordToCycle

namespace PNPLab.Outerplanar

/-- Long nested inner ear → peel to len-2 → total outer residual peel. -/
structure NestedLongEarInduction where
  diagram : NoncrossingChordDiagram
  nested : diagram.pairing = .nested
  hlen : diagram.innerLenGe3
  hEarBwd : 0 < (diagram.n - (diagram.innerFwd - 1)) - ((diagram.earA + 2) - diagram.earA) - 1
  hOuter : diagram.p0 < diagram.p1 ∧
    diagram.earA + 2 < diagram.p3 - (diagram.innerFwd - 1) + 1
  /-- Outer residual bwd on the *peeled* diagram. -/
  hOuterBwd :
    let p := diagram.peelInnerToLen2 nested hlen hEarBwd hOuter
    0 < p.n - (p.p3 - p.p0) - 1
  /-- Outer residual has ≥ 2 vertices after tip delete. -/
  hOuterNPos :
    let p := diagram.peelInnerToLen2 nested hlen hEarBwd hOuter
    let hb : 0 < p.n - (p.p3 - p.p0) - 1 := hOuterBwd
    1 < (p.residualOuterChord rfl
      (NoncrossingChordDiagram.peelInnerToLen2_innerLen2 diagram nested hlen hEarBwd hOuter)
      hb).n

def NestedLongEarInduction.peeled (s : NestedLongEarInduction) : NoncrossingChordDiagram :=
  s.diagram.peelInnerToLen2 s.nested s.hlen s.hEarBwd s.hOuter

noncomputable def NestedLongEarInduction.len2 (s : NestedLongEarInduction) :
    NestedLen2Induction where
  diagram := s.peeled
  nested := rfl
  innerLen2 := NoncrossingChordDiagram.peelInnerToLen2_innerLen2
    s.diagram s.nested s.hlen s.hEarBwd s.hOuter
  outerBwd := s.hOuterBwd
  innerTri := NoncrossingChordDiagram.peelInnerToLen2_toEar_triangle
    s.diagram s.nested s.hlen s.hEarBwd s.hOuter
  nPos := NoncrossingChordDiagram.peelInnerToLen2_nPos
    s.diagram s.nested s.hlen s.hEarBwd s.hOuter
  outerNPos := s.hOuterNPos

noncomputable def NestedLongEarInduction.toCycleBase (s : NestedLongEarInduction) :
    FacialCycleBase :=
  s.len2.toCycleBase

theorem NestedLongEarInduction.reaches_cycle (s : NestedLongEarInduction) :
    let b := s.toCycleBase
    s.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  s.len2.reaches_cycle

/-- C₁₀ nested long ear → peel → total (outer residual is a triangle). -/
noncomputable def c10NestedLongEarInduction : NestedLongEarInduction where
  diagram := c10NestedDiagram
  nested := rfl
  hlen := by native_decide
  hEarBwd := by decide
  hOuter := by decide
  hOuterBwd := by decide
  hOuterNPos := by native_decide

theorem c10Nested_long_ear_reaches_cycle :
    let b := c10NestedLongEarInduction.toCycleBase
    c10NestedLongEarInduction.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c10NestedLongEarInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

/--
  C₁₄ nested long ear: outer `{0,10}`, inner `{2,6}`.
  Peel → C₁₂-style `{0,8}`/`{2,4}`; outer residual `{0,7}` on 11 (shorter ≥ 2).
-/
def c14NestedLongEar : NoncrossingChordDiagram where
  n := 14
  p0 := 0
  p1 := 2
  p2 := 6
  p3 := 10
  pairing := .nested
  ordered := by decide
  earA := 2
  earB := 6
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c14Nested_peel_shape :
    let d := c14NestedLongEar.peelInnerToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 12 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 4 ∧ d.p3 = 8 ∧
      d.innerLen2 := by
  native_decide

theorem c14Nested_peel_residual_long :
    let d := c14NestedLongEar.peelInnerToLen2
      rfl (by native_decide) (by decide) (by decide)
    let c := d.residualOuterChord rfl (by native_decide) (by decide)
    c.n = 11 ∧ c.a = 0 ∧ c.b = 7 ∧ 2 ≤ c.shorterInternals := by
  native_decide

noncomputable def c14NestedLongEarInduction : NestedLongEarInduction where
  diagram := c14NestedLongEar
  nested := rfl
  hlen := by native_decide
  hEarBwd := by decide
  hOuter := by decide
  hOuterBwd := by decide
  hOuterNPos := by native_decide

theorem c14Nested_long_ear_reaches_cycle :
    let b := c14NestedLongEarInduction.toCycleBase
    c14NestedLongEarInduction.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c14NestedLongEarInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1⟩

def nestedLongEarToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
