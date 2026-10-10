/-
  Nested-triple → long residual → peel → Len2 → cycle (Category C / G6).

  Extends the C₁₂ triangle-outer path: after innermost fold, the nested pair
  may have a long mid ear; peel to len-2 and finish with `NestedLen2Induction`
  (outer residual need not be a triangle).
-/

import PNPLab.NestedTripleResidual
import PNPLab.NestedLongEarToCycle

namespace PNPLab.Outerplanar

/-- Triple → residual nested pair → long-ear peel → total outer peel. -/
structure NestedTripleLongInduction where
  triple : NestedTripleChords
  hlen2 : triple.innerLen2
  hEarBwd : 0 < (triple.n - 1) - ((triple.p4 - 1) - triple.p1) - 1
  longEar : NestedLongEarInduction
  residual_eq :
    longEar.diagram = triple.residualNestedPair hlen2 hEarBwd

noncomputable def NestedTripleLongInduction.toCycleBase
    (s : NestedTripleLongInduction) : FacialCycleBase :=
  s.longEar.toCycleBase

theorem NestedTripleLongInduction.after_inner_not_cycle
    (s : NestedTripleLongInduction) :
    (s.triple.afterInnerTriangle s.hlen2 s.hEarBwd).isCycle = false :=
  s.triple.afterInnerTriangle_not_cycle s.hlen2 s.hEarBwd

theorem NestedTripleLongInduction.reaches_cycle (s : NestedTripleLongInduction) :
    let b := s.toCycleBase
    (s.triple.afterInnerTriangle s.hlen2 s.hEarBwd).isCycle = false ∧
      s.longEar.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let h := s.longEar.reaches_cycle
  ⟨s.after_inner_not_cycle, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- C₁₅ residual nested pair after innermost triangle. -/
def c15NestedPair : NoncrossingChordDiagram :=
  c15NestedTriple.residualNestedPair (by native_decide) (by decide)

theorem c15NestedPair_shape :
    c15NestedPair.n = 14 ∧ c15NestedPair.p0 = 0 ∧ c15NestedPair.p1 = 2 ∧
      c15NestedPair.p2 = 6 ∧ c15NestedPair.p3 = 10 ∧
      c15NestedPair.innerLenGe3 ∧ c15NestedPair.innerFwd = 3 := by
  native_decide

theorem c15Nested_peel_shape :
    let d := c15NestedPair.peelInnerToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 12 ∧ d.p0 = 0 ∧ d.p1 = 2 ∧ d.p2 = 4 ∧ d.p3 = 8 ∧
      d.innerLen2 := by
  native_decide

theorem c15Nested_peel_residual_long :
    let d := c15NestedPair.peelInnerToLen2
      rfl (by native_decide) (by decide) (by decide)
    let c := d.residualOuterChord rfl (by native_decide) (by decide)
    c.n = 11 ∧ c.a = 0 ∧ c.b = 7 ∧ 2 ≤ c.shorterInternals := by
  native_decide

noncomputable def c15NestedTripleLongInduction : NestedTripleLongInduction where
  triple := c15NestedTriple
  hlen2 := by native_decide
  hEarBwd := by decide
  longEar := {
    diagram := c15NestedPair
    nested := rfl
    hlen := by native_decide
    hEarBwd := by decide
    hOuter := by decide
    hOuterBwd := by decide
    hOuterNPos := by native_decide
  }
  residual_eq := rfl

theorem c15NestedTriple_long_path_to_cycle :
    let b := c15NestedTripleLongInduction.toCycleBase
    (c15NestedTriple.afterInnerTriangle (by native_decide) (by decide)).isCycle = false ∧
      c15NestedTripleLongInduction.longEar.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c15NestedTripleLongInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def nestedTripleLongToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
