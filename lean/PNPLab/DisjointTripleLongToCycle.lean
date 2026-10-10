/-
  Disjoint-triple → long residual → peel → Len2 → cycle (Category C / G6).

  Mirror of `NestedTripleLongToCycle`: after first fold, the residual pair may
  have a long first ear; peel to len-2 and finish with `DisjointLen2Induction`
  (second residual need not be a triangle).
-/

import PNPLab.DisjointTripleResidual
import PNPLab.DisjointLongEarToCycle

namespace PNPLab.Outerplanar

/-- Triple → residual disjoint pair → long-ear peel → total second peel. -/
structure DisjointTripleLongInduction where
  triple : DisjointTripleChords
  hlen2 : triple.firstLen2
  hFirstGap : triple.p2 + 2 ≤ triple.p3
  hEarBwd : 0 < (triple.n - 1) - ((triple.p3 - 1) - (triple.p2 - 1)) - 1
  longEar : DisjointLongEarInduction
  residual_eq :
    longEar.diagram = triple.residualDisjointPair hlen2 hFirstGap hEarBwd

noncomputable def DisjointTripleLongInduction.toCycleBase
    (s : DisjointTripleLongInduction) : FacialCycleBase :=
  s.longEar.toCycleBase

theorem DisjointTripleLongInduction.after_first_not_cycle
    (s : DisjointTripleLongInduction) :
    (s.triple.afterFirstTriangle s.hlen2 s.hFirstGap s.hEarBwd).isCycle = false :=
  s.triple.afterFirstTriangle_not_cycle s.hlen2 s.hFirstGap s.hEarBwd

theorem DisjointTripleLongInduction.reaches_cycle (s : DisjointTripleLongInduction) :
    let b := s.toCycleBase
    (s.triple.afterFirstTriangle s.hlen2 s.hFirstGap s.hEarBwd).isCycle = false ∧
      s.longEar.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let h := s.longEar.reaches_cycle
  ⟨s.after_first_not_cycle, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- C₁₅ residual disjoint pair after first triangle. -/
def c15DisjointPair : NoncrossingChordDiagram :=
  c15DisjointTriple.residualDisjointPair
    (by native_decide) (by decide) (by decide)

theorem c15DisjointPair_shape :
    c15DisjointPair.n = 14 ∧ c15DisjointPair.p0 = 3 ∧ c15DisjointPair.p1 = 8 ∧
      c15DisjointPair.p2 = 10 ∧ c15DisjointPair.p3 = 13 ∧
      c15DisjointPair.firstLenGe3 ∧ c15DisjointPair.firstFwd = 4 := by
  native_decide

theorem c15Disjoint_peel_shape :
    let d := c15DisjointPair.peelFirstToLen2
      rfl (by native_decide) (by decide) (by decide)
    d.n = 11 ∧ d.p0 = 3 ∧ d.p1 = 5 ∧ d.p2 = 7 ∧ d.p3 = 10 ∧
      d.firstLen2 := by
  native_decide

theorem c15Disjoint_peel_residual_long :
    let d := c15DisjointPair.peelFirstToLen2
      rfl (by native_decide) (by decide) (by decide)
    let c := d.residualSecondChord rfl (by native_decide) (by decide) (by decide)
    c.n = 10 ∧ c.a = 6 ∧ c.b = 9 ∧ 2 ≤ c.shorterInternals := by
  native_decide

noncomputable def c15DisjointTripleLongInduction : DisjointTripleLongInduction where
  triple := c15DisjointTriple
  hlen2 := by native_decide
  hFirstGap := by decide
  hEarBwd := by decide
  longEar := {
    diagram := c15DisjointPair
    disjoint := rfl
    hlen := by native_decide
    hEarBwd := by decide
    hSecond := by decide
    hSecondBwd := by decide
    hSecondNPos := by native_decide
  }
  residual_eq := rfl

theorem c15DisjointTriple_long_path_to_cycle :
    let b := c15DisjointTripleLongInduction.toCycleBase
    (c15DisjointTriple.afterFirstTriangle
      (by native_decide) (by decide) (by decide)).isCycle = false ∧
      c15DisjointTripleLongInduction.longEar.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c15DisjointTripleLongInduction.reaches_cycle
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def disjointTripleLongToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
