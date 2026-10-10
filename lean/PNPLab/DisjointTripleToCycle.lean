/-
  Disjoint-triple path to cycle when residual first ear is already length-2
  (Category C / G6).  Mirror of `NestedTripleToCycle`.
-/

import PNPLab.DisjointTripleResidual
import PNPLab.DisjointChordToCycle

namespace PNPLab.Outerplanar

/-- C₁₂ residual disjoint pair after first triangle. -/
def c12DisjointPair : NoncrossingChordDiagram :=
  c12DisjointTriple.residualDisjointPair
    (by native_decide) (by decide) (by decide)

theorem c12DisjointPair_len2 :
    c12DisjointPair.firstLen2 ∧ c12DisjointPair.toEar.shorterInternals = 1 := by
  native_decide

/-- Full induction on the residual pair (second may be triangle). -/
def c12DisjointTripleInduction : DisjointTriangleInduction where
  diagram := c12DisjointPair
  disjoint := rfl
  firstLen2 := by native_decide
  secondGap := by decide
  secondBwd := by decide
  firstTri := by native_decide
  nPos := by decide
  secondTri := by native_decide
  secondNPos := by native_decide

noncomputable def c12DisjointTripleLen2Induction : DisjointLen2Induction :=
  c12DisjointTripleInduction.toLen2

theorem c12DisjointTriple_full_path_to_cycle :
    (c12DisjointTriple.afterFirstTriangle
      (by native_decide) (by decide) (by decide)).isCycle = false ∧
      c12DisjointTripleInduction.midEmbed.isCycle = false ∧
      c12DisjointTripleInduction.step2.after.isCycle = true ∧
      gf2Sum c12DisjointTripleInduction.step2.chargesAfter.charges = 1 :=
  ⟨rfl, c12DisjointTripleInduction.mid_not_cycle, c12DisjointTripleInduction.final_is_cycle,
    c12DisjointTripleInduction.step2.charges_remain_odd⟩

theorem c12DisjointTriple_full_path_via_total :
    let b := c12DisjointTripleLen2Induction.toCycleBase
    (c12DisjointTriple.afterFirstTriangle
      (by native_decide) (by decide) (by decide)).isCycle = false ∧
      c12DisjointTripleLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c12DisjointTripleLen2Induction.reaches_cycle
  ⟨rfl, h.1, h.2.1, h.2.2.1⟩

def disjointTripleToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
