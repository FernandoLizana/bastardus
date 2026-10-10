/-
  Nested-triple path to cycle (Category C / G6).

  Schedule:
    1. fold innermost triangle → nested two-chord residual
    2. peel inner ear to length-2 (`peelInnerToLen2`)
    3. `NestedLen2Induction` / total outer residual peel (via `toLen2`)
-/

import PNPLab.NestedTripleResidual
import PNPLab.NestedChordPeel
import PNPLab.NestedChordToCycle

namespace PNPLab.Outerplanar

/-- C₁₂ nested-triple residual pair (after inner triangle). -/
def c12NestedPair : NoncrossingChordDiagram :=
  c12NestedTriple.residualNestedPair (by native_decide) (by decide)

theorem c12NestedPair_long_ear :
    c12NestedPair.innerLenGe3 ∧ c12NestedPair.innerFwd = 4 := by
  native_decide

/-- Peel the C₁₂ residual pair to a length-2 nested diagram. -/
def c12NestedPeeled : NoncrossingChordDiagram :=
  c12NestedPair.peelInnerToLen2 rfl (by native_decide) (by decide) (by decide)

theorem c12NestedPeeled_shape :
    c12NestedPeeled.n = 8 ∧ c12NestedPeeled.p0 = 0 ∧ c12NestedPeeled.p1 = 2 ∧
      c12NestedPeeled.p2 = 4 ∧ c12NestedPeeled.p3 = 6 ∧
      c12NestedPeeled.innerLen2 := by
  native_decide

/-- Full induction after peel (triangle outer; also via total). -/
def c12NestedTripleInduction : NestedTriangleInduction where
  diagram := c12NestedPeeled
  nested := rfl
  innerLen2 := by native_decide
  outerBwd := by decide
  innerTri := by native_decide
  nPos := by decide
  outerTri := by native_decide
  outerNPos := by native_decide

noncomputable def c12NestedTripleLen2Induction : NestedLen2Induction :=
  c12NestedTripleInduction.toLen2

theorem c12NestedTriple_full_path_to_cycle :
    (c12NestedTriple.afterInnerTriangle (by native_decide) (by decide)).isCycle = false ∧
      c12NestedTripleInduction.midEmbed.isCycle = false ∧
      c12NestedTripleInduction.step2.after.isCycle = true ∧
      gf2Sum c12NestedTripleInduction.step2.chargesAfter.charges = 1 :=
  ⟨rfl, c12NestedTripleInduction.mid_not_cycle, c12NestedTripleInduction.final_is_cycle,
    c12NestedTripleInduction.step2.charges_remain_odd⟩

theorem c12NestedTriple_full_path_via_total :
    let b := c12NestedTripleLen2Induction.toCycleBase
    (c12NestedTriple.afterInnerTriangle (by native_decide) (by decide)).isCycle = false ∧
      c12NestedTripleLen2Induction.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c12NestedTripleLen2Induction.reaches_cycle
  ⟨rfl, h.1, h.2.1, h.2.2.1⟩

def nestedTripleToCycleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
