/-
  Aggregate: all six alt fresh G₀→R ProjectionInclusions beyond packs.
-/

import PNPLab.Alt1FoldProjection
import PNPLab.Alt2LongArcBridge
import PNPLab.Alt3FoldProjection
import PNPLab.Alt4FoldProjection
import PNPLab.Alt5FoldProjection
import PNPLab.Alt6FoldProjection

namespace PNPLab.Resolution

def altFreshG0Count : Nat := 6

theorem altFreshG0Count_eq : altFreshG0Count = 6 := rfl

theorem all_alt_fresh_g0_no_empty :
    ¬ alt1GProjection.gClosure.mem [] ∧
      ¬ alt2GProjection.gClosure.mem [] ∧
      ¬ alt3GProjection.gClosure.mem [] ∧
      ¬ alt4GProjection.gClosure.mem [] ∧
      ¬ alt5GProjection.gClosure.mem [] ∧
      ¬ alt6GProjection.gClosure.mem [] :=
  ⟨alt1G_no_empty_of_projection, alt2G_no_empty_of_projection,
    alt3G_no_empty_of_projection, alt4G_no_empty_of_projection,
    alt5G_no_empty_of_projection, alt6G_no_empty_of_projection⟩

theorem all_alt_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    residualAxioms e = k4Axioms ∧
      ¬ alt1GProjection.gClosure.mem [] ∧
      ¬ alt2GProjection.gClosure.mem [] ∧
      ¬ alt3GProjection.gClosure.mem [] ∧
      ¬ alt4GProjection.gClosure.mem [] ∧
      ¬ alt5GProjection.gClosure.mem [] ∧
      ¬ alt6GProjection.gClosure.mem [] :=
  ⟨residualAxioms_eq_k4 e,
    alt1G_no_empty_of_projection, alt2G_no_empty_of_projection,
    alt3G_no_empty_of_projection, alt4G_no_empty_of_projection,
    alt5G_no_empty_of_projection, alt6G_no_empty_of_projection⟩

def altFreshG0Doc : String :=
  "alt1..alt6 fresh G₀→R; alt2 = LongArc; alt3..6 via emit_alt_fold_lean"

end PNPLab.Resolution
