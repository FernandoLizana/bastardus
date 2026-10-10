/-
  Total, terminating ear-fold elimination (Category C / G6).

  The sketch layer in `Outerplanar.lean` only tracks a *measure* (`FoldMeasure`)
  under one fold, not an actual successor sketch or a fold count to a base. This
  module closes that honest gap for the "earLaw outerplanar general" projection:

    * `foldSucc`   : a deterministic successor sketch (drops one vertex on any
                     non-cycle positive sketch, otherwise a fixpoint at the base);
    * `foldNormal` : the total fold-to-base normal form (well-founded recursion);
    * `foldSteps`  : the number of legal folds to reach the base.

  We prove termination, that the normal form is a base (cycle or degenerate),
  and that the fold count is bounded by the vertex count. `earLaw` guarantees a
  legal fold exists at each non-cycle step, so this is a faithful termination
  witness for the ear-peeling induction (not the Whitney existence proof itself).
-/

import PNPLab.Outerplanar

namespace PNPLab.Outerplanar

/-- A sketch is at the elimination base when it is a cycle or has no vertices. -/
def ResidualSketch.atBase (g : ResidualSketch) : Prop :=
  g.isCycle = true ∨ g.nVertices = 0

instance (g : ResidualSketch) : Decidable g.atBase := by
  unfold ResidualSketch.atBase
  infer_instance

/-- Deterministic fold successor: peel one vertex off a non-base sketch. -/
def foldSucc (g : ResidualSketch) : ResidualSketch :=
  if g.atBase then g
  else
    { nVertices := g.nVertices - 1
      isCycle := g.isCycle
      hasTriangleEar := g.hasTriangleEar
      hasShortcutTip := g.hasShortcutTip
      earLaw := g.earLaw }

/-- On a non-base sketch the successor strictly drops the vertex measure. -/
theorem foldSucc_lt (g : ResidualSketch) (h : ¬ g.atBase) :
    (foldSucc g).nVertices < g.nVertices := by
  have hpos : 0 < g.nVertices := by
    rcases Nat.eq_zero_or_pos g.nVertices with h0 | hp
    · exact absurd (Or.inr h0) h
    · exact hp
  unfold foldSucc
  rw [if_neg h]
  show g.nVertices - 1 < g.nVertices
  omega

/-- On a base sketch the successor is a fixpoint. -/
theorem foldSucc_base (g : ResidualSketch) (h : g.atBase) :
    foldSucc g = g := by
  unfold foldSucc
  rw [if_pos h]

/-- Total fold-to-base normal form via well-founded recursion on vertices. -/
def foldNormal (g : ResidualSketch) : ResidualSketch :=
  if _h : g.atBase then g
  else foldNormal (foldSucc g)
termination_by g.nVertices
decreasing_by exact foldSucc_lt g _h

/-- Number of legal folds to reach the base. -/
def foldSteps (g : ResidualSketch) : Nat :=
  if h : g.atBase then 0
  else 1 + foldSteps (foldSucc g)
termination_by g.nVertices
decreasing_by exact foldSucc_lt g h

/-- The normal form is always a base (cycle or degenerate). -/
theorem foldNormal_atBase (g : ResidualSketch) : (foldNormal g).atBase := by
  unfold foldNormal
  by_cases h : g.atBase
  · rw [dif_pos h]; exact h
  · rw [dif_neg h]; exact foldNormal_atBase (foldSucc g)
termination_by g.nVertices
decreasing_by exact foldSucc_lt g h

/-- A base sketch needs no folds. -/
theorem foldSteps_base (g : ResidualSketch) (h : g.atBase) : foldSteps g = 0 := by
  unfold foldSteps; rw [dif_pos h]

/-- The fold count is bounded by the vertex count. -/
theorem foldSteps_le (g : ResidualSketch) : foldSteps g ≤ g.nVertices := by
  unfold foldSteps
  by_cases h : g.atBase
  · rw [dif_pos h]; exact Nat.zero_le _
  · rw [dif_neg h]
    have hlt : (foldSucc g).nVertices < g.nVertices := foldSucc_lt g h
    have ih : foldSteps (foldSucc g) ≤ (foldSucc g).nVertices := foldSteps_le (foldSucc g)
    omega
termination_by g.nVertices
decreasing_by exact foldSucc_lt g h

/-- Non-base sketches take at least one fold. -/
theorem foldSteps_pos (g : ResidualSketch) (h : ¬ g.atBase) : 0 < foldSteps g := by
  unfold foldSteps; rw [dif_neg h]; omega

/-- Normal form preserves the cycle base once reached. -/
theorem foldNormal_cycle (g : ResidualSketch) (h : g.isCycle = true) :
    foldNormal g = g := by
  have hb : g.atBase := Or.inl h
  unfold foldNormal
  rw [dif_pos hb]

/-- A cycle base is fixed by `foldSteps` (zero folds). -/
theorem foldSteps_cycle (n : Nat) : foldSteps (sketchCycle n) = 0 := by
  apply foldSteps_base
  left
  rfl

/-- A triangle-ear sketch on `n` vertices folds to base in at most `n` steps. -/
theorem foldSteps_triangleEar_le (n : Nat) :
    foldSteps (sketchTriangleEar n) ≤ n :=
  foldSteps_le (sketchTriangleEar n)

/-- Concrete: the C₄ triangle-ear residual folds down in a bounded number of steps. -/
theorem foldSteps_c4_le : foldSteps residualC4Triangle ≤ 4 :=
  foldSteps_le residualC4Triangle

def foldTerminationDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
