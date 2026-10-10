/-
  Parametric fold schedule for crossing residuals (Category C / G5 draft).

  Goal (count-level): every crossing residual `CrossingArcs` reduces to the
  K₄ skeleton (`total = 0`) in exactly `total` frontier shortcut folds, each a
  legal `OpenArcPath` tip. This is the ∀-instance schedule skeleton the packs
  (OneFold…SixFold) instantiate concretely.

  Still count-level: does not itself discharge the resolution `Closure₃`
  inclusion (that stays in the concrete packs / E2 mass 461/461).
-/

import PNPLab.OpenArcPath

set_option linter.unusedSimpArgs false

namespace PNPLab.Bicyclic

/-- Fold the first positive arc (left-to-right frontier choice). -/
def CrossingArcs.foldSome (c : CrossingArcs) : CrossingArcs :=
  if 0 < c.a0 then c.foldAt ⟨0, by decide⟩
  else if 0 < c.a1 then c.foldAt ⟨1, by decide⟩
  else if 0 < c.a2 then c.foldAt ⟨2, by decide⟩
  else c.foldAt ⟨3, by decide⟩

theorem CrossingArcs.foldSome_total (c : CrossingArcs) (h : 0 < c.total) :
    (c.foldSome).total = c.total - 1 := by
  simp only [CrossingArcs.total] at h ⊢
  unfold CrossingArcs.foldSome CrossingArcs.foldAt
  by_cases h0 : 0 < c.a0
  · rw [if_pos h0]; simp only [CrossingArcs.total]; omega
  · rw [if_neg h0]
    by_cases h1 : 0 < c.a1
    · rw [if_pos h1]; simp only [CrossingArcs.total]; omega
    · rw [if_neg h1]
      by_cases h2 : 0 < c.a2
      · rw [if_pos h2]; simp only [CrossingArcs.total]; omega
      · rw [if_neg h2]; simp only [CrossingArcs.total]; omega

/-- Frontier tip kind chosen by `foldSome` is a shortcut (while nonempty). -/
theorem CrossingArcs.foldSome_tip (c : CrossingArcs) (h : 0 < c.total) :
    ∃ i : Fin 4, frontierTipKind (c.get i) = some .shortcutOnShorterArc :=
  crossing_frontier_tip_exists c h

/-- Number of frontier folds to reach the K₄ skeleton = total internals. -/
def CrossingArcs.stepsToK4 (c : CrossingArcs) : Nat :=
  c.total

theorem CrossingArcs.stepsToK4_eq (c : CrossingArcs) :
    c.stepsToK4 = c.total := rfl

/-- Iterate the frontier fold `steps` times. -/
def CrossingArcs.foldIter : Nat → CrossingArcs → CrossingArcs
  | 0, c => c
  | n + 1, c => CrossingArcs.foldIter n c.foldSome

theorem CrossingArcs.foldSome_total_of_zero (c : CrossingArcs) (h : c.total = 0) :
    (c.foldSome).total = 0 := by
  simp only [CrossingArcs.total] at h
  have h0 : c.a0 = 0 := by omega
  have h1 : c.a1 = 0 := by omega
  have h2 : c.a2 = 0 := by omega
  have h3 : c.a3 = 0 := by omega
  unfold CrossingArcs.foldSome CrossingArcs.foldAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [CrossingArcs.total] at *; omega

/-- After `steps` frontier folds, total internals drop by `steps` (capped at 0). -/
theorem CrossingArcs.foldIter_total (c : CrossingArcs) (steps : Nat) :
    (c.foldIter steps).total = c.total - steps := by
  induction steps generalizing c with
  | zero => simp [CrossingArcs.foldIter]
  | succ n ih =>
    unfold CrossingArcs.foldIter
    rw [ih c.foldSome]
    by_cases h : 0 < c.total
    · rw [c.foldSome_total h]; omega
    · have hz : c.total = 0 := Nat.eq_zero_of_not_pos h
      rw [c.foldSome_total_of_zero hz, hz]
      simp

/-- Parametric G5 (count-level): every crossing residual reaches the K₄
    skeleton (total = 0) in exactly `total` frontier shortcut folds. -/
theorem CrossingArcs.reaches_k4 (c : CrossingArcs) :
    (c.foldIter c.total).total = 0 := by
  rw [c.foldIter_total]; simp

/-- Base case sanity: K₄ skeleton needs zero folds. -/
theorem k4_stepsToK4_zero : k4CrossingArcs.stepsToK4 = 0 := rfl

/-- C₆ crossing: 4 folds to K₄. -/
theorem c6_stepsToK4 : c6CrossingArcs.stepsToK4 = 4 := rfl

/-- C₆ crossing reaches K₄ after its 4 folds. -/
theorem c6_reaches_k4 : (c6CrossingArcs.foldIter 4).total = 0 :=
  c6CrossingArcs.reaches_k4

/-- Each fold in the schedule is a legal open-arc frontier tip. -/
theorem crossing_fold_is_frontier_tip (c : CrossingArcs) (h : 0 < c.total) :
    ∃ i : Fin 4, (c.toOpen i).hasFrontierTip = true :=
  crossing_open_frontier_exists c h

def foldScheduleDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

end PNPLab.Bicyclic
