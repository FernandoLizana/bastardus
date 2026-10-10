/-
  Open-arc path model for crossing multihop frontier tips (Category C / G1).

  Finitary stand-in for a residual open branch during left-to-right fold:
    left (deg≥3) — v₀ — … — v_{k-1} — right (deg≥3),
  with ends not yet adjacent.

  Proves: k > 0 ⇒ legal frontier shortcut tip (matches fold_deg2_tip /
  multihop_frontier_invariant_mass: 461/461, 2310 hops).

  Not a Mathlib SimpleGraph embedding; parallels ThetaResidue for θ-graphs.
-/

import PNPLab.Bicyclic
import PNPLab.CrossingTipSchedule

namespace PNPLab.Bicyclic

/--
  Residual open arc during left-to-right multihop fold.
  `internals` = remaining deg-2 vertices on the path between branch ends.
-/
structure OpenArcPath where
  internals : Nat
  /-- Left frontier endpoint has degree ≥ 3 (branch point). -/
  leftDegGe3 : Bool
  /-- Right endpoint has degree ≥ 3. -/
  rightDegGe3 : Bool
  /-- Neighbors of the next tip are not yet adjacent (no triangle ear). -/
  endsAdjacent : Bool

/-- Crossing open arcs on an untouched Cₙ+2 chords residual. -/
def crossingOpenArc (k : Nat) : OpenArcPath where
  internals := k
  leftDegGe3 := true
  rightDegGe3 := true
  endsAdjacent := false

/-- Legal frontier tip: positive internals, left deg≥3, ends not adjacent. -/
def OpenArcPath.hasFrontierTip (p : OpenArcPath) : Bool :=
  (decide (0 < p.internals) && p.leftDegGe3) && !p.endsAdjacent

theorem crossingOpenArc_frontier (k : Nat) (hk : 0 < k) :
    (crossingOpenArc k).hasFrontierTip = true := by
  dsimp [crossingOpenArc, OpenArcPath.hasFrontierTip]
  rw [decide_eq_true hk]
  rfl

/-- Fold-mode tip kind on this arc matches `frontierTipKind`. -/
theorem OpenArcPath.tipKind_of_frontier (p : OpenArcPath)
    (hk : 0 < p.internals) :
    frontierTipKind p.internals = some .shortcutOnShorterArc :=
  frontierTipKind_pos hk

/-- Left-to-right fold: consume one internal; frontier flags preserved. -/
def OpenArcPath.foldLeft (p : OpenArcPath) : OpenArcPath where
  internals := p.internals - 1
  leftDegGe3 := p.leftDegGe3
  rightDegGe3 := p.rightDegGe3
  endsAdjacent := p.endsAdjacent

theorem OpenArcPath.foldLeft_preserves_flags (p : OpenArcPath) :
    (p.foldLeft).leftDegGe3 = p.leftDegGe3 ∧
      (p.foldLeft).endsAdjacent = p.endsAdjacent ∧
      (p.foldLeft).rightDegGe3 = p.rightDegGe3 := by
  simp [OpenArcPath.foldLeft]

/-- Crossing open arc: after one fold, either done or frontier tip remains. -/
theorem crossingOpenArc_fold_step (k : Nat) (hk : 0 < k) :
    (crossingOpenArc k).hasFrontierTip = true ∧
      ((crossingOpenArc k).foldLeft.internals = 0 ∨
        (crossingOpenArc k).foldLeft.hasFrontierTip = true) := by
  refine ⟨crossingOpenArc_frontier k hk, ?_⟩
  match k with
  | 0 => cases hk
  | 1 =>
    left
    rfl
  | n + 2 =>
    right
    dsimp [OpenArcPath.foldLeft, crossingOpenArc, OpenArcPath.hasFrontierTip]
    rw [decide_eq_true (Nat.succ_pos n)]
    rfl

/-- Four crossing arcs: each positive-length arc is a `crossingOpenArc`. -/
def CrossingArcs.toOpen (c : CrossingArcs) (i : Fin 4) : OpenArcPath :=
  crossingOpenArc (c.get i)

theorem CrossingArcs.open_frontier_of_pos (c : CrossingArcs) (i : Fin 4)
    (h : 0 < c.get i) :
    (c.toOpen i).hasFrontierTip = true :=
  crossingOpenArc_frontier (c.get i) h

theorem frontierTipKind_pos_implies (k : Nat)
    (h : frontierTipKind k = some .shortcutOnShorterArc) : 0 < k := by
  dsimp [frontierTipKind] at h
  by_cases hz : k = 0
  · simp [hz] at h
  · exact Nat.pos_iff_ne_zero.mpr hz

/-- If the crossing residual still has internals, some open arc has a frontier tip. -/
theorem crossing_open_frontier_exists (c : CrossingArcs) (h : 0 < c.total) :
    ∃ i : Fin 4, (c.toOpen i).hasFrontierTip = true := by
  obtain ⟨i, hi⟩ := crossing_frontier_tip_exists c h
  exact ⟨i, c.open_frontier_of_pos i (frontierTipKind_pos_implies _ hi)⟩

/-- Concrete: C₆ length-1 arc has a frontier tip. -/
theorem c6_open_arcs_frontier :
    (crossingOpenArc 1).hasFrontierTip = true :=
  crossingOpenArc_frontier 1 (by decide)

/-- Concrete: longer arc still frontier-shortcut after first fold. -/
theorem openArc_len2_fold_keeps_tip :
    ((crossingOpenArc 2).foldLeft).hasFrontierTip = true := by
  have h := crossingOpenArc_fold_step 2 (by decide)
  cases h.2 with
  | inl hz =>
    simp [OpenArcPath.foldLeft, crossingOpenArc] at hz
  | inr htip =>
    exact htip

def openArcPathDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/SHORT_ARC_TIP_LAW.md"

def frontierInvariantMassDoc : String :=
  "reports/discovery/multihop_frontier_invariant_mass.json"

end PNPLab.Bicyclic
