/-
  Crossing short-arc tip schedule (Category C / SHORT_ARC_TIP_LAW).

  Combinatorial sketch: C_n + two crossing chords ⇒ four open branch arcs.
  Tip classifier on an arc with `internals` remaining (θ-style):
    - 0 → none
    - 1 → triangleEar
    - ≥2 → shortcutOnShorterArc

  Multihop mass (`multihop_tip_kinds_mass.json`): the left-to-right projection
  schedule is **all** `shortcut_fold` (2310/2310 tips on 461 instances).
  Consecutive branch ends are not adjacent until the arc is folded, so each
  tip extends a frontier shortcut — unlike θ where a pre-existing chord can
  make internals=1 a triangle ear.

  Proves: if any internals remain, some arc admits a tip kind.
  Graph realization of that tip on the concrete embedding remains E2.
-/

import PNPLab.Bicyclic

namespace PNPLab.Bicyclic

/-- Four open-arc internal counts for a crossing residual. -/
structure CrossingArcs where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat

def CrossingArcs.total (c : CrossingArcs) : Nat :=
  c.a0 + c.a1 + c.a2 + c.a3

def CrossingArcs.get (c : CrossingArcs) (i : Fin 4) : Nat :=
  match i.val with
  | 0 => c.a0
  | 1 => c.a1
  | 2 => c.a2
  | _ => c.a3

/-- Tip kind on one open arc given remaining internals (θ-style classifier). -/
def arcTipKind (internals : Nat) : Option ChordTipKind :=
  match internals with
  | 0 => none
  | 1 => some .triangleEar
  | _ => some .shortcutOnShorterArc

theorem arcTipKind_zero : arcTipKind 0 = none := rfl
theorem arcTipKind_one : arcTipKind 1 = some .triangleEar := rfl
theorem arcTipKind_two : arcTipKind 2 = some .shortcutOnShorterArc := rfl

theorem arcTipKind_isSome_of_pos {k : Nat} (hk : 0 < k) :
    (arcTipKind k).isSome = true := by
  match k with
  | 0 => cases hk
  | 1 => rfl
  | _ + 2 => rfl

/-- Some arc still has internals ⇒ that arc has a concrete tip kind. -/
theorem crossing_schedule_tip_exists (c : CrossingArcs) (h : 0 < c.total) :
    ∃ i : Fin 4, (arcTipKind (c.get i)).isSome = true := by
  have hsum : 0 < c.a0 + c.a1 + c.a2 + c.a3 := h
  match Nat.eq_zero_or_pos c.a0 with
  | Or.inr h0 =>
    refine ⟨⟨0, by decide⟩, arcTipKind_isSome_of_pos ?_⟩
    simpa [CrossingArcs.get] using h0
  | Or.inl h0z =>
    match Nat.eq_zero_or_pos c.a1 with
    | Or.inr h1 =>
      refine ⟨⟨1, by decide⟩, arcTipKind_isSome_of_pos ?_⟩
      simpa [CrossingArcs.get] using h1
    | Or.inl h1z =>
      match Nat.eq_zero_or_pos c.a2 with
      | Or.inr h2 =>
        refine ⟨⟨2, by decide⟩, arcTipKind_isSome_of_pos ?_⟩
        simpa [CrossingArcs.get] using h2
      | Or.inl h2z =>
        have ha3 : 0 < c.a3 := by
          simpa [h0z, h1z, h2z, Nat.add_zero] using hsum
        refine ⟨⟨3, by decide⟩, arcTipKind_isSome_of_pos ?_⟩
        simpa [CrossingArcs.get] using ha3

/-- Fold one tip on arc `i` (decrease that arc's internals by 1). -/
def CrossingArcs.foldAt (c : CrossingArcs) (i : Fin 4) : CrossingArcs :=
  match i.val with
  | 0 => { c with a0 := c.a0 - 1 }
  | 1 => { c with a1 := c.a1 - 1 }
  | 2 => { c with a2 := c.a2 - 1 }
  | _ => { c with a3 := c.a3 - 1 }

/--
  Fold-mode tip kind for the left-to-right multihop schedule.
  Matches Python `fold_deg2_tip`: every positive-length open branch tip is a
  shortcut (branch ends are not adjacent until the arc is contracted).
-/
def frontierTipKind (internals : Nat) : Option ChordTipKind :=
  if internals = 0 then none else some .shortcutOnShorterArc

theorem frontierTipKind_zero : frontierTipKind 0 = none := rfl

theorem frontierTipKind_pos {k : Nat} (hk : 0 < k) :
    frontierTipKind k = some .shortcutOnShorterArc := by
  simp [frontierTipKind]
  intro h
  exact absurd h (Nat.pos_iff_ne_zero.mp hk)

theorem frontierTipKind_isSome_of_pos {k : Nat} (hk : 0 < k) :
    (frontierTipKind k).isSome = true := by
  simp [frontierTipKind_pos hk]

/-- Schedule (fold-mode): remaining internals ⇒ some arc has a frontier shortcut tip. -/
theorem crossing_frontier_tip_exists (c : CrossingArcs) (h : 0 < c.total) :
    ∃ i : Fin 4, frontierTipKind (c.get i) = some .shortcutOnShorterArc := by
  have hsum : 0 < c.a0 + c.a1 + c.a2 + c.a3 := h
  match Nat.eq_zero_or_pos c.a0 with
  | Or.inr h0 =>
    refine ⟨⟨0, by decide⟩, ?_⟩
    have : 0 < c.get ⟨0, by decide⟩ := by simpa [CrossingArcs.get] using h0
    exact frontierTipKind_pos this
  | Or.inl h0z =>
    match Nat.eq_zero_or_pos c.a1 with
    | Or.inr h1 =>
      refine ⟨⟨1, by decide⟩, ?_⟩
      have : 0 < c.get ⟨1, by decide⟩ := by simpa [CrossingArcs.get] using h1
      exact frontierTipKind_pos this
    | Or.inl h1z =>
      match Nat.eq_zero_or_pos c.a2 with
      | Or.inr h2 =>
        refine ⟨⟨2, by decide⟩, ?_⟩
        have : 0 < c.get ⟨2, by decide⟩ := by simpa [CrossingArcs.get] using h2
        exact frontierTipKind_pos this
      | Or.inl h2z =>
        have ha3 : 0 < c.a3 := by
          simpa [h0z, h1z, h2z, Nat.add_zero] using hsum
        refine ⟨⟨3, by decide⟩, ?_⟩
        have : 0 < c.get ⟨3, by decide⟩ := by simpa [CrossingArcs.get] using ha3
        exact frontierTipKind_pos this

/-- θ-classifier vs fold-mode: length-1 arcs disagree on tip kind. -/
theorem length1_classifier_vs_frontier :
    arcTipKind 1 = some .triangleEar ∧
      frontierTipKind 1 = some .shortcutOnShorterArc :=
  ⟨arcTipKind_one, frontierTipKind_pos (Nat.zero_lt_one)⟩

/-- Concrete K₄ skeleton: four empty arcs. -/
def k4CrossingArcs : CrossingArcs := { a0 := 0, a1 := 0, a2 := 0, a3 := 0 }

theorem k4CrossingArcs_done : k4CrossingArcs.total = 0 := rfl

/-- C₆ crossing: four length-1 arcs. -/
def c6CrossingArcs : CrossingArcs := { a0 := 1, a1 := 1, a2 := 1, a3 := 1 }

theorem c6Crossing_tip :
    ∃ i : Fin 4, (arcTipKind (c6CrossingArcs.get i)).isSome = true :=
  crossing_schedule_tip_exists c6CrossingArcs (by decide)

theorem c6Crossing_arc0_triangle :
    arcTipKind c6CrossingArcs.a0 = some .triangleEar :=
  arcTipKind_one

/-- Longer arc sample: internals 2 ⇒ shortcut classifier. -/
def arcShortcutSample : CrossingArcs := { a0 := 2, a1 := 0, a2 := 0, a3 := 0 }

theorem arcShortcutSample_kind :
    arcTipKind arcShortcutSample.a0 = some .shortcutOnShorterArc :=
  arcTipKind_two

/-- Document: θ-classifier vs multihop fold mode diverge on length-1 arcs. -/
def scheduleVsFoldModeDoc : String :=
  "Crossing length-1 arcs: arcTipKind = triangleEar (θ-style), but multihop \
   left-to-right fold_deg2_tip observes shortcut_fold because branch ends are \
   not yet adjacent. See multihop_tip_kinds_mass.json."

def crossingTipScheduleDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/SHORT_ARC_TIP_LAW.md"

def tipKindsMassDoc : String :=
  "reports/discovery/multihop_tip_kinds_mass.json"

end PNPLab.Bicyclic
