/-
  Finitary discharge of θ-graph tip existence (Category C).

  Cycle length `n≥4` with one chord of span `a` (`2 ≤ a ≤ n-2`) is a θ-graph.
  Shorter arc span `s = min(a, n-a)` satisfies `s ≥ 2`, so internals `s-1 ≥ 1`:
  - internals = 1 ⇒ triangle ear;
  - internals ≥ 2 ⇒ shortcut tip.

  Proves tip existence for all θ-residues (combinatorial content of
  `chordFoldLaw`). Not a general outerplanar ear-decomposition theorem.
-/

import PNPLab.Bicyclic

namespace PNPLab.Bicyclic

/-- Cycle length `n` with one chord of combinatorial span `a`. -/
structure ThetaResidue where
  n : Nat
  a : Nat
  hn : 4 ≤ n
  ha1 : 2 ≤ a
  ha2 : a ≤ n - 2

/-- Edge-count of the shorter open path between chord ends. -/
def ThetaResidue.shortArc (t : ThetaResidue) : Nat :=
  min t.a (t.n - t.a)

theorem ThetaResidue.n_sub_a_ge_two (t : ThetaResidue) : 2 ≤ t.n - t.a := by
  have h2n : 2 ≤ t.n := Nat.le_trans (by decide : 2 ≤ 4) t.hn
  have hadd : t.a + 2 ≤ t.n := by
    have h := Nat.add_le_add_right t.ha2 2
    have hn2 : t.n - 2 + 2 = t.n := Nat.sub_add_cancel h2n
    simpa [hn2] using h
  have hab : 2 + t.a ≤ t.n := by
    rw [Nat.add_comm]
    exact hadd
  have ha_le_n : t.a ≤ t.n := Nat.le_trans t.ha2 (Nat.sub_le _ _)
  exact (Nat.le_sub_iff_add_le ha_le_n).mpr hab

theorem ThetaResidue.shortArc_ge_two (t : ThetaResidue) : 2 ≤ t.shortArc := by
  dsimp [ThetaResidue.shortArc]
  exact Nat.le_min.mpr ⟨t.ha1, t.n_sub_a_ge_two⟩

/-- Internals on the shorter open arc. -/
def ThetaResidue.shortInternals (t : ThetaResidue) : Nat :=
  t.shortArc - 1

theorem ThetaResidue.shortInternals_ge_one (t : ThetaResidue) :
    1 ≤ t.shortInternals := by
  dsimp [ThetaResidue.shortInternals]
  exact Nat.le_sub_of_add_le t.shortArc_ge_two

def ThetaResidue.hasTriangleEar (t : ThetaResidue) : Bool :=
  decide (t.shortInternals = 1)

def ThetaResidue.hasShortcutTip (t : ThetaResidue) : Bool :=
  decide (1 < t.shortInternals)

theorem ThetaResidue.chordFoldLaw (t : ThetaResidue) :
    t.hasTriangleEar = true ∨ t.hasShortcutTip = true := by
  dsimp [ThetaResidue.hasTriangleEar, ThetaResidue.hasShortcutTip]
  by_cases h : t.shortInternals = 1
  · left
    exact decide_eq_true h
  · right
    have hge : 1 ≤ t.shortInternals := t.shortInternals_ge_one
    have : 1 < t.shortInternals := Nat.lt_of_le_of_ne hge (Ne.symm h)
    exact decide_eq_true this

def ThetaResidue.tipKind (t : ThetaResidue) : ChordTipKind :=
  if t.hasTriangleEar then .triangleEar else .shortcutOnShorterArc

def c5chord : ThetaResidue where
  n := 5
  a := 2
  hn := by decide
  ha1 := by decide
  ha2 := by decide

theorem c5chord_triangle :
    c5chord.hasTriangleEar = true ∧ c5chord.shortInternals = 1 := by
  native_decide

def c6chordLong : ThetaResidue where
  n := 6
  a := 3
  hn := by decide
  ha1 := by decide
  ha2 := by decide

theorem c6chordLong_shortcut :
    c6chordLong.hasShortcutTip = true ∧ 1 < c6chordLong.shortInternals := by
  native_decide

def ThetaResidue.toSketch (t : ThetaResidue) : ThetaSketch where
  nVertices := t.n
  isCycle := false
  hasFoldTip := true
  chordFoldLaw := by simp

theorem toSketch_needsFold (t : ThetaResidue) :
    (t.toSketch.classify).status = .needsChordFold :=
  classify_needsFold t.toSketch rfl

def thetaResidueDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

def earMassDoc : String :=
  "reports/discovery/outerplanar_ear_existence_mass.json"

end PNPLab.Bicyclic
