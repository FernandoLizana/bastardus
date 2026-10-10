/-
  G6 constructive ear from a single chord on a cycle (Category C).

  Any `C_n` (`n ≥ 4`) plus one non-boundary chord has a shorter open arc
  between the chord endpoints; that arc is a legal `OuterplanarEarPath`
  (attachments deg≥3, base = the chord). Discharges the Whitney ear hook
  for the **unicyclic / one-chord** peel case without Mathlib outerplanar API.
-/

import PNPLab.WhitneyEarAxiom

namespace PNPLab.Outerplanar

open WhitneyEar

/--
  Chord `{a,b}` on `C_n` that is not a cycle edge: both open arcs between
  the endpoints have positive length.
-/
structure CycleChord where
  n : Nat
  a : Nat
  b : Nat
  gap : a + 2 ≤ b
  b_lt_n : b < n
  /-- Wrap arc also nonempty (excludes cycle edge `{0,n-1}` and similar). -/
  bwd_pos : 0 < n - (b - a) - 1

/-- Forward arc internals `a → b` (exclusive). -/
def CycleChord.fwdInternals (c : CycleChord) : Nat :=
  c.b - c.a - 1

/-- Backward arc internals `b → a` wrapping around. -/
def CycleChord.bwdInternals (c : CycleChord) : Nat :=
  c.n - (c.b - c.a) - 1

/-- Shorter open arc length (Whitney ear internals). -/
def CycleChord.shorterInternals (c : CycleChord) : Nat :=
  min c.fwdInternals c.bwdInternals

theorem CycleChord.fwd_pos (c : CycleChord) : 0 < c.fwdInternals := by
  have h := c.gap
  simp [CycleChord.fwdInternals]
  omega

theorem CycleChord.shorter_pos (c : CycleChord) : 0 < c.shorterInternals := by
  have hf := c.fwd_pos
  have hb : 0 < c.bwdInternals := by
    simpa [CycleChord.bwdInternals] using c.bwd_pos
  simp [CycleChord.shorterInternals]
  omega

/-- Legal ear path: chord as base edge, attachments treated as deg≥3 on the 2-core. -/
def CycleChord.toEarPath (c : CycleChord) : OuterplanarEarPath where
  internals := c.shorterInternals
  leftDegGe3 := true
  rightDegGe3 := true
  endsAdjacent := true

theorem CycleChord.toEarPath_isLegal (c : CycleChord) :
    (c.toEarPath).isLegal :=
  ⟨c.shorter_pos, Or.inl rfl⟩

/-- Non-cycle 2-core sketch from a cycle+chord. -/
def CycleChord.toSketch (c : CycleChord) : PeeledOuterplanarSketch where
  nCore := c.n
  isCycle := false
  pendingLeaves := 0
  earInternals := c.shorterInternals
  earLeftDegGe3 := true
  earRightDegGe3 := true
  earEndsAdjacent := true
  notCycle_hasLegalEar := fun _ => ⟨c.shorter_pos, Or.inl rfl⟩

/-- Whitney ear exists constructively from the chord. -/
theorem CycleChord.whitney_ear (c : CycleChord) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  ⟨c.toEarPath, c.toEarPath_isLegal⟩

/-- C₄ + diagonal: triangle ear. -/
def c4Diagonal : CycleChord where
  n := 4
  a := 0
  b := 2
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

theorem c4Diagonal_triangle :
    (c4Diagonal.toEarPath).hasTriangleEar = true := by
  native_decide

/-- C₆ + short chord: shorter arc length 1 (triangle ear). -/
def c6Chord02 : CycleChord where
  n := 6
  a := 0
  b := 2
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

theorem c6Chord02_shorter_one :
    c6Chord02.shorterInternals = 1 := by
  native_decide

theorem cycle_chord_ear_bundle (c : CycleChord) :
    0 < c.shorterInternals ∧
      (c.toEarPath).isLegal ∧
      (c.toSketch).isCycle = false :=
  ⟨c.shorter_pos, c.toEarPath_isLegal, rfl⟩

def cycleChordEarDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
