/-
  Total one-chord peel: every `CycleChord` reaches the cycle base (Category C / G6).

  Routes by shorter-arc case analysis (independent of the specialized schedule tags):

    * shorter = 1          → facial triangle fold
    * fwd shorter (≥2)     → `FwdShortcut.toCycleBase`
    * bwd shorter, a = 0   → `BwdShortcut0.toCycleBase`
    * bwd shorter, a ≥ 1   → `BwdShortcut.toCycleBaseAny`
-/

import PNPLab.OuterplanarOneChordDispatch

namespace PNPLab.Outerplanar

/-- If the shorter arc is not a triangle, it has length ≥ 2. -/
theorem CycleChord.shorter_ge2_of_ne_one (c : CycleChord)
    (hne : c.shorterInternals ≠ 1) : 2 ≤ c.shorterInternals := by
  have hp := c.shorter_pos
  omega

/-- Non-triangle + not fwd-peel ⇒ wrap arc is strictly shorter and ≥ 2. -/
theorem CycleChord.bwd_short_of_not_fwd (c : CycleChord)
    (hne : c.shorterInternals ≠ 1)
    (hnfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals)) :
    c.bwdInternals < c.fwdInternals ∧ 2 ≤ c.bwdInternals := by
  have hge := c.shorter_ge2_of_ne_one hne
  by_cases hle : c.fwdInternals ≤ c.bwdInternals
  · have : 2 ≤ c.fwdInternals := by
      simp only [CycleChord.shorterInternals, hle, min_eq_left] at hge
      exact hge
    exact False.elim (hnfwd ⟨hle, this⟩)
  · have hlt : c.bwdInternals < c.fwdInternals := Nat.lt_of_not_ge hle
    have hsEq : c.shorterInternals = c.bwdInternals := by
      simp only [CycleChord.shorterInternals]
      exact (min_eq_right (Nat.le_of_lt hlt))
    refine ⟨hlt, ?_⟩
    simpa [hsEq] using hge

/-- `schedule` never returns `none` on a well-formed one-chord core. -/
theorem CycleChord.schedule_isSome (c : CycleChord) :
    (c.schedule).isSome = true := by
  by_cases htri : c.shorterInternals = 1
  · simp [CycleChord.schedule, htri]
  · by_cases hfwd : c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals
    · simp [CycleChord.schedule, htri, hfwd]
    · have ⟨hs, hge⟩ := c.bwd_short_of_not_fwd htri hfwd
      by_cases ha0 : c.a = 0
      · simp [CycleChord.schedule, htri, hfwd, ha0, hs, hge]
      · have ha : 0 < c.a := Nat.pos_of_ne_zero ha0
        simp [CycleChord.schedule, htri, hfwd, ha0, ha, hs, hge]
        split_ifs <;> simp

/-- Total facial peel of a one-chord core to the cycle base. -/
noncomputable def CycleChord.toCycleBase (c : CycleChord) (hPos : 1 < c.n) :
    FacialCycleBase :=
  if htri : c.shorterInternals = 1 then
    (FacialTriangleFoldStep.ofTriangleChord c htri hPos).toCycleBase
  else if hfwd : c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals then
    ({ chord := c, fwdShort := hfwd.1, fwdGe2 := hfwd.2 } : CycleChord.FwdShortcut).toCycleBase
      hPos
  else if ha0 : c.a = 0 then
    have ⟨hs, hge⟩ := c.bwd_short_of_not_fwd htri hfwd
    ({ chord := c, a0 := ha0, bwdShort := hs, bwdGe2 := hge } : CycleChord.BwdShortcut0).toCycleBase
      hPos
  else
    have ⟨hs, hge⟩ := c.bwd_short_of_not_fwd htri hfwd
    have ha : 0 < c.a := Nat.pos_of_ne_zero ha0
    ({ chord := c, aPos := ha, bwdShort := hs, bwdGe2 := hge } : CycleChord.BwdShortcut).toCycleBaseAny
      hPos

theorem CycleChord.reaches_cycle (c : CycleChord) (hPos : 1 < c.n) :
    let b := c.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let b := c.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter⟩

/-- Concrete: C₄ diagonal via total peel. -/
theorem c4Diagonal_total_reaches_cycle :
    let b := c4Diagonal.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c4Diagonal.reaches_cycle (by decide)
  ⟨h.1, h.2.1⟩

/-- Concrete: C₁₀ `{0,5}` via total peel (fwd). -/
theorem c10Chord05_total_reaches_cycle :
    let b := c10Chord05.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c10Chord05.reaches_cycle (by decide)
  ⟨h.1, h.2.1⟩

/-- Concrete: C₉ `{0,5}` via total peel (bwd₀). -/
theorem c9Chord05_total_reaches_cycle :
    let b := c9Chord05Bwd.chord.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c9Chord05Bwd.chord.reaches_cycle (by decide)
  ⟨h.1, h.2.1⟩

/-- Concrete: C₁₅ `{5,13}` via total peel (bwd ∀a). -/
theorem c15Chord513_total_reaches_cycle :
    let b := c15Chord513.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c15Chord513.reaches_cycle (by decide)
  ⟨h.1, h.2.1⟩

/-- Concrete: C₈ `{1,6}` via total peel (bwd Tri). -/
theorem c8Chord16_total_reaches_cycle :
    let b := c8Chord16.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c8Chord16.reaches_cycle (by decide)
  ⟨h.1, h.2.1⟩

def oneChordTotalDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

end PNPLab.Outerplanar
