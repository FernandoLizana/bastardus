/-
  Parametric bwd wrap peel for all `a ≥ 1` (Category C / G6).

  Well-founded recursion on `a`:
    * bwd = 2       → `BwdShortcutTri`
    * a = 1, bwd≥3  → `BwdShortcutVia0`
    * a ≥ 2, bwd≥3  → tip once, recurse
  Yields `nAfter = n - bwdInternals` in every case.
-/

import PNPLab.OuterplanarBwdPeelPos

namespace PNPLab.Outerplanar

/-- Residual after one wrap tip is again a `BwdShortcut` when `a ≥ 2`, `bwd ≥ 3`. -/
def CycleChord.BwdShortcut.tip (s : CycleChord.BwdShortcut)
    (ha : 2 ≤ s.chord.a) (hb : 3 ≤ s.chord.bwdInternals) :
    CycleChord.BwdShortcut where
  chord := s.after
  aPos := by
    simp only [CycleChord.BwdShortcut.after]
    omega
  bwdShort := by
    have hf := s.after_fwd
    have hbw := s.after_bwd
    have hs := s.bwdShort
    omega
  bwdGe2 := by
    have hbw := s.after_bwd
    omega

theorem CycleChord.BwdShortcut.tip_a_lt (s : CycleChord.BwdShortcut)
    (ha : 2 ≤ s.chord.a) (hb : 3 ≤ s.chord.bwdInternals) :
    (s.tip ha hb).chord.a < s.chord.a := by
  simp only [tip, CycleChord.BwdShortcut.after]
  omega

theorem CycleChord.BwdShortcut.tip_n (s : CycleChord.BwdShortcut)
    (ha : 2 ≤ s.chord.a) (hb : 3 ≤ s.chord.bwdInternals) :
    (s.tip ha hb).chord.n = s.chord.n - 1 := by
  simp only [tip, CycleChord.BwdShortcut.after]

theorem CycleChord.BwdShortcut.tip_bwd (s : CycleChord.BwdShortcut)
    (ha : 2 ≤ s.chord.a) (hb : 3 ≤ s.chord.bwdInternals) :
    (s.tip ha hb).chord.bwdInternals = s.chord.bwdInternals - 1 := by
  simpa [tip] using s.after_bwd

theorem CycleChord.BwdShortcut.after_nPos_any (s : CycleChord.BwdShortcut)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aPos
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hge := s.bwdGe2
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s).n
  simp only [CycleChord.BwdShortcut.after]
  omega

/-- Lift to Via0 when `a = 1` and `bwd ≥ 3`. -/
def CycleChord.BwdShortcut.toVia0 (s : CycleChord.BwdShortcut)
    (ha : s.chord.a = 1) (hge : 3 ≤ s.chord.bwdInternals) :
    CycleChord.BwdShortcutVia0 where
  toBwdShortcut := s
  aEq1 := ha
  bwdGe3 := hge

/-- Parametric peel to the cycle base for any bwd wrap with `a ≥ 1`. -/
noncomputable def CycleChord.BwdShortcut.toCycleBaseAny (s : CycleChord.BwdShortcut)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  if h2 : s.chord.bwdInternals = 2 then
    (s.toTri h2).toCycleBase hPos
  else if ha1 : s.chord.a = 1 then
    (s.toVia0 ha1 (by
      have hge := s.bwdGe2
      omega)).toCycleBase hPos
  else
    have ha : 2 ≤ s.chord.a := by
      have : 0 < s.chord.a := s.aPos
      omega
    have hb : 3 ≤ s.chord.bwdInternals := by
      have hge := s.bwdGe2
      omega
    (s.tip ha hb).toCycleBaseAny (s.after_nPos_any hPos)
termination_by s.chord.a
decreasing_by
  exact s.tip_a_lt ha hb

theorem CycleChord.BwdShortcut.toCycleBaseAny_nAfter (s : CycleChord.BwdShortcut)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBaseAny hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  induction s, hPos using CycleChord.BwdShortcut.toCycleBaseAny.induct with
  | case1 s hPos h2 =>
    have hn := (s.toTri h2).toCycleBase_nAfter hPos
    have heq : s.toCycleBaseAny hPos = (s.toTri h2).toCycleBase hPos := by
      unfold toCycleBaseAny
      simp only [h2, ↓reduceDIte]
    rw [heq, hn]
    have heqN : (s.toTri h2).chord.n = s.chord.n := rfl
    omega
  | case2 s hPos h2 ha1 =>
    have hge : 3 ≤ s.chord.bwdInternals := by
      have hge := s.bwdGe2
      omega
    have hn := (s.toVia0 ha1 hge).toCycleBase_nAfter hPos
    have heq : s.toCycleBaseAny hPos = (s.toVia0 ha1 hge).toCycleBase hPos := by
      unfold toCycleBaseAny
      simp only [h2, ha1, ↓reduceDIte]
    rw [heq, hn]
    rfl
  | case3 s hPos h2 ha1 ha hb ih =>
    have heq : s.toCycleBaseAny hPos =
        (s.tip ha hb).toCycleBaseAny (s.after_nPos_any hPos) := by
      conv => lhs; unfold toCycleBaseAny
      rw [dif_neg h2, dif_neg ha1]
    rw [heq, ih, s.tip_n ha hb, s.tip_bwd ha hb]
    omega

theorem CycleChord.BwdShortcut.reaches_cycle_any (s : CycleChord.BwdShortcut)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBaseAny hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBaseAny hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBaseAny_nAfter hPos⟩

/-- Concrete: C₁₅ `{5,13}` a=5, bwd=6 → parametric peel → C₉ base. -/
def c15Chord513 : CycleChord where
  n := 15
  a := 5
  b := 13
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c15Chord513Bwd : CycleChord.BwdShortcut where
  chord := c15Chord513
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

theorem c15Chord513_reaches_cycle_any :
    let b := c15Chord513Bwd.toCycleBaseAny (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 9 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c15Chord513Bwd.reaches_cycle_any (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c15Chord513Bwd.chord.n = 15 := rfl
  have hb : c15Chord513Bwd.chord.bwdInternals = 6 := by native_decide
  rw [h.2.2.2, hn, hb]

/-- Concrete: C₁₇ `{5,14}` a=5, bwd=7 → parametric Via-chain → C₁₀ base. -/
def c17Chord514 : CycleChord where
  n := 17
  a := 5
  b := 14
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c17Chord514Bwd : CycleChord.BwdShortcut where
  chord := c17Chord514
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

theorem c17Chord514_reaches_cycle_any :
    let b := c17Chord514Bwd.toCycleBaseAny (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 10 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c17Chord514Bwd.reaches_cycle_any (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c17Chord514Bwd.chord.n = 17 := rfl
  have hb : c17Chord514Bwd.chord.bwdInternals = 7 := by native_decide
  rw [h.2.2.2, hn, hb]

/-- Sanity: parametric path matches A4Tri size on C₁₃ `{4,11}`. -/
theorem c13Chord411_any_nAfter :
    (c13Chord411Bwd.toCycleBaseAny (by decide)).nAfter = 8 := by
  have h := c13Chord411Bwd.toCycleBaseAny_nAfter (by decide)
  have hn : c13Chord411Bwd.chord.n = 13 := rfl
  have hb : c13Chord411Bwd.chord.bwdInternals = 5 := by native_decide
  omega

def bwdPeelAnyDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

end PNPLab.Outerplanar
