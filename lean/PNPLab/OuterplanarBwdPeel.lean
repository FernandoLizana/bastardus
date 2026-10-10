/-
  Bwd wrap-shortcut peel (a = 0): any `BwdShortcut0` has an explicit triangle
  residual after `bwdInternals - 1` wrap tip deletions, then one facial
  triangle fold reaches the cycle base (Category C / G6).
-/

import PNPLab.OuterplanarShortcutPeel

namespace PNPLab.Outerplanar

/--
  Triangle residual after `bwdInternals - 1` wrap shortcuts:
  same chord endpoints `{0, b}` on `n - (bwdInternals - 1)` vertices,
  with wrap arc length 1.
-/
def CycleChord.BwdShortcut0.peelToTriangle (s : CycleChord.BwdShortcut0) : CycleChord where
  n := s.chord.n - (s.chord.bwdInternals - 1)
  a := 0
  b := s.chord.b
  gap := by
    have ha := s.a0
    have hg := s.chord.gap
    omega
  b_lt_n := by
    have ha := s.a0
    have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
    have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
    have hge := s.bwdGe2
    omega
  bwd_pos := by
    have ha := s.a0
    have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
    have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
    have hge := s.bwdGe2
    -- residual bwd = 1
    change 0 < (s.chord.n - (s.chord.bwdInternals - 1)) - (s.chord.b - 0) - 1
    omega

theorem CycleChord.BwdShortcut0.peelToTriangle_bwd (s : CycleChord.BwdShortcut0) :
    (s.peelToTriangle).bwdInternals = 1 := by
  have ha := s.a0
  have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  have hge := s.bwdGe2
  simp only [CycleChord.bwdInternals, CycleChord.BwdShortcut0.peelToTriangle, ha]
  omega

theorem CycleChord.BwdShortcut0.peelToTriangle_fwd (s : CycleChord.BwdShortcut0) :
    (s.peelToTriangle).fwdInternals = s.chord.fwdInternals := by
  have ha := s.a0
  simp only [CycleChord.fwdInternals, CycleChord.BwdShortcut0.peelToTriangle, ha]

theorem CycleChord.BwdShortcut0.peelToTriangle_shorter (s : CycleChord.BwdShortcut0) :
    (s.peelToTriangle).shorterInternals = 1 := by
  have hb := s.peelToTriangle_bwd
  have hf := s.peelToTriangle_fwd
  have hs := s.bwdShort
  have hge := s.bwdGe2
  unfold CycleChord.shorterInternals
  rw [hb]
  omega

theorem CycleChord.BwdShortcut0.peelToTriangle_n (s : CycleChord.BwdShortcut0) :
    (s.peelToTriangle).n = s.chord.n - (s.chord.bwdInternals - 1) :=
  rfl

theorem CycleChord.BwdShortcut0.peel_nPos (s : CycleChord.BwdShortcut0) (_hPos : 1 < s.chord.n) :
    1 < (s.peelToTriangle).n := by
  have ha := s.a0
  have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  have hge := s.bwdGe2
  have hs := s.bwdShort
  simp only [CycleChord.BwdShortcut0.peelToTriangle]
  omega

noncomputable def CycleChord.BwdShortcut0.toCycleBase (s : CycleChord.BwdShortcut0)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  (FacialTriangleFoldStep.ofTriangleChord
    s.peelToTriangle s.peelToTriangle_shorter (s.peel_nPos hPos)).toCycleBase

theorem CycleChord.BwdShortcut0.toCycleBase_nAfter (s : CycleChord.BwdShortcut0)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  have hge := s.bwdGe2
  have hn : (s.toCycleBase hPos).nAfter = (s.peelToTriangle).n - 1 := rfl
  rw [hn, s.peelToTriangle_n]
  omega

theorem CycleChord.BwdShortcut0.reaches_cycle (s : CycleChord.BwdShortcut0)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₉ + chord `{0,5}`: bwd=3 → peel → triangle → C₆ base. -/
def c9Chord05 : CycleChord where
  n := 9
  a := 0
  b := 5
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c9Chord05Bwd : CycleChord.BwdShortcut0 where
  chord := c9Chord05
  a0 := rfl
  bwdShort := by native_decide
  bwdGe2 := by native_decide

theorem c9Chord05_peel :
    c9Chord05Bwd.peelToTriangle.a = 0 ∧
      c9Chord05Bwd.peelToTriangle.b = 5 ∧
      c9Chord05Bwd.peelToTriangle.n = 7 ∧
      c9Chord05Bwd.peelToTriangle.shorterInternals = 1 := by
  native_decide

theorem c9Chord05_reaches_cycle :
    let b := c9Chord05Bwd.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 6 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c9Chord05Bwd.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c9Chord05Bwd.chord.n = 9 := rfl
  have hb : c9Chord05Bwd.chord.bwdInternals = 3 := by native_decide
  simpa [hn, hb] using h.2.2.2

/-- C₈ `{0,5}` bwd peel agrees with one-step shortcut (bwd=2). -/
theorem c8Chord05_peel_agrees_after :
    c8Chord05Bwd.peelToTriangle.n = c8Chord05Bwd.after.n ∧
      c8Chord05Bwd.peelToTriangle.b = c8Chord05Bwd.after.b := by
  native_decide

def bwdPeelDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
