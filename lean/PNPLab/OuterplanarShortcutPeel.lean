/-
  General fwd-shortcut peel: any `FwdShortcut` has an explicit triangle residual
  after `fwdInternals - 1` tip deletions, then one facial triangle fold reaches
  the cycle base (Category C / G6).  Extends the explicit length-3 chain.
-/

import PNPLab.OuterplanarShortcutChain

namespace PNPLab.Outerplanar

/--
  Triangle residual after `fwdInternals - 1` forward shortcuts:
  chord `{a, a+2}` on `n - (fwdInternals - 1)` vertices.
-/
def CycleChord.FwdShortcut.peelToTriangle (s : CycleChord.FwdShortcut) : CycleChord where
  n := s.chord.n - (s.chord.fwdInternals - 1)
  a := s.chord.a
  b := s.chord.a + 2
  gap := Nat.le_refl _
  b_lt_n := by
    have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
    have hfwd : s.chord.fwdInternals = s.chord.b - s.chord.a - 1 := rfl
    have hge := s.fwdGe2
    omega
  bwd_pos := by
    have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
    have hfwd : s.chord.fwdInternals = s.chord.b - s.chord.a - 1 := rfl
    have hbwd : 0 < s.chord.n - (s.chord.b - s.chord.a) - 1 := s.chord.bwd_pos
    have hge := s.fwdGe2
    have hs := s.fwdShort
    -- residual bwd equals original bwd
    change 0 <
      (s.chord.n - (s.chord.fwdInternals - 1)) - ((s.chord.a + 2) - s.chord.a) - 1
    omega

theorem CycleChord.FwdShortcut.peelToTriangle_fwd (s : CycleChord.FwdShortcut) :
    (s.peelToTriangle).fwdInternals = 1 := by
  simp only [CycleChord.fwdInternals, CycleChord.FwdShortcut.peelToTriangle]
  omega

theorem CycleChord.FwdShortcut.peelToTriangle_shorter (s : CycleChord.FwdShortcut) :
    (s.peelToTriangle).shorterInternals = 1 := by
  have hf := s.peelToTriangle_fwd
  have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
  have hfwd : s.chord.fwdInternals = s.chord.b - s.chord.a - 1 := rfl
  have hbwd : 0 < s.chord.n - (s.chord.b - s.chord.a) - 1 := s.chord.bwd_pos
  have hge := s.fwdGe2
  have hs := s.fwdShort
  unfold CycleChord.shorterInternals
  rw [hf]
  simp only [CycleChord.bwdInternals, CycleChord.FwdShortcut.peelToTriangle]
  omega

theorem CycleChord.FwdShortcut.peelToTriangle_n (s : CycleChord.FwdShortcut) :
    (s.peelToTriangle).n = s.chord.n - (s.chord.fwdInternals - 1) :=
  rfl

theorem CycleChord.FwdShortcut.peel_nPos (s : CycleChord.FwdShortcut) (_hPos : 1 < s.chord.n) :
    1 < (s.peelToTriangle).n := by
  have hb : s.chord.b < s.chord.n := s.chord.b_lt_n
  have hfwd : s.chord.fwdInternals = s.chord.b - s.chord.a - 1 := rfl
  have hbwd : 0 < s.chord.n - (s.chord.b - s.chord.a) - 1 := s.chord.bwd_pos
  have hge := s.fwdGe2
  have hs := s.fwdShort
  simp only [CycleChord.FwdShortcut.peelToTriangle]
  omega

/-- Peel shortcuts then triangle-fold to the cycle base. -/
noncomputable def CycleChord.FwdShortcut.toCycleBase (s : CycleChord.FwdShortcut)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  (FacialTriangleFoldStep.ofTriangleChord
    s.peelToTriangle s.peelToTriangle_shorter (s.peel_nPos hPos)).toCycleBase

theorem CycleChord.FwdShortcut.toCycleBase_nAfter (s : CycleChord.FwdShortcut)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.fwdInternals := by
  have hge := s.fwdGe2
  have hn : (s.toCycleBase hPos).nAfter = (s.peelToTriangle).n - 1 := rfl
  rw [hn, s.peelToTriangle_n]
  omega

theorem CycleChord.FwdShortcut.reaches_cycle (s : CycleChord.FwdShortcut)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.fwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₁₀ + chord `{0,5}`: fwd=4 → peel → triangle → C₆ base. -/
def c10Chord05 : CycleChord where
  n := 10
  a := 0
  b := 5
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c10Chord05Fwd : CycleChord.FwdShortcut where
  chord := c10Chord05
  fwdShort := by native_decide
  fwdGe2 := by native_decide

theorem c10Chord05_peel :
    c10Chord05Fwd.peelToTriangle.a = 0 ∧
      c10Chord05Fwd.peelToTriangle.b = 2 ∧
      c10Chord05Fwd.peelToTriangle.n = 7 ∧
      c10Chord05Fwd.peelToTriangle.shorterInternals = 1 := by
  native_decide

theorem c10Chord05_reaches_cycle :
    let b := c10Chord05Fwd.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 6 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c10Chord05Fwd.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c10Chord05Fwd.chord.n = 10 := rfl
  have hf : c10Chord05Fwd.chord.fwdInternals = 4 := by native_decide
  simpa [hn, hf] using h.2.2.2

/-- Chain-3 agrees with general peel on C₈ `{0,4}`. -/
theorem c8Chord04_peel_agrees_chain :
    c8Chord04Fwd.peelToTriangle.n = c8Chord04Chain.mid2Chord.n ∧
      c8Chord04Fwd.peelToTriangle.b = c8Chord04Chain.mid2Chord.b := by
  native_decide

def shortcutPeelDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
