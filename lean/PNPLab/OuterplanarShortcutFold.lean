/-
  Facial shortcut fold on a cycle+chord (Category C / G6 / E3).

  When the shorter open arc has ≥ 2 internals, the Whitney tip is a deg-2
  shortcut (not a triangle).  Deleting the tip adjacent to the left endpoint
  on the forward arc yields another `CycleChord` on `n-1` vertices whose
  forward internals drop by exactly one — still a facial one-chord embed
  cert, not a pure cycle.
-/

import PNPLab.OuterplanarFoldStep
import PNPLab.OddChargeFold

namespace PNPLab.Outerplanar

/-- Forward arc is the Whitney shorter ear and has room for a shortcut tip. -/
structure CycleChord.FwdShortcut where
  chord : CycleChord
  fwdShort : chord.fwdInternals ≤ chord.bwdInternals
  fwdGe2 : 2 ≤ chord.fwdInternals

/-- Residual chord after deleting tip `a+1` on the forward arc. -/
def CycleChord.FwdShortcut.after (s : CycleChord.FwdShortcut) : CycleChord where
  n := s.chord.n - 1
  a := s.chord.a
  b := s.chord.b - 1
  gap := by
    have hg := s.chord.gap
    have hge : 2 ≤ s.chord.b - s.chord.a - 1 := s.fwdGe2
    omega
  b_lt_n := by
    have hb := s.chord.b_lt_n
    have hg := s.chord.gap
    omega
  bwd_pos := by
    have hb := s.chord.bwd_pos
    have hbnd := s.chord.b_lt_n
    have hg := s.chord.gap
    -- residual bwd = original bwd
    have : (s.chord.n - 1) - ((s.chord.b - 1) - s.chord.a) - 1 =
        s.chord.n - (s.chord.b - s.chord.a) - 1 := by omega
    simpa [this] using hb

theorem CycleChord.FwdShortcut.after_n (s : CycleChord.FwdShortcut) :
    s.after.n = s.chord.n - 1 :=
  rfl

theorem CycleChord.FwdShortcut.after_fwd (s : CycleChord.FwdShortcut) :
    s.after.fwdInternals = s.chord.fwdInternals - 1 := by
  have hg := s.chord.gap
  have hge : 2 ≤ s.chord.b - s.chord.a - 1 := s.fwdGe2
  simp only [CycleChord.fwdInternals, CycleChord.FwdShortcut.after]
  omega

theorem CycleChord.FwdShortcut.after_bwd (s : CycleChord.FwdShortcut) :
    s.after.bwdInternals = s.chord.bwdInternals := by
  have hbnd := s.chord.b_lt_n
  have hg := s.chord.gap
  simp only [CycleChord.bwdInternals, CycleChord.FwdShortcut.after]
  omega

theorem CycleChord.FwdShortcut.shorter_drops (s : CycleChord.FwdShortcut) :
    s.after.shorterInternals < s.chord.shorterInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hshort := s.fwdShort
  have hge := s.fwdGe2
  simp only [CycleChord.shorterInternals, hf, hb]
  omega

theorem CycleChord.FwdShortcut.after_fwdShort (s : CycleChord.FwdShortcut) :
    s.after.fwdInternals ≤ s.after.bwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.fwdShort
  have hge := s.fwdGe2
  simp only [hf, hb]
  omega

/-- After a fwd shortcut with ≥3 forward internals, the residual is again a fwd shortcut. -/
def CycleChord.FwdShortcut.continue (s : CycleChord.FwdShortcut)
    (hGe3 : 3 ≤ s.chord.fwdInternals) : CycleChord.FwdShortcut where
  chord := s.after
  fwdShort := s.after_fwdShort
  fwdGe2 := by
    have hf := s.after_fwd
    -- goal: 2 ≤ after.fwdInternals; hf: after.fwd = chord.fwd - 1; hGe3: 3 ≤ chord.fwd
    omega

theorem CycleChord.FwdShortcut.continue_shorter (s : CycleChord.FwdShortcut)
    (hGe3 : 3 ≤ s.chord.fwdInternals) :
    (s.continue hGe3).chord.shorterInternals = s.chord.shorterInternals - 1 := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.fwdShort
  have hge := s.fwdGe2
  simp only [CycleChord.FwdShortcut.continue, CycleChord.shorterInternals]
  omega

/-- Backward arc is strictly shorter and has room for a wrap-around tip (a = 0). -/
structure CycleChord.BwdShortcut0 where
  chord : CycleChord
  a0 : chord.a = 0
  bwdShort : chord.bwdInternals < chord.fwdInternals
  bwdGe2 : 2 ≤ chord.bwdInternals

/-- Residual after deleting tip `n-1` on the wrap arc (chord starts at 0). -/
def CycleChord.BwdShortcut0.after (s : CycleChord.BwdShortcut0) : CycleChord where
  n := s.chord.n - 1
  a := 0
  b := s.chord.b
  gap := by
    have hg := s.chord.gap
    have ha := s.a0
    omega
  b_lt_n := by
    -- b ≤ n-3 from bwd ≥ 2 and a = 0
    have hb := s.chord.b_lt_n
    have hbwd : 2 ≤ s.chord.n - (s.chord.b - s.chord.a) - 1 := s.bwdGe2
    have ha := s.a0
    omega
  bwd_pos := by
    have hbwd : 2 ≤ s.chord.n - (s.chord.b - s.chord.a) - 1 := s.bwdGe2
    have ha := s.a0
    have hb := s.chord.b_lt_n
    -- residual bwd = original bwd - 1
    change 0 < (s.chord.n - 1) - (s.chord.b - 0) - 1
    omega

theorem CycleChord.BwdShortcut0.after_fwd (s : CycleChord.BwdShortcut0) :
    s.after.fwdInternals = s.chord.fwdInternals := by
  have ha := s.a0
  simp only [CycleChord.fwdInternals, CycleChord.BwdShortcut0.after, ha]

theorem CycleChord.BwdShortcut0.after_bwd (s : CycleChord.BwdShortcut0) :
    s.after.bwdInternals = s.chord.bwdInternals - 1 := by
  have ha := s.a0
  have hb := s.chord.b_lt_n
  have hbwd : 2 ≤ s.chord.n - (s.chord.b - s.chord.a) - 1 := s.bwdGe2
  simp only [CycleChord.bwdInternals, CycleChord.BwdShortcut0.after, ha]
  omega

theorem CycleChord.BwdShortcut0.shorter_drops (s : CycleChord.BwdShortcut0) :
    s.after.shorterInternals < s.chord.shorterInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe2
  simp only [CycleChord.shorterInternals, hf, hb]
  omega

def OuterplanarEmbedCert.foldShortcutBwd0 (s : CycleChord.BwdShortcut0) :
    OuterplanarEmbedCert :=
  .oneChord s.after

theorem OuterplanarEmbedCert.foldShortcutBwd0_not_cycle (s : CycleChord.BwdShortcut0) :
    (foldShortcutBwd0 s).isCycle = false :=
  rfl

/-- C₈ + chord `{0,5}`: bwd arc length 2 → wrap shortcut. -/
def c8Chord05 : CycleChord where
  n := 8
  a := 0
  b := 5
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c8Chord05Bwd : CycleChord.BwdShortcut0 where
  chord := c8Chord05
  a0 := rfl
  bwdShort := by native_decide
  bwdGe2 := by native_decide

theorem c8Chord05_after_shorter :
    c8Chord05Bwd.after.a = 0 ∧
      c8Chord05Bwd.after.b = 5 ∧
      c8Chord05Bwd.after.n = 7 ∧
      c8Chord05Bwd.after.shorterInternals = 1 := by
  native_decide

/-- Backward arc strictly shorter with tip adjacent to `a` on the wrap (`a ≥ 1`). -/
structure CycleChord.BwdShortcut where
  chord : CycleChord
  aPos : 0 < chord.a
  bwdShort : chord.bwdInternals < chord.fwdInternals
  bwdGe2 : 2 ≤ chord.bwdInternals

/-- Residual after deleting tip `a - 1` on the wrap arc. -/
def CycleChord.BwdShortcut.after (s : CycleChord.BwdShortcut) : CycleChord where
  n := s.chord.n - 1
  a := s.chord.a - 1
  b := s.chord.b - 1
  gap := by
    have hg := s.chord.gap
    have ha := s.aPos
    omega
  b_lt_n := by
    have hb := s.chord.b_lt_n
    have ha := s.aPos
    have hg := s.chord.gap
    omega
  bwd_pos := by
    have hbwd : 2 ≤ s.chord.n - (s.chord.b - s.chord.a) - 1 := s.bwdGe2
    have hb := s.chord.b_lt_n
    have ha := s.aPos
    have hg := s.chord.gap
    -- (b-1)-(a-1) = b-a when a≥1
    have hab : (s.chord.b - 1) - (s.chord.a - 1) = s.chord.b - s.chord.a := by omega
    change 0 < (s.chord.n - 1) - ((s.chord.b - 1) - (s.chord.a - 1)) - 1
    omega

theorem CycleChord.BwdShortcut.after_fwd (s : CycleChord.BwdShortcut) :
    s.after.fwdInternals = s.chord.fwdInternals := by
  have ha := s.aPos
  have hg := s.chord.gap
  simp only [CycleChord.fwdInternals, CycleChord.BwdShortcut.after]
  omega

theorem CycleChord.BwdShortcut.after_bwd (s : CycleChord.BwdShortcut) :
    s.after.bwdInternals = s.chord.bwdInternals - 1 := by
  have ha := s.aPos
  have hb := s.chord.b_lt_n
  have hg := s.chord.gap
  have hbwd : 2 ≤ s.chord.n - (s.chord.b - s.chord.a) - 1 := s.bwdGe2
  simp only [CycleChord.bwdInternals, CycleChord.BwdShortcut.after]
  omega

theorem CycleChord.BwdShortcut.shorter_drops (s : CycleChord.BwdShortcut) :
    s.after.shorterInternals < s.chord.shorterInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe2
  simp only [CycleChord.shorterInternals, hf, hb]
  omega

def OuterplanarEmbedCert.foldShortcutBwd (s : CycleChord.BwdShortcut) :
    OuterplanarEmbedCert :=
  .oneChord s.after

theorem OuterplanarEmbedCert.foldShortcutBwd_not_cycle (s : CycleChord.BwdShortcut) :
    (foldShortcutBwd s).isCycle = false :=
  rfl

/-- C₈ + chord `{1,6}`: bwd=2 < fwd=4, tip at 0. -/
def c8Chord16 : CycleChord where
  n := 8
  a := 1
  b := 6
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c8Chord16Bwd : CycleChord.BwdShortcut where
  chord := c8Chord16
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

theorem c8Chord16_after_shorter :
    c8Chord16Bwd.after.a = 0 ∧
      c8Chord16Bwd.after.b = 5 ∧
      c8Chord16Bwd.after.n = 7 ∧
      c8Chord16Bwd.after.shorterInternals = 1 := by
  native_decide

/-- Embed cert: shortcut fold stays `oneChord` (not a cycle). -/
def OuterplanarEmbedCert.foldShortcutFwd (s : CycleChord.FwdShortcut) :
    OuterplanarEmbedCert :=
  .oneChord s.after

theorem OuterplanarEmbedCert.foldShortcutFwd_not_cycle (s : CycleChord.FwdShortcut) :
    (foldShortcutFwd s).isCycle = false :=
  rfl

theorem OuterplanarEmbedCert.foldShortcutFwd_lt (s : CycleChord.FwdShortcut)
    (hPos : 1 < s.chord.n) :
    (foldShortcutFwd s).nVertices < s.chord.n := by
  simp [foldShortcutFwd, OuterplanarEmbedCert.nVertices, CycleChord.FwdShortcut.after]
  omega

/-- Residual sketch for a fwd-shortcut ear. -/
def CycleChord.toShortcutSketch (c : CycleChord)
    (_hshort : 1 < c.shorterInternals) : ResidualSketch :=
  c.toEarPath.toSketch c.n c.shorter_pos (Or.inl rfl)

theorem CycleChord.toEarPath_shortcut (c : CycleChord)
    (hshort : 1 < c.shorterInternals) :
    c.toEarPath.hasShortcutTip = true := by
  have hne : c.shorterInternals ≠ 1 := Nat.ne_of_gt hshort
  simp [CycleChord.toEarPath, OuterplanarEarPath.hasShortcutTip, hne]
  exact c.shorter_pos

theorem CycleChord.toEarPath_not_triangle (c : CycleChord)
    (hshort : 1 < c.shorterInternals) :
    c.toEarPath.hasTriangleEar = false := by
  have hne : c.shorterInternals ≠ 1 := Nat.ne_of_gt hshort
  simp [CycleChord.toEarPath, OuterplanarEarPath.hasTriangleEar, hne]

theorem CycleChord.toShortcutSketch_tip (c : CycleChord)
    (hshort : 1 < c.shorterInternals) :
    (c.toShortcutSketch hshort).classify.tipKind = some .shortcutDeg2NextToDeg3 := by
  have hTri := c.toEarPath_not_triangle hshort
  simp [CycleChord.toShortcutSketch, OuterplanarEarPath.toSketch,
    ResidualSketch.classify, hTri]

/--
  One facial shortcut-fold step: tip witness + oneChord residual +
  odd-charge residual + strict measure / shorter-arc drop.
-/
structure FacialShortcutFoldStep where
  fwd : CycleChord.FwdShortcut
  nPos : 1 < fwd.chord.n
  shorterGe2 : 1 < fwd.chord.shorterInternals
  charges : OddChargeVec
  charges_len : charges.charges.length = fwd.chord.n
  tip : Nat
  foldInto : Nat
  tip_lt : tip < charges.charges.length
  foldInto_lt : foldInto < charges.charges.length
  tip_ne : foldInto ≠ tip

namespace FacialShortcutFoldStep

def before (s : FacialShortcutFoldStep) : OuterplanarEmbedCert :=
  .oneChord s.fwd.chord

def after (s : FacialShortcutFoldStep) : OuterplanarEmbedCert :=
  OuterplanarEmbedCert.foldShortcutFwd s.fwd

def sketch (s : FacialShortcutFoldStep) : ResidualSketch :=
  s.fwd.chord.toShortcutSketch s.shorterGe2

def tipWitness (s : FacialShortcutFoldStep) : FoldTipWitness 3 where
  sketch := s.sketch
  tipKind := .shortcutDeg2NextToDeg3
  tipMatches := s.fwd.chord.toShortcutSketch_tip s.shorterGe2

def chargesAfter (s : FacialShortcutFoldStep) : OddChargeVec :=
  s.charges.foldTip s.foldInto s.tip s.foldInto_lt s.tip_lt s.tip_ne

theorem before_not_cycle (s : FacialShortcutFoldStep) :
    s.before.isCycle = false :=
  rfl

theorem after_not_cycle (s : FacialShortcutFoldStep) :
    s.after.isCycle = false :=
  OuterplanarEmbedCert.foldShortcutFwd_not_cycle s.fwd

theorem measure_drops (s : FacialShortcutFoldStep) :
    s.after.nVertices < s.before.nVertices := by
  simpa [before, after, OuterplanarEmbedCert.nVertices] using
    OuterplanarEmbedCert.foldShortcutFwd_lt s.fwd s.nPos

theorem shorter_drops (s : FacialShortcutFoldStep) :
    s.fwd.after.shorterInternals < s.fwd.chord.shorterInternals :=
  s.fwd.shorter_drops

theorem charges_remain_odd (s : FacialShortcutFoldStep) :
    gf2Sum s.chargesAfter.charges = 1 :=
  s.chargesAfter.odd

theorem bundle (s : FacialShortcutFoldStep) :
    s.before.isCycle = false ∧
      s.after.isCycle = false ∧
      s.after.nVertices < s.before.nVertices ∧
      s.fwd.after.shorterInternals < s.fwd.chord.shorterInternals ∧
      gf2Sum s.chargesAfter.charges = 1 ∧
      s.tipWitness.tipKind = .shortcutDeg2NextToDeg3 :=
  ⟨s.before_not_cycle, s.after_not_cycle, s.measure_drops, s.shorter_drops,
    s.charges_remain_odd, rfl⟩

end FacialShortcutFoldStep

/-- C₈ + chord `{0,4}`: shorter arc length 3 → shortcut. -/
def c8Chord04 : CycleChord where
  n := 8
  a := 0
  b := 4
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c8Chord04Fwd : CycleChord.FwdShortcut where
  chord := c8Chord04
  fwdShort := by native_decide
  fwdGe2 := by native_decide

theorem c8Chord04_after_shorter :
    c8Chord04Fwd.after.a = 0 ∧
      c8Chord04Fwd.after.b = 3 ∧
      c8Chord04Fwd.after.n = 7 ∧
      c8Chord04Fwd.after.shorterInternals = 2 := by
  native_decide

noncomputable def c8FacialShortcutFold : FacialShortcutFoldStep where
  fwd := c8Chord04Fwd
  nPos := by decide
  shorterGe2 := by native_decide
  charges := unitOddCharge 8 (by decide)
  charges_len := by native_decide
  tip := 1
  foldInto := 0
  tip_lt := by native_decide
  foldInto_lt := by native_decide
  tip_ne := by decide

theorem c8FacialShortcutFold_bundle :
    c8FacialShortcutFold.after.isCycle = false ∧
      c8FacialShortcutFold.after.nVertices = 7 ∧
      c8Chord04Fwd.after.shorterInternals = 2 ∧
      gf2Sum c8FacialShortcutFold.chargesAfter.charges = 1 :=
  ⟨c8FacialShortcutFold.after_not_cycle, rfl,
    by native_decide, c8FacialShortcutFold.charges_remain_odd⟩

def shortcutFoldDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

end PNPLab.Outerplanar
