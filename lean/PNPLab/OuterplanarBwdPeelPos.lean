/-
  Bwd wrap-shortcut for `a ≥ 1` (Category C / G6).

  * `bwd = 2`           → tip → triangle → cycle (`BwdShortcutTri`)
  * `a = 1`, `bwd ≥ 3`  → tip → `a = 0` → bwd₀ peel (`BwdShortcutVia0`)
  * `a = 2`, `bwd = 3`  → tip → Tri (`BwdShortcutA2Tri`)
  * `a = 2`, `bwd ≥ 4`  → tip → Via0 (`BwdShortcutA2Via`)
-/

import PNPLab.OuterplanarBwdPeel

namespace PNPLab.Outerplanar

/-- Wrap length exactly 2 ⇒ residual after one tip is a triangle. -/
structure CycleChord.BwdShortcutTri extends CycleChord.BwdShortcut where
  bwdEq2 : chord.bwdInternals = 2

theorem CycleChord.BwdShortcutTri.after_triangle (s : CycleChord.BwdShortcutTri) :
    s.after.shorterInternals = 1 := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have heq := s.bwdEq2
  have hs := s.bwdShort
  simp only [CycleChord.shorterInternals, hf, hb, heq]
  omega

theorem CycleChord.BwdShortcutTri.after_nPos (s : CycleChord.BwdShortcutTri)
    (_hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have heq := s.bwdEq2
  have ha := s.aPos
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutTri.toCycleBase (s : CycleChord.BwdShortcutTri)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  (FacialTriangleFoldStep.ofTriangleChord
    s.after s.after_triangle (s.after_nPos hPos)).toCycleBase

theorem CycleChord.BwdShortcutTri.toCycleBase_nAfter (s : CycleChord.BwdShortcutTri)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - 2 := by
  have hn : (s.toCycleBase hPos).nAfter = s.after.n - 1 := rfl
  have heq := s.bwdEq2
  have ha := s.aPos
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  rw [hn]
  change (CycleChord.BwdShortcut.after s.toBwdShortcut).n - 1 = s.chord.n - 2
  simp only [CycleChord.BwdShortcut.after]
  omega

theorem CycleChord.BwdShortcutTri.reaches_cycle (s : CycleChord.BwdShortcutTri)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - 2 :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- Lift a `BwdShortcut` with `bwd = 2` to the triangle residual schedule. -/
def CycleChord.BwdShortcut.toTri (s : CycleChord.BwdShortcut)
    (h : s.chord.bwdInternals = 2) : CycleChord.BwdShortcutTri where
  toBwdShortcut := s
  bwdEq2 := h

def c8Chord16BwdTri : CycleChord.BwdShortcutTri :=
  c8Chord16Bwd.toTri (by native_decide)

theorem c8Chord16_reaches_cycle :
    let b := c8Chord16BwdTri.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 6 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c8Chord16BwdTri.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c8Chord16BwdTri.chord.n = 8 := rfl
  rw [h.2.2.2, hn]

/--
  Wrap length ≥ 3 with `a = 1`: first tip lands on `a = 0`, then the residual
  is a `BwdShortcut0` that peels to the cycle base.
-/
structure CycleChord.BwdShortcutVia0 extends CycleChord.BwdShortcut where
  aEq1 : chord.a = 1
  bwdGe3 : 3 ≤ chord.bwdInternals

theorem CycleChord.BwdShortcutVia0.after_a0 (s : CycleChord.BwdShortcutVia0) :
    s.after.a = 0 := by
  have ha := s.aEq1
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutVia0.after_bwdShort (s : CycleChord.BwdShortcutVia0) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe3
  omega

theorem CycleChord.BwdShortcutVia0.after_bwdGe2 (s : CycleChord.BwdShortcutVia0) :
    2 ≤ s.after.bwdInternals := by
  have hb := s.after_bwd
  have hge := s.bwdGe3
  omega

def CycleChord.BwdShortcutVia0.afterBwd0 (s : CycleChord.BwdShortcutVia0) :
    CycleChord.BwdShortcut0 where
  chord := s.after
  a0 := s.after_a0
  bwdShort := s.after_bwdShort
  bwdGe2 := s.after_bwdGe2

theorem CycleChord.BwdShortcutVia0.after_nPos (s : CycleChord.BwdShortcutVia0)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq1
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hge := s.bwdGe3
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutVia0.toCycleBase (s : CycleChord.BwdShortcutVia0)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterBwd0.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutVia0.toCycleBase_nAfter (s : CycleChord.BwdShortcutVia0)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  have h0 := s.afterBwd0.toCycleBase_nAfter (s.after_nPos hPos)
  have hb := s.after_bwd
  have hge := s.bwdGe3
  have hn : s.afterBwd0.chord.n = s.chord.n - 1 := by
    simp only [afterBwd0, CycleChord.BwdShortcut.after]
  have hb' : s.afterBwd0.chord.bwdInternals = s.chord.bwdInternals - 1 := by
    simpa [afterBwd0] using hb
  simp only [toCycleBase] at h0 ⊢
  omega

theorem CycleChord.BwdShortcutVia0.reaches_cycle (s : CycleChord.BwdShortcutVia0)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₁₀ `{1,7}`: bwd=3, a=1 → after a=0 → bwd₀ peel → C₇ base. -/
def c10Chord17 : CycleChord where
  n := 10
  a := 1
  b := 7
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c10Chord17Bwd : CycleChord.BwdShortcut where
  chord := c10Chord17
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c10Chord17Via0 : CycleChord.BwdShortcutVia0 where
  toBwdShortcut := c10Chord17Bwd
  aEq1 := rfl
  bwdGe3 := by native_decide

theorem c10Chord17_after_a0 :
    c10Chord17Via0.after.a = 0 ∧
      c10Chord17Via0.after.b = 6 ∧
      c10Chord17Via0.after.n = 9 ∧
      c10Chord17Via0.after.bwdInternals = 2 := by
  native_decide

theorem c10Chord17_reaches_cycle :
    let b := c10Chord17Via0.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 7 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c10Chord17Via0.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c10Chord17Via0.chord.n = 10 := rfl
  have hb : c10Chord17Via0.chord.bwdInternals = 3 := by native_decide
  rw [h.2.2.2, hn, hb]

/--
  Wrap with `a = 2`, `bwd = 3`: tip → `a = 1`, `bwd = 2` → Tri → cycle.
-/
structure CycleChord.BwdShortcutA2Tri extends CycleChord.BwdShortcut where
  aEq2 : chord.a = 2
  bwdEq3 : chord.bwdInternals = 3

theorem CycleChord.BwdShortcutA2Tri.after_a1 (s : CycleChord.BwdShortcutA2Tri) :
    s.after.a = 1 := by
  have ha := s.aEq2
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA2Tri.after_bwd2 (s : CycleChord.BwdShortcutA2Tri) :
    s.after.bwdInternals = 2 := by
  have hb := s.after_bwd
  have heq := s.bwdEq3
  omega

theorem CycleChord.BwdShortcutA2Tri.after_bwdShort (s : CycleChord.BwdShortcutA2Tri) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd2
  have hs := s.bwdShort
  have heq := s.bwdEq3
  -- after.bwd=2, after.fwd=fwd, and 3=bwd < fwd ⇒ 2 < fwd
  omega

def CycleChord.BwdShortcutA2Tri.afterTri (s : CycleChord.BwdShortcutA2Tri) :
    CycleChord.BwdShortcutTri where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a1; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwd2; omega
  }
  bwdEq2 := s.after_bwd2

theorem CycleChord.BwdShortcutA2Tri.after_nPos (s : CycleChord.BwdShortcutA2Tri)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq2
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have heq := s.bwdEq3
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA2Tri.toCycleBase (s : CycleChord.BwdShortcutA2Tri)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterTri.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA2Tri.toCycleBase_nAfter (s : CycleChord.BwdShortcutA2Tri)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - 3 := by
  have hn := s.afterTri.toCycleBase_nAfter (s.after_nPos hPos)
  have heq := s.bwdEq3
  simp only [toCycleBase, afterTri, CycleChord.BwdShortcut.after] at hn ⊢
  omega

theorem CycleChord.BwdShortcutA2Tri.reaches_cycle (s : CycleChord.BwdShortcutA2Tri)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - 3 :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/--
  Wrap with `a = 2`, `bwd ≥ 4`: tip → `a = 1`, `bwd ≥ 3` → Via0 → cycle.
-/
structure CycleChord.BwdShortcutA2Via extends CycleChord.BwdShortcut where
  aEq2 : chord.a = 2
  bwdGe4 : 4 ≤ chord.bwdInternals

theorem CycleChord.BwdShortcutA2Via.after_a1 (s : CycleChord.BwdShortcutA2Via) :
    s.after.a = 1 := by
  have ha := s.aEq2
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA2Via.after_bwdGe3 (s : CycleChord.BwdShortcutA2Via) :
    3 ≤ s.after.bwdInternals := by
  have hb := s.after_bwd
  have hge := s.bwdGe4
  omega

theorem CycleChord.BwdShortcutA2Via.after_bwdShort (s : CycleChord.BwdShortcutA2Via) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe4
  omega

def CycleChord.BwdShortcutA2Via.afterVia0 (s : CycleChord.BwdShortcutA2Via) :
    CycleChord.BwdShortcutVia0 where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a1; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwdGe3; omega
  }
  aEq1 := s.after_a1
  bwdGe3 := s.after_bwdGe3

theorem CycleChord.BwdShortcutA2Via.after_nPos (s : CycleChord.BwdShortcutA2Via)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq2
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hge := s.bwdGe4
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA2Via.toCycleBase (s : CycleChord.BwdShortcutA2Via)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterVia0.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA2Via.toCycleBase_nAfter (s : CycleChord.BwdShortcutA2Via)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  have h0 := s.afterVia0.toCycleBase_nAfter (s.after_nPos hPos)
  have hb := s.after_bwd
  have hge := s.bwdGe4
  have hn : s.afterVia0.chord.n = s.chord.n - 1 := by
    simp only [afterVia0, CycleChord.BwdShortcut.after]
  have hb' : s.afterVia0.chord.bwdInternals = s.chord.bwdInternals - 1 := by
    simpa [afterVia0] using hb
  simp only [toCycleBase] at h0 ⊢
  omega

theorem CycleChord.BwdShortcutA2Via.reaches_cycle (s : CycleChord.BwdShortcutA2Via)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₉ `{2,7}`: a=2, bwd=3 → tip → Tri → C₆ base. -/
def c9Chord27 : CycleChord where
  n := 9
  a := 2
  b := 7
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c9Chord27Bwd : CycleChord.BwdShortcut where
  chord := c9Chord27
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c9Chord27A2Tri : CycleChord.BwdShortcutA2Tri where
  toBwdShortcut := c9Chord27Bwd
  aEq2 := rfl
  bwdEq3 := by native_decide

theorem c9Chord27_reaches_cycle :
    let b := c9Chord27A2Tri.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 6 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c9Chord27A2Tri.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c9Chord27A2Tri.chord.n = 9 := rfl
  rw [h.2.2.2, hn]

/-- C₁₂ `{2,9}`: a=2, bwd=4 → tip → Via0 → C₈ base. -/
def c12Chord29 : CycleChord where
  n := 12
  a := 2
  b := 9
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c12Chord29Bwd : CycleChord.BwdShortcut where
  chord := c12Chord29
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c12Chord29A2Via : CycleChord.BwdShortcutA2Via where
  toBwdShortcut := c12Chord29Bwd
  aEq2 := rfl
  bwdGe4 := by native_decide

theorem c12Chord29_after :
    c12Chord29A2Via.after.a = 1 ∧
      c12Chord29A2Via.after.b = 8 ∧
      c12Chord29A2Via.after.n = 11 ∧
      c12Chord29A2Via.after.bwdInternals = 3 := by
  native_decide

theorem c12Chord29_reaches_cycle :
    let b := c12Chord29A2Via.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 8 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c12Chord29A2Via.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c12Chord29A2Via.chord.n = 12 := rfl
  have hb : c12Chord29A2Via.chord.bwdInternals = 4 := by native_decide
  rw [h.2.2.2, hn, hb]

/--
  Wrap with `a = 3`, `bwd = 4`: tip → `a = 2`, `bwd = 3` → A2Tri → cycle.
-/
structure CycleChord.BwdShortcutA3Tri extends CycleChord.BwdShortcut where
  aEq3 : chord.a = 3
  bwdEq4 : chord.bwdInternals = 4

theorem CycleChord.BwdShortcutA3Tri.after_a2 (s : CycleChord.BwdShortcutA3Tri) :
    s.after.a = 2 := by
  have ha := s.aEq3
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA3Tri.after_bwd3 (s : CycleChord.BwdShortcutA3Tri) :
    s.after.bwdInternals = 3 := by
  have hb := s.after_bwd
  have heq := s.bwdEq4
  omega

theorem CycleChord.BwdShortcutA3Tri.after_bwdShort (s : CycleChord.BwdShortcutA3Tri) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd3
  have hs := s.bwdShort
  have heq := s.bwdEq4
  omega

def CycleChord.BwdShortcutA3Tri.afterA2Tri (s : CycleChord.BwdShortcutA3Tri) :
    CycleChord.BwdShortcutA2Tri where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a2; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwd3; omega
  }
  aEq2 := s.after_a2
  bwdEq3 := s.after_bwd3

theorem CycleChord.BwdShortcutA3Tri.after_nPos (s : CycleChord.BwdShortcutA3Tri)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq3
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have heq := s.bwdEq4
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA3Tri.toCycleBase (s : CycleChord.BwdShortcutA3Tri)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterA2Tri.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA3Tri.toCycleBase_nAfter (s : CycleChord.BwdShortcutA3Tri)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - 4 := by
  have hn := s.afterA2Tri.toCycleBase_nAfter (s.after_nPos hPos)
  have heq := s.bwdEq4
  simp only [toCycleBase, afterA2Tri, CycleChord.BwdShortcut.after] at hn ⊢
  omega

theorem CycleChord.BwdShortcutA3Tri.reaches_cycle (s : CycleChord.BwdShortcutA3Tri)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - 4 :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/--
  Wrap with `a = 3`, `bwd ≥ 5`: tip → `a = 2`, `bwd ≥ 4` → A2Via → cycle.
-/
structure CycleChord.BwdShortcutA3Via extends CycleChord.BwdShortcut where
  aEq3 : chord.a = 3
  bwdGe5 : 5 ≤ chord.bwdInternals

theorem CycleChord.BwdShortcutA3Via.after_a2 (s : CycleChord.BwdShortcutA3Via) :
    s.after.a = 2 := by
  have ha := s.aEq3
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA3Via.after_bwdGe4 (s : CycleChord.BwdShortcutA3Via) :
    4 ≤ s.after.bwdInternals := by
  have hb := s.after_bwd
  have hge := s.bwdGe5
  omega

theorem CycleChord.BwdShortcutA3Via.after_bwdShort (s : CycleChord.BwdShortcutA3Via) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe5
  omega

def CycleChord.BwdShortcutA3Via.afterA2Via (s : CycleChord.BwdShortcutA3Via) :
    CycleChord.BwdShortcutA2Via where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a2; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwdGe4; omega
  }
  aEq2 := s.after_a2
  bwdGe4 := s.after_bwdGe4

theorem CycleChord.BwdShortcutA3Via.after_nPos (s : CycleChord.BwdShortcutA3Via)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq3
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hge := s.bwdGe5
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA3Via.toCycleBase (s : CycleChord.BwdShortcutA3Via)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterA2Via.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA3Via.toCycleBase_nAfter (s : CycleChord.BwdShortcutA3Via)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  have h0 := s.afterA2Via.toCycleBase_nAfter (s.after_nPos hPos)
  have hb := s.after_bwd
  have hge := s.bwdGe5
  have hn : s.afterA2Via.chord.n = s.chord.n - 1 := by
    simp only [afterA2Via, CycleChord.BwdShortcut.after]
  have hb' : s.afterA2Via.chord.bwdInternals = s.chord.bwdInternals - 1 := by
    simpa [afterA2Via] using hb
  simp only [toCycleBase] at h0 ⊢
  omega

theorem CycleChord.BwdShortcutA3Via.reaches_cycle (s : CycleChord.BwdShortcutA3Via)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₁₁ `{3,9}`: a=3, bwd=4 → tip → A2Tri → C₇ base. -/
def c11Chord39 : CycleChord where
  n := 11
  a := 3
  b := 9
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c11Chord39Bwd : CycleChord.BwdShortcut where
  chord := c11Chord39
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c11Chord39A3Tri : CycleChord.BwdShortcutA3Tri where
  toBwdShortcut := c11Chord39Bwd
  aEq3 := rfl
  bwdEq4 := by native_decide

theorem c11Chord39_reaches_cycle :
    let b := c11Chord39A3Tri.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 7 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c11Chord39A3Tri.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c11Chord39A3Tri.chord.n = 11 := rfl
  rw [h.2.2.2, hn]

/-- C₁₃ `{3,10}`: a=3, bwd=5 → tip → A2Via → C₈ base. -/
def c13Chord310 : CycleChord where
  n := 13
  a := 3
  b := 10
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c13Chord310Bwd : CycleChord.BwdShortcut where
  chord := c13Chord310
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c13Chord310A3Via : CycleChord.BwdShortcutA3Via where
  toBwdShortcut := c13Chord310Bwd
  aEq3 := rfl
  bwdGe5 := by native_decide

theorem c13Chord310_after :
    c13Chord310A3Via.after.a = 2 ∧
      c13Chord310A3Via.after.b = 9 ∧
      c13Chord310A3Via.after.n = 12 ∧
      c13Chord310A3Via.after.bwdInternals = 4 := by
  native_decide

theorem c13Chord310_reaches_cycle :
    let b := c13Chord310A3Via.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 8 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c13Chord310A3Via.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c13Chord310A3Via.chord.n = 13 := rfl
  have hb : c13Chord310A3Via.chord.bwdInternals = 5 := by native_decide
  rw [h.2.2.2, hn, hb]

/--
  Wrap with `a = 4`, `bwd = 5`: tip → `a = 3`, `bwd = 4` → A3Tri → cycle.
-/
structure CycleChord.BwdShortcutA4Tri extends CycleChord.BwdShortcut where
  aEq4 : chord.a = 4
  bwdEq5 : chord.bwdInternals = 5

theorem CycleChord.BwdShortcutA4Tri.after_a3 (s : CycleChord.BwdShortcutA4Tri) :
    s.after.a = 3 := by
  have ha := s.aEq4
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA4Tri.after_bwd4 (s : CycleChord.BwdShortcutA4Tri) :
    s.after.bwdInternals = 4 := by
  have hb := s.after_bwd
  have heq := s.bwdEq5
  omega

theorem CycleChord.BwdShortcutA4Tri.after_bwdShort (s : CycleChord.BwdShortcutA4Tri) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd4
  have hs := s.bwdShort
  have heq := s.bwdEq5
  omega

def CycleChord.BwdShortcutA4Tri.afterA3Tri (s : CycleChord.BwdShortcutA4Tri) :
    CycleChord.BwdShortcutA3Tri where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a3; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwd4; omega
  }
  aEq3 := s.after_a3
  bwdEq4 := s.after_bwd4

theorem CycleChord.BwdShortcutA4Tri.after_nPos (s : CycleChord.BwdShortcutA4Tri)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq4
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have heq := s.bwdEq5
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA4Tri.toCycleBase (s : CycleChord.BwdShortcutA4Tri)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterA3Tri.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA4Tri.toCycleBase_nAfter (s : CycleChord.BwdShortcutA4Tri)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - 5 := by
  have hn := s.afterA3Tri.toCycleBase_nAfter (s.after_nPos hPos)
  have heq := s.bwdEq5
  simp only [toCycleBase, afterA3Tri, CycleChord.BwdShortcut.after] at hn ⊢
  omega

theorem CycleChord.BwdShortcutA4Tri.reaches_cycle (s : CycleChord.BwdShortcutA4Tri)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - 5 :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/--
  Wrap with `a = 4`, `bwd ≥ 6`: tip → `a = 3`, `bwd ≥ 5` → A3Via → cycle.
-/
structure CycleChord.BwdShortcutA4Via extends CycleChord.BwdShortcut where
  aEq4 : chord.a = 4
  bwdGe6 : 6 ≤ chord.bwdInternals

theorem CycleChord.BwdShortcutA4Via.after_a3 (s : CycleChord.BwdShortcutA4Via) :
    s.after.a = 3 := by
  have ha := s.aEq4
  simp only [CycleChord.BwdShortcut.after, ha]

theorem CycleChord.BwdShortcutA4Via.after_bwdGe5 (s : CycleChord.BwdShortcutA4Via) :
    5 ≤ s.after.bwdInternals := by
  have hb := s.after_bwd
  have hge := s.bwdGe6
  omega

theorem CycleChord.BwdShortcutA4Via.after_bwdShort (s : CycleChord.BwdShortcutA4Via) :
    s.after.bwdInternals < s.after.fwdInternals := by
  have hf := s.after_fwd
  have hb := s.after_bwd
  have hs := s.bwdShort
  have hge := s.bwdGe6
  omega

def CycleChord.BwdShortcutA4Via.afterA3Via (s : CycleChord.BwdShortcutA4Via) :
    CycleChord.BwdShortcutA3Via where
  toBwdShortcut := {
    chord := s.after
    aPos := by have h := s.after_a3; omega
    bwdShort := s.after_bwdShort
    bwdGe2 := by have h := s.after_bwdGe5; omega
  }
  aEq3 := s.after_a3
  bwdGe5 := s.after_bwdGe5

theorem CycleChord.BwdShortcutA4Via.after_nPos (s : CycleChord.BwdShortcutA4Via)
    (hPos : 1 < s.chord.n) : 1 < s.after.n := by
  have ha := s.aEq4
  have hg := s.chord.gap
  have hb := s.chord.b_lt_n
  have hge := s.bwdGe6
  have hbwd : s.chord.bwdInternals = s.chord.n - (s.chord.b - s.chord.a) - 1 := rfl
  change 1 < (CycleChord.BwdShortcut.after s.toBwdShortcut).n
  simp only [CycleChord.BwdShortcut.after]
  omega

noncomputable def CycleChord.BwdShortcutA4Via.toCycleBase (s : CycleChord.BwdShortcutA4Via)
    (hPos : 1 < s.chord.n) : FacialCycleBase :=
  s.afterA3Via.toCycleBase (s.after_nPos hPos)

theorem CycleChord.BwdShortcutA4Via.toCycleBase_nAfter (s : CycleChord.BwdShortcutA4Via)
    (hPos : 1 < s.chord.n) :
    (s.toCycleBase hPos).nAfter = s.chord.n - s.chord.bwdInternals := by
  have h0 := s.afterA3Via.toCycleBase_nAfter (s.after_nPos hPos)
  have hb := s.after_bwd
  have hge := s.bwdGe6
  have hn : s.afterA3Via.chord.n = s.chord.n - 1 := by
    simp only [afterA3Via, CycleChord.BwdShortcut.after]
  have hb' : s.afterA3Via.chord.bwdInternals = s.chord.bwdInternals - 1 := by
    simpa [afterA3Via] using hb
  simp only [toCycleBase] at h0 ⊢
  omega

theorem CycleChord.BwdShortcutA4Via.reaches_cycle (s : CycleChord.BwdShortcutA4Via)
    (hPos : 1 < s.chord.n) :
    let b := s.toCycleBase hPos
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 ∧
      b.nAfter = s.chord.n - s.chord.bwdInternals :=
  let b := s.toCycleBase hPos
  ⟨b.embed_cycle, b.charges_odd, foldSteps_cycle b.nAfter, s.toCycleBase_nAfter hPos⟩

/-- C₁₃ `{4,11}`: a=4, bwd=5 → tip → A3Tri → C₈ base. -/
def c13Chord411 : CycleChord where
  n := 13
  a := 4
  b := 11
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c13Chord411Bwd : CycleChord.BwdShortcut where
  chord := c13Chord411
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c13Chord411A4Tri : CycleChord.BwdShortcutA4Tri where
  toBwdShortcut := c13Chord411Bwd
  aEq4 := rfl
  bwdEq5 := by native_decide

theorem c13Chord411_reaches_cycle :
    let b := c13Chord411A4Tri.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 8 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c13Chord411A4Tri.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c13Chord411A4Tri.chord.n = 13 := rfl
  rw [h.2.2.2, hn]

/-- C₁₅ `{4,12}`: a=4, bwd=6 → tip → A3Via → C₉ base. -/
def c15Chord412 : CycleChord where
  n := 15
  a := 4
  b := 12
  gap := by decide
  b_lt_n := by decide
  bwd_pos := by decide

def c15Chord412Bwd : CycleChord.BwdShortcut where
  chord := c15Chord412
  aPos := by decide
  bwdShort := by native_decide
  bwdGe2 := by native_decide

def c15Chord412A4Via : CycleChord.BwdShortcutA4Via where
  toBwdShortcut := c15Chord412Bwd
  aEq4 := rfl
  bwdGe6 := by native_decide

theorem c15Chord412_after :
    c15Chord412A4Via.after.a = 3 ∧
      c15Chord412A4Via.after.b = 11 ∧
      c15Chord412A4Via.after.n = 14 ∧
      c15Chord412A4Via.after.bwdInternals = 5 := by
  native_decide

theorem c15Chord412_reaches_cycle :
    let b := c15Chord412A4Via.toCycleBase (by decide)
    b.embedAfter.isCycle = true ∧
      b.nAfter = 9 ∧
      gf2Sum b.chargesAfter.charges = 1 := by
  have h := c15Chord412A4Via.reaches_cycle (by decide)
  refine ⟨h.1, ?_, h.2.1⟩
  have hn : c15Chord412A4Via.chord.n = 15 := rfl
  have hb : c15Chord412A4Via.chord.bwdInternals = 6 := by native_decide
  rw [h.2.2.2, hn, hb]

def bwdPeelPosDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
