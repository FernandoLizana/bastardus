/-
  Unified one-chord facial path to the cycle base (Category C / G6).

  Schedules:

    * triangle ear             → `FacialTriangleFoldStep.toCycleBase`
    * fwd shorter arc (≥2)     → `FwdShortcut.toCycleBase`
    * bwd wrap, a=0 (≥2)       → `BwdShortcut0.toCycleBase`
    * bwd wrap, a≥1, bwd=2     → `BwdShortcutTri.toCycleBase`
    * bwd wrap, a=1, bwd≥3     → `BwdShortcutVia0.toCycleBase`
    * bwd wrap, a=2, bwd=3     → `BwdShortcutA2Tri.toCycleBase`
    * bwd wrap, a=2, bwd≥4     → `BwdShortcutA2Via.toCycleBase`
    * bwd wrap, a=3, bwd=4     → `BwdShortcutA3Tri.toCycleBase`
    * bwd wrap, a=3, bwd≥5     → `BwdShortcutA3Via.toCycleBase`
    * bwd wrap, a=4, bwd=5     → `BwdShortcutA4Tri.toCycleBase`
    * bwd wrap, a=4, bwd≥6     → `BwdShortcutA4Via.toCycleBase`
    * bwd wrap, a≥1 (∀a)       → `BwdShortcut.toCycleBaseAny` (catch-all)
-/

import PNPLab.OuterplanarShortcutPeel
import PNPLab.OuterplanarBwdPeel
import PNPLab.OuterplanarBwdPeelPos
import PNPLab.OuterplanarBwdPeelAny

namespace PNPLab.Outerplanar

/-- Which facial schedule applies to a one-chord core. -/
inductive OneChordSchedule where
  | triangle
  | fwdPeel
  | bwdPeel0
  | bwdPeel
  | bwdVia0
  | bwdA2Tri
  | bwdA2Via
  | bwdA3Tri
  | bwdA3Via
  | bwdA4Tri
  | bwdA4Via
  | bwdAny
  deriving DecidableEq, Repr

/-- Classify a chord into a facial schedule. -/
def CycleChord.schedule (c : CycleChord) : Option OneChordSchedule :=
  if c.shorterInternals = 1 then
    some .triangle
  else if c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals then
    some .fwdPeel
  else if c.a = 0 ∧ c.bwdInternals < c.fwdInternals ∧ 2 ≤ c.bwdInternals then
    some .bwdPeel0
  else if 0 < c.a ∧ c.bwdInternals < c.fwdInternals ∧ c.bwdInternals = 2 then
    some .bwdPeel
  else if c.a = 1 ∧ c.bwdInternals < c.fwdInternals ∧ 3 ≤ c.bwdInternals then
    some .bwdVia0
  else if c.a = 2 ∧ c.bwdInternals < c.fwdInternals ∧ c.bwdInternals = 3 then
    some .bwdA2Tri
  else if c.a = 2 ∧ c.bwdInternals < c.fwdInternals ∧ 4 ≤ c.bwdInternals then
    some .bwdA2Via
  else if c.a = 3 ∧ c.bwdInternals < c.fwdInternals ∧ c.bwdInternals = 4 then
    some .bwdA3Tri
  else if c.a = 3 ∧ c.bwdInternals < c.fwdInternals ∧ 5 ≤ c.bwdInternals then
    some .bwdA3Via
  else if c.a = 4 ∧ c.bwdInternals < c.fwdInternals ∧ c.bwdInternals = 5 then
    some .bwdA4Tri
  else if c.a = 4 ∧ c.bwdInternals < c.fwdInternals ∧ 6 ≤ c.bwdInternals then
    some .bwdA4Via
  else if 0 < c.a ∧ c.bwdInternals < c.fwdInternals ∧ 2 ≤ c.bwdInternals then
    some .bwdAny
  else
    none

theorem CycleChord.schedule_triangle (c : CycleChord)
    (h : c.shorterInternals = 1) :
    c.schedule = some .triangle := by
  simp [CycleChord.schedule, h]

theorem CycleChord.schedule_fwd (c : CycleChord)
    (hs : c.fwdInternals ≤ c.bwdInternals)
    (hge : 2 ≤ c.fwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .fwdPeel := by
  simp [CycleChord.schedule, hs, hge, hne]

theorem CycleChord.schedule_bwd0 (c : CycleChord)
    (ha : c.a = 0)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 2 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdPeel0 := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  simp [CycleChord.schedule, hne', hfwd, ha, hs, hge]

theorem CycleChord.schedule_bwd (c : CycleChord)
    (ha : 0 < c.a)
    (hs : c.bwdInternals < c.fwdInternals)
    (h2 : c.bwdInternals = 2)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdPeel := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have ha0 : ¬ (c.a = 0) := Nat.pos_iff_ne_zero.mp ha
  have hle2 : ¬ (c.fwdInternals ≤ 2) := by
    have : 2 < c.fwdInternals := by omega
    exact Nat.not_le_of_gt this
  simp [CycleChord.schedule, hne', ha0, ha, h2, hle2]

theorem CycleChord.schedule_bwdVia0 (c : CycleChord)
    (ha : c.a = 1)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 3 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdVia0 := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have h2 : ¬ (c.bwdInternals = 2) := by omega
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  simp [CycleChord.schedule, hne', hfwd, ha, hs, hge, h2]

theorem CycleChord.schedule_bwdA2Tri (c : CycleChord)
    (ha : c.a = 2)
    (hs : c.bwdInternals < c.fwdInternals)
    (h3 : c.bwdInternals = 3)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA2Tri := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have hle3 : ¬ (c.fwdInternals ≤ 3) := by
    have : 3 < c.fwdInternals := by omega
    exact Nat.not_le_of_gt this
  simp [CycleChord.schedule, hne', ha, h3, hle3]

theorem CycleChord.schedule_bwdA2Via (c : CycleChord)
    (ha : c.a = 2)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 4 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA2Via := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have h2 : ¬ (c.bwdInternals = 2) := by omega
  have h3 : ¬ (c.bwdInternals = 3) := by omega
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  simp [CycleChord.schedule, hne', hfwd, ha, hs, hge, h2, h3]

theorem CycleChord.schedule_bwdA3Tri (c : CycleChord)
    (ha : c.a = 3)
    (hs : c.bwdInternals < c.fwdInternals)
    (h4 : c.bwdInternals = 4)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA3Tri := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have hle4 : ¬ (c.fwdInternals ≤ 4) := by
    have : 4 < c.fwdInternals := by omega
    exact Nat.not_le_of_gt this
  simp [CycleChord.schedule, hne', ha, h4, hle4]

theorem CycleChord.schedule_bwdA3Via (c : CycleChord)
    (ha : c.a = 3)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 5 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA3Via := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have h2 : ¬ (c.bwdInternals = 2) := by omega
  have h3 : ¬ (c.bwdInternals = 3) := by omega
  have h4 : ¬ (c.bwdInternals = 4) := by omega
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  simp [CycleChord.schedule, hne', hfwd, ha, hs, hge, h2, h3, h4]

theorem CycleChord.schedule_bwdA4Tri (c : CycleChord)
    (ha : c.a = 4)
    (hs : c.bwdInternals < c.fwdInternals)
    (h5 : c.bwdInternals = 5)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA4Tri := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have hle5 : ¬ (c.fwdInternals ≤ 5) := by
    have : 5 < c.fwdInternals := by omega
    exact Nat.not_le_of_gt this
  simp [CycleChord.schedule, hne', ha, h5, hle5]

theorem CycleChord.schedule_bwdA4Via (c : CycleChord)
    (ha : c.a = 4)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 6 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdA4Via := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have h2 : ¬ (c.bwdInternals = 2) := by omega
  have h3 : ¬ (c.bwdInternals = 3) := by omega
  have h4 : ¬ (c.bwdInternals = 4) := by omega
  have h5 : ¬ (c.bwdInternals = 5) := by omega
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  simp [CycleChord.schedule, hne', hfwd, ha, hs, hge, h2, h3, h4, h5]

theorem CycleChord.schedule_bwdAny (c : CycleChord)
    (ha : 5 ≤ c.a)
    (hs : c.bwdInternals < c.fwdInternals)
    (hge : 3 ≤ c.bwdInternals)
    (hne : c.shorterInternals ≠ 1) :
    c.schedule = some .bwdAny := by
  have hne' : ¬ (c.shorterInternals = 1) := hne
  have hfwd : ¬ (c.fwdInternals ≤ c.bwdInternals ∧ 2 ≤ c.fwdInternals) := by
    intro ⟨hle, _⟩
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hs hle)
  have ha0 : ¬ (c.a = 0) := by omega
  have ha1 : ¬ (c.a = 1) := by omega
  have ha2 : ¬ (c.a = 2) := by omega
  have ha3 : ¬ (c.a = 3) := by omega
  have ha4 : ¬ (c.a = 4) := by omega
  have h2 : ¬ (c.bwdInternals = 2) := by omega
  have haPos : 0 < c.a := by omega
  have hge2 : 2 ≤ c.bwdInternals := by omega
  simp [CycleChord.schedule, hne', hfwd, ha0, ha1, ha2, ha3, ha4, h2, haPos, hs, hge2]

/-- One-chord facial path packaged as a schedule witness. -/
inductive FacialOneChordPath where
  | triangle (s : FacialTriangleFoldStep)
  | fwd (s : CycleChord.FwdShortcut) (hPos : 1 < s.chord.n)
  | bwd0 (s : CycleChord.BwdShortcut0) (hPos : 1 < s.chord.n)
  | bwd (s : CycleChord.BwdShortcutTri) (hPos : 1 < s.chord.n)
  | bwdVia0 (s : CycleChord.BwdShortcutVia0) (hPos : 1 < s.chord.n)
  | bwdA2Tri (s : CycleChord.BwdShortcutA2Tri) (hPos : 1 < s.chord.n)
  | bwdA2Via (s : CycleChord.BwdShortcutA2Via) (hPos : 1 < s.chord.n)
  | bwdA3Tri (s : CycleChord.BwdShortcutA3Tri) (hPos : 1 < s.chord.n)
  | bwdA3Via (s : CycleChord.BwdShortcutA3Via) (hPos : 1 < s.chord.n)
  | bwdA4Tri (s : CycleChord.BwdShortcutA4Tri) (hPos : 1 < s.chord.n)
  | bwdA4Via (s : CycleChord.BwdShortcutA4Via) (hPos : 1 < s.chord.n)
  | bwdAny (s : CycleChord.BwdShortcut) (ha : 5 ≤ s.chord.a)
      (hb : 3 ≤ s.chord.bwdInternals) (hPos : 1 < s.chord.n)

namespace FacialOneChordPath

def chord : FacialOneChordPath → CycleChord
  | .triangle s => s.chord
  | .fwd s _ => s.chord
  | .bwd0 s _ => s.chord
  | .bwd s _ => s.chord
  | .bwdVia0 s _ => s.chord
  | .bwdA2Tri s _ => s.chord
  | .bwdA2Via s _ => s.chord
  | .bwdA3Tri s _ => s.chord
  | .bwdA3Via s _ => s.chord
  | .bwdA4Tri s _ => s.chord
  | .bwdA4Via s _ => s.chord
  | .bwdAny s _ _ _ => s.chord

def scheduleOf : FacialOneChordPath → OneChordSchedule
  | .triangle _ => .triangle
  | .fwd _ _ => .fwdPeel
  | .bwd0 _ _ => .bwdPeel0
  | .bwd _ _ => .bwdPeel
  | .bwdVia0 _ _ => .bwdVia0
  | .bwdA2Tri _ _ => .bwdA2Tri
  | .bwdA2Via _ _ => .bwdA2Via
  | .bwdA3Tri _ _ => .bwdA3Tri
  | .bwdA3Via _ _ => .bwdA3Via
  | .bwdA4Tri _ _ => .bwdA4Tri
  | .bwdA4Via _ _ => .bwdA4Via
  | .bwdAny _ _ _ _ => .bwdAny

noncomputable def toCycleBase : FacialOneChordPath → FacialCycleBase
  | .triangle s => s.toCycleBase
  | .fwd s hPos => s.toCycleBase hPos
  | .bwd0 s hPos => s.toCycleBase hPos
  | .bwd s hPos => s.toCycleBase hPos
  | .bwdVia0 s hPos => s.toCycleBase hPos
  | .bwdA2Tri s hPos => s.toCycleBase hPos
  | .bwdA2Via s hPos => s.toCycleBase hPos
  | .bwdA3Tri s hPos => s.toCycleBase hPos
  | .bwdA3Via s hPos => s.toCycleBase hPos
  | .bwdA4Tri s hPos => s.toCycleBase hPos
  | .bwdA4Via s hPos => s.toCycleBase hPos
  | .bwdAny s _ _ hPos => s.toCycleBaseAny hPos

theorem reaches_cycle (p : FacialOneChordPath) :
    (p.toCycleBase).embedAfter.isCycle = true ∧
      gf2Sum (p.toCycleBase).chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle (p.toCycleBase).nAfter) = 0 :=
  ⟨(p.toCycleBase).embed_cycle, (p.toCycleBase).charges_odd,
    foldSteps_cycle (p.toCycleBase).nAfter⟩

theorem schedule_matches (p : FacialOneChordPath) :
    (p.chord).schedule = some (p.scheduleOf) := by
  match p with
  | .triangle s =>
    exact CycleChord.schedule_triangle s.chord s.triangle
  | .fwd s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.fwdGe2
      have hs := s.fwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_fwd s.chord s.fwdShort s.fwdGe2 hne
  | .bwd0 s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.bwdGe2
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwd0 s.chord s.a0 s.bwdShort s.bwdGe2 hne
  | .bwd s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have heq := s.bwdEq2
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals, heq] at *
      omega
    exact CycleChord.schedule_bwd s.chord s.aPos s.bwdShort s.bwdEq2 hne
  | .bwdVia0 s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.bwdGe3
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwdVia0 s.chord s.aEq1 s.bwdShort s.bwdGe3 hne
  | .bwdA2Tri s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have heq := s.bwdEq3
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals, heq] at *
      omega
    exact CycleChord.schedule_bwdA2Tri s.chord s.aEq2 s.bwdShort s.bwdEq3 hne
  | .bwdA2Via s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.bwdGe4
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwdA2Via s.chord s.aEq2 s.bwdShort s.bwdGe4 hne
  | .bwdA3Tri s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have heq := s.bwdEq4
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals, heq] at *
      omega
    exact CycleChord.schedule_bwdA3Tri s.chord s.aEq3 s.bwdShort s.bwdEq4 hne
  | .bwdA3Via s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.bwdGe5
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwdA3Via s.chord s.aEq3 s.bwdShort s.bwdGe5 hne
  | .bwdA4Tri s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have heq := s.bwdEq5
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals, heq] at *
      omega
    exact CycleChord.schedule_bwdA4Tri s.chord s.aEq4 s.bwdShort s.bwdEq5 hne
  | .bwdA4Via s _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hge := s.bwdGe6
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwdA4Via s.chord s.aEq4 s.bwdShort s.bwdGe6 hne
  | .bwdAny s ha hb _ =>
    have hne : s.chord.shorterInternals ≠ 1 := by
      have hs := s.bwdShort
      simp only [CycleChord.shorterInternals] at *
      omega
    exact CycleChord.schedule_bwdAny s.chord ha s.bwdShort hb hne

end FacialOneChordPath

/-- Concrete: C₄ diagonal via triangle schedule. -/
noncomputable def c4OneChordPath : FacialOneChordPath :=
  .triangle c4FacialTriangleFold

theorem c4OneChordPath_reaches_cycle :
    c4OneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c4OneChordPath.toCycleBase.nAfter = 3 :=
  ⟨c4OneChordPath.toCycleBase.embed_cycle, rfl⟩

theorem c4OneChordPath_schedule :
    c4OneChordPath.chord.schedule = some .triangle :=
  c4OneChordPath.schedule_matches

/-- Concrete: C₁₀ `{0,5}` via fwd peel. -/
noncomputable def c10FwdOneChordPath : FacialOneChordPath :=
  .fwd c10Chord05Fwd (by decide)

theorem c10FwdOneChordPath_reaches_cycle :
    c10FwdOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c10FwdOneChordPath.toCycleBase.nAfter = 6 ∧
      gf2Sum c10FwdOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c10FwdOneChordPath.toCycleBase.embed_cycle, rfl,
    c10FwdOneChordPath.toCycleBase.charges_odd⟩

theorem c10FwdOneChordPath_schedule :
    c10FwdOneChordPath.chord.schedule = some .fwdPeel :=
  c10FwdOneChordPath.schedule_matches

/-- Concrete: C₉ `{0,5}` via bwd₀ peel. -/
noncomputable def c9BwdOneChordPath : FacialOneChordPath :=
  .bwd0 c9Chord05Bwd (by decide)

theorem c9BwdOneChordPath_reaches_cycle :
    c9BwdOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c9BwdOneChordPath.toCycleBase.nAfter = 6 ∧
      gf2Sum c9BwdOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c9BwdOneChordPath.toCycleBase.embed_cycle, rfl,
    c9BwdOneChordPath.toCycleBase.charges_odd⟩

theorem c9BwdOneChordPath_schedule :
    c9BwdOneChordPath.chord.schedule = some .bwdPeel0 :=
  c9BwdOneChordPath.schedule_matches

/-- Concrete: C₈ `{1,6}` via bwd peel (a≥1, bwd=2). -/
noncomputable def c8BwdOneChordPath : FacialOneChordPath :=
  .bwd c8Chord16BwdTri (by decide)

theorem c8BwdOneChordPath_reaches_cycle :
    c8BwdOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c8BwdOneChordPath.toCycleBase.nAfter = 6 ∧
      gf2Sum c8BwdOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c8BwdOneChordPath.toCycleBase.embed_cycle, rfl,
    c8BwdOneChordPath.toCycleBase.charges_odd⟩

theorem c8BwdOneChordPath_schedule :
    c8BwdOneChordPath.chord.schedule = some .bwdPeel :=
  c8BwdOneChordPath.schedule_matches

/-- Concrete: C₁₀ `{1,7}` via bwdVia0 (a=1, bwd≥3). -/
noncomputable def c10BwdVia0OneChordPath : FacialOneChordPath :=
  .bwdVia0 c10Chord17Via0 (by decide)

theorem c10BwdVia0OneChordPath_reaches_cycle :
    c10BwdVia0OneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c10BwdVia0OneChordPath.toCycleBase.nAfter = 7 ∧
      gf2Sum c10BwdVia0OneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c10BwdVia0OneChordPath.toCycleBase.embed_cycle, rfl,
    c10BwdVia0OneChordPath.toCycleBase.charges_odd⟩

theorem c10BwdVia0OneChordPath_schedule :
    c10BwdVia0OneChordPath.chord.schedule = some .bwdVia0 :=
  c10BwdVia0OneChordPath.schedule_matches

/-- Concrete: C₉ `{2,7}` via bwdA2Tri (a=2, bwd=3). -/
noncomputable def c9BwdA2TriOneChordPath : FacialOneChordPath :=
  .bwdA2Tri c9Chord27A2Tri (by decide)

theorem c9BwdA2TriOneChordPath_reaches_cycle :
    c9BwdA2TriOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c9BwdA2TriOneChordPath.toCycleBase.nAfter = 6 ∧
      gf2Sum c9BwdA2TriOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c9BwdA2TriOneChordPath.toCycleBase.embed_cycle, rfl,
    c9BwdA2TriOneChordPath.toCycleBase.charges_odd⟩

theorem c9BwdA2TriOneChordPath_schedule :
    c9BwdA2TriOneChordPath.chord.schedule = some .bwdA2Tri :=
  c9BwdA2TriOneChordPath.schedule_matches

/-- Concrete: C₁₂ `{2,9}` via bwdA2Via (a=2, bwd≥4). -/
noncomputable def c12BwdA2ViaOneChordPath : FacialOneChordPath :=
  .bwdA2Via c12Chord29A2Via (by decide)

theorem c12BwdA2ViaOneChordPath_reaches_cycle :
    c12BwdA2ViaOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c12BwdA2ViaOneChordPath.toCycleBase.nAfter = 8 ∧
      gf2Sum c12BwdA2ViaOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c12BwdA2ViaOneChordPath.toCycleBase.embed_cycle, rfl,
    c12BwdA2ViaOneChordPath.toCycleBase.charges_odd⟩

theorem c12BwdA2ViaOneChordPath_schedule :
    c12BwdA2ViaOneChordPath.chord.schedule = some .bwdA2Via :=
  c12BwdA2ViaOneChordPath.schedule_matches

/-- Concrete: C₁₁ `{3,9}` via bwdA3Tri (a=3, bwd=4). -/
noncomputable def c11BwdA3TriOneChordPath : FacialOneChordPath :=
  .bwdA3Tri c11Chord39A3Tri (by decide)

theorem c11BwdA3TriOneChordPath_reaches_cycle :
    c11BwdA3TriOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c11BwdA3TriOneChordPath.toCycleBase.nAfter = 7 ∧
      gf2Sum c11BwdA3TriOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c11BwdA3TriOneChordPath.toCycleBase.embed_cycle, rfl,
    c11BwdA3TriOneChordPath.toCycleBase.charges_odd⟩

theorem c11BwdA3TriOneChordPath_schedule :
    c11BwdA3TriOneChordPath.chord.schedule = some .bwdA3Tri :=
  c11BwdA3TriOneChordPath.schedule_matches

/-- Concrete: C₁₃ `{3,10}` via bwdA3Via (a=3, bwd≥5). -/
noncomputable def c13BwdA3ViaOneChordPath : FacialOneChordPath :=
  .bwdA3Via c13Chord310A3Via (by decide)

theorem c13BwdA3ViaOneChordPath_reaches_cycle :
    c13BwdA3ViaOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c13BwdA3ViaOneChordPath.toCycleBase.nAfter = 8 ∧
      gf2Sum c13BwdA3ViaOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c13BwdA3ViaOneChordPath.toCycleBase.embed_cycle, rfl,
    c13BwdA3ViaOneChordPath.toCycleBase.charges_odd⟩

theorem c13BwdA3ViaOneChordPath_schedule :
    c13BwdA3ViaOneChordPath.chord.schedule = some .bwdA3Via :=
  c13BwdA3ViaOneChordPath.schedule_matches

/-- Concrete: C₁₃ `{4,11}` via bwdA4Tri (a=4, bwd=5). -/
noncomputable def c13BwdA4TriOneChordPath : FacialOneChordPath :=
  .bwdA4Tri c13Chord411A4Tri (by decide)

theorem c13BwdA4TriOneChordPath_reaches_cycle :
    c13BwdA4TriOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c13BwdA4TriOneChordPath.toCycleBase.nAfter = 8 ∧
      gf2Sum c13BwdA4TriOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c13BwdA4TriOneChordPath.toCycleBase.embed_cycle, rfl,
    c13BwdA4TriOneChordPath.toCycleBase.charges_odd⟩

theorem c13BwdA4TriOneChordPath_schedule :
    c13BwdA4TriOneChordPath.chord.schedule = some .bwdA4Tri :=
  c13BwdA4TriOneChordPath.schedule_matches

/-- Concrete: C₁₅ `{4,12}` via bwdA4Via (a=4, bwd≥6). -/
noncomputable def c15BwdA4ViaOneChordPath : FacialOneChordPath :=
  .bwdA4Via c15Chord412A4Via (by decide)

theorem c15BwdA4ViaOneChordPath_reaches_cycle :
    c15BwdA4ViaOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c15BwdA4ViaOneChordPath.toCycleBase.nAfter = 9 ∧
      gf2Sum c15BwdA4ViaOneChordPath.toCycleBase.chargesAfter.charges = 1 :=
  ⟨c15BwdA4ViaOneChordPath.toCycleBase.embed_cycle, rfl,
    c15BwdA4ViaOneChordPath.toCycleBase.charges_odd⟩

theorem c15BwdA4ViaOneChordPath_schedule :
    c15BwdA4ViaOneChordPath.chord.schedule = some .bwdA4Via :=
  c15BwdA4ViaOneChordPath.schedule_matches

/-- Concrete: C₁₅ `{5,13}` via parametric bwdAny (a=5). -/
noncomputable def c15BwdAnyOneChordPath : FacialOneChordPath :=
  .bwdAny c15Chord513Bwd (by decide) (by native_decide) (by decide)

theorem c15BwdAnyOneChordPath_reaches_cycle :
    c15BwdAnyOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c15BwdAnyOneChordPath.toCycleBase.nAfter = 9 ∧
      gf2Sum c15BwdAnyOneChordPath.toCycleBase.chargesAfter.charges = 1 := by
  refine ⟨c15BwdAnyOneChordPath.toCycleBase.embed_cycle, ?_,
    c15BwdAnyOneChordPath.toCycleBase.charges_odd⟩
  have h := c15Chord513Bwd.toCycleBaseAny_nAfter (by decide)
  have hn : c15Chord513Bwd.chord.n = 15 := rfl
  have hb : c15Chord513Bwd.chord.bwdInternals = 6 := by native_decide
  change (c15Chord513Bwd.toCycleBaseAny (by decide)).nAfter = 9
  omega

theorem c15BwdAnyOneChordPath_schedule :
    c15BwdAnyOneChordPath.chord.schedule = some .bwdAny :=
  c15BwdAnyOneChordPath.schedule_matches

/-- Concrete: C₁₇ `{5,14}` via parametric bwdAny (a=5, bwd=7). -/
noncomputable def c17BwdAnyOneChordPath : FacialOneChordPath :=
  .bwdAny c17Chord514Bwd (by decide) (by native_decide) (by decide)

theorem c17BwdAnyOneChordPath_reaches_cycle :
    c17BwdAnyOneChordPath.toCycleBase.embedAfter.isCycle = true ∧
      c17BwdAnyOneChordPath.toCycleBase.nAfter = 10 ∧
      gf2Sum c17BwdAnyOneChordPath.toCycleBase.chargesAfter.charges = 1 := by
  refine ⟨c17BwdAnyOneChordPath.toCycleBase.embed_cycle, ?_,
    c17BwdAnyOneChordPath.toCycleBase.charges_odd⟩
  have h := c17Chord514Bwd.toCycleBaseAny_nAfter (by decide)
  have hn : c17Chord514Bwd.chord.n = 17 := rfl
  have hb : c17Chord514Bwd.chord.bwdInternals = 7 := by native_decide
  change (c17Chord514Bwd.toCycleBaseAny (by decide)).nAfter = 10
  omega

theorem c17BwdAnyOneChordPath_schedule :
    c17BwdAnyOneChordPath.chord.schedule = some .bwdAny :=
  c17BwdAnyOneChordPath.schedule_matches

def oneChordDispatchDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_TO_ELIMINATION.md"

end PNPLab.Outerplanar
