/-
  Total two-chord peel dispatch (Category C / G6).

  Packs existing Nested/Disjoint Len2 + LongEar inductions into a diagram-level
  schedule / facial path / `toCycleBase`, mirroring `OuterplanarOneChordTotal`.

  Side conditions (outerBwd, secondGap, peel hyps, …) remain packaged in the
  induction witnesses — the schedule only classifies pairing × ear length.
-/

import PNPLab.NestedLongEarToCycle
import PNPLab.DisjointLongEarToCycle

namespace PNPLab.Outerplanar

/-- Which two-chord schedule applies to a noncrossing diagram. -/
inductive TwoChordSchedule where
  | nestedLen2
  | nestedLong
  | disjointLen2
  | disjointLong
  deriving DecidableEq, Repr

/-- Ear is length-2 or longer (from `ear_gap`). -/
theorem NoncrossingChordDiagram.ear_len_dichotomy (d : NoncrossingChordDiagram) :
    d.earB = d.earA + 2 ∨ d.earA + 3 ≤ d.earB := by
  have := d.ear_gap
  omega

/-- Combinatorial schedule tag from pairing and ear length. -/
def NoncrossingChordDiagram.schedule (d : NoncrossingChordDiagram) :
    Option TwoChordSchedule :=
  match d.pairing with
  | .nested =>
      if d.earB = d.earA + 2 then some .nestedLen2
      else if d.earA + 3 ≤ d.earB then some .nestedLong
      else none
  | .disjoint =>
      if d.earB = d.earA + 2 then some .disjointLen2
      else if d.earA + 3 ≤ d.earB then some .disjointLong
      else none

theorem NoncrossingChordDiagram.schedule_isSome (d : NoncrossingChordDiagram) :
    (d.schedule).isSome = true := by
  cases h : d.pairing with
  | nested =>
      simp only [NoncrossingChordDiagram.schedule, h]
      rcases d.ear_len_dichotomy with h2 | h3
      · simp [h2]
      · have hne : d.earB ≠ d.earA + 2 := by omega
        simp [hne, h3]
  | disjoint =>
      simp only [NoncrossingChordDiagram.schedule, h]
      rcases d.ear_len_dichotomy with h2 | h3
      · simp [h2]
      · have hne : d.earB ≠ d.earA + 2 := by omega
        simp [hne, h3]

/-- Unified facial path: nested/disjoint × len2/long. -/
inductive FacialTwoChordPath where
  | nestedLen2 (s : NestedLen2Induction)
  | nestedLong (s : NestedLongEarInduction)
  | disjointLen2 (s : DisjointLen2Induction)
  | disjointLong (s : DisjointLongEarInduction)

def FacialTwoChordPath.diagram (p : FacialTwoChordPath) : NoncrossingChordDiagram :=
  match p with
  | .nestedLen2 s => s.diagram
  | .nestedLong s => s.diagram
  | .disjointLen2 s => s.diagram
  | .disjointLong s => s.diagram

def FacialTwoChordPath.scheduleTag (p : FacialTwoChordPath) : TwoChordSchedule :=
  match p with
  | .nestedLen2 _ => .nestedLen2
  | .nestedLong _ => .nestedLong
  | .disjointLen2 _ => .disjointLen2
  | .disjointLong _ => .disjointLong

noncomputable def FacialTwoChordPath.toCycleBase (p : FacialTwoChordPath) :
    FacialCycleBase :=
  match p with
  | .nestedLen2 s => s.toCycleBase
  | .nestedLong s => s.toCycleBase
  | .disjointLen2 s => s.toCycleBase
  | .disjointLong s => s.toCycleBase

theorem FacialTwoChordPath.reaches_cycle (p : FacialTwoChordPath) :
    let b := p.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  match p with
  | .nestedLen2 s =>
      let h := s.reaches_cycle
      ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  | .nestedLong s =>
      let h := s.reaches_cycle
      ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  | .disjointLen2 s =>
      let h := s.reaches_cycle
      ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  | .disjointLong s =>
      let h := s.reaches_cycle
      ⟨h.2.1, h.2.2.1, h.2.2.2⟩

theorem FacialTwoChordPath.schedule_matches (p : FacialTwoChordPath) :
    (p.diagram.schedule) = some p.scheduleTag := by
  match p with
  | .nestedLen2 s =>
      have hn : s.diagram.pairing = .nested := s.nested
      have h2 : s.diagram.earB = s.diagram.earA + 2 := s.innerLen2
      simp [FacialTwoChordPath.diagram, FacialTwoChordPath.scheduleTag,
        NoncrossingChordDiagram.schedule, hn, h2]
  | .nestedLong s =>
      have hn : s.diagram.pairing = .nested := s.nested
      have hlen : s.diagram.innerLenGe3 := s.hlen
      simp only [NoncrossingChordDiagram.innerLenGe3] at hlen
      have hne : ¬ (s.diagram.earB = s.diagram.earA + 2) := by omega
      simp [FacialTwoChordPath.diagram, FacialTwoChordPath.scheduleTag,
        NoncrossingChordDiagram.schedule, hn, hne, hlen]
  | .disjointLen2 s =>
      have hd : s.diagram.pairing = .disjoint := s.disjoint
      have h2 : s.diagram.earB = s.diagram.earA + 2 := s.firstLen2
      simp [FacialTwoChordPath.diagram, FacialTwoChordPath.scheduleTag,
        NoncrossingChordDiagram.schedule, hd, h2]
  | .disjointLong s =>
      have hd : s.diagram.pairing = .disjoint := s.disjoint
      have hlen : s.diagram.firstLenGe3 := s.hlen
      simp only [NoncrossingChordDiagram.firstLenGe3] at hlen
      have hne : ¬ (s.diagram.earB = s.diagram.earA + 2) := by omega
      simp [FacialTwoChordPath.diagram, FacialTwoChordPath.scheduleTag,
        NoncrossingChordDiagram.schedule, hd, hne, hlen]

/-- Smoke: C₈ nested len-2 via unified path. -/
noncomputable def c8NestedTwoChordPath : FacialTwoChordPath :=
  .nestedLen2 c8NestedLen2Induction

theorem c8Nested_twoChord_reaches_cycle :
    let b := c8NestedTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c8NestedTwoChordPath.diagram.schedule = some .nestedLen2 :=
  let h := c8NestedTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1, c8NestedTwoChordPath.schedule_matches⟩

/-- Smoke: C₁₂ nested long outer via unified path. -/
noncomputable def c12NestedTwoChordPath : FacialTwoChordPath :=
  .nestedLen2 c12NestedLen2Induction

theorem c12Nested_twoChord_reaches_cycle :
    let b := c12NestedTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c12NestedTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1⟩

/-- Smoke: C₁₄ nested long ear via unified path. -/
noncomputable def c14NestedTwoChordPath : FacialTwoChordPath :=
  .nestedLong c14NestedLongEarInduction

theorem c14Nested_twoChord_reaches_cycle :
    let b := c14NestedTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c14NestedTwoChordPath.diagram.schedule = some .nestedLong :=
  let h := c14NestedTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1, c14NestedTwoChordPath.schedule_matches⟩

/-- Smoke: C₈ disjoint len-2 via unified path. -/
noncomputable def c8DisjointTwoChordPath : FacialTwoChordPath :=
  .disjointLen2 c8DisjointLen2Induction

theorem c8Disjoint_twoChord_reaches_cycle :
    let b := c8DisjointTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c8DisjointTwoChordPath.diagram.schedule = some .disjointLen2 :=
  let h := c8DisjointTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1, c8DisjointTwoChordPath.schedule_matches⟩

/-- Smoke: C₁₂ disjoint long second via unified path. -/
noncomputable def c12DisjointTwoChordPath : FacialTwoChordPath :=
  .disjointLen2 c12DisjointLen2Induction

theorem c12Disjoint_twoChord_reaches_cycle :
    let b := c12DisjointTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c12DisjointTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1⟩

/-- Smoke: C₁₄ disjoint long ear via unified path. -/
noncomputable def c14DisjointTwoChordPath : FacialTwoChordPath :=
  .disjointLong c14DisjointLongEarInduction

theorem c14Disjoint_twoChord_reaches_cycle :
    let b := c14DisjointTwoChordPath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c14DisjointTwoChordPath.diagram.schedule = some .disjointLong :=
  let h := c14DisjointTwoChordPath.reaches_cycle
  ⟨h.1, h.2.1, c14DisjointTwoChordPath.schedule_matches⟩

/-- Every diagram has a schedule tag (pairing × ear length). -/
theorem twoChord_schedule_bundle (d : NoncrossingChordDiagram) :
    (d.schedule).isSome = true ∧
      (d.earB = d.earA + 2 ∨ d.earA + 3 ≤ d.earB) :=
  ⟨d.schedule_isSome, d.ear_len_dichotomy⟩

def twoChordTotalDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
