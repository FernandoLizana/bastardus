/-
  Total triple-chord peel dispatch (Category C / G6).

  Packs Nested/Disjoint Triple Len2 + Long inductions into a unified facial
  path / schedule, mirroring `OuterplanarTwoChordTotal`.

  Nested residual after innermost fold is always a long mid ear
  (`residual_innerLenGe3`); disjoint residual is len2 or long.
-/

import PNPLab.NestedTripleLongToCycle
import PNPLab.DisjointTripleLongToCycle
import PNPLab.NestedTripleToCycle
import PNPLab.DisjointTripleToCycle
import PNPLab.OuterplanarTwoChordTotal

namespace PNPLab.Outerplanar

/-- Which triple-chord schedule applies after the first triangle fold. -/
inductive TripleChordSchedule where
  | nestedLong
  | disjointLen2
  | disjointLong
  deriving DecidableEq, Repr

/-- Nested residual mid ear is always length ≥ 3 (innermost △ forces it). -/
theorem NestedTripleChords.residual_innerLenGe3 (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.residualNestedPair hlen2 hEarBwd).innerLenGe3 := by
  simp only [NoncrossingChordDiagram.innerLenGe3,
    NestedTripleChords.residualNestedPair]
  have ord := c.ordered
  simp [NestedTripleChords.innerLen2] at hlen2
  -- p1 < p2 < p3 = p2+2 < p4 ⇒ p4 ≥ p1+4 ⇒ (p4-1) ≥ p1+3
  omega

/-- Nested triple schedule: residual is always the long-ear arm. -/
def NestedTripleChords.schedule (c : NestedTripleChords)
    (_hlen2 : c.innerLen2)
    (_hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    Option TripleChordSchedule :=
  some .nestedLong

theorem NestedTripleChords.schedule_isSome (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.schedule hlen2 hEarBwd).isSome = true :=
  rfl

/-- Disjoint triple schedule from residual first-ear length. -/
def DisjointTripleChords.schedule (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    Option TripleChordSchedule :=
  let d := c.residualDisjointPair hlen2 hFirstGap hEarBwd
  if d.earB = d.earA + 2 then some .disjointLen2
  else if d.earA + 3 ≤ d.earB then some .disjointLong
  else none

theorem DisjointTripleChords.schedule_isSome (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    (c.schedule hlen2 hFirstGap hEarBwd).isSome = true := by
  simp only [DisjointTripleChords.schedule]
  set d := c.residualDisjointPair hlen2 hFirstGap hEarBwd
  rcases d.ear_len_dichotomy with h2 | h3
  · simp [h2]
  · have hne : d.earB ≠ d.earA + 2 := by omega
    simp [hne, h3]

/-- Disjoint triple with residual already length-2 → `DisjointLen2Induction`. -/
structure DisjointTripleLen2Induction where
  triple : DisjointTripleChords
  hlen2 : triple.firstLen2
  hFirstGap : triple.p2 + 2 ≤ triple.p3
  hEarBwd : 0 < (triple.n - 1) - ((triple.p3 - 1) - (triple.p2 - 1)) - 1
  len2 : DisjointLen2Induction
  residual_eq :
    len2.diagram = triple.residualDisjointPair hlen2 hFirstGap hEarBwd

noncomputable def DisjointTripleLen2Induction.toCycleBase
    (s : DisjointTripleLen2Induction) : FacialCycleBase :=
  s.len2.toCycleBase

theorem DisjointTripleLen2Induction.after_first_not_cycle
    (s : DisjointTripleLen2Induction) :
    (s.triple.afterFirstTriangle s.hlen2 s.hFirstGap s.hEarBwd).isCycle = false :=
  s.triple.afterFirstTriangle_not_cycle s.hlen2 s.hFirstGap s.hEarBwd

theorem DisjointTripleLen2Induction.reaches_cycle (s : DisjointTripleLen2Induction) :
    let b := s.toCycleBase
    (s.triple.afterFirstTriangle s.hlen2 s.hFirstGap s.hEarBwd).isCycle = false ∧
      s.len2.midEmbed.isCycle = false ∧
      b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  let h := s.len2.reaches_cycle
  ⟨s.after_first_not_cycle, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Unified facial path for noncrossing triples. -/
inductive FacialTriplePath where
  | nestedLong (s : NestedTripleLongInduction)
  | disjointLen2 (s : DisjointTripleLen2Induction)
  | disjointLong (s : DisjointTripleLongInduction)

def FacialTriplePath.scheduleTag (p : FacialTriplePath) : TripleChordSchedule :=
  match p with
  | .nestedLong _ => .nestedLong
  | .disjointLen2 _ => .disjointLen2
  | .disjointLong _ => .disjointLong

noncomputable def FacialTriplePath.toCycleBase (p : FacialTriplePath) :
    FacialCycleBase :=
  match p with
  | .nestedLong s => s.toCycleBase
  | .disjointLen2 s => s.toCycleBase
  | .disjointLong s => s.toCycleBase

theorem FacialTriplePath.reaches_cycle (p : FacialTriplePath) :
    let b := p.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle b.nAfter) = 0 :=
  match p with
  | .nestedLong s =>
      let h := s.reaches_cycle
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | .disjointLen2 s =>
      let h := s.reaches_cycle
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | .disjointLong s =>
      let h := s.reaches_cycle
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FacialTriplePath.schedule_matches (p : FacialTriplePath) :
    match p with
    | .nestedLong s =>
        s.triple.schedule s.hlen2 s.hEarBwd = some .nestedLong
    | .disjointLen2 s =>
        s.triple.schedule s.hlen2 s.hFirstGap s.hEarBwd = some .disjointLen2
    | .disjointLong s =>
        s.triple.schedule s.hlen2 s.hFirstGap s.hEarBwd = some .disjointLong := by
  match p with
  | .nestedLong s =>
      rfl
  | .disjointLen2 s =>
      have heq := s.residual_eq
      have h2 : s.len2.diagram.earB = s.len2.diagram.earA + 2 := s.len2.firstLen2
      simp only [DisjointTripleChords.schedule]
      simp [heq.symm, h2]
  | .disjointLong s =>
      have heq := s.residual_eq
      have hlen : s.longEar.diagram.firstLenGe3 := s.longEar.hlen
      simp only [NoncrossingChordDiagram.firstLenGe3] at hlen
      have hne : s.longEar.diagram.earB ≠ s.longEar.diagram.earA + 2 := by omega
      simp only [DisjointTripleChords.schedule]
      simp [heq.symm, hne, hlen]

/-- C₁₂ nested triple via long residual path. -/
noncomputable def c12NestedTripleLongInduction : NestedTripleLongInduction where
  triple := c12NestedTriple
  hlen2 := by native_decide
  hEarBwd := by decide
  longEar := {
    diagram := c12NestedPair
    nested := rfl
    hlen := by native_decide
    hEarBwd := by decide
    hOuter := by decide
    hOuterBwd := by decide
    hOuterNPos := by native_decide
  }
  residual_eq := rfl

noncomputable def c12NestedTriplePath : FacialTriplePath :=
  .nestedLong c12NestedTripleLongInduction

theorem c12Nested_triplePath_reaches_cycle :
    let b := c12NestedTriplePath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c12NestedTriple.schedule (by native_decide) (by decide) = some .nestedLong :=
  let h := c12NestedTriplePath.reaches_cycle
  ⟨h.1, h.2.1, rfl⟩

/-- C₁₅ nested triple long via unified path. -/
noncomputable def c15NestedTriplePath : FacialTriplePath :=
  .nestedLong c15NestedTripleLongInduction

theorem c15Nested_triplePath_reaches_cycle :
    let b := c15NestedTriplePath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 :=
  let h := c15NestedTriplePath.reaches_cycle
  ⟨h.1, h.2.1⟩

/-- C₁₂ disjoint triple len-2 residual via unified path. -/
noncomputable def c12DisjointTripleLen2Pack : DisjointTripleLen2Induction where
  triple := c12DisjointTriple
  hlen2 := by native_decide
  hFirstGap := by decide
  hEarBwd := by decide
  len2 := c12DisjointTripleLen2Induction
  residual_eq := rfl

noncomputable def c12DisjointTriplePath : FacialTriplePath :=
  .disjointLen2 c12DisjointTripleLen2Pack

theorem c12Disjoint_triplePath_reaches_cycle :
    let b := c12DisjointTriplePath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c12DisjointTriple.schedule (by native_decide) (by decide) (by decide) =
        some .disjointLen2 :=
  let h := c12DisjointTriplePath.reaches_cycle
  ⟨h.1, h.2.1, c12DisjointTriplePath.schedule_matches⟩

/-- C₁₅ disjoint triple long via unified path. -/
noncomputable def c15DisjointTriplePath : FacialTriplePath :=
  .disjointLong c15DisjointTripleLongInduction

theorem c15Disjoint_triplePath_reaches_cycle :
    let b := c15DisjointTriplePath.toCycleBase
    b.embedAfter.isCycle = true ∧
      gf2Sum b.chargesAfter.charges = 1 ∧
      c15DisjointTriple.schedule (by native_decide) (by decide) (by decide) =
        some .disjointLong :=
  let h := c15DisjointTriplePath.reaches_cycle
  ⟨h.1, h.2.1, c15DisjointTriplePath.schedule_matches⟩

theorem tripleChord_schedule_bundle_nested (c : NestedTripleChords)
    (hlen2 : c.innerLen2)
    (hEarBwd : 0 < (c.n - 1) - ((c.p4 - 1) - c.p1) - 1) :
    (c.schedule hlen2 hEarBwd).isSome = true ∧
      (c.residualNestedPair hlen2 hEarBwd).innerLenGe3 :=
  ⟨c.schedule_isSome hlen2 hEarBwd, c.residual_innerLenGe3 hlen2 hEarBwd⟩

theorem tripleChord_schedule_bundle_disjoint (c : DisjointTripleChords)
    (hlen2 : c.firstLen2)
    (hFirstGap : c.p2 + 2 ≤ c.p3)
    (hEarBwd : 0 < (c.n - 1) - ((c.p3 - 1) - (c.p2 - 1)) - 1) :
    (c.schedule hlen2 hFirstGap hEarBwd).isSome = true :=
  c.schedule_isSome hlen2 hFirstGap hEarBwd

def tripleChordTotalDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
