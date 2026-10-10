/-
  G6: constructive Whitney ear from a **noncrossing chord diagram**
  on a cycle (Category C).

  Four sorted endpoints `p0 < p1 < p2 < p3 < n`. The ear `CycleChord` is
  **derived** from explicit ear endpoints that match the pairing
  (not supplied as a free `OuterplanarEarPath` witness).

  Pairings:
    - nested  → ear `{p1,p2}` (innermost)
    - disjoint → ear `{p0,p1}` (first block)
-/

import PNPLab.CycleChordEar
import PNPLab.OuterplanarPeel

namespace PNPLab.Outerplanar

open WhitneyEar

/-- Noncrossing pairing of four sorted cycle endpoints. -/
inductive ChordPairing where
  | nested
  | disjoint
  deriving DecidableEq

/--
  Noncrossing two-chord diagram. Ear endpoints `earA < earB` are constrained
  to match the pairing; `toEar` builds a legal `CycleChord`.
-/
structure NoncrossingChordDiagram where
  n : Nat
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  pairing : ChordPairing
  ordered : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < n
  earA : Nat
  earB : Nat
  ear_match :
    match pairing with
    | .nested => earA = p1 ∧ earB = p2
    | .disjoint => earA = p0 ∧ earB = p1
  ear_gap : earA + 2 ≤ earB
  ear_b_lt_n : earB < n
  ear_bwd_pos : 0 < n - (earB - earA) - 1

/-- Derived ear chord (no free path witness). -/
def NoncrossingChordDiagram.toEar (d : NoncrossingChordDiagram) : CycleChord where
  n := d.n
  a := d.earA
  b := d.earB
  gap := d.ear_gap
  b_lt_n := d.ear_b_lt_n
  bwd_pos := d.ear_bwd_pos

theorem NoncrossingChordDiagram.toEar_n (d : NoncrossingChordDiagram) :
    (d.toEar).n = d.n :=
  rfl

theorem NoncrossingChordDiagram.toEar_ab (d : NoncrossingChordDiagram) :
    (d.toEar).a = d.earA ∧ (d.toEar).b = d.earB :=
  ⟨rfl, rfl⟩

/-- Whitney ear extracted from the diagram. -/
theorem NoncrossingChordDiagram.whitney_ear (d : NoncrossingChordDiagram) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  (d.toEar).whitney_ear

def NoncrossingChordDiagram.toEarPath (d : NoncrossingChordDiagram) : OuterplanarEarPath :=
  (d.toEar).toEarPath

theorem NoncrossingChordDiagram.toEarPath_isLegal (d : NoncrossingChordDiagram) :
    (d.toEarPath).isLegal :=
  (d.toEar).toEarPath_isLegal

def NoncrossingChordDiagram.toSketch (d : NoncrossingChordDiagram) : PeeledOuterplanarSketch :=
  (d.toEar).toSketch

/-- After peel, residual carries the derived ear. -/
def NoncrossingChordDiagram.toPeel (d : NoncrossingChordDiagram) (pending : Nat) : PeelSketch where
  coreVertices := d.n
  pendingLeaves := pending
  core := coreWithEar d.n (d.toEar).toEarPath (d.toEar).toEarPath_isLegal

theorem NoncrossingChordDiagram.peelAll_has_ear (d : NoncrossingChordDiagram) (pending : Nat) :
    ∃ p : OuterplanarEarPath, p.isLegal ∧
      ((d.toPeel pending).peelAll).core.ear = some p := by
  refine ⟨(d.toEar).toEarPath, (d.toEar).toEarPath_isLegal, ?_⟩
  simp [NoncrossingChordDiagram.toPeel, PeelSketch.peelAll, PeelSketch.peelFuel_core,
    coreWithEar]

/-- C₈ nested: outer `{0,6}`, inner `{2,4}` — ear derived. -/
def c8NestedDiagram : NoncrossingChordDiagram where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  pairing := .nested
  ordered := by decide
  earA := 2
  earB := 4
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c8NestedDiagram_ear_ends :
    (c8NestedDiagram.toEar).a = 2 ∧ (c8NestedDiagram.toEar).b = 4 :=
  ⟨rfl, rfl⟩

theorem c8NestedDiagram_shorter_one :
    (c8NestedDiagram.toEar).shorterInternals = 1 := by
  native_decide

/-- C₈ disjoint: `{0,2}` and `{4,6}`. -/
def c8DisjointDiagram : NoncrossingChordDiagram where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  pairing := .disjoint
  ordered := by decide
  earA := 0
  earB := 2
  ear_match := ⟨rfl, rfl⟩
  ear_gap := by decide
  ear_b_lt_n := by decide
  ear_bwd_pos := by decide

theorem c8DisjointDiagram_ear_ends :
    (c8DisjointDiagram.toEar).a = 0 ∧ (c8DisjointDiagram.toEar).b = 2 :=
  ⟨rfl, rfl⟩

theorem noncrossing_diagram_ear_bundle (d : NoncrossingChordDiagram) :
    (d.toEarPath).isLegal ∧ (d.toSketch).isCycle = false :=
  ⟨d.toEarPath_isLegal, by
    have : (d.toEar.toSketch).isCycle = false := rfl
    simpa [NoncrossingChordDiagram.toSketch] using this⟩

def chordDiagramEarDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
