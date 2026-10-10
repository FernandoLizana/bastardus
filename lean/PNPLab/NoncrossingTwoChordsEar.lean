/-
  G6: Whitney ear for C_n + **two noncrossing** chords (Category C).

  Four distinct endpoints `p0 < p1 < p2 < p3 < n`. Noncrossing pairings:
    - nested: chords `{p0,p3}` and `{p1,p2}`
    - disjoint: chords `{p0,p1}` and `{p2,p3}`

  Constructive ear: reuse `CycleChord` on one of the two chords
  (inner for nested; first for disjoint).
-/

import PNPLab.CycleChordEar

namespace PNPLab.Outerplanar

open WhitneyEar

/-- Noncrossing pairing of four sorted cycle endpoints. -/
inductive NoncrossingPairing where
  | nested
  | disjoint

/-- C_n + two noncrossing chords, with an explicit legal ear chord. -/
structure NoncrossingTwoChords where
  n : Nat
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  pairing : NoncrossingPairing
  ordered : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < n
  ear : CycleChord
  ear_n : ear.n = n
  /-- Ear endpoints match the pairing choice. -/
  ear_ends :
    match pairing with
    | .nested => ear.a = p1 ∧ ear.b = p2
    | .disjoint => ear.a = p0 ∧ ear.b = p1

theorem NoncrossingTwoChords.whitney_ear (c : NoncrossingTwoChords) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  c.ear.whitney_ear

def NoncrossingTwoChords.toEarPath (c : NoncrossingTwoChords) : OuterplanarEarPath :=
  c.ear.toEarPath

theorem NoncrossingTwoChords.toEarPath_isLegal (c : NoncrossingTwoChords) :
    (c.toEarPath).isLegal :=
  c.ear.toEarPath_isLegal

def NoncrossingTwoChords.toSketch (c : NoncrossingTwoChords) : PeeledOuterplanarSketch :=
  c.ear.toSketch

/-- C₈ nested: outer `{0,6}`, inner `{2,4}`. -/
def c8Nested : NoncrossingTwoChords where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  pairing := .nested
  ordered := by decide
  ear := {
    n := 8
    a := 2
    b := 4
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c8Nested_shorter_one :
    c8Nested.ear.shorterInternals = 1 := by
  native_decide

/-- C₈ disjoint: `{0,2}` and `{4,6}`. -/
def c8Disjoint : NoncrossingTwoChords where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  pairing := .disjoint
  ordered := by decide
  ear := {
    n := 8
    a := 0
    b := 2
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c8Disjoint_shorter_one :
    c8Disjoint.ear.shorterInternals = 1 := by
  native_decide

theorem noncrossing_two_chords_ear_bundle (c : NoncrossingTwoChords) :
    (c.toEarPath).isLegal ∧ (c.toSketch).isCycle = false :=
  ⟨c.toEarPath_isLegal, by
    have : (c.ear.toSketch).isCycle = false := rfl
    simpa [NoncrossingTwoChords.toSketch] using this⟩

def noncrossingTwoChordsEarDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
