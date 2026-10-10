/-
  G6: Whitney ear for **nested triple** chords on a cycle (Category C).

  Six endpoints `p0 < … < p5 < n` with nested chords
    `{p0,p5}`, `{p1,p4}`, `{p2,p3}`
  (fully nested, outerplanar). The innermost chord `{p2,p3}` is a legal ear.
-/

import PNPLab.CycleChordEar
import PNPLab.OuterplanarPeel

namespace PNPLab.Outerplanar

open WhitneyEar

/-- Fully nested triple of chords on C_n. -/
structure NestedTripleChords where
  n : Nat
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p4 : Nat
  p5 : Nat
  ordered :
    p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ p4 < p5 ∧ p5 < n
  ear : CycleChord
  ear_n : ear.n = n
  /-- Innermost chord is the ear. -/
  ear_ends : ear.a = p2 ∧ ear.b = p3

theorem NestedTripleChords.whitney_ear (c : NestedTripleChords) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  c.ear.whitney_ear

def NestedTripleChords.toEarPath (c : NestedTripleChords) : OuterplanarEarPath :=
  c.ear.toEarPath

theorem NestedTripleChords.toEarPath_isLegal (c : NestedTripleChords) :
    (c.toEarPath).isLegal :=
  c.ear.toEarPath_isLegal

def NestedTripleChords.toSketch (c : NestedTripleChords) : PeeledOuterplanarSketch :=
  c.ear.toSketch

/-- After tree peel, residual is the non-cycle sketch from the innermost ear. -/
def NestedTripleChords.toPeel (c : NestedTripleChords) (pending : Nat) : PeelSketch where
  coreVertices := c.n
  pendingLeaves := pending
  core := coreWithEar c.n c.ear.toEarPath c.ear.toEarPath_isLegal

theorem NestedTripleChords.peelAll_ear (c : NestedTripleChords) (pending : Nat) :
    ∃ p : OuterplanarEarPath, p.isLegal ∧
      ((c.toPeel pending).peelAll).core.ear = some p := by
  refine ⟨c.ear.toEarPath, c.ear.toEarPath_isLegal, ?_⟩
  simp [NestedTripleChords.toPeel, PeelSketch.peelAll, PeelSketch.peelFuel_core,
    coreWithEar]

/-- C₁₂ nested triple: chords `{0,10}`, `{2,8}`, `{4,6}`. -/
def c12NestedTriple : NestedTripleChords where
  n := 12
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  p4 := 8
  p5 := 10
  ordered := by decide
  ear := {
    n := 12
    a := 4
    b := 6
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c12NestedTriple_shorter_one :
    c12NestedTriple.ear.shorterInternals = 1 := by
  native_decide

/-- C₁₅ nested triple: chords `{0,11}`, `{2,7}`, `{4,6}`.
    Residual pair is C₁₄-style `{0,10}`/`{2,6}` (long mid ear). -/
def c15NestedTriple : NestedTripleChords where
  n := 15
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  p4 := 7
  p5 := 11
  ordered := by decide
  ear := {
    n := 15
    a := 4
    b := 6
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c15NestedTriple_shorter_one :
    c15NestedTriple.ear.shorterInternals = 1 := by
  native_decide

theorem nested_triple_ear_bundle (c : NestedTripleChords) :
    (c.toEarPath).isLegal ∧ (c.toSketch).isCycle = false :=
  ⟨c.toEarPath_isLegal, by
    have : (c.ear.toSketch).isCycle = false := rfl
    simpa [NestedTripleChords.toSketch] using this⟩

def nestedTripleChordsDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
