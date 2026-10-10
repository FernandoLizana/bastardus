/-
  G6: Whitney ear for **disjoint triple** chords on a cycle (Category C).

  Six endpoints `p0 < … < p5 < n` with mutually disjoint chords
    `{p0,p1}`, `{p2,p3}`, `{p4,p5}`
  (outerplanar). The first chord `{p0,p1}` is a legal ear.
-/

import PNPLab.CycleChordEar
import PNPLab.OuterplanarPeel

namespace PNPLab.Outerplanar

open WhitneyEar

/-- Three mutually disjoint chords on C_n. -/
structure DisjointTripleChords where
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
  /-- First chord is the ear. -/
  ear_ends : ear.a = p0 ∧ ear.b = p1

theorem DisjointTripleChords.whitney_ear (c : DisjointTripleChords) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  c.ear.whitney_ear

def DisjointTripleChords.toEarPath (c : DisjointTripleChords) : OuterplanarEarPath :=
  c.ear.toEarPath

theorem DisjointTripleChords.toEarPath_isLegal (c : DisjointTripleChords) :
    (c.toEarPath).isLegal :=
  c.ear.toEarPath_isLegal

def DisjointTripleChords.toSketch (c : DisjointTripleChords) : PeeledOuterplanarSketch :=
  c.ear.toSketch

def DisjointTripleChords.toPeel (c : DisjointTripleChords) (pending : Nat) : PeelSketch where
  coreVertices := c.n
  pendingLeaves := pending
  core := coreWithEar c.n c.ear.toEarPath c.ear.toEarPath_isLegal

theorem DisjointTripleChords.peelAll_ear (c : DisjointTripleChords) (pending : Nat) :
    ∃ p : OuterplanarEarPath, p.isLegal ∧
      ((c.toPeel pending).peelAll).core.ear = some p := by
  refine ⟨c.ear.toEarPath, c.ear.toEarPath_isLegal, ?_⟩
  simp [DisjointTripleChords.toPeel, PeelSketch.peelAll, PeelSketch.peelFuel_core,
    coreWithEar]

/-- C₁₂ disjoint triple: `{0,2}`, `{4,6}`, `{8,10}`. -/
def c12DisjointTriple : DisjointTripleChords where
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
    a := 0
    b := 2
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c12DisjointTriple_shorter_one :
    c12DisjointTriple.ear.shorterInternals = 1 := by
  native_decide

/-- C₁₅ disjoint triple: `{0,2}`, `{4,9}`, `{11,14}`.
    Residual pair has a long first ear. -/
def c15DisjointTriple : DisjointTripleChords where
  n := 15
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 9
  p4 := 11
  p5 := 14
  ordered := by decide
  ear := {
    n := 15
    a := 0
    b := 2
    gap := by decide
    b_lt_n := by decide
    bwd_pos := by decide
  }
  ear_n := rfl
  ear_ends := ⟨rfl, rfl⟩

theorem c15DisjointTriple_shorter_one :
    c15DisjointTriple.ear.shorterInternals = 1 := by
  native_decide

theorem disjoint_triple_ear_bundle (c : DisjointTripleChords) :
    (c.toEarPath).isLegal ∧ (c.toSketch).isCycle = false :=
  ⟨c.toEarPath_isLegal, by
    have : (c.ear.toSketch).isCycle = false := rfl
    simpa [DisjointTripleChords.toSketch] using this⟩

def disjointTripleChordsDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
