/-
  k-chord diagrams on C_n: cycle + matching of k vertex pairs.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import PNPLab.ChordWidth.LineGraph

namespace PNPLab.ChordWidth

open SimpleGraph

structure Chord (n : Nat) where
  u : Fin n
  v : Fin n
  ne : u ≠ v

namespace Chord

def isCycleEdge (n : Nat) (c : Chord n) : Prop :=
  c.u.val + 1 = c.v.val ∨ c.v.val + 1 = c.u.val ∨
    (c.u.val = n - 1 ∧ c.v.val = 0) ∨ (c.v.val = n - 1 ∧ c.u.val = 0)

end Chord

structure ChordDiagram (n k : Nat) where
  n_pos : 0 < n
  chords : Fin k → Chord n
  atMostOne : Function.Injective chords
  realChords : ∀ i : Fin k, ¬ Chord.isCycleEdge n (chords i)

namespace ChordDiagram

def cycleGraph (D : ChordDiagram n k) : SimpleGraph (Fin n) :=
  SimpleGraph.cycleGraph n

def chordEdgeSet (D : ChordDiagram n k) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin k)).image fun i =>
    Sym2.mk (D.chords i).u (D.chords i).v

def underlyingGraph (D : ChordDiagram n k) : SimpleGraph (Fin n) :=
  D.cycleGraph ⊔ SimpleGraph.fromEdgeSet D.chordEdgeSet

def lineGraph (D : ChordDiagram n k) [Fintype D.underlyingGraph.edgeSet]
    [DecidableEq D.underlyingGraph.edgeSet] :
    SimpleGraph D.underlyingGraph.edgeSet :=
  D.underlyingGraph.lineGraph

def chordDiagramDoc : String :=
  "ChordDiagram n k; underlyingGraph; lineGraph; intersectionGraph en IntersectionGraph.lean."

end ChordDiagram

end PNPLab.ChordWidth
