/-
  Intersection graph of a chord diagram: vertices = chords, adjacency = crossing.
-/

import PNPLab.ChordWidth.ChordDiagram

namespace PNPLab.ChordWidth

open SimpleGraph

variable {n k : Nat}

def chordsCrossOnCycle (n : Nat) (c₁ c₂ : Chord n) : Prop :=
  let a := min c₁.u.val c₁.v.val
  let b := max c₁.u.val c₁.v.val
  let c := min c₂.u.val c₂.v.val
  let d := max c₂.u.val c₂.v.val
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

theorem chordsCrossOnCycle_symm (n : Nat) (c₁ c₂ : Chord n) :
    chordsCrossOnCycle n c₁ c₂ ↔ chordsCrossOnCycle n c₂ c₁ := by
  unfold chordsCrossOnCycle
  constructor <;> intro h <;> cases h <;> omega

def ChordDiagram.intersectionGraphAdj (D : ChordDiagram n k) (i j : Fin k) : Prop :=
  i ≠ j ∧ chordsCrossOnCycle n (D.chords i) (D.chords j)

instance ChordDiagram.decidableIntersectionGraphAdj (D : ChordDiagram n k) (i j : Fin k) :
    Decidable (D.intersectionGraphAdj i j) := by
  unfold ChordDiagram.intersectionGraphAdj chordsCrossOnCycle
  infer_instance

theorem ChordDiagram.intersectionGraphAdj_symm (D : ChordDiagram n k) :
    Std.Symm (D.intersectionGraphAdj) where
  symm := fun {i j} h => ⟨h.1.symm, (chordsCrossOnCycle_symm n _ _).mp h.2⟩

theorem ChordDiagram.intersectionGraphAdj_irrefl (D : ChordDiagram n k) :
    Std.Irrefl (D.intersectionGraphAdj) where
  irrefl i := fun h => h.1 rfl

def ChordDiagram.intersectionGraph (D : ChordDiagram n k) : SimpleGraph (Fin k) where
  Adj := D.intersectionGraphAdj
  symm := D.intersectionGraphAdj_symm
  loopless := D.intersectionGraphAdj_irrefl

def intersectionGraphDoc : String :=
  "I(D): vértices = acordes; arista ⟺ cruce en C_n."

end PNPLab.ChordWidth
