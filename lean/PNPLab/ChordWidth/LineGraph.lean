/-
  Line graph scaffolding for the ChordWidth pivot (Fase 1).

  Reuses Mathlib `SimpleGraph.lineGraph` (v4.32.0); PNPLab adds naming
  aliases and smoke lemmas for cycle + chord graphs.
-/

import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace PNPLab.ChordWidth

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- PNPLab alias: line graph `L(G)` with vertices = edges of `G`. -/
abbrev lineGraph (G : SimpleGraph V) : SimpleGraph G.edgeSet :=
  G.lineGraph

theorem lineGraph_is_simpleGraph (G : SimpleGraph V) :
    lineGraph G = G.lineGraph :=
  rfl

/-- Adjacency in the line graph: distinct edges sharing a vertex. -/
theorem lineGraph_adj_iff {e₁ e₂ : G.edgeSet} :
    (lineGraph G).Adj e₁ e₂ ↔
      e₁ ≠ e₂ ∧ ∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V) :=
  G.lineGraph_adj_iff_exists

def lineGraphDoc : String :=
  "Mathlib.Combinatorics.SimpleGraph.LineGraph (v4.32.0); vertices = G.edgeSet"

end PNPLab.ChordWidth
