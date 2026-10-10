/-
  CrossingEndpoints → graph / Python-matching `_edge_var_map` scaffolding
  (Category C / G5 parametric gap).

  Shared foundation for:
  - non-pack Closure₃(G_e) synthesis (graph + edge vars first)
  - parametric global-edge residual iso (edgeVar as a function of endpoints)

  `CrossingEndpointsTseitin.tseitinAxioms` matches Python `_all_axioms`;
  `CrossingEndpointsClosure3.closure3` saturates on c5 smokes; ∀e + residual XOR open.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import PNPLab.CrossingChordsToArcs

namespace PNPLab.Bicyclic

open SimpleGraph

/-- Crossing chords from sorted endpoints: `(p0,p2)` and `(p1,p3)`. -/
def CrossingEndpoints.chord1 (e : CrossingEndpoints) : Nat × Nat :=
  if e.p0 ≤ e.p2 then (e.p0, e.p2) else (e.p2, e.p0)

def CrossingEndpoints.chord2 (e : CrossingEndpoints) : Nat × Nat :=
  if e.p1 ≤ e.p3 then (e.p1, e.p3) else (e.p3, e.p1)

/-- Undirected edge as sorted pair (matches Python `tuple(sorted(e))`). -/
def sortedEdge (u v : Nat) : Nat × Nat :=
  if u ≤ v then (u, v) else (v, u)

/-- Lex order on sorted pairs (Python `sorted` on edge tuples). -/
def pairLe (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

def insertSortedPair (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if pairLe x y then x :: y :: ys else y :: insertSortedPair x ys

def sortEdgePairs : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insertSortedPair x (sortEdgePairs xs)

/-- Cycle edges `{i, i+1 mod n}` as sorted pairs. -/
def CrossingEndpoints.cycleEdges (e : CrossingEndpoints) : List (Nat × Nat) :=
  (List.range e.n).map fun i => sortedEdge i ((i + 1) % e.n)

/--
  All undirected edges of C_n + two crossing chords, sorted exactly as Python
  `_edge_var_map` keys.
-/
def CrossingEndpoints.edgeList (e : CrossingEndpoints) : List (Nat × Nat) :=
  sortEdgePairs (e.cycleEdges ++ [e.chord1, e.chord2])

/-- 1-based edge variable id, or `none` if `{u,v}` is not an edge. -/
def CrossingEndpoints.edgeVar (e : CrossingEndpoints) (u v : Nat) : Option Nat :=
  let p := sortedEdge u v
  let rec go (i : Nat) : List (Nat × Nat) → Option Nat
    | [] => none
    | y :: ys => if y = p then some (i + 1) else go (i + 1) ys
  go 0 e.edgeList

/-- Smoke endpoints: ofold instance C₅ + (0,2),(1,3). -/
def c5OfoldEndpoints : CrossingEndpoints where
  n := 5
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  ordered := by decide

/-- Smoke endpoints: alt1 instance C₅ + (0,2),(1,4). -/
def c5Alt1Endpoints : CrossingEndpoints where
  n := 5
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 4
  ordered := by decide

/-- Vres-collision witness A (catalog idx 10): C₆ endpoints `0,2,3,4`, arcs `(1,0,0,1)`. -/
def c6Endpoints0234 : CrossingEndpoints where
  n := 6
  p0 := 0
  p1 := 2
  p2 := 3
  p3 := 4
  ordered := by decide

/-- Vres-collision witness B (catalog idx 18): same `(n, toArcs, Vres)`, different perm dst. -/
def c6Endpoints1345 : CrossingEndpoints where
  n := 6
  p0 := 1
  p1 := 3
  p2 := 4
  p3 := 5
  ordered := by decide

theorem c5Ofold_edgeList :
    c5OfoldEndpoints.edgeList =
      [(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)] := by
  native_decide

theorem c5Ofold_edgeVar_map :
    c5OfoldEndpoints.edgeVar 0 1 = some 1 ∧
      c5OfoldEndpoints.edgeVar 0 2 = some 2 ∧
      c5OfoldEndpoints.edgeVar 0 4 = some 3 ∧
      c5OfoldEndpoints.edgeVar 1 2 = some 4 ∧
      c5OfoldEndpoints.edgeVar 1 3 = some 5 ∧
      c5OfoldEndpoints.edgeVar 2 3 = some 6 ∧
      c5OfoldEndpoints.edgeVar 3 4 = some 7 := by
  native_decide

theorem c5Alt1_edgeList :
    c5Alt1Endpoints.edgeList =
      [(0, 1), (0, 2), (0, 4), (1, 2), (1, 4), (2, 3), (3, 4)] := by
  native_decide

theorem c5Alt1_edgeVar_map :
    c5Alt1Endpoints.edgeVar 0 1 = some 1 ∧
      c5Alt1Endpoints.edgeVar 0 2 = some 2 ∧
      c5Alt1Endpoints.edgeVar 0 4 = some 3 ∧
      c5Alt1Endpoints.edgeVar 1 2 = some 4 ∧
      c5Alt1Endpoints.edgeVar 1 4 = some 5 ∧
      c5Alt1Endpoints.edgeVar 2 3 = some 6 ∧
      c5Alt1Endpoints.edgeVar 3 4 = some 7 := by
  native_decide

theorem c5_smoke_edgeList_length :
    c5OfoldEndpoints.edgeList.length = 7 ∧
      c5Alt1Endpoints.edgeList.length = 7 ∧
      c5OfoldEndpoints.edgeList.length = c5OfoldEndpoints.n + 2 ∧
      c5Alt1Endpoints.edgeList.length = c5Alt1Endpoints.n + 2 := by
  native_decide

/-- Mathlib `SimpleGraph` for C_n + two crossing chords. -/
def CrossingEndpoints.toSimpleGraph (e : CrossingEndpoints) :
    SimpleGraph (Fin e.n) :=
  have hp0 : e.p0 < e.n := by
    obtain ⟨_, _, _, h⟩ := e.ordered; omega
  have hp1 : e.p1 < e.n := by
    obtain ⟨_, _, _, h⟩ := e.ordered; omega
  have hp2 : e.p2 < e.n := by
    obtain ⟨_, _, _, h⟩ := e.ordered; omega
  have hp3 : e.p3 < e.n := by
    obtain ⟨_, _, _, h⟩ := e.ordered; omega
  cycleGraph e.n ⊔
    edge (⟨e.p0, hp0⟩ : Fin e.n) ⟨e.p2, hp2⟩ ⊔
    edge (⟨e.p1, hp1⟩ : Fin e.n) ⟨e.p3, hp3⟩

def crossingEndpointsGraphDoc : String :=
  "edgeList/edgeVar match Python _edge_var_map; toSimpleGraph = C_n ⊔ chords"

def crossingEndpointsGraphOpenDoc : String :=
  "tseitinAxioms + residualGlobalVres + residualGlobalAxioms smoke OK; open: Closure₃ sat(G_e) ∀e"

end PNPLab.Bicyclic
