/-
  Degree-2 suppression and branch-vertex core (Fase 3).

  Combinatorial definitions: branch vertices (degree ≠ 2), suppressible
  walks (internal vertices degree 2), `suppressDegreeTwoPaths`, and
  `canonicalSuppressedCore` on `CycleTwoChordGraph`.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords

namespace PNPLab.ChordWidth

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Branch vertex: degree is not 2 (tip or junction in the Δ = 3 regime). -/
def isBranchVertex (v : V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  G.degree v ≠ 2

/-- Degree-2 internal vertex (suppressible in a path). -/
def isDegreeTwoInternal (v : V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  G.degree v = 2

/-- All branch vertices of `G`. -/
def branchVertices [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v ≠ 2

theorem mem_branchVertices_iff {v : V} [Fintype V] [DecidableRel G.Adj] :
    v ∈ branchVertices G ↔ isBranchVertex G v := by
  simp [branchVertices, isBranchVertex]

theorem branchVertex_of_mem {v : V} [Fintype V] [DecidableRel G.Adj]
    (hv : v ∈ branchVertices G) : G.degree v ≠ 2 :=
  (mem_branchVertices_iff (G := G)).mp hv

/-- Internal vertices of a walk (excluding endpoints). -/
def walkInternalSupport {u w : V} (p : G.Walk u w) : List V :=
  p.support.tail.dropLast

/-- Walk whose internal vertices all have degree 2 (suppressible path). -/
def walkIsSuppressible {u w : V} (p : G.Walk u w) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∀ x ∈ walkInternalSupport (G := G) p, G.degree x = 2

/-- There exists a suppressible walk of exact length `k` from `u` to `w`. -/
def existsSuppressPathOfLength (u w : V) (k : Nat)
    [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∃ p : G.Walk u w, p.length = k ∧ walkIsSuppressible (G := G) p

/--
  Decidable check: suppressible path of length `k` exists (`k` bounded by `Fintype.card V`).
  Length 0 = same vertex; 1 = direct edge; `k+2` = one degree-2 internal vertex.
-/
def hasSuppressPathLen [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u w : V) :
    Nat → Bool
  | 0 => decide (u = w)
  | 1 => decide (G.Adj u w)
  | k + 2 =>
    decide (((Finset.univ : Finset V).filter fun x =>
      x != u && x != w && decide (G.degree x = 2) && decide (G.Adj u x) &&
        hasSuppressPathLen x w (k + 1)).Nonempty)

/--
  Shortest suppressible path length between `u` and `w` (`some 0` when `u = w`,
  `none` when no suppressible path exists).
-/
def suppressDegreeTwoPaths (u w : V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Option Nat :=
  if u = w then
    some 0
  else
    (List.range (Fintype.card V + 1)).find? fun k => hasSuppressPathLen (G := G) u w k

/-- Two branch vertices are suppress-adjacent when a suppressible path connects them. -/
def branchSuppressAdjacent (u w : V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Prop :=
  u ≠ w ∧ (suppressDegreeTwoPaths (G := G) u w).isSome

instance branchSuppressAdjacentDecidable (u w : V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : Decidable (branchSuppressAdjacent (G := G) u w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/--
  Suppressed core: branch-vertex set plus path-length data between branch pairs.

  `pathLength bu bw` records the shortest suppressible walk length.
-/
structure SuppressedCore (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  branch : Finset V
  pathLength : branch → branch → Option Nat

/-- Branch vertices are non-degree-2. -/
def SuppressedCore.branch_isBranch [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) : Prop :=
  ∀ v ∈ c.branch, G.degree v ≠ 2

/-- Branch set equals `branchVertices` and path lengths from suppression. -/
def canonicalSuppressedCore [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    SuppressedCore V G :=
  { branch := branchVertices G
    pathLength := fun bu bw =>
      suppressDegreeTwoPaths (G := G) (bu : V) (bw : V) }

theorem canonicalSuppressedCore_branch_isBranch [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (canonicalSuppressedCore (V := V) (G := G)).branch_isBranch :=
  fun _ hv => branchVertex_of_mem G hv

theorem canonicalSuppressedCore_branch_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (canonicalSuppressedCore (V := V) (G := G)).branch = branchVertices G :=
  rfl

theorem branchVertices_congr {G G' : SimpleGraph V} [Fintype V]
    [instG : DecidableRel G.Adj] [instG' : DecidableRel G'.Adj] (h : G = G') :
    @branchVertices V G _ instG = @branchVertices V G' _ instG' := by
  subst h
  have hinst : instG = instG' := Subsingleton.elim _ _
  rw [hinst]

theorem branchVertices_eq_of_graph_eq {G G' : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G = G') :
    branchVertices G = branchVertices G' :=
  branchVertices_congr h

theorem branchSuppressAdjacent_of_graph_eq {G G' : SimpleGraph V} [Fintype V] [DecidableEq V]
    [instG : DecidableRel G.Adj] [instG' : DecidableRel G'.Adj] (h : G = G') (u w : V) :
    branchSuppressAdjacent (G := G) u w ↔ branchSuppressAdjacent (G := G') u w := by
  subst h
  have hinst : instG = instG' := Subsingleton.elim _ _
  rw [hinst]

theorem canonicalSuppressedCore_branch_eq_of_graph_eq {G G' : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [DecidableRel G'.Adj] (h : G = G') :
    (canonicalSuppressedCore (V := V) (G := G)).branch =
      (canonicalSuppressedCore (V := V) (G := G')).branch := by
  rw [canonicalSuppressedCore_branch_eq, canonicalSuppressedCore_branch_eq, branchVertices_eq_of_graph_eq h]

/-- Count unordered suppress-adjacent pairs among branch vertices. -/
def SuppressedCore.branchEdgeCount [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) : Nat :=
  (c.branch.sum fun u =>
    (c.branch.filter fun w => branchSuppressAdjacent (G := G) u w).card) / 2

theorem SuppressedCore.branchEdgeCount_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) (hbranch : c.branch = branchVertices G) :
    c.branchEdgeCount (G := G) =
      (branchVertices G).sum (fun u =>
        ((branchVertices G).filter fun w => branchSuppressAdjacent (G := G) u w).card) / 2 := by
  simp [SuppressedCore.branchEdgeCount, hbranch]

/-- Branch vertex degree in the suppressed adjacency relation. -/
def SuppressedCore.branchSuppressDegree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : SuppressedCore V G) (v : V) (_hv : v ∈ c.branch) : Nat :=
  (c.branch.filter fun w => branchSuppressAdjacent (G := G) v w).card

/-- Empty branch set (degenerate smoke). -/
def emptyBranchSuppressedCore [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    SuppressedCore V G :=
  { branch := ∅
    pathLength := fun _ _ => none }

noncomputable def CycleTwoChordGraph.suppressedCore (g : CycleTwoChordGraph) :
    SuppressedCore (Fin g.n) g.toSimpleGraph :=
  canonicalSuppressedCore (V := Fin g.n) (G := g.toSimpleGraph)

theorem CycleTwoChordGraph.suppressedCore_branch_eq (g : CycleTwoChordGraph) :
    g.suppressedCore.branch = branchVertices g.toSimpleGraph := by
  classical
  unfold CycleTwoChordGraph.suppressedCore canonicalSuppressedCore
  rfl

def degreeTwoSuppressionDoc : String :=
  "Branch vertices (deg ≠ 2); suppressDegreeTwoPaths; canonicalSuppressedCore on CycleTwoChordGraph"

end PNPLab.ChordWidth
