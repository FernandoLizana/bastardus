/-
  Global `_edge_var_map` residual after deg-2 tip fold (Category C / E5 track 2).

  Matches Python `emit_crossing_residual_catalog.residual_of`:
    1. `crossing_branch_sets` open-arc internals
    2. left-to-right `fold_deg2_tip` on each arc (default `fold_into = first neighbor`)
    3. sorted surviving edge variable ids = `Vres`

  Distinct from contracted-endpoint `residualVres` / `k4TemplateVars` in
  `ResidualAxiomsFromEndpoints` (permutation iso only; see E2 catalog).
-/

import PNPLab.CrossingEndpointsGraph
import PNPLab.K4ResidualID
import PNPLab.AltResidualWitnesses

namespace PNPLab.Bicyclic

open CrossingEndpoints

/-- Internal vertices strictly between sorted cycle endpoints `lo < hi`. -/
def internalsBetween (lo hi : Nat) : List Nat :=
  if lo + 1 < hi then
    (List.range (hi - lo - 1)).map fun i => lo + 1 + i
  else
    []

/-- Wrap arc internals between last endpoint `p3` and first `p0` on `C_n`. -/
def wrappingInternals (n p0 p3 : Nat) : List Nat :=
  let tail := (List.range (n - p3 - 1)).map fun i => p3 + 1 + i
  let head := List.range p0
  tail ++ head

/-- Open-arc internals for arc `i` (Python `crossing_branch_sets` arc list). -/
def CrossingEndpoints.arcInternals (e : CrossingEndpoints) (i : Fin 4) : List Nat :=
  match i with
  | 0 => internalsBetween e.p0 e.p1
  | 1 => internalsBetween e.p1 e.p2
  | 2 => internalsBetween e.p2 e.p3
  | 3 => wrappingInternals e.n e.p0 e.p3

/-- All fold tips in Python `residual_of` order (arcs 0..3, left-to-right). -/
def CrossingEndpoints.foldTips (e : CrossingEndpoints) : List Nat :=
  (List.finRange 4).flatMap fun i => e.arcInternals i

theorem c5Ofold_arc3_internals :
    c5OfoldEndpoints.arcInternals 3 = [4] := by native_decide

theorem c5Ofold_arc012_empty :
    c5OfoldEndpoints.arcInternals 0 = [] ∧
      c5OfoldEndpoints.arcInternals 1 = [] ∧
      c5OfoldEndpoints.arcInternals 2 = [] := by
  native_decide

theorem c5Alt1_arc2_internals :
    c5Alt1Endpoints.arcInternals 2 = [3] := by native_decide

theorem c5Ofold_foldTips :
    c5OfoldEndpoints.foldTips = [4] := by native_decide

theorem c5Alt1_foldTips :
    c5Alt1Endpoints.foldTips = [3] := by native_decide

/-- Global edge triple `(u, v, varId)` with `u ≤ v`. -/
abbrev GlobalEdge := Nat × Nat × Nat

def initGlobalEdges (e : CrossingEndpoints) : List GlobalEdge :=
  e.edgeList.mapIdx fun i p => (p.1, p.2, i + 1)

def insertSortedNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSortedNat x ys

def sortedUnique (xs : List Nat) : List Nat :=
  let rec go (acc : List Nat) : List Nat → List Nat
    | [] => acc
    | x :: xs =>
      if acc.contains x then go acc xs else go (insertSortedNat x acc) xs
  go [] xs

def sortedNeighbors (edges : List GlobalEdge) (v : Nat) : List Nat :=
  sortedUnique <|
    edges.foldl
      (fun acc (u, w, _) =>
        if u = v then insertSortedNat w acc
        else if w = v then insertSortedNat u acc
        else acc)
      []

def edgePair (a b : Nat) : Nat × Nat :=
  if a ≤ b then (a, b) else (b, a)

def graphHasEdge (edges : List GlobalEdge) (a b : Nat) : Bool :=
  let p := edgePair a b
  edges.any fun (u, w, _) => u = p.1 && w = p.2

def graphEdgeVar (edges : List GlobalEdge) (a b : Nat) : Option Nat :=
  let p := edgePair a b
  match edges.find? fun (u, w, _) => u = p.1 && w = p.2 with
  | none => none
  | some (_, _, vid) => some vid

def removeEdgePair (edges : List GlobalEdge) (a b : Nat) : List GlobalEdge :=
  let p := edgePair a b
  edges.filter fun (u, w, _) => !(u = p.1 && w = p.2)

def addEdgeVar (edges : List GlobalEdge) (a b : Nat) (varId : Nat) : List GlobalEdge :=
  let p := edgePair a b
  (p.1, p.2, varId) :: removeEdgePair edges a b

/-- One `fold_deg2_tip` step under global edge labels (shortcut or triangle ear). -/
def foldDeg2TipGlobal (edges : List GlobalEdge) (tip : Nat) : Option (List GlobalEdge) :=
  match sortedNeighbors edges tip with
  | u :: w :: [] =>
    let fold_into := u
    let other := w
    match graphEdgeVar edges fold_into tip, graphEdgeVar edges tip other with
    | some _x, some y =>
      let edges' :=
        removeEdgePair (removeEdgePair edges fold_into tip) tip other
      if graphHasEdge edges fold_into other then
        some edges'
      else
        some (addEdgeVar edges' fold_into other y)
    | _, _ => none
  | _ => none

def foldAllTips (edges : List GlobalEdge) (tips : List Nat) : List GlobalEdge :=
  tips.foldl
    (fun es tip =>
      match foldDeg2TipGlobal es tip with
      | some es' => es'
      | none => es)
    edges

def edgeVarIds (edges : List GlobalEdge) : List Nat :=
  sortedUnique (edges.map fun (_, _, vid) => vid)

/-- Residual global edge variables after folding all open-arc internals. -/
def residualGlobalVres (e : CrossingEndpoints) : List Nat :=
  edgeVarIds (foldAllTips (initGlobalEdges e) e.foldTips)

theorem c5Ofold_globalVres :
    residualGlobalVres c5OfoldEndpoints = [1, 2, 4, 5, 6, 7] := by
  native_decide

theorem c5Alt1_globalVres :
    residualGlobalVres c5Alt1Endpoints = [1, 2, 3, 4, 5, 7] := by
  native_decide

theorem c5Ofold_globalVres_len :
    (residualGlobalVres c5OfoldEndpoints).length = 6 := by
  native_decide

theorem c5Alt1_globalVres_len :
    (residualGlobalVres c5Alt1Endpoints).length = 6 := by
  native_decide

theorem c5Alt1_globalVres_eq_alt1Vres :
    residualGlobalVres c5Alt1Endpoints = Resolution.alt1Vres := by
  native_decide

theorem c6Endpoints0123_arc3_internals :
    c6Endpoints0123.arcInternals 3 = [4, 5] := by native_decide

theorem c6Endpoints0123_globalVres :
    residualGlobalVres c6Endpoints0123 = [1, 2, 4, 5, 6, 8] := by
  native_decide

def crossingEndpointsGlobalResidualDoc : String :=
  "residualGlobalVres: Python residual_of Vres under global _edge_var_map"

def crossingEndpointsGlobalResidualOpenDoc : String :=
  "Vres/foldTips OK; residual XOR axioms in CrossingEndpointsGlobalResidualXor"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

/-- Smoke: parametric global Vres agrees with alt1 catalog witness on C₅ alt1. -/
theorem global_vres_alt1_smoke :
    residualGlobalVres c5Alt1Endpoints = alt1Vres := by
  native_decide

/-- Contracted template vars differ from global labels on canonical one-fold C₅. -/
theorem global_vres_ofold_ne_template :
    residualGlobalVres c5OfoldEndpoints ≠ k4TemplateVars := by
  native_decide

def parametricGlobalVresDoc : String :=
  "residualGlobalVres(e) = Python residual_of Vres; rename to k4Axioms via E2 iso"

end PNPLab.Resolution
