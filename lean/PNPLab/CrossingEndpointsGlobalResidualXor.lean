/-
  Residual XOR axioms under global `_edge_var_map` after deg-2 tip fold.

  Matches Python `emit_crossing_residual_catalog.residual_of`:
    1. `fold_deg2_tip` on open-arc internals (charges: χ_foldInto ← χ_u ⊕ χ_v)
    2. `_xor_axioms` on remaining endpoint vertices
    3. width-3 closure (= axioms for K₄ residual; RAxioms in catalog)

  Distinct from contracted-endpoint `ofoldRClosed` / `residualAxioms` (template vars).
-/

import PNPLab.CrossingEndpointsGlobalResidual
import PNPLab.CrossingEndpointsTseitin
import PNPLab.K4Width3
import PNPLab.RenameClosedTransport
import PNPLab.CatalogIsoTransport

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-- GF(2) charge lookup (default 0). -/
def chargeAt (charges : List (Nat × Nat)) (v : Nat) : Nat :=
  match charges.find? fun p => p.1 = v with
  | some (_, c) => c % 2
  | none => 0

def removeVertexCharge (charges : List (Nat × Nat)) (v : Nat) : List (Nat × Nat) :=
  charges.filter fun p => p.1 ≠ v

def setCharge (charges : List (Nat × Nat)) (v : Nat) (c : Nat) : List (Nat × Nat) :=
  removeVertexCharge charges v ++ [(v, c % 2)]

/-- Initial vertex charges (Python `_odd_charge_for_crossing` for Δ ≤ 3). -/
def initCharges (e : CrossingEndpoints) : List (Nat × Nat) :=
  (List.range e.n).map fun v => (v, e.oddCharge v)

/-- One `fold_deg2_tip` step updating edge labels and charges. -/
def foldDeg2TipGlobalCharges (edges : List GlobalEdge) (charges : List (Nat × Nat))
    (tip : Nat) : Option (List GlobalEdge × List (Nat × Nat)) :=
  match sortedNeighbors edges tip with
  | u :: _w :: [] =>
    match foldDeg2TipGlobal edges tip with
    | none => none
    | some edges' =>
      let chi_new := (chargeAt charges u + chargeAt charges tip) % 2
      let charges' := setCharge (removeVertexCharge charges tip) u chi_new
      some (edges', charges')
  | _ => none

def foldAllTipsState (edges : List GlobalEdge) (charges : List (Nat × Nat))
    (tips : List Nat) : List GlobalEdge × List (Nat × Nat) :=
  tips.foldl
    (fun (es, ch) tip =>
      match foldDeg2TipGlobalCharges es ch tip with
      | some (es', ch') => (es', ch')
      | none => (es, ch))
    (edges, charges)

/-- Vertices incident to at least one surviving edge. -/
def graphVertices (edges : List GlobalEdge) : List Nat :=
  sortedUnique <|
    edges.foldl
      (fun acc (u, w, _) => insertSortedNat w (insertSortedNat u acc))
      []

/-- Positive literals for edges incident to `v` in the folded graph. -/
def incidentLits (edges : List GlobalEdge) (v : Nat) : List Lit :=
  (sortedNeighbors edges v).filterMap fun u => graphEdgeVar edges v u

def xorClausesForResidualVertex (edges : List GlobalEdge) (charges : List (Nat × Nat))
    (v : Nat) : List Clause :=
  xorCnfNorm (incidentLits edges v) (chargeAt charges v)

def residualGlobalFoldState (e : CrossingEndpoints) :
    List GlobalEdge × List (Nat × Nat) :=
  foldAllTipsState (initGlobalEdges e) (initCharges e) e.foldTips

/-- Residual XOR CNF after all tip folds (Python `_xor_axioms` / pre-closure RAxioms). -/
def residualGlobalAxioms (e : CrossingEndpoints) : List Clause :=
  let (edges, charges) := residualGlobalFoldState e
  let raw := (graphVertices edges).flatMap fun v =>
    xorClausesForResidualVertex edges charges v
  dedupSortedClauses (sortClauses raw)

/-- K₄ residual: width-3 closure equals XOR axioms (no new clauses). -/
def residualGlobalClosed (e : CrossingEndpoints) : List Clause :=
  residualGlobalAxioms e

def residualGlobalPivots : List Lit :=
  [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- Python `residual_of(5,(0,2),(1,3))['RAxioms']` under global labels. -/
def ofoldGlobalRAxioms : List Clause :=
  [ [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  ]

theorem c5Alt1_residual_axioms_eq_alt1 :
    residualGlobalAxioms c5Alt1Endpoints = alt1RClosed := by
  native_decide

theorem c5Ofold_residual_axioms_eq_python :
    residualGlobalAxioms c5OfoldEndpoints = ofoldGlobalRAxioms := by
  native_decide

theorem c5Alt1_residual_closed_eq_alt1 :
    residualGlobalClosed c5Alt1Endpoints = alt1RClosed := by
  native_decide

theorem c5Ofold_residual_closed_eq_python :
    residualGlobalClosed c5OfoldEndpoints = ofoldGlobalRAxioms := by
  native_decide

theorem c5Alt1_residual_axioms_size :
    (residualGlobalAxioms c5Alt1Endpoints).length = 16 := by
  native_decide

theorem c5Ofold_residual_axioms_size :
    (residualGlobalAxioms c5OfoldEndpoints).length = 16 := by
  native_decide

theorem c5Alt1_residual_axioms_no_empty :
    ¬ ([] ∈ residualGlobalAxioms c5Alt1Endpoints) := by
  native_decide

theorem c5Ofold_residual_axioms_no_empty :
    ¬ ([] ∈ residualGlobalAxioms c5OfoldEndpoints) := by
  native_decide

theorem c5Alt1_residual_closed_under :
    k4ClosedUnder (residualGlobalAxioms c5Alt1Endpoints) 3 residualGlobalPivots = true := by
  native_decide

theorem c5Ofold_residual_closed_under :
    k4ClosedUnder (residualGlobalAxioms c5OfoldEndpoints) 3 residualGlobalPivots = true := by
  native_decide

theorem c5Alt1_residual_topology_set_eq :
    topologySetEq alt1TopologyRename (residualGlobalAxioms c5Alt1Endpoints) = true := by
  native_decide

theorem c5Ofold_globalVres_matches_axioms :
    residualGlobalVres c5OfoldEndpoints = [1, 2, 4, 5, 6, 7] ∧
      residualGlobalVres c5Alt1Endpoints = alt1Vres := by
  native_decide

def crossingEndpointsGlobalResidualXorDoc : String :=
  "residualGlobalAxioms/Closed: Python residual_of RAxioms under global edge labels"

def crossingEndpointsGlobalResidualXorOpenDoc : String :=
  "alt1/ofold smoke OK; open: ∀e residualGlobalAxioms + parametric VarRename"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem global_residual_xor_alt1_smoke :
    residualGlobalClosed c5Alt1Endpoints = alt1RClosed ∧
      topologySetEq alt1TopologyRename (residualGlobalAxioms c5Alt1Endpoints) = true := by
  native_decide

theorem global_residual_xor_ofold_smoke :
    residualGlobalClosed c5OfoldEndpoints = ofoldGlobalRAxioms ∧
      residualGlobalVres c5OfoldEndpoints = [1, 2, 4, 5, 6, 7] := by
  native_decide

def parametricGlobalResidualXorDoc : String :=
  "residualGlobalAxioms(e) = Python residual_of RAxioms; alt1 topology-set-eq OK"

end PNPLab.Resolution
