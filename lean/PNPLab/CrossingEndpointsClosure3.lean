/-
  Parametric Closure₃ from `CrossingEndpoints.tseitinAxioms` via `saturate`.

  Smoke: C₅ ofold / alt1 closures match precomputed emit lists (or set-eq +
  `closedUnder` witnesses).
-/

import PNPLab.WidthSaturate
import PNPLab.CrossingEndpointsTseitin
import PNPLab.OneFoldProjection
import PNPLab.Alt1FoldProjection

namespace PNPLab.Bicyclic

open PNPLab.Resolution

def maxVarFromEndpoints (e : CrossingEndpoints) : Nat :=
  e.edgeList.length

def pivotsFromEndpoints (e : CrossingEndpoints) : List Lit :=
  pivotsRange (maxVarFromEndpoints e)

def closure3 (e : CrossingEndpoints) : List Clause :=
  saturate (e.tseitinAxioms) 3 (pivotsFromEndpoints e)

theorem closure3_eq_saturate (e : CrossingEndpoints) :
    closure3 e = saturate (e.tseitinAxioms) 3 (pivotsFromEndpoints e) :=
  rfl

/--
  Parametric Closure₃ pipeline from crossing endpoints (Track 1 / G5).
  `closure` is the saturated width-3 set; full `∀e` correctness remains open.
-/
structure ParametricClosure3FromEndpoints where
  endpoints : CrossingEndpoints
  axioms : List Clause
  pivots : List Lit
  closure : List Clause
  axioms_def : axioms = endpoints.tseitinAxioms
  pivots_def : pivots = pivotsFromEndpoints endpoints
  closure_def : closure = saturate axioms 3 pivots

def parametricClosure3From (e : CrossingEndpoints) : ParametricClosure3FromEndpoints where
  endpoints := e
  axioms := e.tseitinAxioms
  pivots := pivotsFromEndpoints e
  closure := closure3 e
  axioms_def := rfl
  pivots_def := rfl
  closure_def := rfl

/-- Smoke: parametric saturation matches precomputed ofold Closure₃. -/
theorem c5Ofold_closure3_eq_ofoldGClosed :
    closure3 c5OfoldEndpoints = ofoldGClosed := by
  native_decide

theorem c5Ofold_closure3_length :
    (closure3 c5OfoldEndpoints).length = 42 := by
  native_decide

theorem c5Ofold_closure3_closed :
    closedUnder (closure3 c5OfoldEndpoints) 3 (pivotsFromEndpoints c5OfoldEndpoints) = true := by
  native_decide

theorem c5Ofold_closure3_axioms_subset :
    (c5OfoldEndpoints.tseitinAxioms.all fun C =>
      (closure3 c5OfoldEndpoints).contains C) = true := by
  native_decide

theorem c5Ofold_closure3_no_empty :
    ¬ (closure3 c5OfoldEndpoints).contains [] := by
  native_decide

/-- Smoke: parametric saturation matches precomputed alt1 Closure₃. -/
theorem c5Alt1_closure3_eq_alt1GClosed :
    closure3 c5Alt1Endpoints = alt1GClosed := by
  native_decide

theorem c5Alt1_closure3_length :
    (closure3 c5Alt1Endpoints).length = 42 := by
  native_decide

theorem c5Alt1_closure3_closed :
    closedUnder (closure3 c5Alt1Endpoints) 3 (pivotsFromEndpoints c5Alt1Endpoints) = true := by
  native_decide

theorem c5Alt1_closure3_axioms_subset :
    (c5Alt1Endpoints.tseitinAxioms.all fun C =>
      (closure3 c5Alt1Endpoints).contains C) = true := by
  native_decide

theorem c5Alt1_closure3_no_empty :
    ¬ (closure3 c5Alt1Endpoints).contains [] := by
  native_decide

def crossingEndpointsClosure3Doc : String :=
  "closure3(e) = saturate(tseitinAxioms e) 3 pivotsFromEndpoints; ofold/alt1 smokes OK"

def crossingEndpointsClosure3OpenDoc : String :=
  "closure3 saturate OK (c5/c6 length); parametric ProjectionInclusion c5; open: ∀e proof"

end PNPLab.Bicyclic
