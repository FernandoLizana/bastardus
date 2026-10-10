/-
  Parametric G₀→R projection from crossing endpoints (no pack lookup).

  Pipeline:
    G axioms  = `tseitinAxioms e`
    G closure = `closure3 e`           (width-3 saturate)
    R closure = `residualGlobalClosed e` (post-fold XOR under global labels)
    Vres      = `residualGlobalVres e`

  Smoke: C₅ ofold, C₅ alt1, C₆ (0,1,2,3) — matches Python `residual_of` projection.
-/

import PNPLab.ClosureFromList
import PNPLab.CrossingEndpointsClosure3
import PNPLab.CrossingEndpointsGlobalResidualXor
import PNPLab.CrossingChordsToArcs
import PNPLab.AltResidualWitnesses
import PNPLab.FreshG0Obligation

namespace PNPLab.Bicyclic

open PNPLab.Resolution

def parametricVres (e : CrossingEndpoints) : List Nat :=
  residualGlobalVres e

def parametricGAxioms (e : CrossingEndpoints) : List Clause :=
  e.tseitinAxioms

def parametricGClosed (e : CrossingEndpoints) : List Clause :=
  closure3 e

def parametricRAxioms (e : CrossingEndpoints) : List Clause :=
  residualGlobalAxioms e

def parametricRClosed (e : CrossingEndpoints) : List Clause :=
  residualGlobalClosed e

def parametricGPivots (e : CrossingEndpoints) : List Lit :=
  pivotsFromEndpoints e

/-- G-clause supported on residual vars ⇒ in R-closure (Python projection check). -/
def parametricProjOK (e : CrossingEndpoints) : Bool :=
  (parametricGClosed e).all fun C =>
    !(supportedOn C (parametricVres e)) || (parametricRClosed e).contains C

/-- Prop-level projection inclusion (G-clause on Vres ⇒ in R-closure). -/
def parametricProjHolds (e : CrossingEndpoints) : Prop :=
  ∀ C, C ∈ closure3 e → supportedOn C (parametricVres e) = true → C ∈ residualGlobalClosed e

theorem parametricProjOK_iff_holds (e : CrossingEndpoints) :
    parametricProjOK e = true ↔ parametricProjHolds e := by
  unfold parametricProjOK parametricProjHolds
  constructor
  · intro h C hG hsup
    have hall := (List.all_eq_true.mp h) C hG
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
    cases hall with
    | inl hneg => exact absurd hsup (by simpa using hneg)
    | inr hmem => exact (List.contains_iff_mem).mp hmem
  · intro h
    rw [List.all_eq_true]
    intro C hG
    by_cases hsup : supportedOn C (parametricVres e) = true
    · rw [Bool.or_eq_true, Bool.not_eq_true']
      right
      exact (List.contains_iff_mem.mpr (h C hG hsup))
    · rw [Bool.or_eq_true, Bool.not_eq_true']
      left
      simpa using hsup

theorem parametricProjHolds_of_projOK {e : CrossingEndpoints}
    (h : parametricProjOK e = true) : parametricProjHolds e :=
  (parametricProjOK_iff_holds e).mp h

theorem parametricProjOK_of_holds {e : CrossingEndpoints}
    (h : parametricProjHolds e) : parametricProjOK e = true :=
  (parametricProjOK_iff_holds e).mpr h

theorem parametric_supported_in_R {e : CrossingEndpoints} {C : Clause}
    (hproj : parametricProjOK e = true)
    (hG : C ∈ closure3 e)
    (hsup : supportedOn C (parametricVres e) = true) :
    C ∈ residualGlobalClosed e :=
  parametricProjHolds_of_projOK hproj C hG hsup

def parametricGClosureOf (e : CrossingEndpoints)
    (h_closed : closedUnder (closure3 e) 3 (parametricGPivots e) = true)
    (h_lits : ((closure3 e).all fun C => C.all fun lit => decide (lit ∈ parametricGPivots e)) = true)
    (h_axioms : (e.tseitinAxioms.all fun A => (closure3 e).contains A) = true) : WidthClosure 3 :=
  closureFromSaturated (e.tseitinAxioms) 3 (parametricGPivots e) (closure3 e)
    (closure3_eq_saturate e) h_closed h_lits h_axioms

def parametricRPivots (e : CrossingEndpoints) : List Lit :=
  parametricGPivots e

def parametricRClosureOf (e : CrossingEndpoints)
    (h_closed : k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true)
    (h_lits : ((residualGlobalClosed e).all fun C =>
        C.all fun lit => decide (lit ∈ parametricRPivots e)) = true)
    (h_axioms : ((residualGlobalAxioms e).all fun A =>
        (residualGlobalClosed e).contains A) = true) : WidthClosure 3 :=
  closureFromEnumerated (residualGlobalAxioms e) (residualGlobalClosed e) 3 (parametricRPivots e)
    h_closed h_lits h_axioms

theorem parametricGClosureOf_mem (e : CrossingEndpoints)
    (h_closed : closedUnder (closure3 e) 3 (parametricGPivots e) = true)
    (h_lits : ((closure3 e).all fun C => C.all fun lit => decide (lit ∈ parametricGPivots e)) = true)
    (h_axioms : (e.tseitinAxioms.all fun A => (closure3 e).contains A) = true)
    (C : Clause) :
    (parametricGClosureOf e h_closed h_lits h_axioms).mem C ↔ C ∈ closure3 e := by
  simp [parametricGClosureOf, closureFromSaturated, closureFromEnumerated]

theorem parametricRClosureOf_mem (e : CrossingEndpoints)
    (h_closed : k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true)
    (h_lits : ((residualGlobalClosed e).all fun C =>
        C.all fun lit => decide (lit ∈ parametricRPivots e)) = true)
    (h_axioms : ((residualGlobalAxioms e).all fun A =>
        (residualGlobalClosed e).contains A) = true)
    (C : Clause) :
    (parametricRClosureOf e h_closed h_lits h_axioms).mem C ↔ C ∈ residualGlobalClosed e := by
  simp [parametricRClosureOf, closureFromEnumerated]

theorem parametricProjHolds_of_projection {e : CrossingEndpoints}
    (P : ProjectionInclusion 3)
    (hG : ∀ C, P.gClosure.mem C ↔ C ∈ closure3 e)
    (hR : ∀ C, P.rClosure.mem C ↔ C ∈ residualGlobalClosed e)
    (hV : P.Vres = parametricVres e) :
    parametricProjHolds e := by
  intro C hGmem hsup
  have hRmem := P.holds C ((hG C).mpr hGmem) (by simpa [hV] using hsup)
  exact (hR C).mp hRmem

def parametricProjectionOf (e : CrossingEndpoints) (hproj : parametricProjOK e = true)
    (hG_closed : closedUnder (closure3 e) 3 (parametricGPivots e) = true)
    (hG_lits : ((closure3 e).all fun C => C.all fun lit => decide (lit ∈ parametricGPivots e)) = true)
    (hG_axioms : (e.tseitinAxioms.all fun A => (closure3 e).contains A) = true)
    (hR_closed : k4ClosedUnder (residualGlobalAxioms e) 3 (parametricRPivots e) = true)
    (hR_lits : ((residualGlobalClosed e).all fun C =>
        C.all fun lit => decide (lit ∈ parametricRPivots e)) = true)
    (hR_axioms : ((residualGlobalAxioms e).all fun A =>
        (residualGlobalClosed e).contains A) = true) : ProjectionInclusion 3 where
  gClosure := parametricGClosureOf e hG_closed hG_lits hG_axioms
  rClosure := parametricRClosureOf e hR_closed hR_lits hR_axioms
  Vres := parametricVres e
  holds := fun _ hG hsup => parametric_supported_in_R hproj hG hsup

theorem c5Ofold_parametricProjOK :
    parametricProjOK c5OfoldEndpoints = true := by
  native_decide

theorem c5Alt1_parametricProjOK :
    parametricProjOK c5Alt1Endpoints = true := by
  native_decide

theorem c6_parametricProjOK :
    parametricProjOK c6Endpoints0123 = true := by
  native_decide

theorem c6_closure3_length :
    (closure3 c6Endpoints0123).length = 92 := by
  native_decide

theorem c6_residual_axioms_eq_alt2 :
    residualGlobalAxioms c6Endpoints0123 = alt2RClosed := by
  native_decide

theorem c6_globalVres_eq_alt2 :
    residualGlobalVres c6Endpoints0123 = alt2Vres := by
  native_decide

theorem c5Ofold_parametricG_lits_in_pivots :
    ((closure3 c5OfoldEndpoints).all fun C =>
      C.all fun lit => decide (lit ∈ parametricGPivots c5OfoldEndpoints)) = true := by
  native_decide

theorem c5Alt1_parametricG_lits_in_pivots :
    ((closure3 c5Alt1Endpoints).all fun C =>
      C.all fun lit => decide (lit ∈ parametricGPivots c5Alt1Endpoints)) = true := by
  native_decide

theorem c5Ofold_parametricR_lits_in_pivots :
    ((residualGlobalClosed c5OfoldEndpoints).all fun C =>
      C.all fun lit => decide (lit ∈ residualGlobalPivots)) = true := by
  native_decide

theorem c5Alt1_parametricR_lits_in_pivots :
    ((residualGlobalClosed c5Alt1Endpoints).all fun C =>
      C.all fun lit => decide (lit ∈ residualGlobalPivots)) = true := by
  native_decide

theorem c5Ofold_parametricG_axioms_subset :
    (c5OfoldEndpoints.tseitinAxioms.all fun A =>
      (closure3 c5OfoldEndpoints).contains A) = true := by
  native_decide

theorem c5Alt1_parametricG_axioms_subset :
    (c5Alt1Endpoints.tseitinAxioms.all fun A =>
      (closure3 c5Alt1Endpoints).contains A) = true := by
  native_decide

theorem c5Ofold_parametricR_axioms_subset :
    ((residualGlobalAxioms c5OfoldEndpoints).all fun A =>
      (residualGlobalClosed c5OfoldEndpoints).contains A) = true := by
  native_decide

theorem c5Alt1_parametricR_axioms_subset :
    ((residualGlobalAxioms c5Alt1Endpoints).all fun A =>
      (residualGlobalClosed c5Alt1Endpoints).contains A) = true := by
  native_decide

def parametricOfoldGClosure : WidthClosure 3 :=
  closureFromEnumerated
    (c5OfoldEndpoints.tseitinAxioms) (closure3 c5OfoldEndpoints) 3
    (parametricGPivots c5OfoldEndpoints)
    c5Ofold_closure3_closed c5Ofold_parametricG_lits_in_pivots
    c5Ofold_parametricG_axioms_subset

def parametricOfoldRClosure : WidthClosure 3 :=
  closureFromEnumerated
    (residualGlobalAxioms c5OfoldEndpoints) (residualGlobalClosed c5OfoldEndpoints) 3
    residualGlobalPivots
    c5Ofold_residual_closed_under c5Ofold_parametricR_lits_in_pivots
    c5Ofold_parametricR_axioms_subset

def parametricAlt1GClosure : WidthClosure 3 :=
  closureFromEnumerated
    (c5Alt1Endpoints.tseitinAxioms) (closure3 c5Alt1Endpoints) 3
    (parametricGPivots c5Alt1Endpoints)
    c5Alt1_closure3_closed c5Alt1_parametricG_lits_in_pivots
    c5Alt1_parametricG_axioms_subset

def parametricAlt1RClosure : WidthClosure 3 :=
  closureFromEnumerated
    (residualGlobalAxioms c5Alt1Endpoints) (residualGlobalClosed c5Alt1Endpoints) 3
    residualGlobalPivots
    c5Alt1_residual_closed_under c5Alt1_parametricR_lits_in_pivots
    c5Alt1_parametricR_axioms_subset

theorem parametricOfold_supported_in_R
    {C : Clause} (hG : C ∈ closure3 c5OfoldEndpoints)
    (hsup : supportedOn C (parametricVres c5OfoldEndpoints) = true) :
    C ∈ residualGlobalClosed c5OfoldEndpoints := by
  have hall := (List.all_eq_true.mp c5Ofold_parametricProjOK) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

theorem parametricAlt1_supported_in_R
    {C : Clause} (hG : C ∈ closure3 c5Alt1Endpoints)
    (hsup : supportedOn C (parametricVres c5Alt1Endpoints) = true) :
    C ∈ residualGlobalClosed c5Alt1Endpoints := by
  have hall := (List.all_eq_true.mp c5Alt1_parametricProjOK) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def parametricOfoldProjection : ProjectionInclusion 3 where
  gClosure := parametricOfoldGClosure
  rClosure := parametricOfoldRClosure
  Vres := parametricVres c5OfoldEndpoints
  holds := fun _ hG hsup => parametricOfold_supported_in_R hG hsup

def parametricAlt1Projection : ProjectionInclusion 3 where
  gClosure := parametricAlt1GClosure
  rClosure := parametricAlt1RClosure
  Vres := parametricVres c5Alt1Endpoints
  holds := fun _ hG hsup => parametricAlt1_supported_in_R hG hsup

theorem parametricOfoldG_no_empty :
    ¬ parametricOfoldGClosure.mem [] := fun h =>
  c5Ofold_closure3_no_empty ((List.contains_iff_mem).mpr h)

theorem parametricOfoldR_no_empty :
    ¬ parametricOfoldRClosure.mem [] := fun h =>
  c5Ofold_residual_axioms_no_empty (by simpa [parametricOfoldRClosure, closureFromEnumerated, residualGlobalClosed] using h)

theorem parametricAlt1G_no_empty :
    ¬ parametricAlt1GClosure.mem [] := fun h =>
  c5Alt1_closure3_no_empty ((List.contains_iff_mem).mpr h)

theorem parametricAlt1R_no_empty :
    ¬ parametricAlt1RClosure.mem [] := fun h =>
  c5Alt1_residual_axioms_no_empty (by simpa [parametricAlt1RClosure, closureFromEnumerated, residualGlobalClosed] using h)

def freshG0_parametric_ofold : FreshG0Obligation :=
  freshG0_of_projection parametricOfoldProjection parametricOfoldR_no_empty

def freshG0_parametric_alt1 : FreshG0Obligation :=
  freshG0_of_projection parametricAlt1Projection parametricAlt1R_no_empty

theorem c6_parametricG_lits_in_pivots :
    ((closure3 c6Endpoints0123).all fun C =>
      C.all fun lit => decide (lit ∈ parametricGPivots c6Endpoints0123)) = true := by
  native_decide

theorem c6_parametricG_axioms_subset :
    (c6Endpoints0123.tseitinAxioms.all fun A =>
      (closure3 c6Endpoints0123).contains A) = true := by
  native_decide

theorem c6_parametricR_lits_in_pivots :
    ((residualGlobalClosed c6Endpoints0123).all fun C =>
      C.all fun lit => decide (lit ∈ residualGlobalPivots)) = true := by
  native_decide

theorem c6_parametricR_axioms_subset :
    ((residualGlobalAxioms c6Endpoints0123).all fun A =>
      (residualGlobalClosed c6Endpoints0123).contains A) = true := by
  native_decide

theorem c6_closure3_closed :
    closedUnder (closure3 c6Endpoints0123) 3 (parametricGPivots c6Endpoints0123) = true := by
  native_decide

theorem c6_residual_closed_under :
    k4ClosedUnder (residualGlobalAxioms c6Endpoints0123) 3 residualGlobalPivots = true := by
  native_decide

def parametricC6GClosure : WidthClosure 3 :=
  closureFromEnumerated
    (c6Endpoints0123.tseitinAxioms) (closure3 c6Endpoints0123) 3
    (parametricGPivots c6Endpoints0123)
    c6_closure3_closed c6_parametricG_lits_in_pivots c6_parametricG_axioms_subset

def parametricC6RClosure : WidthClosure 3 :=
  closureFromEnumerated
    (residualGlobalAxioms c6Endpoints0123) (residualGlobalClosed c6Endpoints0123) 3
    residualGlobalPivots
    c6_residual_closed_under c6_parametricR_lits_in_pivots c6_parametricR_axioms_subset

theorem parametricC6_supported_in_R
    {C : Clause} (hG : C ∈ closure3 c6Endpoints0123)
    (hsup : supportedOn C (parametricVres c6Endpoints0123) = true) :
    C ∈ residualGlobalClosed c6Endpoints0123 := by
  have hall := (List.all_eq_true.mp c6_parametricProjOK) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def parametricC6Projection : ProjectionInclusion 3 where
  gClosure := parametricC6GClosure
  rClosure := parametricC6RClosure
  Vres := parametricVres c6Endpoints0123
  holds := fun _ hG hsup => parametricC6_supported_in_R hG hsup

theorem c6_closure3_no_empty :
    ¬ (closure3 c6Endpoints0123).contains [] := by
  native_decide

theorem parametricC6G_no_empty :
    ¬ parametricC6GClosure.mem [] := fun h =>
  c6_closure3_no_empty ((List.contains_iff_mem).mpr h)

theorem c6_residual_axioms_no_empty :
    ¬ ([] ∈ residualGlobalAxioms c6Endpoints0123) := by
  native_decide

theorem parametricC6R_no_empty :
    ¬ parametricC6RClosure.mem [] := fun h =>
  c6_residual_axioms_no_empty (by simpa [parametricC6RClosure, closureFromEnumerated, residualGlobalClosed] using h)

def freshG0_parametric_c6 : FreshG0Obligation :=
  freshG0_of_projection parametricC6Projection parametricC6R_no_empty

def crossingEndpointsParametricProjectionDoc : String :=
  "parametricOfold/Alt1 ProjectionInclusion from closure3 + residualGlobal (no pack)"

def crossingEndpointsParametricProjectionOpenDoc : String :=
  "parametricProjectionOf generic; FreshG0 c5/c6 + SmokeMass n=7..10; open: ∀e sin emit"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem parametric_ofold_fresh_g0_no_empty :
    ¬ freshG0_parametric_ofold.projection.gClosure.mem [] :=
  freshG0_parametric_ofold.g_no_empty

theorem parametric_alt1_fresh_g0_no_empty :
    ¬ freshG0_parametric_alt1.projection.gClosure.mem [] :=
  freshG0_parametric_alt1.g_no_empty

theorem parametric_c6_fresh_g0_no_empty :
    ¬ freshG0_parametric_c6.projection.gClosure.mem [] :=
  freshG0_parametric_c6.g_no_empty

theorem parametric_c6_proj_ok :
    parametricProjOK c6Endpoints0123 = true :=
  c6_parametricProjOK

end PNPLab.Resolution
