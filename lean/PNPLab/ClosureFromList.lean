/-
  Generic `WidthClosure` from an enumerated saturated clause list.

  Factored from pack emit scripts (`ofold_mem_of_closed`, pivot lemmas).
-/

import PNPLab.ResolutionClosure
import PNPLab.WidthSaturate

namespace PNPLab.Resolution

theorem pivot_of_lits_in_pivots
    {S : List Clause} {pivots : List Lit} {C D R : Clause} {p : Lit}
    (hLits : (S.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (hC : C ∈ S) (hRes : resolveOriented C D p = some R) :
    p ∈ pivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp hLits) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : closedUnder S w pivots = true)
    {C D R : Clause} {p : Lit}
    (hC : C ∈ S) (hD : D ∈ S)
    (hRes : resolveOriented C D p = some R)
    (hw : clauseWidth R ≤ w)
    (hp : p ∈ pivots) :
    R ∈ S := by
  have hpall := (List.all_eq_true.mp hbool) p hp
  have hCall := (List.all_eq_true.mp hpall) C hC
  have hDall := (List.all_eq_true.mp hCall) D hD
  simp only [hRes] at hDall
  have hnotlt : ¬ w < clauseWidth R := Nat.not_lt.mpr hw
  cases hwidth : decide (w < clauseWidth R) with
  | false =>
    simp only [hwidth, Bool.false_or] at hDall
    exact (List.contains_iff_mem).mp hDall
  | true =>
    exact absurd (of_decide_eq_true hwidth) hnotlt

/--
  Package a width-`w` closure given an enumerated saturated list,
  a `closedUnder` witness, and pivot literals covering all clause lits.
-/
def closureFromEnumerated (axioms closed : List Clause) (w : Nat) (pivots : List Lit)
    (closed_bool : closedUnder closed w pivots = true)
    (lits_in_pivots : (closed.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (axioms_subset : (axioms.all fun A => closed.contains A) = true) :
    WidthClosure w where
  axioms := axioms
  mem := fun C => C ∈ closed
  axiom_mem := by
    intro C hC _
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp axioms_subset) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact mem_of_closed closed_bool hC hD hRes hw
      (pivot_of_lits_in_pivots lits_in_pivots hC hRes)

theorem closureFromEnumerated_no_empty
    (axioms closed : List Clause) (w : Nat) (pivots : List Lit)
    (closed_bool : closedUnder closed w pivots = true)
    (lits_in_pivots : (closed.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (axioms_subset : (axioms.all fun A => closed.contains A) = true)
    (hne : ¬ ([] ∈ closed)) :
    ¬ (closureFromEnumerated axioms closed w pivots closed_bool lits_in_pivots axioms_subset).mem [] :=
  hne

def closureFromListDoc : String :=
  "closureFromEnumerated: WidthClosure from saturate emit lists + closedUnder"

/--
  Same as `closureFromEnumerated`, but names the upstream `saturate` pipeline
  explicitly when the saturated list is already materialized as `closed`.
-/
def closureFromSaturated (axioms : List Clause) (w : Nat) (pivots : List Lit)
    (closed : List Clause)
    (_h_sat : saturate axioms w pivots = closed)
    (closed_bool : closedUnder closed w pivots = true)
    (lits_in_pivots : (closed.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (axioms_subset : (axioms.all fun A => closed.contains A) = true) :
    WidthClosure w :=
  closureFromEnumerated axioms closed w pivots closed_bool lits_in_pivots axioms_subset

theorem closureFromSaturated_eq_enumerated (axioms closed : List Clause) (w : Nat)
    (pivots : List Lit) (h_sat : saturate axioms w pivots = closed)
    (closed_bool : closedUnder closed w pivots = true)
    (lits_in_pivots : (closed.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (axioms_subset : (axioms.all fun A => closed.contains A) = true) :
    closureFromSaturated axioms w pivots closed h_sat closed_bool lits_in_pivots axioms_subset =
      closureFromEnumerated axioms closed w pivots closed_bool lits_in_pivots axioms_subset :=
  rfl

theorem closureFromSaturated_no_empty
    (axioms : List Clause) (w : Nat) (pivots : List Lit) (closed : List Clause)
    (h_sat : saturate axioms w pivots = closed)
    (closed_bool : closedUnder closed w pivots = true)
    (lits_in_pivots : (closed.all fun C => C.all fun lit => decide (lit ∈ pivots)) = true)
    (axioms_subset : (axioms.all fun A => closed.contains A) = true)
    (hne : ¬ ([] ∈ closed)) :
    ¬ (closureFromSaturated axioms w pivots closed h_sat closed_bool lits_in_pivots
        axioms_subset).mem [] :=
  closureFromEnumerated_no_empty axioms closed w pivots closed_bool lits_in_pivots
    axioms_subset hne

def closureFromSaturatedDoc : String :=
  "saturate axioms w pivots = closed + closedUnder/lits/axioms witnesses ⇒ WidthClosure"

end PNPLab.Resolution
