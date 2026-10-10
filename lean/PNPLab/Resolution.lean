/-
  Minimal resolution scaffolding (no Mathlib).

  Provides executable `resolveOriented` and width combinators with simple proofs.
  Full soundness of resolution remains future work (link to Python certificates).
-/

namespace PNPLab.Resolution

abbrev Lit := Int
abbrev Clause := List Lit

def clauseWidth (C : Clause) : Nat := C.length

def stripPivot (C : Clause) (p : Lit) : Clause :=
  C.filter (fun lit => !decide (lit = p) && !decide (lit = -p))

/-- Complementary pair in a clause (unordered tautology marker). -/
def isTautology (C : Clause) : Bool :=
  C.any fun lit => decide (lit ≠ 0) && C.contains (-lit)

/-- Sorted unique literals (identity on already-normalized nontaut clauses). -/
def normClause (C : Clause) : Clause :=
  C.eraseDups.mergeSort (fun a b => decide (a ≤ b))

/-- Oriented resolve on pivot `p` when `p ∈ C` and `-p ∈ D`.
    Tautological resolvents are rejected (`none`); survivors are normalized
    so width-bounded closures of nontaut sets stay exact under `List.contains`. -/
def resolveOriented (C D : Clause) (p : Lit) : Option Clause :=
  if p = 0 then
    none
  else if C.contains p && D.contains (-p) then
    if isTautology (stripPivot C p ++ stripPivot D p) then
      none
    else
      some (normClause (stripPivot C p ++ stripPivot D p))
  else
    none

theorem empty_width : clauseWidth ([] : Clause) = 0 := rfl

theorem clauseWidth_append (C D : Clause) :
    clauseWidth (C ++ D) = clauseWidth C + clauseWidth D := by
  simp [clauseWidth, List.length_append]

/-- Example: resolving complementary units yields □. -/
theorem resolve_units_example :
    resolveOriented ([1] : Clause) ([-1] : Clause) (1 : Lit) = some [] := by
  native_decide

/-- Pivot side-conditions when oriented resolve succeeds. -/
theorem resolveOriented_some_mem
    {C D R : Clause} {p : Lit}
    (hRes : resolveOriented C D p = some R) :
    p ≠ 0 ∧ p ∈ C ∧ (-p) ∈ D := by
  unfold resolveOriented at hRes
  split at hRes
  · cases hRes
  · next hp0 =>
    split at hRes
    · next hcond =>
      split at hRes
      · cases hRes
      · next _ht =>
        obtain ⟨hp, hm⟩ := (Bool.and_eq_true_iff).1 hcond
        exact ⟨hp0, (List.contains_iff_mem).1 hp, (List.contains_iff_mem).1 hm⟩
    · cases hRes

def maxWidth : List Nat → Nat
  | [] => 0
  | w :: ws => max w (maxWidth ws)

theorem maxWidth_singleton (w : Nat) : maxWidth [w] = w := by
  simp [maxWidth]

theorem maxWidth_ge_of_mem {w : Nat} {ws : List Nat} (h : w ∈ ws) :
    w ≤ maxWidth ws := by
  induction ws with
  | nil => cases h
  | cons x rest ih =>
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h' => exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-- If a width-bounded projected closure sits in the residual closure and the
residual is free of □, then the original formula is free of □ at that width. -/
theorem restriction_empty_transfer
    (gHasEmpty resHasEmpty projIncludes : Prop)
    (hIncl : projIncludes)
    (hRes : ¬ resHasEmpty)
    (hTransfer : projIncludes → gHasEmpty → resHasEmpty) :
    ¬ gHasEmpty :=
  fun hg => hRes (hTransfer hIncl hg)

end PNPLab.Resolution
