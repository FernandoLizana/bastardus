/-
  Executable width-w resolution saturation (no Mathlib).

  Iteratively adds `resolveOriented` resolvents with `clauseWidth ≤ w` until
  fixpoint, with deduped `(len, clause)` sort matching Python emit scripts.
-/

import PNPLab.Resolution

namespace PNPLab.Resolution

def clauseSortLt (a b : Clause) : Bool :=
  a.length < b.length ||
    (decide (a.length = b.length) && decide (a < b))

def sortClauses (cs : List Clause) : List Clause :=
  cs.mergeSort clauseSortLt

def dedupSortedClauses : List Clause → List Clause
  | [] => []
  | [c] => [c]
  | c :: c' :: rest =>
    if c = c' then dedupSortedClauses (c' :: rest) else c :: dedupSortedClauses (c' :: rest)

def normalizeClauseList (cs : List Clause) : List Clause :=
  dedupSortedClauses (sortClauses cs)

def filterWidthLe (w : Nat) (cs : List Clause) : List Clause :=
  cs.filter fun C => decide (clauseWidth C ≤ w)

/-- Pivot literals `[-maxVar, …, maxVar]`. -/
def pivotsRange (maxVar : Nat) : List Lit :=
  (List.range (2 * maxVar + 1)).map (fun i : Nat => Int.ofNat i - Int.ofNat maxVar)

def maxVarFromClauses (cs : List Clause) : Nat :=
  cs.foldl (init := 0) fun acc C =>
    C.foldl (init := acc) fun a lit => max a lit.natAbs

def pivotsFromAxioms (axioms : List Clause) : List Lit :=
  pivotsRange (maxVarFromClauses axioms)

/-- One pass: all width-bounded oriented resolvents on `pivots`. -/
def collectResolvents (S : List Clause) (w : Nat) (pivots : List Lit) : List Clause :=
  pivots.foldl (init := ([] : List Clause)) fun acc p =>
    S.foldl (init := acc) fun acc' C =>
      S.foldl (init := acc') fun acc'' D =>
        match resolveOriented C D p with
        | none => acc''
        | some R =>
          if clauseWidth R ≤ w then acc'' ++ [R] else acc''

def hasNewClause (S news : List Clause) : Bool :=
  news.any fun R => !S.contains R

def saturateFuel (fuel : Nat) (S : List Clause) (w : Nat) (pivots : List Lit) : List Clause :=
  match fuel with
  | 0 => S
  | fuel' + 1 =>
    let news := collectResolvents S w pivots
    if !hasNewClause S news then
      S
    else
      saturateFuel fuel' (normalizeClauseList (S ++ news)) w pivots

/-- Width-`w` saturation of `axioms` using pivot list `pivots`. -/
def saturate (axioms : List Clause) (w : Nat) (pivots : List Lit) : List Clause :=
  saturateFuel 500 (normalizeClauseList (filterWidthLe w axioms)) w pivots

def closedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

def clausesSubset (xs ys : List Clause) : Bool :=
  xs.all fun C => ys.contains C

def sameClauseMultiset (xs ys : List Clause) : Bool :=
  xs.length = ys.length && clausesSubset xs ys && clausesSubset ys xs

def widthSaturateDoc : String :=
  "saturate axioms w pivots → fixpoint list; pair with closedUnder + " ++
  "ClosureFromList.closureFromSaturated for Prop-level WidthClosure"

end PNPLab.Resolution
