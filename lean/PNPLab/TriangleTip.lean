/-
  Triangle Tseitin tip-fold projection witness (real XOR axioms).

  Enumerated Lean `resolveOriented` closures; projection on V={2,3} by
  literal-set equality (`triNormClause`).
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure

namespace PNPLab.Resolution

def triGAxioms : List Clause :=
  [ [(1 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  ]

def triRAxioms : List Clause :=
  [ [(2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  ]

def triGClosed : List Clause :=
  [ [(1 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-1 : Lit)]
  , [(-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (1 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(3 : Lit), (-3 : Lit)]
  , [(1 : Lit), (-1 : Lit)]
  , [(3 : Lit), (2 : Lit)]
  , [(1 : Lit), (2 : Lit)]
  , [(-1 : Lit), (1 : Lit)]
  , [(-3 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-1 : Lit), (-2 : Lit)]
  , [(2 : Lit), (3 : Lit)]
  , [(2 : Lit), (-2 : Lit)]
  , [(-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-3 : Lit)]
  , [(-2 : Lit), (2 : Lit)]
  , [(1 : Lit), (-3 : Lit)]
  , [(-2 : Lit), (-1 : Lit)]
  , [(3 : Lit), (-1 : Lit)]
  , [(2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (1 : Lit)]
  , [(1 : Lit)]
  , [(3 : Lit)]
  , [(1 : Lit), (-2 : Lit)]
  , [(3 : Lit), (-2 : Lit)]
  , [(3 : Lit), (3 : Lit)]
  , [(1 : Lit), (1 : Lit)]
  , [(-1 : Lit)]
  , [(-3 : Lit)]
  , [(-1 : Lit), (-1 : Lit)]
  , [(-3 : Lit), (-3 : Lit)]
  , [(2 : Lit)]
  , [(2 : Lit), (2 : Lit)]
  , [(-1 : Lit), (-3 : Lit)]
  , [(2 : Lit), (-3 : Lit)]
  , [(-2 : Lit)]
  , [(-2 : Lit), (-2 : Lit)]
  , [(3 : Lit), (1 : Lit)]
  , [(2 : Lit), (-1 : Lit)]
  , []
  ]

def triRClosed : List Clause :=
  [ [(2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (-2 : Lit)]
  , [(-2 : Lit), (3 : Lit)]
  , [(-3 : Lit), (2 : Lit)]
  , [(3 : Lit), (-3 : Lit)]
  , [(2 : Lit), (-2 : Lit)]
  , [(3 : Lit), (3 : Lit)]
  , [(2 : Lit), (2 : Lit)]
  , [(-2 : Lit), (2 : Lit)]
  , [(-3 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-2 : Lit)]
  , [(-3 : Lit), (-3 : Lit)]
  , [(2 : Lit)]
  , [(3 : Lit)]
  , [(-2 : Lit)]
  , [(-3 : Lit)]
  , []
  ]

def triPivots : List Lit := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def triNormClause (C : Clause) : Clause :=
  C.eraseDups.mergeSort (fun a b => decide (a ≤ b))

def triClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem triG_closed_bool : triClosedUnder triGClosed 2 triPivots = true := by
  native_decide

theorem triR_closed_bool : triClosedUnder triRClosed 2 triPivots = true := by
  native_decide

def triVres : List Nat := [2, 3]

def triProjOK : Bool :=
  triGClosed.all fun C =>
    !(supportedOn C triVres) ||
      triRClosed.any fun D => decide (triNormClause C = triNormClause D)

theorem triProjOK_true : triProjOK = true := by native_decide

theorem triG_has_empty : [] ∈ triGClosed := by decide
theorem triR_has_empty : [] ∈ triRClosed := by decide

def triXorEarDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/XOR_EAR.md"

end PNPLab.Resolution
