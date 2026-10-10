/-
  Three-tip path-fold projection chain (n=7 crossing).

  Instance: C_7 + chords (0,4),(1,5):
    G0 Closure₃ size 118
    → G1 size 68
    → G2 size 42
    → R  size 16 (residual K₄).

  Projection G0→R via `composeProjection3`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def tfG0Axioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def tfG0Closed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (4 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

def tfG1Axioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def tfG1Closed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

def tfG2Axioms : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def tfG2Closed : List Clause :=
  [ [(-9 : Lit), (3 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

def tfRAxioms : List Clause :=
  [ [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  ]

abbrev tfRClosed : List Clause := tfRAxioms

def tfPivots : List Lit := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def tfV1 : List Nat := [1, 2, 3, 5, 6, 7, 8, 9]

def tfV2 : List Nat := [1, 2, 3, 5, 6, 8, 9]

def tfVres : List Nat := [1, 2, 5, 6, 8, 9]

def tfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem tf_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : tfClosedUnder S w pivots = true)
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

theorem tfG0_closed_bool : tfClosedUnder tfG0Closed 3 tfPivots = true := by
  native_decide

theorem tfG0_lits_in_pivots :
    (tfG0Closed.all fun C => C.all fun lit => decide (lit ∈ tfPivots)) = true := by
  native_decide

theorem tfG0_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tfG0Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ tfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp tfG0_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def tfG0Closure : WidthClosure 3 where
  axioms := tfG0Axioms
  mem := fun C => C ∈ tfG0Closed
  axiom_mem := by
    intro C hC _
    have h : (tfG0Axioms.all fun A => tfG0Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact tf_mem_of_closed tfG0_closed_bool hC hD hRes hw (tfG0_pivot hC hRes)

theorem tfG0_no_empty : ¬ tfG0Closure.mem [] := by
  simp [tfG0Closure]
  native_decide


theorem tfG1_closed_bool : tfClosedUnder tfG1Closed 3 tfPivots = true := by
  native_decide

theorem tfG1_lits_in_pivots :
    (tfG1Closed.all fun C => C.all fun lit => decide (lit ∈ tfPivots)) = true := by
  native_decide

theorem tfG1_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tfG1Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ tfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp tfG1_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def tfG1Closure : WidthClosure 3 where
  axioms := tfG1Axioms
  mem := fun C => C ∈ tfG1Closed
  axiom_mem := by
    intro C hC _
    have h : (tfG1Axioms.all fun A => tfG1Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact tf_mem_of_closed tfG1_closed_bool hC hD hRes hw (tfG1_pivot hC hRes)

theorem tfG1_no_empty : ¬ tfG1Closure.mem [] := by
  simp [tfG1Closure]
  native_decide


theorem tfG2_closed_bool : tfClosedUnder tfG2Closed 3 tfPivots = true := by
  native_decide

theorem tfG2_lits_in_pivots :
    (tfG2Closed.all fun C => C.all fun lit => decide (lit ∈ tfPivots)) = true := by
  native_decide

theorem tfG2_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tfG2Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ tfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp tfG2_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def tfG2Closure : WidthClosure 3 where
  axioms := tfG2Axioms
  mem := fun C => C ∈ tfG2Closed
  axiom_mem := by
    intro C hC _
    have h : (tfG2Axioms.all fun A => tfG2Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact tf_mem_of_closed tfG2_closed_bool hC hD hRes hw (tfG2_pivot hC hRes)

theorem tfG2_no_empty : ¬ tfG2Closure.mem [] := by
  simp [tfG2Closure]
  native_decide


theorem tfR_closed_bool : tfClosedUnder tfRClosed 3 tfPivots = true := by
  native_decide

theorem tfR_lits_in_pivots :
    (tfRClosed.all fun C => C.all fun lit => decide (lit ∈ tfPivots)) = true := by
  native_decide

theorem tfR_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ tfRClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ tfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp tfR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def tfRClosure : WidthClosure 3 where
  axioms := tfRAxioms
  mem := fun C => C ∈ tfRClosed
  axiom_mem := by
    intro C hC _
    have h : (tfRAxioms.all fun A => tfRClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact tf_mem_of_closed tfR_closed_bool hC hD hRes hw (tfR_pivot hC hRes)

theorem tfR_no_empty : ¬ tfRClosure.mem [] := by
  simp [tfRClosure]
  native_decide


def tfProj01OK : Bool :=
  tfG0Closed.all fun C =>
    !(supportedOn C tfV1) || tfG1Closed.contains C

theorem tfProj01OK_true : tfProj01OK = true := by native_decide

theorem tf_supported_01
    {C : Clause} (hG : C ∈ tfG0Closed) (hsup : supportedOn C tfV1 = true) :
    C ∈ tfG1Closed := by
  have hall := (List.all_eq_true.mp tfProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def tfProj12OK : Bool :=
  tfG1Closed.all fun C =>
    !(supportedOn C tfV2) || tfG2Closed.contains C

theorem tfProj12OK_true : tfProj12OK = true := by native_decide

theorem tf_supported_12
    {C : Clause} (hG : C ∈ tfG1Closed) (hsup : supportedOn C tfV2 = true) :
    C ∈ tfG2Closed := by
  have hall := (List.all_eq_true.mp tfProj12OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def tfProj2ROK : Bool :=
  tfG2Closed.all fun C =>
    !(supportedOn C tfVres) || tfRClosed.contains C

theorem tfProj2ROK_true : tfProj2ROK = true := by native_decide

theorem tf_supported_2R
    {C : Clause} (hG : C ∈ tfG2Closed) (hsup : supportedOn C tfVres = true) :
    C ∈ tfRClosed := by
  have hall := (List.all_eq_true.mp tfProj2ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def tfStep01 : EliminationStep 3 where
  before := tfG0Closure
  after := tfG1Closure
  V_after := tfV1
  preserves := fun _ hB hsup => tf_supported_01 hB hsup

def tfStep12 : EliminationStep 3 where
  before := tfG1Closure
  after := tfG2Closure
  V_after := tfV2
  preserves := fun _ hB hsup => tf_supported_12 hB hsup

def tfStep2R : EliminationStep 3 where
  before := tfG2Closure
  after := tfRClosure
  V_after := tfVres
  preserves := fun _ hB hsup => tf_supported_2R hB hsup

def tfEliminationChain : EliminationChain 3 where
  steps := [tfStep01, tfStep12, tfStep2R]
  certDoc := "lean/PNPLab/TripleFoldProjection.lean"

theorem tfNest12 : varsSubset tfV2 tfV1 = true := by native_decide
theorem tfNest2R : varsSubset tfVres tfV2 = true := by native_decide

theorem tfLink12 : StepLink 3 tfStep01 tfStep12 where
  bridge := rfl
  nest := tfNest12

theorem tfLink2R : StepLink 3 tfStep12 tfStep2R where
  bridge := rfl
  nest := tfNest2R

def tfLinked : LinkedChain 3 [tfStep01, tfStep12, tfStep2R] :=
  linkedChainCons tfLink12 (linkedChainCons tfLink2R (LinkedChain.singleton tfStep2R))

/-- G0 → R via generic `projectionOfLinkedChain` fold over `tfLinked`. -/
def tfProjection : ProjectionInclusion 3 :=
  projectionOfLinkedChain tfLinked

theorem tf_no_empty_of_projection :
    ¬ tfProjection.gClosure.mem [] :=
  no_empty_of_projection tfProjection tfR_no_empty

def tfDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
