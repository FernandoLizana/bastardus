/-
  Fresh G₀→R for non-pack alt4: C_8 + chords [0, 2],[1, 3] (hop 4).

  Machine fact: Closure₃(G) has size 288 and excludes □; residual
  `alt4RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `alt4RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.AltResidualClosures

namespace PNPLab.Resolution

def alt4GAxioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def alt4GClosed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (7 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-7 : Lit), (3 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (6 : Lit)]
  , [(-10 : Lit), (3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (6 : Lit)]
  , [(-10 : Lit), (5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (10 : Lit)]
  , [(-7 : Lit), (9 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-5 : Lit), (6 : Lit), (10 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def alt4GPivots : List Lit := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def alt4GVres : List Nat := [1, 2, 4, 5, 6, 8]

theorem alt4GVres_eq_alt : alt4GVres = alt4Vres := by native_decide

def alt4GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem alt4G_closed_bool : alt4GClosedUnder alt4GClosed 3 alt4GPivots = true := by
  native_decide

theorem alt4G_lits_in_pivots :
    (alt4GClosed.all fun C => C.all fun lit => decide (lit ∈ alt4GPivots)) = true := by
  native_decide

theorem alt4G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ alt4GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ alt4GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp alt4G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem alt4G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : alt4GClosedUnder S w pivots = true)
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

def alt4GClosure : WidthClosure 3 where
  axioms := alt4GAxioms
  mem := fun C => C ∈ alt4GClosed
  axiom_mem := by
    intro C hC _
    have h : (alt4GAxioms.all fun A => alt4GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact alt4G_mem_of_closed alt4G_closed_bool hC hD hRes hw (alt4G_pivot hC hRes)

theorem alt4G_no_empty : ¬ alt4GClosure.mem [] := by
  simp [alt4GClosure]
  native_decide

def alt4GProjOK : Bool :=
  alt4GClosed.all fun C =>
    !(supportedOn C alt4Vres) || alt4RClosed.contains C

theorem alt4GProjOK_true : alt4GProjOK = true := by native_decide

theorem alt4G_supported_in_R
    {C : Clause} (hG : C ∈ alt4GClosed) (hsup : supportedOn C alt4Vres = true) :
    C ∈ alt4RClosed := by
  have hall := (List.all_eq_true.mp alt4GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def alt4GProjection : ProjectionInclusion 3 where
  gClosure := alt4GClosure
  rClosure := alt4RClosure
  Vres := alt4Vres
  holds := fun _ hG hsup => alt4G_supported_in_R hG hsup

def alt4GEliminationStep : EliminationStep 3 where
  before := alt4GClosure
  after := alt4RClosure
  V_after := alt4Vres
  preserves := fun _ hB hsup => alt4G_supported_in_R hB hsup

theorem alt4G_no_empty_of_projection :
    ¬ alt4GProjection.gClosure.mem [] :=
  no_empty_of_projection alt4GProjection alt4R_closure_no_empty

theorem alt4_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt4TopologyRename alt4RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt4GProjection.gClosure.mem [] :=
  ⟨(alt4_global_edge_iso_to_residualAxioms e).1,
    (alt4_global_edge_iso_to_residualAxioms e).2,
    alt4G_no_empty_of_projection⟩

def alt4GDoc : String :=
  "fresh G₀ Closure₃ for alt4; ProjectionInclusion beyond packs"

end PNPLab.Resolution
