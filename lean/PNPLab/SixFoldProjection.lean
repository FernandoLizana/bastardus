/-
  Six-tip path-fold projection chain (n=10 crossing).

  Instance: C_10 + chords (0,2),(1,3):
    652 → 446 → 288 → 172 → 92 → 42 → 16.

  Projection G0→R via `composeProjection6`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def sfG0Axioms : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
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

def sfG0Closed : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (7 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-12 : Lit), (9 : Lit)]
  , [(-12 : Lit), (10 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (7 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (9 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (7 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-10 : Lit), (12 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-7 : Lit), (3 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (10 : Lit)]
  , [(-7 : Lit), (11 : Lit)]
  , [(-7 : Lit), (12 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (1 : Lit), (7 : Lit)]
  , [(-12 : Lit), (1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (1 : Lit), (9 : Lit)]
  , [(-12 : Lit), (1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (2 : Lit), (7 : Lit)]
  , [(-12 : Lit), (2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (2 : Lit), (9 : Lit)]
  , [(-12 : Lit), (2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (3 : Lit), (5 : Lit)]
  , [(-12 : Lit), (3 : Lit), (6 : Lit)]
  , [(-12 : Lit), (3 : Lit), (7 : Lit)]
  , [(-12 : Lit), (3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (3 : Lit), (9 : Lit)]
  , [(-12 : Lit), (3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (5 : Lit), (6 : Lit)]
  , [(-12 : Lit), (5 : Lit), (7 : Lit)]
  , [(-12 : Lit), (5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (5 : Lit), (9 : Lit)]
  , [(-12 : Lit), (5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (6 : Lit), (7 : Lit)]
  , [(-12 : Lit), (6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (6 : Lit), (9 : Lit)]
  , [(-12 : Lit), (6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (7 : Lit), (8 : Lit)]
  , [(-12 : Lit), (7 : Lit), (9 : Lit)]
  , [(-12 : Lit), (7 : Lit), (10 : Lit)]
  , [(-12 : Lit), (7 : Lit), (11 : Lit)]
  , [(-12 : Lit), (8 : Lit), (9 : Lit)]
  , [(-12 : Lit), (8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (9 : Lit), (10 : Lit)]
  , [(-12 : Lit), (9 : Lit), (11 : Lit)]
  , [(-12 : Lit), (10 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (7 : Lit)]
  , [(-11 : Lit), (1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (7 : Lit)]
  , [(-11 : Lit), (2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (6 : Lit)]
  , [(-11 : Lit), (3 : Lit), (7 : Lit)]
  , [(-11 : Lit), (3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (5 : Lit), (6 : Lit)]
  , [(-11 : Lit), (5 : Lit), (7 : Lit)]
  , [(-11 : Lit), (5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (6 : Lit), (7 : Lit)]
  , [(-11 : Lit), (6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (7 : Lit), (8 : Lit)]
  , [(-11 : Lit), (7 : Lit), (9 : Lit)]
  , [(-11 : Lit), (7 : Lit), (10 : Lit)]
  , [(-11 : Lit), (7 : Lit), (12 : Lit)]
  , [(-11 : Lit), (8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (12 : Lit)]
  , [(-11 : Lit), (10 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (6 : Lit)]
  , [(-10 : Lit), (3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (5 : Lit), (6 : Lit)]
  , [(-10 : Lit), (5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (7 : Lit), (11 : Lit)]
  , [(-10 : Lit), (7 : Lit), (12 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (12 : Lit)]
  , [(-10 : Lit), (11 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (1 : Lit), (12 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (12 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (3 : Lit), (12 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (5 : Lit), (12 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (6 : Lit), (12 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (7 : Lit), (11 : Lit)]
  , [(-9 : Lit), (7 : Lit), (12 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit), (12 : Lit)]
  , [(-9 : Lit), (10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (10 : Lit), (12 : Lit)]
  , [(-9 : Lit), (11 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit), (11 : Lit)]
  , [(-8 : Lit), (7 : Lit), (12 : Lit)]
  , [(-8 : Lit), (9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit), (11 : Lit)]
  , [(-8 : Lit), (9 : Lit), (12 : Lit)]
  , [(-8 : Lit), (10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (10 : Lit), (12 : Lit)]
  , [(-8 : Lit), (11 : Lit), (12 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-7 : Lit), (1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (1 : Lit), (11 : Lit)]
  , [(-7 : Lit), (1 : Lit), (12 : Lit)]
  , [(-7 : Lit), (2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (2 : Lit), (11 : Lit)]
  , [(-7 : Lit), (2 : Lit), (12 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (3 : Lit), (11 : Lit)]
  , [(-7 : Lit), (3 : Lit), (12 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (5 : Lit), (11 : Lit)]
  , [(-7 : Lit), (5 : Lit), (12 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit), (11 : Lit)]
  , [(-7 : Lit), (6 : Lit), (12 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (10 : Lit)]
  , [(-7 : Lit), (8 : Lit), (11 : Lit)]
  , [(-7 : Lit), (8 : Lit), (12 : Lit)]
  , [(-7 : Lit), (9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (9 : Lit), (11 : Lit)]
  , [(-7 : Lit), (9 : Lit), (12 : Lit)]
  , [(-7 : Lit), (10 : Lit), (11 : Lit)]
  , [(-7 : Lit), (10 : Lit), (12 : Lit)]
  , [(-7 : Lit), (11 : Lit), (12 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (5 : Lit), (12 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-5 : Lit), (6 : Lit), (10 : Lit)]
  , [(-5 : Lit), (6 : Lit), (11 : Lit)]
  , [(-5 : Lit), (6 : Lit), (12 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (12 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (10 : Lit)]
  , [(-3 : Lit), (6 : Lit), (11 : Lit)]
  , [(-3 : Lit), (6 : Lit), (12 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit), (11 : Lit)]
  , [(-3 : Lit), (7 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (12 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (12 : Lit)]
  , [(-3 : Lit), (11 : Lit), (12 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  , [(1 : Lit), (2 : Lit), (12 : Lit)]
  ]

def sfG1Axioms : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def sfG1Closed : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-12 : Lit), (9 : Lit)]
  , [(-12 : Lit), (10 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (9 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-10 : Lit), (12 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (1 : Lit), (9 : Lit)]
  , [(-12 : Lit), (1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (2 : Lit), (9 : Lit)]
  , [(-12 : Lit), (2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (3 : Lit), (5 : Lit)]
  , [(-12 : Lit), (3 : Lit), (6 : Lit)]
  , [(-12 : Lit), (3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (3 : Lit), (9 : Lit)]
  , [(-12 : Lit), (3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (5 : Lit), (6 : Lit)]
  , [(-12 : Lit), (5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (5 : Lit), (9 : Lit)]
  , [(-12 : Lit), (5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (6 : Lit), (9 : Lit)]
  , [(-12 : Lit), (6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (8 : Lit), (9 : Lit)]
  , [(-12 : Lit), (8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (9 : Lit), (10 : Lit)]
  , [(-12 : Lit), (9 : Lit), (11 : Lit)]
  , [(-12 : Lit), (10 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (6 : Lit)]
  , [(-11 : Lit), (3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (5 : Lit), (6 : Lit)]
  , [(-11 : Lit), (5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (12 : Lit)]
  , [(-11 : Lit), (10 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (6 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (5 : Lit), (6 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (12 : Lit)]
  , [(-10 : Lit), (11 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (1 : Lit), (12 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (12 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (3 : Lit), (12 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (5 : Lit), (12 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (6 : Lit), (12 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit), (12 : Lit)]
  , [(-9 : Lit), (10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (10 : Lit), (12 : Lit)]
  , [(-9 : Lit), (11 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit), (11 : Lit)]
  , [(-8 : Lit), (9 : Lit), (12 : Lit)]
  , [(-8 : Lit), (10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (10 : Lit), (12 : Lit)]
  , [(-8 : Lit), (11 : Lit), (12 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (5 : Lit), (12 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-5 : Lit), (6 : Lit), (10 : Lit)]
  , [(-5 : Lit), (6 : Lit), (11 : Lit)]
  , [(-5 : Lit), (6 : Lit), (12 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (12 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (10 : Lit)]
  , [(-3 : Lit), (6 : Lit), (11 : Lit)]
  , [(-3 : Lit), (6 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (12 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (12 : Lit)]
  , [(-3 : Lit), (11 : Lit), (12 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  , [(1 : Lit), (2 : Lit), (12 : Lit)]
  ]

def sfG2Axioms : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def sfG2Closed : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-12 : Lit), (10 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-10 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-10 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (1 : Lit), (10 : Lit)]
  , [(-12 : Lit), (1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (2 : Lit), (10 : Lit)]
  , [(-12 : Lit), (2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (3 : Lit), (5 : Lit)]
  , [(-12 : Lit), (3 : Lit), (6 : Lit)]
  , [(-12 : Lit), (3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (3 : Lit), (10 : Lit)]
  , [(-12 : Lit), (3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (5 : Lit), (6 : Lit)]
  , [(-12 : Lit), (5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (5 : Lit), (10 : Lit)]
  , [(-12 : Lit), (5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (6 : Lit), (10 : Lit)]
  , [(-12 : Lit), (6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (8 : Lit), (10 : Lit)]
  , [(-12 : Lit), (8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (10 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (6 : Lit)]
  , [(-11 : Lit), (3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (5 : Lit), (6 : Lit)]
  , [(-11 : Lit), (5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (10 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (12 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (12 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (6 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (12 : Lit)]
  , [(-10 : Lit), (5 : Lit), (6 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (12 : Lit)]
  , [(-10 : Lit), (6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (6 : Lit), (12 : Lit)]
  , [(-10 : Lit), (8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (8 : Lit), (12 : Lit)]
  , [(-10 : Lit), (11 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (10 : Lit), (12 : Lit)]
  , [(-8 : Lit), (11 : Lit), (12 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (5 : Lit), (12 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (10 : Lit)]
  , [(-5 : Lit), (6 : Lit), (11 : Lit)]
  , [(-5 : Lit), (6 : Lit), (12 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (12 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (10 : Lit)]
  , [(-3 : Lit), (6 : Lit), (11 : Lit)]
  , [(-3 : Lit), (6 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (12 : Lit)]
  , [(-3 : Lit), (11 : Lit), (12 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  , [(1 : Lit), (2 : Lit), (12 : Lit)]
  ]

def sfG3Axioms : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def sfG3Closed : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-12 : Lit), (11 : Lit)]
  , [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-11 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (1 : Lit), (11 : Lit)]
  , [(-12 : Lit), (2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (2 : Lit), (11 : Lit)]
  , [(-12 : Lit), (3 : Lit), (5 : Lit)]
  , [(-12 : Lit), (3 : Lit), (6 : Lit)]
  , [(-12 : Lit), (3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (3 : Lit), (11 : Lit)]
  , [(-12 : Lit), (5 : Lit), (6 : Lit)]
  , [(-12 : Lit), (5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (5 : Lit), (11 : Lit)]
  , [(-12 : Lit), (6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (6 : Lit), (11 : Lit)]
  , [(-12 : Lit), (8 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (1 : Lit), (12 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (2 : Lit), (12 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (6 : Lit)]
  , [(-11 : Lit), (3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (3 : Lit), (12 : Lit)]
  , [(-11 : Lit), (5 : Lit), (6 : Lit)]
  , [(-11 : Lit), (5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (5 : Lit), (12 : Lit)]
  , [(-11 : Lit), (6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (6 : Lit), (12 : Lit)]
  , [(-11 : Lit), (8 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (11 : Lit), (12 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (5 : Lit), (12 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (11 : Lit)]
  , [(-5 : Lit), (6 : Lit), (12 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (12 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (11 : Lit)]
  , [(-3 : Lit), (6 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (11 : Lit), (12 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  , [(1 : Lit), (2 : Lit), (12 : Lit)]
  ]

def sfG4Axioms : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def sfG4Closed : List Clause :=
  [ [(-12 : Lit), (3 : Lit)]
  , [(-12 : Lit), (8 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (12 : Lit)]
  , [(-12 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (1 : Lit), (3 : Lit)]
  , [(-12 : Lit), (1 : Lit), (8 : Lit)]
  , [(-12 : Lit), (2 : Lit), (3 : Lit)]
  , [(-12 : Lit), (2 : Lit), (8 : Lit)]
  , [(-12 : Lit), (3 : Lit), (5 : Lit)]
  , [(-12 : Lit), (3 : Lit), (6 : Lit)]
  , [(-12 : Lit), (3 : Lit), (8 : Lit)]
  , [(-12 : Lit), (5 : Lit), (6 : Lit)]
  , [(-12 : Lit), (5 : Lit), (8 : Lit)]
  , [(-12 : Lit), (6 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (12 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (12 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (12 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (12 : Lit)]
  , [(-8 : Lit), (6 : Lit), (12 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (12 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (12 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (12 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (12 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (12 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (12 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (12 : Lit)]
  , [(-3 : Lit), (8 : Lit), (12 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (12 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (12 : Lit)]
  ]

def sfG5Axioms : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def sfG5Closed : List Clause :=
  [ [(-8 : Lit), (3 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  ]

def sfRAxioms : List Clause :=
  [ [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  ]

abbrev sfRClosed : List Clause := sfRAxioms

def sfPivots : List Lit := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

def sfV1 : List Nat := [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12]
def sfV2 : List Nat := [1, 2, 3, 4, 5, 6, 8, 10, 11, 12]
def sfV3 : List Nat := [1, 2, 3, 4, 5, 6, 8, 11, 12]
def sfV4 : List Nat := [1, 2, 3, 4, 5, 6, 8, 12]
def sfV5 : List Nat := [1, 2, 3, 4, 5, 6, 8]
def sfVres : List Nat := [1, 2, 4, 5, 6, 8]

def sfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem sf_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : sfClosedUnder S w pivots = true)
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

theorem sfG0_closed_bool : sfClosedUnder sfG0Closed 3 sfPivots = true := by
  native_decide

theorem sfG0_lits_in_pivots :
    (sfG0Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG0_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG0Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG0_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG0Closure : WidthClosure 3 where
  axioms := sfG0Axioms
  mem := fun C => C ∈ sfG0Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG0Axioms.all fun A => sfG0Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG0_closed_bool hC hD hRes hw (sfG0_pivot hC hRes)

theorem sfG0_no_empty : ¬ sfG0Closure.mem [] := by
  simp [sfG0Closure]
  native_decide


theorem sfG1_closed_bool : sfClosedUnder sfG1Closed 3 sfPivots = true := by
  native_decide

theorem sfG1_lits_in_pivots :
    (sfG1Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG1_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG1Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG1_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG1Closure : WidthClosure 3 where
  axioms := sfG1Axioms
  mem := fun C => C ∈ sfG1Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG1Axioms.all fun A => sfG1Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG1_closed_bool hC hD hRes hw (sfG1_pivot hC hRes)

theorem sfG1_no_empty : ¬ sfG1Closure.mem [] := by
  simp [sfG1Closure]
  native_decide


theorem sfG2_closed_bool : sfClosedUnder sfG2Closed 3 sfPivots = true := by
  native_decide

theorem sfG2_lits_in_pivots :
    (sfG2Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG2_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG2Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG2_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG2Closure : WidthClosure 3 where
  axioms := sfG2Axioms
  mem := fun C => C ∈ sfG2Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG2Axioms.all fun A => sfG2Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG2_closed_bool hC hD hRes hw (sfG2_pivot hC hRes)

theorem sfG2_no_empty : ¬ sfG2Closure.mem [] := by
  simp [sfG2Closure]
  native_decide


theorem sfG3_closed_bool : sfClosedUnder sfG3Closed 3 sfPivots = true := by
  native_decide

theorem sfG3_lits_in_pivots :
    (sfG3Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG3_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG3Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG3_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG3Closure : WidthClosure 3 where
  axioms := sfG3Axioms
  mem := fun C => C ∈ sfG3Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG3Axioms.all fun A => sfG3Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG3_closed_bool hC hD hRes hw (sfG3_pivot hC hRes)

theorem sfG3_no_empty : ¬ sfG3Closure.mem [] := by
  simp [sfG3Closure]
  native_decide


theorem sfG4_closed_bool : sfClosedUnder sfG4Closed 3 sfPivots = true := by
  native_decide

theorem sfG4_lits_in_pivots :
    (sfG4Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG4_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG4Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG4_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG4Closure : WidthClosure 3 where
  axioms := sfG4Axioms
  mem := fun C => C ∈ sfG4Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG4Axioms.all fun A => sfG4Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG4_closed_bool hC hD hRes hw (sfG4_pivot hC hRes)

theorem sfG4_no_empty : ¬ sfG4Closure.mem [] := by
  simp [sfG4Closure]
  native_decide


theorem sfG5_closed_bool : sfClosedUnder sfG5Closed 3 sfPivots = true := by
  native_decide

theorem sfG5_lits_in_pivots :
    (sfG5Closed.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfG5_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfG5Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfG5_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfG5Closure : WidthClosure 3 where
  axioms := sfG5Axioms
  mem := fun C => C ∈ sfG5Closed
  axiom_mem := by
    intro C hC _
    have h : (sfG5Axioms.all fun A => sfG5Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfG5_closed_bool hC hD hRes hw (sfG5_pivot hC hRes)

theorem sfG5_no_empty : ¬ sfG5Closure.mem [] := by
  simp [sfG5Closure]
  native_decide

theorem sfR_closed_bool : sfClosedUnder sfRAxioms 3 sfPivots = true := by
  native_decide

theorem sfR_lits_in_pivots :
    (sfRAxioms.all fun C => C.all fun lit => decide (lit ∈ sfPivots)) = true := by
  native_decide

theorem sfR_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ sfRAxioms) (hRes : resolveOriented C D p = some R) :
    p ∈ sfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp sfR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def sfRClosure : WidthClosure 3 where
  axioms := sfRAxioms
  mem := fun C => C ∈ sfRAxioms
  axiom_mem := by
    intro C hC _
    have h : (sfRAxioms.all fun A => sfRAxioms.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact sf_mem_of_closed sfR_closed_bool hC hD hRes hw (sfR_pivot hC hRes)

theorem sfR_no_empty : ¬ sfRClosure.mem [] := by
  simp [sfRClosure]
  native_decide


def sfProj01OK : Bool :=
  sfG0Closed.all fun C =>
    !(supportedOn C sfV1) || sfG1Closed.contains C

theorem sfProj01OK_true : sfProj01OK = true := by native_decide

theorem sf_supported_01
    {C : Clause} (hG : C ∈ sfG0Closed) (hsup : supportedOn C sfV1 = true) :
    C ∈ sfG1Closed := by
  have hall := (List.all_eq_true.mp sfProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfProj12OK : Bool :=
  sfG1Closed.all fun C =>
    !(supportedOn C sfV2) || sfG2Closed.contains C

theorem sfProj12OK_true : sfProj12OK = true := by native_decide

theorem sf_supported_12
    {C : Clause} (hG : C ∈ sfG1Closed) (hsup : supportedOn C sfV2 = true) :
    C ∈ sfG2Closed := by
  have hall := (List.all_eq_true.mp sfProj12OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfProj23OK : Bool :=
  sfG2Closed.all fun C =>
    !(supportedOn C sfV3) || sfG3Closed.contains C

theorem sfProj23OK_true : sfProj23OK = true := by native_decide

theorem sf_supported_23
    {C : Clause} (hG : C ∈ sfG2Closed) (hsup : supportedOn C sfV3 = true) :
    C ∈ sfG3Closed := by
  have hall := (List.all_eq_true.mp sfProj23OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfProj34OK : Bool :=
  sfG3Closed.all fun C =>
    !(supportedOn C sfV4) || sfG4Closed.contains C

theorem sfProj34OK_true : sfProj34OK = true := by native_decide

theorem sf_supported_34
    {C : Clause} (hG : C ∈ sfG3Closed) (hsup : supportedOn C sfV4 = true) :
    C ∈ sfG4Closed := by
  have hall := (List.all_eq_true.mp sfProj34OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfProj45OK : Bool :=
  sfG4Closed.all fun C =>
    !(supportedOn C sfV5) || sfG5Closed.contains C

theorem sfProj45OK_true : sfProj45OK = true := by native_decide

theorem sf_supported_45
    {C : Clause} (hG : C ∈ sfG4Closed) (hsup : supportedOn C sfV5 = true) :
    C ∈ sfG5Closed := by
  have hall := (List.all_eq_true.mp sfProj45OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfProj5ROK : Bool :=
  sfG5Closed.all fun C =>
    !(supportedOn C sfVres) || sfRClosed.contains C

theorem sfProj5ROK_true : sfProj5ROK = true := by native_decide

theorem sf_supported_5R
    {C : Clause} (hG : C ∈ sfG5Closed) (hsup : supportedOn C sfVres = true) :
    C ∈ sfRClosed := by
  have hall := (List.all_eq_true.mp sfProj5ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def sfStep01 : EliminationStep 3 where
  before := sfG0Closure
  after := sfG1Closure
  V_after := sfV1
  preserves := fun _ hB hsup => sf_supported_01 hB hsup

def sfStep12 : EliminationStep 3 where
  before := sfG1Closure
  after := sfG2Closure
  V_after := sfV2
  preserves := fun _ hB hsup => sf_supported_12 hB hsup

def sfStep23 : EliminationStep 3 where
  before := sfG2Closure
  after := sfG3Closure
  V_after := sfV3
  preserves := fun _ hB hsup => sf_supported_23 hB hsup

def sfStep34 : EliminationStep 3 where
  before := sfG3Closure
  after := sfG4Closure
  V_after := sfV4
  preserves := fun _ hB hsup => sf_supported_34 hB hsup

def sfStep45 : EliminationStep 3 where
  before := sfG4Closure
  after := sfG5Closure
  V_after := sfV5
  preserves := fun _ hB hsup => sf_supported_45 hB hsup

def sfStep5R : EliminationStep 3 where
  before := sfG5Closure
  after := sfRClosure
  V_after := sfVres
  preserves := fun _ hB hsup => sf_supported_5R hB hsup

def sfEliminationChain : EliminationChain 3 where
  steps := [sfStep01, sfStep12, sfStep23, sfStep34, sfStep45, sfStep5R]
  certDoc := "lean/PNPLab/SixFoldProjection.lean"

theorem sfNest12 : varsSubset sfV2 sfV1 = true := by native_decide
theorem sfNest23 : varsSubset sfV3 sfV2 = true := by native_decide
theorem sfNest34 : varsSubset sfV4 sfV3 = true := by native_decide
theorem sfNest45 : varsSubset sfV5 sfV4 = true := by native_decide
theorem sfNest5R : varsSubset sfVres sfV5 = true := by native_decide

theorem sfLink12 : StepLink 3 sfStep01 sfStep12 where
  bridge := rfl
  nest := sfNest12

theorem sfLink23 : StepLink 3 sfStep12 sfStep23 where
  bridge := rfl
  nest := sfNest23

theorem sfLink34 : StepLink 3 sfStep23 sfStep34 where
  bridge := rfl
  nest := sfNest34

theorem sfLink45 : StepLink 3 sfStep34 sfStep45 where
  bridge := rfl
  nest := sfNest45

theorem sfLink5R : StepLink 3 sfStep45 sfStep5R where
  bridge := rfl
  nest := sfNest5R

def sfLinked : LinkedChain 3
    [sfStep01, sfStep12, sfStep23, sfStep34, sfStep45, sfStep5R] :=
  linkedChainCons sfLink12
    (linkedChainCons sfLink23
      (linkedChainCons sfLink34
        (linkedChainCons sfLink45
          (linkedChainCons sfLink5R (LinkedChain.singleton sfStep5R)))))

/-- G0 → R via generic `projectionOfLinkedChain` fold over `sfLinked`. -/
def sfProjection : ProjectionInclusion 3 :=
  projectionOfLinkedChain sfLinked

theorem sf_no_empty_of_projection :
    ¬ sfProjection.gClosure.mem [] :=
  no_empty_of_projection sfProjection sfR_no_empty

end PNPLab.Resolution
