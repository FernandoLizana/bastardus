/-
  Five-tip path-fold projection chain (n=9 crossing).

  Instance: C_9 + chords (0,5),(1,6):
    248 → 168 → 118 → 92 → 42 → 16.

  Projection G0→R via `composeProjection5`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def xfG0Axioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def xfG0Closed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (4 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (4 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (7 : Lit)]
  , [(-4 : Lit), (8 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (4 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (4 : Lit)]
  , [(-8 : Lit), (1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (4 : Lit), (5 : Lit)]
  , [(-8 : Lit), (4 : Lit), (6 : Lit)]
  , [(-8 : Lit), (4 : Lit), (7 : Lit)]
  , [(-8 : Lit), (4 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (4 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (4 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (4 : Lit), (5 : Lit)]
  , [(-7 : Lit), (4 : Lit), (6 : Lit)]
  , [(-7 : Lit), (4 : Lit), (8 : Lit)]
  , [(-7 : Lit), (4 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (1 : Lit), (4 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (4 : Lit), (5 : Lit)]
  , [(-6 : Lit), (4 : Lit), (7 : Lit)]
  , [(-6 : Lit), (4 : Lit), (8 : Lit)]
  , [(-6 : Lit), (4 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (6 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (1 : Lit), (6 : Lit)]
  , [(-4 : Lit), (1 : Lit), (7 : Lit)]
  , [(-4 : Lit), (1 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-4 : Lit), (2 : Lit), (7 : Lit)]
  , [(-4 : Lit), (2 : Lit), (8 : Lit)]
  , [(-4 : Lit), (2 : Lit), (9 : Lit)]
  , [(-4 : Lit), (5 : Lit), (6 : Lit)]
  , [(-4 : Lit), (5 : Lit), (7 : Lit)]
  , [(-4 : Lit), (5 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit), (8 : Lit)]
  , [(-4 : Lit), (6 : Lit), (9 : Lit)]
  , [(-4 : Lit), (7 : Lit), (8 : Lit)]
  , [(-4 : Lit), (7 : Lit), (9 : Lit)]
  , [(-4 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (4 : Lit), (9 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def xfG1Axioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def xfG1Closed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (5 : Lit)]
  , [(-7 : Lit), (1 : Lit), (6 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (6 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (7 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (7 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (8 : Lit)]
  , [(-6 : Lit), (7 : Lit), (9 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (7 : Lit), (9 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(-1 : Lit), (5 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def xfG2Axioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def xfG2Closed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit)]
  , [(-6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (6 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (1 : Lit), (5 : Lit)]
  , [(-8 : Lit), (1 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (1 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (8 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-2 : Lit), (8 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def xfG3Axioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def xfG3Closed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (9 : Lit), (10 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def xfG4Axioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def xfG4Closed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def xfRAxioms : List Clause :=
  [ [(-11 : Lit), (-9 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-9 : Lit), (2 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (9 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (9 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (6 : Lit), (9 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

abbrev xfRClosed : List Clause := xfRAxioms

def xfPivots : List Lit := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def xfV1 : List Nat := [1, 2, 3, 5, 6, 7, 8, 9, 10, 11]
def xfV2 : List Nat := [1, 2, 3, 5, 6, 8, 9, 10, 11]
def xfV3 : List Nat := [1, 2, 3, 5, 6, 9, 10, 11]
def xfV4 : List Nat := [1, 2, 3, 5, 6, 9, 11]
def xfVres : List Nat := [1, 2, 5, 6, 9, 11]

def xfClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem xf_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : xfClosedUnder S w pivots = true)
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

theorem xfG0_closed_bool : xfClosedUnder xfG0Closed 3 xfPivots = true := by
  native_decide

theorem xfG0_lits_in_pivots :
    (xfG0Closed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfG0_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfG0Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfG0_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfG0Closure : WidthClosure 3 where
  axioms := xfG0Axioms
  mem := fun C => C ∈ xfG0Closed
  axiom_mem := by
    intro C hC _
    have h : (xfG0Axioms.all fun A => xfG0Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfG0_closed_bool hC hD hRes hw (xfG0_pivot hC hRes)

theorem xfG0_no_empty : ¬ xfG0Closure.mem [] := by
  simp [xfG0Closure]
  native_decide


theorem xfG1_closed_bool : xfClosedUnder xfG1Closed 3 xfPivots = true := by
  native_decide

theorem xfG1_lits_in_pivots :
    (xfG1Closed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfG1_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfG1Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfG1_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfG1Closure : WidthClosure 3 where
  axioms := xfG1Axioms
  mem := fun C => C ∈ xfG1Closed
  axiom_mem := by
    intro C hC _
    have h : (xfG1Axioms.all fun A => xfG1Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfG1_closed_bool hC hD hRes hw (xfG1_pivot hC hRes)

theorem xfG1_no_empty : ¬ xfG1Closure.mem [] := by
  simp [xfG1Closure]
  native_decide


theorem xfG2_closed_bool : xfClosedUnder xfG2Closed 3 xfPivots = true := by
  native_decide

theorem xfG2_lits_in_pivots :
    (xfG2Closed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfG2_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfG2Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfG2_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfG2Closure : WidthClosure 3 where
  axioms := xfG2Axioms
  mem := fun C => C ∈ xfG2Closed
  axiom_mem := by
    intro C hC _
    have h : (xfG2Axioms.all fun A => xfG2Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfG2_closed_bool hC hD hRes hw (xfG2_pivot hC hRes)

theorem xfG2_no_empty : ¬ xfG2Closure.mem [] := by
  simp [xfG2Closure]
  native_decide


theorem xfG3_closed_bool : xfClosedUnder xfG3Closed 3 xfPivots = true := by
  native_decide

theorem xfG3_lits_in_pivots :
    (xfG3Closed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfG3_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfG3Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfG3_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfG3Closure : WidthClosure 3 where
  axioms := xfG3Axioms
  mem := fun C => C ∈ xfG3Closed
  axiom_mem := by
    intro C hC _
    have h : (xfG3Axioms.all fun A => xfG3Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfG3_closed_bool hC hD hRes hw (xfG3_pivot hC hRes)

theorem xfG3_no_empty : ¬ xfG3Closure.mem [] := by
  simp [xfG3Closure]
  native_decide


theorem xfG4_closed_bool : xfClosedUnder xfG4Closed 3 xfPivots = true := by
  native_decide

theorem xfG4_lits_in_pivots :
    (xfG4Closed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfG4_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfG4Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfG4_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfG4Closure : WidthClosure 3 where
  axioms := xfG4Axioms
  mem := fun C => C ∈ xfG4Closed
  axiom_mem := by
    intro C hC _
    have h : (xfG4Axioms.all fun A => xfG4Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfG4_closed_bool hC hD hRes hw (xfG4_pivot hC hRes)

theorem xfG4_no_empty : ¬ xfG4Closure.mem [] := by
  simp [xfG4Closure]
  native_decide


theorem xfR_closed_bool : xfClosedUnder xfRClosed 3 xfPivots = true := by
  native_decide

theorem xfR_lits_in_pivots :
    (xfRClosed.all fun C => C.all fun lit => decide (lit ∈ xfPivots)) = true := by
  native_decide

theorem xfR_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ xfRClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ xfPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp xfR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def xfRClosure : WidthClosure 3 where
  axioms := xfRAxioms
  mem := fun C => C ∈ xfRClosed
  axiom_mem := by
    intro C hC _
    have h : (xfRAxioms.all fun A => xfRClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact xf_mem_of_closed xfR_closed_bool hC hD hRes hw (xfR_pivot hC hRes)

theorem xfR_no_empty : ¬ xfRClosure.mem [] := by
  simp [xfRClosure]
  native_decide


def xfProj01OK : Bool :=
  xfG0Closed.all fun C =>
    !(supportedOn C xfV1) || xfG1Closed.contains C

theorem xfProj01OK_true : xfProj01OK = true := by native_decide

theorem xf_supported_01
    {C : Clause} (hG : C ∈ xfG0Closed) (hsup : supportedOn C xfV1 = true) :
    C ∈ xfG1Closed := by
  have hall := (List.all_eq_true.mp xfProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def xfProj12OK : Bool :=
  xfG1Closed.all fun C =>
    !(supportedOn C xfV2) || xfG2Closed.contains C

theorem xfProj12OK_true : xfProj12OK = true := by native_decide

theorem xf_supported_12
    {C : Clause} (hG : C ∈ xfG1Closed) (hsup : supportedOn C xfV2 = true) :
    C ∈ xfG2Closed := by
  have hall := (List.all_eq_true.mp xfProj12OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def xfProj23OK : Bool :=
  xfG2Closed.all fun C =>
    !(supportedOn C xfV3) || xfG3Closed.contains C

theorem xfProj23OK_true : xfProj23OK = true := by native_decide

theorem xf_supported_23
    {C : Clause} (hG : C ∈ xfG2Closed) (hsup : supportedOn C xfV3 = true) :
    C ∈ xfG3Closed := by
  have hall := (List.all_eq_true.mp xfProj23OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def xfProj34OK : Bool :=
  xfG3Closed.all fun C =>
    !(supportedOn C xfV4) || xfG4Closed.contains C

theorem xfProj34OK_true : xfProj34OK = true := by native_decide

theorem xf_supported_34
    {C : Clause} (hG : C ∈ xfG3Closed) (hsup : supportedOn C xfV4 = true) :
    C ∈ xfG4Closed := by
  have hall := (List.all_eq_true.mp xfProj34OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def xfProj4ROK : Bool :=
  xfG4Closed.all fun C =>
    !(supportedOn C xfVres) || xfRClosed.contains C

theorem xfProj4ROK_true : xfProj4ROK = true := by native_decide

theorem xf_supported_4R
    {C : Clause} (hG : C ∈ xfG4Closed) (hsup : supportedOn C xfVres = true) :
    C ∈ xfRClosed := by
  have hall := (List.all_eq_true.mp xfProj4ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def xfStep01 : EliminationStep 3 where
  before := xfG0Closure
  after := xfG1Closure
  V_after := xfV1
  preserves := fun _ hB hsup => xf_supported_01 hB hsup

def xfStep12 : EliminationStep 3 where
  before := xfG1Closure
  after := xfG2Closure
  V_after := xfV2
  preserves := fun _ hB hsup => xf_supported_12 hB hsup

def xfStep23 : EliminationStep 3 where
  before := xfG2Closure
  after := xfG3Closure
  V_after := xfV3
  preserves := fun _ hB hsup => xf_supported_23 hB hsup

def xfStep34 : EliminationStep 3 where
  before := xfG3Closure
  after := xfG4Closure
  V_after := xfV4
  preserves := fun _ hB hsup => xf_supported_34 hB hsup

def xfStep4R : EliminationStep 3 where
  before := xfG4Closure
  after := xfRClosure
  V_after := xfVres
  preserves := fun _ hB hsup => xf_supported_4R hB hsup

def xfEliminationChain : EliminationChain 3 where
  steps := [xfStep01, xfStep12, xfStep23, xfStep34, xfStep4R]
  certDoc := "lean/PNPLab/FiveFoldProjection.lean"

theorem xfNest12 : varsSubset xfV2 xfV1 = true := by native_decide
theorem xfNest23 : varsSubset xfV3 xfV2 = true := by native_decide
theorem xfNest34 : varsSubset xfV4 xfV3 = true := by native_decide
theorem xfNest4R : varsSubset xfVres xfV4 = true := by native_decide

theorem xfLink12 : StepLink 3 xfStep01 xfStep12 where
  bridge := rfl
  nest := xfNest12

theorem xfLink23 : StepLink 3 xfStep12 xfStep23 where
  bridge := rfl
  nest := xfNest23

theorem xfLink34 : StepLink 3 xfStep23 xfStep34 where
  bridge := rfl
  nest := xfNest34

theorem xfLink4R : StepLink 3 xfStep34 xfStep4R where
  bridge := rfl
  nest := xfNest4R

def xfLinked : LinkedChain 3 [xfStep01, xfStep12, xfStep23, xfStep34, xfStep4R] :=
  linkedChainCons xfLink12
    (linkedChainCons xfLink23
      (linkedChainCons xfLink34
        (linkedChainCons xfLink4R (LinkedChain.singleton xfStep4R))))

/-- G0 → R via generic `projectionOfLinkedChain` fold over `xfLinked`. -/
def xfProjection : ProjectionInclusion 3 :=
  projectionOfLinkedChain xfLinked

theorem xf_no_empty_of_projection :
    ¬ xfProjection.gClosure.mem [] :=
  no_empty_of_projection xfProjection xfR_no_empty

end PNPLab.Resolution
