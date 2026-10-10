/-
  Four-tip path-fold projection chain (n=8 crossing).

  Instance: C_8 + chords (0,4),(1,5):
    168 → 118 → 92 → 42 → 16 (Closure₃ sizes).

  Projection G0→R via `composeProjection4`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures

namespace PNPLab.Resolution

def ffG0Axioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
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

def ffG0Closed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (4 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (4 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-4 : Lit), (6 : Lit)]
  , [(-4 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
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
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (4 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
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
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
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
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (4 : Lit), (8 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def ffG1Axioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
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

def ffG1Closed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit)]
  , [(-6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (6 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
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
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (1 : Lit), (7 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-2 : Lit), (7 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(-1 : Lit), (5 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def ffG2Axioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
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

def ffG2Closed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (9 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def ffG3Axioms : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  ]

def ffG3Closed : List Clause :=
  [ [(-10 : Lit), (3 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

def ffRAxioms : List Clause :=
  [ [(-10 : Lit), (-8 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-2 : Lit)]
  , [(-8 : Lit), (2 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-1 : Lit)]
  , [(-6 : Lit), (1 : Lit), (5 : Lit)]
  , [(-6 : Lit), (2 : Lit), (8 : Lit)]
  , [(-5 : Lit), (1 : Lit), (6 : Lit)]
  , [(-5 : Lit), (8 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (6 : Lit), (8 : Lit)]
  , [(-1 : Lit), (5 : Lit), (6 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  ]

abbrev ffRClosed : List Clause := ffRAxioms

def ffPivots : List Lit := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def ffV1 : List Nat := [1, 2, 3, 5, 6, 7, 8, 9, 10]

def ffV2 : List Nat := [1, 2, 3, 5, 6, 8, 9, 10]

def ffV3 : List Nat := [1, 2, 3, 5, 6, 8, 10]

def ffVres : List Nat := [1, 2, 5, 6, 8, 10]

def ffClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem ff_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : ffClosedUnder S w pivots = true)
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

theorem ffG0_closed_bool : ffClosedUnder ffG0Closed 3 ffPivots = true := by
  native_decide

theorem ffG0_lits_in_pivots :
    (ffG0Closed.all fun C => C.all fun lit => decide (lit ∈ ffPivots)) = true := by
  native_decide

theorem ffG0_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ffG0Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ ffPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ffG0_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def ffG0Closure : WidthClosure 3 where
  axioms := ffG0Axioms
  mem := fun C => C ∈ ffG0Closed
  axiom_mem := by
    intro C hC _
    have h : (ffG0Axioms.all fun A => ffG0Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ff_mem_of_closed ffG0_closed_bool hC hD hRes hw (ffG0_pivot hC hRes)

theorem ffG0_no_empty : ¬ ffG0Closure.mem [] := by
  simp [ffG0Closure]
  native_decide


theorem ffG1_closed_bool : ffClosedUnder ffG1Closed 3 ffPivots = true := by
  native_decide

theorem ffG1_lits_in_pivots :
    (ffG1Closed.all fun C => C.all fun lit => decide (lit ∈ ffPivots)) = true := by
  native_decide

theorem ffG1_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ffG1Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ ffPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ffG1_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def ffG1Closure : WidthClosure 3 where
  axioms := ffG1Axioms
  mem := fun C => C ∈ ffG1Closed
  axiom_mem := by
    intro C hC _
    have h : (ffG1Axioms.all fun A => ffG1Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ff_mem_of_closed ffG1_closed_bool hC hD hRes hw (ffG1_pivot hC hRes)

theorem ffG1_no_empty : ¬ ffG1Closure.mem [] := by
  simp [ffG1Closure]
  native_decide


theorem ffG2_closed_bool : ffClosedUnder ffG2Closed 3 ffPivots = true := by
  native_decide

theorem ffG2_lits_in_pivots :
    (ffG2Closed.all fun C => C.all fun lit => decide (lit ∈ ffPivots)) = true := by
  native_decide

theorem ffG2_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ffG2Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ ffPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ffG2_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def ffG2Closure : WidthClosure 3 where
  axioms := ffG2Axioms
  mem := fun C => C ∈ ffG2Closed
  axiom_mem := by
    intro C hC _
    have h : (ffG2Axioms.all fun A => ffG2Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ff_mem_of_closed ffG2_closed_bool hC hD hRes hw (ffG2_pivot hC hRes)

theorem ffG2_no_empty : ¬ ffG2Closure.mem [] := by
  simp [ffG2Closure]
  native_decide


theorem ffG3_closed_bool : ffClosedUnder ffG3Closed 3 ffPivots = true := by
  native_decide

theorem ffG3_lits_in_pivots :
    (ffG3Closed.all fun C => C.all fun lit => decide (lit ∈ ffPivots)) = true := by
  native_decide

theorem ffG3_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ffG3Closed) (hRes : resolveOriented C D p = some R) :
    p ∈ ffPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ffG3_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def ffG3Closure : WidthClosure 3 where
  axioms := ffG3Axioms
  mem := fun C => C ∈ ffG3Closed
  axiom_mem := by
    intro C hC _
    have h : (ffG3Axioms.all fun A => ffG3Closed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ff_mem_of_closed ffG3_closed_bool hC hD hRes hw (ffG3_pivot hC hRes)

theorem ffG3_no_empty : ¬ ffG3Closure.mem [] := by
  simp [ffG3Closure]
  native_decide


theorem ffR_closed_bool : ffClosedUnder ffRClosed 3 ffPivots = true := by
  native_decide

theorem ffR_lits_in_pivots :
    (ffRClosed.all fun C => C.all fun lit => decide (lit ∈ ffPivots)) = true := by
  native_decide

theorem ffR_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ ffRClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ ffPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp ffR_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

def ffRClosure : WidthClosure 3 where
  axioms := ffRAxioms
  mem := fun C => C ∈ ffRClosed
  axiom_mem := by
    intro C hC _
    have h : (ffRAxioms.all fun A => ffRClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact ff_mem_of_closed ffR_closed_bool hC hD hRes hw (ffR_pivot hC hRes)

theorem ffR_no_empty : ¬ ffRClosure.mem [] := by
  simp [ffRClosure]
  native_decide


def ffProj01OK : Bool :=
  ffG0Closed.all fun C =>
    !(supportedOn C ffV1) || ffG1Closed.contains C

theorem ffProj01OK_true : ffProj01OK = true := by native_decide

theorem ff_supported_01
    {C : Clause} (hG : C ∈ ffG0Closed) (hsup : supportedOn C ffV1 = true) :
    C ∈ ffG1Closed := by
  have hall := (List.all_eq_true.mp ffProj01OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def ffProj12OK : Bool :=
  ffG1Closed.all fun C =>
    !(supportedOn C ffV2) || ffG2Closed.contains C

theorem ffProj12OK_true : ffProj12OK = true := by native_decide

theorem ff_supported_12
    {C : Clause} (hG : C ∈ ffG1Closed) (hsup : supportedOn C ffV2 = true) :
    C ∈ ffG2Closed := by
  have hall := (List.all_eq_true.mp ffProj12OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def ffProj23OK : Bool :=
  ffG2Closed.all fun C =>
    !(supportedOn C ffV3) || ffG3Closed.contains C

theorem ffProj23OK_true : ffProj23OK = true := by native_decide

theorem ff_supported_23
    {C : Clause} (hG : C ∈ ffG2Closed) (hsup : supportedOn C ffV3 = true) :
    C ∈ ffG3Closed := by
  have hall := (List.all_eq_true.mp ffProj23OK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def ffProj3ROK : Bool :=
  ffG3Closed.all fun C =>
    !(supportedOn C ffVres) || ffRClosed.contains C

theorem ffProj3ROK_true : ffProj3ROK = true := by native_decide

theorem ff_supported_3R
    {C : Clause} (hG : C ∈ ffG3Closed) (hsup : supportedOn C ffVres = true) :
    C ∈ ffRClosed := by
  have hall := (List.all_eq_true.mp ffProj3ROK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h


def ffStep01 : EliminationStep 3 where
  before := ffG0Closure
  after := ffG1Closure
  V_after := ffV1
  preserves := fun _ hB hsup => ff_supported_01 hB hsup

def ffStep12 : EliminationStep 3 where
  before := ffG1Closure
  after := ffG2Closure
  V_after := ffV2
  preserves := fun _ hB hsup => ff_supported_12 hB hsup

def ffStep23 : EliminationStep 3 where
  before := ffG2Closure
  after := ffG3Closure
  V_after := ffV3
  preserves := fun _ hB hsup => ff_supported_23 hB hsup

def ffStep3R : EliminationStep 3 where
  before := ffG3Closure
  after := ffRClosure
  V_after := ffVres
  preserves := fun _ hB hsup => ff_supported_3R hB hsup

def ffEliminationChain : EliminationChain 3 where
  steps := [ffStep01, ffStep12, ffStep23, ffStep3R]
  certDoc := "lean/PNPLab/FourFoldProjection.lean"

theorem ffNest12 : varsSubset ffV2 ffV1 = true := by native_decide
theorem ffNest23 : varsSubset ffV3 ffV2 = true := by native_decide
theorem ffNest3R : varsSubset ffVres ffV3 = true := by native_decide

theorem ffLink12 : StepLink 3 ffStep01 ffStep12 where
  bridge := rfl
  nest := ffNest12

theorem ffLink23 : StepLink 3 ffStep12 ffStep23 where
  bridge := rfl
  nest := ffNest23

theorem ffLink3R : StepLink 3 ffStep23 ffStep3R where
  bridge := rfl
  nest := ffNest3R

def ffLinked : LinkedChain 3 [ffStep01, ffStep12, ffStep23, ffStep3R] :=
  linkedChainCons ffLink12
    (linkedChainCons ffLink23
      (linkedChainCons ffLink3R (LinkedChain.singleton ffStep3R)))

/-- G0 → R via generic `projectionOfLinkedChain` fold over `ffLinked`. -/
def ffProjection : ProjectionInclusion 3 :=
  projectionOfLinkedChain ffLinked

theorem ff_no_empty_of_projection :
    ¬ ffProjection.gClosure.mem [] :=
  no_empty_of_projection ffProjection ffR_no_empty

def ffDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

end PNPLab.Resolution
