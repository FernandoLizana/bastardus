/-
  Fresh G₀→R for non-pack alt5: C_9 + chords [0, 2],[1, 3] (hop 5).

  Machine fact: Closure₃(G) has size 446 and excludes □; residual
  `alt5RClosed` (16) excludes □; every Closure₃(G) clause supported on
  residual edge vars lies in `alt5RClosed`.
-/

import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.ConcreteClosures
import PNPLab.AltResidualClosures

namespace PNPLab.Resolution

def alt5GAxioms : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
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

def alt5GClosed : List Clause :=
  [ [(-11 : Lit), (3 : Lit)]
  , [(-11 : Lit), (7 : Lit)]
  , [(-11 : Lit), (8 : Lit)]
  , [(-11 : Lit), (9 : Lit)]
  , [(-11 : Lit), (10 : Lit)]
  , [(-10 : Lit), (3 : Lit)]
  , [(-10 : Lit), (7 : Lit)]
  , [(-10 : Lit), (8 : Lit)]
  , [(-10 : Lit), (9 : Lit)]
  , [(-10 : Lit), (11 : Lit)]
  , [(-9 : Lit), (3 : Lit)]
  , [(-9 : Lit), (7 : Lit)]
  , [(-9 : Lit), (8 : Lit)]
  , [(-9 : Lit), (10 : Lit)]
  , [(-9 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit)]
  , [(-8 : Lit), (7 : Lit)]
  , [(-8 : Lit), (9 : Lit)]
  , [(-8 : Lit), (10 : Lit)]
  , [(-8 : Lit), (11 : Lit)]
  , [(-7 : Lit), (3 : Lit)]
  , [(-7 : Lit), (8 : Lit)]
  , [(-7 : Lit), (9 : Lit)]
  , [(-7 : Lit), (10 : Lit)]
  , [(-7 : Lit), (11 : Lit)]
  , [(-3 : Lit), (7 : Lit)]
  , [(-3 : Lit), (8 : Lit)]
  , [(-3 : Lit), (9 : Lit)]
  , [(-3 : Lit), (10 : Lit)]
  , [(-3 : Lit), (11 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-10 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-9 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (1 : Lit), (3 : Lit)]
  , [(-11 : Lit), (1 : Lit), (7 : Lit)]
  , [(-11 : Lit), (1 : Lit), (8 : Lit)]
  , [(-11 : Lit), (1 : Lit), (9 : Lit)]
  , [(-11 : Lit), (1 : Lit), (10 : Lit)]
  , [(-11 : Lit), (2 : Lit), (3 : Lit)]
  , [(-11 : Lit), (2 : Lit), (7 : Lit)]
  , [(-11 : Lit), (2 : Lit), (8 : Lit)]
  , [(-11 : Lit), (2 : Lit), (9 : Lit)]
  , [(-11 : Lit), (2 : Lit), (10 : Lit)]
  , [(-11 : Lit), (3 : Lit), (5 : Lit)]
  , [(-11 : Lit), (3 : Lit), (6 : Lit)]
  , [(-11 : Lit), (3 : Lit), (7 : Lit)]
  , [(-11 : Lit), (3 : Lit), (8 : Lit)]
  , [(-11 : Lit), (3 : Lit), (9 : Lit)]
  , [(-11 : Lit), (3 : Lit), (10 : Lit)]
  , [(-11 : Lit), (5 : Lit), (6 : Lit)]
  , [(-11 : Lit), (5 : Lit), (7 : Lit)]
  , [(-11 : Lit), (5 : Lit), (8 : Lit)]
  , [(-11 : Lit), (5 : Lit), (9 : Lit)]
  , [(-11 : Lit), (5 : Lit), (10 : Lit)]
  , [(-11 : Lit), (6 : Lit), (7 : Lit)]
  , [(-11 : Lit), (6 : Lit), (8 : Lit)]
  , [(-11 : Lit), (6 : Lit), (9 : Lit)]
  , [(-11 : Lit), (6 : Lit), (10 : Lit)]
  , [(-11 : Lit), (7 : Lit), (8 : Lit)]
  , [(-11 : Lit), (7 : Lit), (9 : Lit)]
  , [(-11 : Lit), (7 : Lit), (10 : Lit)]
  , [(-11 : Lit), (8 : Lit), (9 : Lit)]
  , [(-11 : Lit), (8 : Lit), (10 : Lit)]
  , [(-11 : Lit), (9 : Lit), (10 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-9 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (1 : Lit), (3 : Lit)]
  , [(-10 : Lit), (1 : Lit), (7 : Lit)]
  , [(-10 : Lit), (1 : Lit), (8 : Lit)]
  , [(-10 : Lit), (1 : Lit), (9 : Lit)]
  , [(-10 : Lit), (1 : Lit), (11 : Lit)]
  , [(-10 : Lit), (2 : Lit), (3 : Lit)]
  , [(-10 : Lit), (2 : Lit), (7 : Lit)]
  , [(-10 : Lit), (2 : Lit), (8 : Lit)]
  , [(-10 : Lit), (2 : Lit), (9 : Lit)]
  , [(-10 : Lit), (2 : Lit), (11 : Lit)]
  , [(-10 : Lit), (3 : Lit), (5 : Lit)]
  , [(-10 : Lit), (3 : Lit), (6 : Lit)]
  , [(-10 : Lit), (3 : Lit), (7 : Lit)]
  , [(-10 : Lit), (3 : Lit), (8 : Lit)]
  , [(-10 : Lit), (3 : Lit), (9 : Lit)]
  , [(-10 : Lit), (3 : Lit), (11 : Lit)]
  , [(-10 : Lit), (5 : Lit), (6 : Lit)]
  , [(-10 : Lit), (5 : Lit), (7 : Lit)]
  , [(-10 : Lit), (5 : Lit), (8 : Lit)]
  , [(-10 : Lit), (5 : Lit), (9 : Lit)]
  , [(-10 : Lit), (5 : Lit), (11 : Lit)]
  , [(-10 : Lit), (6 : Lit), (7 : Lit)]
  , [(-10 : Lit), (6 : Lit), (8 : Lit)]
  , [(-10 : Lit), (6 : Lit), (9 : Lit)]
  , [(-10 : Lit), (6 : Lit), (11 : Lit)]
  , [(-10 : Lit), (7 : Lit), (8 : Lit)]
  , [(-10 : Lit), (7 : Lit), (9 : Lit)]
  , [(-10 : Lit), (7 : Lit), (11 : Lit)]
  , [(-10 : Lit), (8 : Lit), (9 : Lit)]
  , [(-10 : Lit), (8 : Lit), (11 : Lit)]
  , [(-10 : Lit), (9 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (1 : Lit), (3 : Lit)]
  , [(-9 : Lit), (1 : Lit), (7 : Lit)]
  , [(-9 : Lit), (1 : Lit), (8 : Lit)]
  , [(-9 : Lit), (1 : Lit), (10 : Lit)]
  , [(-9 : Lit), (1 : Lit), (11 : Lit)]
  , [(-9 : Lit), (2 : Lit), (3 : Lit)]
  , [(-9 : Lit), (2 : Lit), (7 : Lit)]
  , [(-9 : Lit), (2 : Lit), (8 : Lit)]
  , [(-9 : Lit), (2 : Lit), (10 : Lit)]
  , [(-9 : Lit), (2 : Lit), (11 : Lit)]
  , [(-9 : Lit), (3 : Lit), (5 : Lit)]
  , [(-9 : Lit), (3 : Lit), (6 : Lit)]
  , [(-9 : Lit), (3 : Lit), (7 : Lit)]
  , [(-9 : Lit), (3 : Lit), (8 : Lit)]
  , [(-9 : Lit), (3 : Lit), (10 : Lit)]
  , [(-9 : Lit), (3 : Lit), (11 : Lit)]
  , [(-9 : Lit), (5 : Lit), (6 : Lit)]
  , [(-9 : Lit), (5 : Lit), (7 : Lit)]
  , [(-9 : Lit), (5 : Lit), (8 : Lit)]
  , [(-9 : Lit), (5 : Lit), (10 : Lit)]
  , [(-9 : Lit), (5 : Lit), (11 : Lit)]
  , [(-9 : Lit), (6 : Lit), (7 : Lit)]
  , [(-9 : Lit), (6 : Lit), (8 : Lit)]
  , [(-9 : Lit), (6 : Lit), (10 : Lit)]
  , [(-9 : Lit), (6 : Lit), (11 : Lit)]
  , [(-9 : Lit), (7 : Lit), (8 : Lit)]
  , [(-9 : Lit), (7 : Lit), (10 : Lit)]
  , [(-9 : Lit), (7 : Lit), (11 : Lit)]
  , [(-9 : Lit), (8 : Lit), (10 : Lit)]
  , [(-9 : Lit), (8 : Lit), (11 : Lit)]
  , [(-9 : Lit), (10 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-7 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (1 : Lit), (3 : Lit)]
  , [(-8 : Lit), (1 : Lit), (7 : Lit)]
  , [(-8 : Lit), (1 : Lit), (9 : Lit)]
  , [(-8 : Lit), (1 : Lit), (10 : Lit)]
  , [(-8 : Lit), (1 : Lit), (11 : Lit)]
  , [(-8 : Lit), (2 : Lit), (3 : Lit)]
  , [(-8 : Lit), (2 : Lit), (7 : Lit)]
  , [(-8 : Lit), (2 : Lit), (9 : Lit)]
  , [(-8 : Lit), (2 : Lit), (10 : Lit)]
  , [(-8 : Lit), (2 : Lit), (11 : Lit)]
  , [(-8 : Lit), (3 : Lit), (5 : Lit)]
  , [(-8 : Lit), (3 : Lit), (6 : Lit)]
  , [(-8 : Lit), (3 : Lit), (7 : Lit)]
  , [(-8 : Lit), (3 : Lit), (9 : Lit)]
  , [(-8 : Lit), (3 : Lit), (10 : Lit)]
  , [(-8 : Lit), (3 : Lit), (11 : Lit)]
  , [(-8 : Lit), (5 : Lit), (6 : Lit)]
  , [(-8 : Lit), (5 : Lit), (7 : Lit)]
  , [(-8 : Lit), (5 : Lit), (9 : Lit)]
  , [(-8 : Lit), (5 : Lit), (10 : Lit)]
  , [(-8 : Lit), (5 : Lit), (11 : Lit)]
  , [(-8 : Lit), (6 : Lit), (7 : Lit)]
  , [(-8 : Lit), (6 : Lit), (9 : Lit)]
  , [(-8 : Lit), (6 : Lit), (10 : Lit)]
  , [(-8 : Lit), (6 : Lit), (11 : Lit)]
  , [(-8 : Lit), (7 : Lit), (9 : Lit)]
  , [(-8 : Lit), (7 : Lit), (10 : Lit)]
  , [(-8 : Lit), (7 : Lit), (11 : Lit)]
  , [(-8 : Lit), (9 : Lit), (10 : Lit)]
  , [(-8 : Lit), (9 : Lit), (11 : Lit)]
  , [(-8 : Lit), (10 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (-5 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-6 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-5 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-7 : Lit), (1 : Lit), (3 : Lit)]
  , [(-7 : Lit), (1 : Lit), (8 : Lit)]
  , [(-7 : Lit), (1 : Lit), (9 : Lit)]
  , [(-7 : Lit), (1 : Lit), (10 : Lit)]
  , [(-7 : Lit), (1 : Lit), (11 : Lit)]
  , [(-7 : Lit), (2 : Lit), (3 : Lit)]
  , [(-7 : Lit), (2 : Lit), (8 : Lit)]
  , [(-7 : Lit), (2 : Lit), (9 : Lit)]
  , [(-7 : Lit), (2 : Lit), (10 : Lit)]
  , [(-7 : Lit), (2 : Lit), (11 : Lit)]
  , [(-7 : Lit), (3 : Lit), (5 : Lit)]
  , [(-7 : Lit), (3 : Lit), (6 : Lit)]
  , [(-7 : Lit), (3 : Lit), (8 : Lit)]
  , [(-7 : Lit), (3 : Lit), (9 : Lit)]
  , [(-7 : Lit), (3 : Lit), (10 : Lit)]
  , [(-7 : Lit), (3 : Lit), (11 : Lit)]
  , [(-7 : Lit), (5 : Lit), (6 : Lit)]
  , [(-7 : Lit), (5 : Lit), (8 : Lit)]
  , [(-7 : Lit), (5 : Lit), (9 : Lit)]
  , [(-7 : Lit), (5 : Lit), (10 : Lit)]
  , [(-7 : Lit), (5 : Lit), (11 : Lit)]
  , [(-7 : Lit), (6 : Lit), (8 : Lit)]
  , [(-7 : Lit), (6 : Lit), (9 : Lit)]
  , [(-7 : Lit), (6 : Lit), (10 : Lit)]
  , [(-7 : Lit), (6 : Lit), (11 : Lit)]
  , [(-7 : Lit), (8 : Lit), (9 : Lit)]
  , [(-7 : Lit), (8 : Lit), (10 : Lit)]
  , [(-7 : Lit), (8 : Lit), (11 : Lit)]
  , [(-7 : Lit), (9 : Lit), (10 : Lit)]
  , [(-7 : Lit), (9 : Lit), (11 : Lit)]
  , [(-7 : Lit), (10 : Lit), (11 : Lit)]
  , [(-6 : Lit), (-5 : Lit), (-3 : Lit)]
  , [(-6 : Lit), (-4 : Lit), (-2 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-6 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-6 : Lit), (2 : Lit), (4 : Lit)]
  , [(-6 : Lit), (3 : Lit), (5 : Lit)]
  , [(-6 : Lit), (5 : Lit), (7 : Lit)]
  , [(-6 : Lit), (5 : Lit), (8 : Lit)]
  , [(-6 : Lit), (5 : Lit), (9 : Lit)]
  , [(-6 : Lit), (5 : Lit), (10 : Lit)]
  , [(-6 : Lit), (5 : Lit), (11 : Lit)]
  , [(-5 : Lit), (-4 : Lit), (-1 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (7 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (8 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (9 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (10 : Lit)]
  , [(-5 : Lit), (-3 : Lit), (11 : Lit)]
  , [(-5 : Lit), (1 : Lit), (4 : Lit)]
  , [(-5 : Lit), (3 : Lit), (6 : Lit)]
  , [(-5 : Lit), (6 : Lit), (7 : Lit)]
  , [(-5 : Lit), (6 : Lit), (8 : Lit)]
  , [(-5 : Lit), (6 : Lit), (9 : Lit)]
  , [(-5 : Lit), (6 : Lit), (10 : Lit)]
  , [(-5 : Lit), (6 : Lit), (11 : Lit)]
  , [(-4 : Lit), (1 : Lit), (5 : Lit)]
  , [(-4 : Lit), (2 : Lit), (6 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (1 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (2 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (1 : Lit), (7 : Lit)]
  , [(-3 : Lit), (1 : Lit), (8 : Lit)]
  , [(-3 : Lit), (1 : Lit), (9 : Lit)]
  , [(-3 : Lit), (1 : Lit), (10 : Lit)]
  , [(-3 : Lit), (1 : Lit), (11 : Lit)]
  , [(-3 : Lit), (2 : Lit), (7 : Lit)]
  , [(-3 : Lit), (2 : Lit), (8 : Lit)]
  , [(-3 : Lit), (2 : Lit), (9 : Lit)]
  , [(-3 : Lit), (2 : Lit), (10 : Lit)]
  , [(-3 : Lit), (2 : Lit), (11 : Lit)]
  , [(-3 : Lit), (5 : Lit), (6 : Lit)]
  , [(-3 : Lit), (5 : Lit), (7 : Lit)]
  , [(-3 : Lit), (5 : Lit), (8 : Lit)]
  , [(-3 : Lit), (5 : Lit), (9 : Lit)]
  , [(-3 : Lit), (5 : Lit), (10 : Lit)]
  , [(-3 : Lit), (5 : Lit), (11 : Lit)]
  , [(-3 : Lit), (6 : Lit), (7 : Lit)]
  , [(-3 : Lit), (6 : Lit), (8 : Lit)]
  , [(-3 : Lit), (6 : Lit), (9 : Lit)]
  , [(-3 : Lit), (6 : Lit), (10 : Lit)]
  , [(-3 : Lit), (6 : Lit), (11 : Lit)]
  , [(-3 : Lit), (7 : Lit), (8 : Lit)]
  , [(-3 : Lit), (7 : Lit), (9 : Lit)]
  , [(-3 : Lit), (7 : Lit), (10 : Lit)]
  , [(-3 : Lit), (7 : Lit), (11 : Lit)]
  , [(-3 : Lit), (8 : Lit), (9 : Lit)]
  , [(-3 : Lit), (8 : Lit), (10 : Lit)]
  , [(-3 : Lit), (8 : Lit), (11 : Lit)]
  , [(-3 : Lit), (9 : Lit), (10 : Lit)]
  , [(-3 : Lit), (9 : Lit), (11 : Lit)]
  , [(-3 : Lit), (10 : Lit), (11 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (3 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (7 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (8 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (9 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (10 : Lit)]
  , [(-2 : Lit), (-1 : Lit), (11 : Lit)]
  , [(-2 : Lit), (4 : Lit), (6 : Lit)]
  , [(-1 : Lit), (4 : Lit), (5 : Lit)]
  , [(1 : Lit), (2 : Lit), (3 : Lit)]
  , [(1 : Lit), (2 : Lit), (7 : Lit)]
  , [(1 : Lit), (2 : Lit), (8 : Lit)]
  , [(1 : Lit), (2 : Lit), (9 : Lit)]
  , [(1 : Lit), (2 : Lit), (10 : Lit)]
  , [(1 : Lit), (2 : Lit), (11 : Lit)]
  ]

def alt5GPivots : List Lit := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

def alt5GVres : List Nat := [1, 2, 4, 5, 6, 8]

theorem alt5GVres_eq_alt : alt5GVres = alt5Vres := by native_decide

def alt5GClosedUnder (S : List Clause) (w : Nat) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R => decide (w < clauseWidth R) || S.contains R

theorem alt5G_closed_bool : alt5GClosedUnder alt5GClosed 3 alt5GPivots = true := by
  native_decide

theorem alt5G_lits_in_pivots :
    (alt5GClosed.all fun C => C.all fun lit => decide (lit ∈ alt5GPivots)) = true := by
  native_decide

theorem alt5G_pivot
    {C D R : Clause} {p : Lit}
    (hC : C ∈ alt5GClosed) (hRes : resolveOriented C D p = some R) :
    p ∈ alt5GPivots := by
  obtain ⟨_, hpC, _⟩ := resolveOriented_some_mem hRes
  have hCall := (List.all_eq_true.mp alt5G_lits_in_pivots) C hC
  exact of_decide_eq_true ((List.all_eq_true.mp hCall) p hpC)

theorem alt5G_mem_of_closed
    {S : List Clause} {w : Nat} {pivots : List Lit}
    (hbool : alt5GClosedUnder S w pivots = true)
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

def alt5GClosure : WidthClosure 3 where
  axioms := alt5GAxioms
  mem := fun C => C ∈ alt5GClosed
  axiom_mem := by
    intro C hC _
    have h : (alt5GAxioms.all fun A => alt5GClosed.contains A) = true := by
      native_decide
    exact (List.contains_iff_mem).mp ((List.all_eq_true.mp h) C hC)
  closed := by
    intro C D R p hC hD hRes hw
    exact alt5G_mem_of_closed alt5G_closed_bool hC hD hRes hw (alt5G_pivot hC hRes)

theorem alt5G_no_empty : ¬ alt5GClosure.mem [] := by
  simp [alt5GClosure]
  native_decide

def alt5GProjOK : Bool :=
  alt5GClosed.all fun C =>
    !(supportedOn C alt5Vres) || alt5RClosed.contains C

theorem alt5GProjOK_true : alt5GProjOK = true := by native_decide

theorem alt5G_supported_in_R
    {C : Clause} (hG : C ∈ alt5GClosed) (hsup : supportedOn C alt5Vres = true) :
    C ∈ alt5RClosed := by
  have hall := (List.all_eq_true.mp alt5GProjOK_true) C hG
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hall
  cases hall with
  | inl h => exact absurd hsup (by simpa using h)
  | inr h => exact (List.contains_iff_mem).mp h

def alt5GProjection : ProjectionInclusion 3 where
  gClosure := alt5GClosure
  rClosure := alt5RClosure
  Vres := alt5Vres
  holds := fun _ hG hsup => alt5G_supported_in_R hG hsup

def alt5GEliminationStep : EliminationStep 3 where
  before := alt5GClosure
  after := alt5RClosure
  V_after := alt5Vres
  preserves := fun _ hB hsup => alt5G_supported_in_R hB hsup

theorem alt5G_no_empty_of_projection :
    ¬ alt5GProjection.gClosure.mem [] :=
  no_empty_of_projection alt5GProjection alt5R_closure_no_empty

theorem alt5_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt5TopologyRename alt5RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt5GProjection.gClosure.mem [] :=
  ⟨(alt5_global_edge_iso_to_residualAxioms e).1,
    (alt5_global_edge_iso_to_residualAxioms e).2,
    alt5G_no_empty_of_projection⟩

def alt5GDoc : String :=
  "fresh G₀ Closure₃ for alt5; ProjectionInclusion beyond packs"

end PNPLab.Resolution
