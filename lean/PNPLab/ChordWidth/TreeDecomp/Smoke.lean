/-
  Proved tree-decomposition certificates for small smoke cores (K₄, C₄).
-/

import PNPLab.ChordWidth.TreeDecomp.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace PNPLab.ChordWidth

open SimpleGraph

theorem k4_hasTreeDecomp_three :
    TreeDecomp.HasTreeDecomp (⊤ : SimpleGraph (Fin 4)) 3 := by
  have h := TreeDecomp.hasTreeDecomp_trivial (⊤ : SimpleGraph (Fin 4))
  simpa using h

theorem fourCycle_hasTreeDecomp_at_most_three :
    TreeDecomp.HasTreeDecomp (cycleGraph 4) 3 :=
  TreeDecomp.hasTreeDecomp_trivial (cycleGraph 4)

def smokeTreeDecompDoc : String :=
  "K₄ HasTreeDecomp 3; C₄ HasTreeDecomp 3 via trivial decomposition."

end PNPLab.ChordWidth
