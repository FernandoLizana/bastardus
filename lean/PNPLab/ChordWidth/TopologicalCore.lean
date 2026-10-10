/-
  Topological core classification: theta, four-branch, degenerate.
-/

import PNPLab.ChordWidth.ChordDiagram
import PNPLab.ChordWidth.IntersectionGraph

namespace PNPLab.ChordWidth

open Classical

inductive TopologicalCoreKind where
  | theta
  | fourBranch
  | degenerate
  | general
  deriving DecidableEq, Repr

/-- Core kind for k = 2 diagrams (theta vs four-branch via intersection graph). -/
noncomputable def ChordDiagram.topologicalCoreKindTwo (D : ChordDiagram n 2) : TopologicalCoreKind :=
  if D.intersectionGraphAdj 0 1 then .theta else .fourBranch

def topologicalCoreDoc : String :=
  "theta = cruce (tipo K₄); fourBranch = sin cruce (tipo C₄); k≠2 → general (ver ChordDiagram)."

end PNPLab.ChordWidth
