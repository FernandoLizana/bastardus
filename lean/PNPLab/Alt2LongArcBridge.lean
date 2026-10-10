/-
  alt2 fresh G₀ is exactly LongArc (same instance: C₆ + (0,2),(1,3)).
-/

import PNPLab.LongArcProjection
import PNPLab.AltResidualClosures
import PNPLab.ResidualAxiomsFromEndpoints
import PNPLab.RenameClosedTransport

namespace PNPLab.Resolution

theorem alt2Vres_eq_laVres : alt2Vres = laVres := by native_decide

theorem alt2RClosed_eq_laRClosed :
    clauseListSetEq alt2RClosed laRClosed = true := by native_decide

/-- Reuse LongArc G₀→R as alt2 fresh projection. -/
def alt2GProjection : ProjectionInclusion 3 := laProjection

theorem alt2G_no_empty_of_projection :
    ¬ alt2GProjection.gClosure.mem [] :=
  la_no_empty_of_projection

theorem alt2_fresh_g0_projects (e : Bicyclic.CrossingEndpoints) :
    topologySetEq alt2TopologyRename alt2RClosed = true ∧
      residualAxioms e = k4Axioms ∧
      ¬ alt2GProjection.gClosure.mem [] :=
  ⟨(alt2_global_edge_iso_to_residualAxioms e).1,
    (alt2_global_edge_iso_to_residualAxioms e).2,
    alt2G_no_empty_of_projection⟩

def alt2FreshG0Doc : String :=
  "alt2 fresh G₀ = LongArc laProjection (identical instance)"

end PNPLab.Resolution
