/-
  Auto-generated certPathGraph IsTree lemmas for asymptotic line-graph orders.
-/

import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes

namespace PNPLab.ChordWidth

namespace AsymptoticLineGraphCert

open SimpleGraph
open SmokeLineGraphCert (certPathGraph certPathGraph_eq_pathGraph)

theorem certPathGraph15_isTree : (certPathGraph 15).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 15).symm ▸ pathGraph_connected 14, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

end AsymptoticLineGraphCert

end PNPLab.ChordWidth
