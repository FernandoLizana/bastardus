/-
  Auto-generated certPathGraph IsTree lemmas for smoke line-graph orders.
-/

import PNPLab.ChordWidth.TreeDecomp.CertPathGraph

namespace PNPLab.ChordWidth

namespace SmokeLineGraphCert

open SimpleGraph

theorem certPathGraph8_isTree : (certPathGraph 8).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 8).symm ▸ pathGraph_connected 7, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph9_isTree : (certPathGraph 9).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 9).symm ▸ pathGraph_connected 8, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph11_isTree : (certPathGraph 11).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 11).symm ▸ pathGraph_connected 10, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph12_isTree : (certPathGraph 12).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 12).symm ▸ pathGraph_connected 11, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

end SmokeLineGraphCert

end PNPLab.ChordWidth
