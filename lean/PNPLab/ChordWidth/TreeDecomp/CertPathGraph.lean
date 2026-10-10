/-
  Decidable path graphs for tree-decomposition certificates (Mathlib `pathGraph`
  lacks `DecidableRel` on `Adj` in v4.32.0).
-/

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace PNPLab.ChordWidth

open SimpleGraph

namespace SmokeLineGraphCert

def certPathGraphAdj (n : Nat) (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

instance (n : Nat) : DecidableRel (certPathGraphAdj n) := fun i j =>
  if h : i.val + 1 = j.val then isTrue (Or.inl h)
  else if h : j.val + 1 = i.val then isTrue (Or.inr h)
  else isFalse fun h => by cases h <;> simp_all

instance certPathGraphAdj_symmInst (n : Nat) : Std.Symm (certPathGraphAdj n) where
  symm := fun _ _ h => by cases h with | inl h => exact Or.inr h | inr h => exact Or.inl h

instance certPathGraphAdj_irreflInst (n : Nat) : Std.Irrefl (certPathGraphAdj n) where
  irrefl := fun i h => by cases h <;> omega

def certPathGraph (n : Nat) : SimpleGraph (Fin n) where
  Adj := certPathGraphAdj n
  symm := inferInstance
  loopless := inferInstance

instance (n : Nat) : DecidableRel (certPathGraph n).Adj := fun i j =>
  inferInstanceAs (Decidable (certPathGraphAdj n i j))

theorem certPathGraph_eq_pathGraph (n : Nat) : certPathGraph n = pathGraph n := by
  ext i j
  simp [certPathGraph, pathGraph, certPathGraphAdj]

theorem certPathGraph7_isTree : (certPathGraph 7).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 7).symm ▸ pathGraph_connected 6, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph10_isTree : (certPathGraph 10).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 10).symm ▸ pathGraph_connected 9, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph_one_isTree : (certPathGraph 1).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 1).symm ▸ pathGraph_connected 0, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  decide

theorem certPathGraph_two_isTree : (certPathGraph 2).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 2).symm ▸ pathGraph_connected 1, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem certPathGraph6_isTree : (certPathGraph 6).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph 6).symm ▸ pathGraph_connected 5, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

def certPathGraphInterval (n a b : Nat) : Set (Fin n) :=
  {w : Fin n | a ≤ w.val ∧ w.val ≤ b}

theorem certPathGraph_adj_succ {n : Nat} (i : Fin n) (h : i.val + 1 < n) :
    (certPathGraph n).Adj i ⟨i.val + 1, h⟩ := by
  simp [certPathGraph, certPathGraphAdj]

theorem certPathGraph_induce_interval_preconnected (n a b : Nat) (ha : a < n) (hb : b < n)
    (hab : a ≤ b) :
    (certPathGraph n).induce (certPathGraphInterval n a b) |>.Preconnected := by
  classical
  by_cases hab_eq : a = b
  · subst hab_eq
    have hset : certPathGraphInterval n a a = {⟨a, ha⟩} := by
      ext w
      simp only [certPathGraphInterval, Set.mem_setOf_eq, Set.mem_singleton_iff, Fin.ext_iff]
      constructor
      · intro ⟨h1, h2⟩
        exact le_antisymm h2 h1
      · intro hw
        subst hw
        exact ⟨le_rfl, le_rfl⟩
    rw [hset]
    exact Preconnected.of_subsingleton
  · have hb_pos : a < b := Nat.lt_of_le_of_ne hab hab_eq
    have hb1_le : a ≤ b - 1 := by omega
    have hb1_lt : b - 1 < n := by omega
    have ih := certPathGraph_induce_interval_preconnected n a (b - 1) ha hb1_lt hb1_le
    have hadj : (certPathGraph n).Adj ⟨b - 1, hb1_lt⟩ ⟨b, hb⟩ := by
      have h : (b - 1) + 1 = b := Nat.sub_add_cancel (Nat.one_le_of_lt hb_pos)
      have hlt : (b - 1) + 1 < n := h ▸ hb
      simpa [h, Fin.mk_val] using certPathGraph_adj_succ ⟨b - 1, hb1_lt⟩ hlt
    have hmem_left : (⟨b - 1, hb1_lt⟩ : Fin n) ∈ certPathGraphInterval n a (b - 1) := by
      simp [certPathGraphInterval]
      omega
    have hmem_right : (⟨b, hb⟩ : Fin n) ∈ certPathGraphInterval n b b := by
      simp [certPathGraphInterval]
    have hunion :
        certPathGraphInterval n a b = certPathGraphInterval n a (b - 1) ∪ certPathGraphInterval n b b := by
      ext w
      simp only [certPathGraphInterval, Set.mem_setOf_eq, Set.mem_union, Fin.ext_iff]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hw : w.val = b
        · right
          simp [hw, certPathGraphInterval]
        · left
          exact ⟨h1, by omega⟩
      · intro h
        cases h with
        | inl h => exact ⟨h.1, by omega⟩
        | inr h => exact ⟨by omega, h.2⟩
    have hsingleton : certPathGraphInterval n b b = {⟨b, hb⟩} := by
      ext w
      simp only [certPathGraphInterval, Set.mem_setOf_eq, Set.mem_singleton_iff, Fin.ext_iff]
      constructor
      · intro ⟨h1, h2⟩
        exact le_antisymm h2 h1
      · intro hw
        subst hw
        exact ⟨le_rfl, le_rfl⟩
    have tconn : (certPathGraph n).induce (certPathGraphInterval n b b) |>.Preconnected := by
      rw [hsingleton]
      exact Preconnected.of_subsingleton
    have hconn := connected_induce_union (G := certPathGraph n)
      (s := certPathGraphInterval n a (b - 1)) (t := certPathGraphInterval n b b)
      ih tconn hmem_left hmem_right hadj
    rw [hunion]
    exact hconn.preconnected
  termination_by b - a
  decreasing_by
    all_goals omega

end SmokeLineGraphCert

end PNPLab.ChordWidth
