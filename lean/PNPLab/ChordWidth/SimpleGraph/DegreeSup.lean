/-
  Sup degree bounds (ChordWidth Δ ≤ 3 track).

  Minimal `⊔` neighbor finset lemmas; cycle/chord bounds in `DegreeBounds.lean`.
-/

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace PNPLab.ChordWidth

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem neighborSet_sup (G H : SimpleGraph V) (v : V) :
    (G ⊔ H).neighborSet v = G.neighborSet v ∪ H.neighborSet v := by
  ext w
  simp [mem_neighborSet, sup_adj, Set.mem_union]

theorem neighborFinset_sup (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (v : V) : (G ⊔ H).neighborFinset v = G.neighborFinset v ∪ H.neighborFinset v := by
  ext w
  simp [mem_neighborFinset, sup_adj]

theorem degree_sup_le_add (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (v : V) :
    (G ⊔ H).degree v ≤ G.degree v + H.degree v := by
  rw [degree, degree, degree, neighborFinset_sup]
  exact Finset.card_union_le _ _

theorem degree_le_degree_sup (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (v : V) :
    G.degree v ≤ (G ⊔ H).degree v := by
  rw [degree, degree, neighborFinset_sup]
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_union_left _ hw

theorem degree_sup_sup_le_add (G H K : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] [DecidableRel K.Adj] (v : V) :
    (G ⊔ H ⊔ K).degree v ≤ G.degree v + H.degree v + K.degree v := by
  calc
    (G ⊔ H ⊔ K).degree v ≤ (G ⊔ H).degree v + K.degree v := degree_sup_le_add _ _ v
    _ ≤ G.degree v + H.degree v + K.degree v := by
      exact Nat.add_le_add_right (degree_sup_le_add G H v) _

/-! ### Single-edge degrees -/

private theorem neighborFinset_edge_fst {s t : V} (h : s ≠ t) :
    (edge s t).neighborFinset s = {t} := by
  ext w
  simp only [mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hadj
    have := (edge_adj s t s w).1 hadj
    rcases this.1 with (⟨_, hw⟩ | ⟨heq, _⟩)
    · exact hw
    · exact absurd heq h
  · intro hw
    subst hw
    exact (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, h⟩

private theorem neighborFinset_edge_snd {s t : V} (h : s ≠ t) :
    (edge s t).neighborFinset t = {s} := by
  ext w
  simp only [mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hadj
    have := (edge_adj s t t w).1 hadj
    rcases this.1 with (⟨heq, _⟩ | ⟨_, hw⟩)
    · exact absurd heq h.symm
    · exact hw
  · intro hw
    subst hw
    exact (edge_adj ..).2 ⟨Or.inr ⟨rfl, rfl⟩, h.symm⟩

theorem degree_edge_endpoint {s t : V} (h : s ≠ t) :
    (edge s t).degree s = 1 := by
  rw [degree, neighborFinset_edge_fst h, Finset.card_singleton]

theorem degree_edge_snd {s t : V} (h : s ≠ t) :
    (edge s t).degree t = 1 := by
  rw [degree, neighborFinset_edge_snd h, Finset.card_singleton]

theorem degree_edge_nonendpoint {s t u : V} (hs : u ≠ s) (ht : u ≠ t) :
    (edge s t).degree u = 0 := by
  rw [degree, show (edge s t).neighborFinset u = ∅ from by
    ext w
    simp only [mem_neighborFinset, Finset.notMem_empty, iff_false]
    intro hadj
    rcases (edge_adj s t u w).1 hadj with (⟨heq, _⟩ | ⟨_, heq⟩) <;> contradiction]
  exact Finset.card_empty

theorem degree_edge_add_degree_edge_le_one_of_endpoint_disjoint {s t u v w : V}
    (hst : s ≠ t) (huv : u ≠ v)
    (hdisj : s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v) :
    (edge s t).degree w + (edge u v).degree w ≤ 1 := by
  by_cases hw1 : w = s ∨ w = t
  · rcases hw1 with hw | hw
    · rw [show (edge s t).degree w = 1 from by rw [hw, degree_edge_endpoint hst],
        show (edge u v).degree w = 0 from by rw [hw, degree_edge_nonendpoint hdisj.1 hdisj.2.1]]
    · rw [show (edge s t).degree w = 1 from by rw [hw, degree_edge_snd hst],
        show (edge u v).degree w = 0 from by
          rw [hw]; exact degree_edge_nonendpoint hdisj.2.2.1 hdisj.2.2.2]
  · have hz : (edge s t).degree w = 0 := by
      have hns : w ≠ s := fun h => hw1 (Or.inl h)
      have hnt : w ≠ t := fun h => hw1 (Or.inr h)
      exact degree_edge_nonendpoint hns hnt
    by_cases hw2 : w = u ∨ w = v
    · rcases hw2 with hw | hw
      · rw [hz, show (edge u v).degree w = 1 from by rw [hw, degree_edge_endpoint huv]]
      · rw [hz, show (edge u v).degree w = 1 from by rw [hw, degree_edge_snd huv]]
    · have hy : (edge u v).degree w = 0 := by
        have hnu : w ≠ u := fun h => hw2 (Or.inl h)
        have hnv : w ≠ v := fun h => hw2 (Or.inr h)
        exact degree_edge_nonendpoint hnu hnv
      simp [hz, hy]

theorem neighborFinset_sup_edge_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V}
    (hne : s ≠ t) (hn : ¬ G.Adj s t) :
    (G ⊔ edge s t).neighborFinset s = insert t (G.neighborFinset s) := by
  ext w
  simp [neighborFinset_sup, mem_neighborFinset, sup_adj, Finset.mem_union, Finset.mem_insert]
  constructor
  · intro h
    rcases h with (hG | hE)
    · exact Or.inr hG
    · have := (edge_adj s t s w).1 hE
      rcases this.1 with (⟨_, hw⟩ | ⟨hw, _⟩)
      · exact Or.inl hw
      · exact absurd hw hne
  · intro h
    rcases h with (rfl | hG)
    · exact Or.inr ((edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
    · exact Or.inl hG

theorem degree_sup_edge_endpoint_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V}
    (hne : s ≠ t) (hn : ¬ G.Adj s t) :
    (G ⊔ edge s t).degree s = G.degree s + 1 := by
  rw [degree, neighborFinset_sup_edge_of_not_adj G hne hn, degree,
    Finset.card_insert_of_notMem]
  intro h
  exact hn ((mem_neighborFinset G s t).1 h)

/-! ### Cycle graph degrees -/

theorem cycleGraph_degree_eq_two_of_four_le {n : Nat} (hn : 4 ≤ n) (v : Fin n) :
    (cycleGraph n).degree v = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  subst hk
  exact cycleGraph_degree_three_le

end PNPLab.ChordWidth
