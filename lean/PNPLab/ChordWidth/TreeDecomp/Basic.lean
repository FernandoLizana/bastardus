/-
  Minimal faithful tree decomposition API for ChordWidth (v4.32.0 pin).
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace PNPLab.ChordWidth

open SimpleGraph

universe u

variable {V : Type u}

structure TreeDecomp (G : SimpleGraph V) (m : Nat) where
  bag : Fin m → Finset V
  tree : SimpleGraph (Fin m)
  isTree : IsTree tree
  vertexCover : ∀ x : V, ∃ w : Fin m, x ∈ bag w
  edgeCover : ∀ ⦃a b : V⦄, G.Adj a b → ∃ w : Fin m, a ∈ bag w ∧ b ∈ bag w
  preconnected_induce_T :
    ∀ x : V, (tree.induce ({w | x ∈ bag w})).Preconnected

namespace TreeDecomp

variable {G : SimpleGraph V}

noncomputable def width {m : Nat} (t : TreeDecomp G m) : Nat :=
  (Finset.univ : Finset (Fin m)).sup fun w => (t.bag w).card - 1

noncomputable def trivialDecomp (G : SimpleGraph V) [Fintype V] : TreeDecomp G 1 where
  bag := fun _ => Finset.univ
  tree := ⊥
  isTree := IsTree.of_subsingleton
  vertexCover := fun x => ⟨0, Finset.mem_univ x⟩
  edgeCover := fun _ _ _ => ⟨0, by simp⟩
  preconnected_induce_T := fun _ => by
    have : ({w : Fin 1 | True} : Set (Fin 1)) = Set.univ := by ext; simp
    simpa [this] using Preconnected.of_subsingleton

lemma trivialDecomp_width [Fintype V] (G : SimpleGraph V) :
    (trivialDecomp G).width = Fintype.card V - 1 := by
  unfold width trivialDecomp
  simp [Finset.card_univ]

def HasTreeDecomp (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ (m : Nat) (t : TreeDecomp G m), t.width ≤ k

lemma hasTreeDecomp_trivial [Fintype V] (G : SimpleGraph V) :
    HasTreeDecomp (G := G) (Fintype.card V - 1) :=
  ⟨1, trivialDecomp G, by rw [trivialDecomp_width]⟩

def mapIso {W : Type u} {H : SimpleGraph W} [DecidableEq W] (φ : G ≃g H) (t : TreeDecomp G m) :
    TreeDecomp H m where
  bag w := (t.bag w).image φ
  tree := t.tree
  isTree := t.isTree
  vertexCover := by
    intro x
    obtain ⟨w, hw⟩ := t.vertexCover (φ.symm x)
    exact ⟨w, by simpa using Finset.mem_image_of_mem φ hw⟩
  edgeCover := by
    intro a b hab
    have hadj : G.Adj (φ.symm a) (φ.symm b) := by
      rw [← φ.map_adj_iff]
      simp [φ.apply_symm_apply]
      exact hab
    obtain ⟨w, ha, hb⟩ := t.edgeCover hadj
    refine ⟨w, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨φ.symm a, ha, φ.apply_symm_apply a⟩
    · exact Finset.mem_image.mpr ⟨φ.symm b, hb, φ.apply_symm_apply b⟩
  preconnected_induce_T := by
    intro x
    have hset : {w : Fin m | x ∈ (t.bag w).image φ} = {w : Fin m | φ.symm x ∈ t.bag w} := by
      ext w
      simp only [Finset.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ⟨y, hy, hxy⟩
        have : φ.symm x = y := by rw [← hxy, φ.symm_apply_apply y]
        rwa [this]
      · intro hy
        exact ⟨φ.symm x, hy, φ.apply_symm_apply x⟩
    rw [hset]
    exact t.preconnected_induce_T (φ.symm x)

lemma mapIso_width {W : Type u} {H : SimpleGraph W} [DecidableEq W] (φ : G ≃g H) (t : TreeDecomp G m) :
    (t.mapIso φ).width = t.width := by
  unfold width mapIso
  refine Finset.sup_congr rfl fun w _ => ?_
  rw [Finset.card_image_of_injective (s := t.bag w) (f := φ) φ.injective]

lemma hasTreeDecomp_mapIso {W : Type u} {H : SimpleGraph W} [DecidableEq W] (φ : G ≃g H) (k : Nat)
    (h : HasTreeDecomp G k) : HasTreeDecomp H k := by
  obtain ⟨m, t, ht⟩ := h
  exact ⟨m, t.mapIso φ, by rw [mapIso_width φ t]; exact ht⟩

lemma hasTreeDecomp_congr {G' : SimpleGraph V} (h : G = G') (k : Nat) (hk : HasTreeDecomp G k) :
    HasTreeDecomp G' k :=
  h ▸ hk

/-- Base-graph equality transports `HasTreeDecomp` on line graphs (same vertex type `V`). -/
lemma hasTreeDecomp_lineGraph_base_eq {V : Type u} [Fintype V] [DecidableEq V]
    {G G' : SimpleGraph V} (h : G = G') (k : Nat)
    (hk : HasTreeDecomp (lineGraph G') k) : HasTreeDecomp (lineGraph G) k := by
  subst h
  exact hk

end TreeDecomp

end PNPLab.ChordWidth
