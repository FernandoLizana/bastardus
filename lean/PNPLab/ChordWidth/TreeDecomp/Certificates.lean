/-
  Verified tree-decomposition certificates for smoke line graphs (c5/c8).

  Python export: `reports/tree_decomp_certificates/*.json`.
-/

import PNPLab.ChordWidth.TreeDecomp.Basic
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace SmokeLineGraphCert

def bagSupWidth {α : Type*} {m : Nat} (bags : Fin m → Finset α) : Nat :=
  (List.finRange m).foldl (fun acc i => Nat.max acc ((bags i).card - 1)) 0

def graphOfEdgeList7Adj (edges : List (Nat × Nat)) (i j : Fin 7) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList7Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList7Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList7Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList7Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList7 (edges : List (Nat × Nat)) : SimpleGraph (Fin 7) where
  Adj := graphOfEdgeList7Adj edges
  symm := inferInstance
  loopless := inferInstance

def graphOfEdgeList10Adj (edges : List (Nat × Nat)) (i j : Fin 10) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList10Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList10Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList10Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList10Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList10 (edges : List (Nat × Nat)) : SimpleGraph (Fin 10) where
  Adj := graphOfEdgeList10Adj edges
  symm := inferInstance
  loopless := inferInstance

/-! ### c5 crossing: tw = 4 -/

def c5Ofold_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 6), (3, 4), (3, 5), (4, 5), (4, 6),
    (5, 6)]

def c5Ofold_lineGraphFin : SimpleGraph (Fin 7) :=
  graphOfEdgeList7 c5Ofold_lineEdges

def c5Ofold_bag : Fin 7 → Finset (Fin 7)
  | 0 => {0, 1, 2, 6}
  | 1 => {0, 1, 3, 4, 6}
  | 2 => {1, 3, 4, 5, 6}
  | 3 => {3, 4, 5, 6}
  | 4 => {4, 5, 6}
  | 5 => {5, 6}
  | 6 => {6}

theorem c5Ofold_edgeCover :
    ∀ ⦃a b : Fin 7⦄, c5Ofold_lineGraphFin.Adj a b →
      ∃ w : Fin 7, a ∈ c5Ofold_bag w ∧ b ∈ c5Ofold_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c5Ofold_lineGraphFin, graphOfEdgeList7, graphOfEdgeList7Adj, c5Ofold_lineEdges, c5Ofold_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c5Ofold_preconnected_bag (x : Fin 7) (a b : Nat)
    (ha : a < 7) (hb : b < 7) (hab : a ≤ b)
    (hset : {w : Fin 7 | x ∈ c5Ofold_bag w} = certPathGraphInterval 7 a b) :
    (certPathGraph 7).induce {w : Fin 7 | x ∈ c5Ofold_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 7 a b ha hb hab

noncomputable def c5Ofold_fin_decomp : TreeDecomp c5Ofold_lineGraphFin 7 where
  bag := c5Ofold_bag
  tree := certPathGraph 7
  isTree := certPathGraph7_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c5Ofold_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c5Ofold_preconnected_bag 0 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · exact c5Ofold_preconnected_bag 1 0 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · exact c5Ofold_preconnected_bag 2 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · exact c5Ofold_preconnected_bag 3 1 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · exact c5Ofold_preconnected_bag 4 1 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · exact c5Ofold_preconnected_bag 5 2 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide)
    · have hset : {w : Fin 7 | (6 : Fin 7) ∈ c5Ofold_bag w} = certPathGraphInterval 7 0 6 := by
        ext w; fin_cases w <;> simp [certPathGraphInterval, c5Ofold_bag] <;> decide
      exact c5Ofold_preconnected_bag 6 0 6 (by decide) (by decide) (by decide) hset

theorem c5Ofold_fin_bagSupWidth : bagSupWidth c5Ofold_bag ≤ 4 := by native_decide

theorem c5Ofold_fin_hasTreeDecomp_four : HasTreeDecomp c5Ofold_lineGraphFin 4 := by
  refine ⟨7, c5Ofold_fin_decomp, ?_⟩
  have hw : c5Ofold_fin_decomp.width = bagSupWidth c5Ofold_bag := by
    dsimp [TreeDecomp.width, c5Ofold_fin_decomp, c5Ofold_bag, bagSupWidth]
    native_decide
  exact hw ▸ c5Ofold_fin_bagSupWidth

/-! ### c8 nested: tw = 3 -/

def c8Nested_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 8), (1, 9), (2, 9), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6),
    (5, 7), (6, 7), (7, 8), (8, 9)]

def c8Nested_lineGraphFin : SimpleGraph (Fin 10) :=
  graphOfEdgeList10 c8Nested_lineEdges

def c8Nested_bag : Fin 10 → Finset (Fin 10)
  | 0 => {0, 1, 2, 3}
  | 1 => {1, 2, 3, 9}
  | 2 => {1, 3, 8, 9}
  | 3 => {3, 8, 9}
  | 4 => {3, 7, 8}
  | 5 => {3, 4, 5, 7}
  | 6 => {4, 5, 6, 7}
  | 7 => {5, 6, 7}
  | 8 => {6, 7}
  | 9 => {7}

theorem c8Nested_edgeCover :
    ∀ ⦃a b : Fin 10⦄, c8Nested_lineGraphFin.Adj a b →
      ∃ w : Fin 10, a ∈ c8Nested_bag w ∧ b ∈ c8Nested_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c8Nested_lineGraphFin, graphOfEdgeList10, graphOfEdgeList10Adj, c8Nested_lineEdges, c8Nested_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c8Nested_preconnected_bag (x : Fin 10) (a b : Nat)
    (ha : a < 10) (hb : b < 10) (hab : a ≤ b)
    (hset : {w : Fin 10 | x ∈ c8Nested_bag w} = certPathGraphInterval 10 a b) :
    (certPathGraph 10).induce {w : Fin 10 | x ∈ c8Nested_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 10 a b ha hb hab

noncomputable def c8Nested_fin_decomp : TreeDecomp c8Nested_lineGraphFin 10 where
  bag := c8Nested_bag
  tree := certPathGraph 10
  isTree := certPathGraph10_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c8Nested_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c8Nested_preconnected_bag 0 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 1 0 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 2 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 3 0 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 4 5 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 5 5 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 6 6 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 7 4 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 8 2 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)
    · exact c8Nested_preconnected_bag 9 1 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Nested_bag] <;> decide)

theorem c8Nested_fin_bagSupWidth : bagSupWidth c8Nested_bag ≤ 3 := by native_decide

theorem c8Nested_fin_hasTreeDecomp_three : HasTreeDecomp c8Nested_lineGraphFin 3 := by
  refine ⟨10, c8Nested_fin_decomp, ?_⟩
  have hw : c8Nested_fin_decomp.width = bagSupWidth c8Nested_bag := by
    dsimp [TreeDecomp.width, c8Nested_fin_decomp, c8Nested_bag, bagSupWidth]
    native_decide
  exact hw ▸ c8Nested_fin_bagSupWidth

def smokeLineGraphCertDoc : String :=
  "Fin-indexed HasTreeDecomp: c5 tw=4, c8 nested tw=3; see CertificatesLine for L(G) transport."

end SmokeLineGraphCert

end PNPLab.ChordWidth
