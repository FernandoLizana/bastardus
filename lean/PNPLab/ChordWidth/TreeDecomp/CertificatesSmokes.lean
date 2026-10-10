/-
  Auto-generated Fin-indexed tree-decomposition certificates (c6–c10, c8Crossing).
  Regenerate: `PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_smokes.py`
-/

import PNPLab.ChordWidth.TreeDecomp.Certificates
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace SmokeLineGraphCert

open SmokeLineGraphCert (bagSupWidth)

def graphOfEdgeList8Adj (edges : List (Nat × Nat)) (i j : Fin 8) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList8Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList8Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList8Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList8Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList8 (edges : List (Nat × Nat)) : SimpleGraph (Fin 8) where
  Adj := graphOfEdgeList8Adj edges
  symm := inferInstance
  loopless := inferInstance

def graphOfEdgeList9Adj (edges : List (Nat × Nat)) (i j : Fin 9) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList9Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList9Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList9Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList9Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList9 (edges : List (Nat × Nat)) : SimpleGraph (Fin 9) where
  Adj := graphOfEdgeList9Adj edges
  symm := inferInstance
  loopless := inferInstance

def graphOfEdgeList11Adj (edges : List (Nat × Nat)) (i j : Fin 11) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList11Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList11Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList11Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList11Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList11 (edges : List (Nat × Nat)) : SimpleGraph (Fin 11) where
  Adj := graphOfEdgeList11Adj edges
  symm := inferInstance
  loopless := inferInstance

def graphOfEdgeList12Adj (edges : List (Nat × Nat)) (i j : Fin 12) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList12Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList12Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList12Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList12Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList12 (edges : List (Nat × Nat)) : SimpleGraph (Fin 12) where
  Adj := graphOfEdgeList12Adj edges
  symm := inferInstance
  loopless := inferInstance
/-! ### c6Crossing: tw = 4 -/
def c6Crossing_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 7), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6), (6, 7)]
def c6Crossing_lineGraphFin : SimpleGraph (Fin 8) :=
  graphOfEdgeList8 c6Crossing_lineEdges
def c6Crossing_bag : Fin 8 → Finset (Fin 8)
  | 0 => {2, 6, 7}
  | 1 => {0, 1, 2, 6}
  | 2 => {0, 1, 3, 4, 6}
  | 3 => {1, 3, 4, 5, 6}
  | 4 => {3, 4, 5, 6}
  | 5 => {4, 5, 6}
  | 6 => {5, 6}
  | 7 => {6}
theorem c6Crossing_edgeCover :
    ∀ ⦃a b : Fin 8⦄, c6Crossing_lineGraphFin.Adj a b →
      ∃ w : Fin 8, a ∈ c6Crossing_bag w ∧ b ∈ c6Crossing_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c6Crossing_lineGraphFin, graphOfEdgeList8, graphOfEdgeList8Adj, c6Crossing_lineEdges, c6Crossing_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c6Crossing_preconnected_bag (x : Fin 8) (a b : Nat)
    (ha : a < 8) (hb : b < 8) (hab : a ≤ b)
    (hset : {w : Fin 8 | x ∈ c6Crossing_bag w} = certPathGraphInterval 8 a b) :
    (certPathGraph 8).induce {w : Fin 8 | x ∈ c6Crossing_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 8 a b ha hb hab

noncomputable def c6Crossing_fin_decomp : TreeDecomp c6Crossing_lineGraphFin 8 where
  bag := c6Crossing_bag
  tree := certPathGraph 8
  isTree := certPathGraph8_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c6Crossing_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c6Crossing_preconnected_bag 0 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 1 1 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 2 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 3 2 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 4 2 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 5 3 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 6 0 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
    · exact c6Crossing_preconnected_bag 7 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c6Crossing_bag] <;> decide)
theorem c6Crossing_fin_bagSupWidth : bagSupWidth c6Crossing_bag ≤ 4 := by native_decide

theorem c6Crossing_fin_hasTreeDecomp_4 : HasTreeDecomp c6Crossing_lineGraphFin 4 := by
  refine ⟨8, c6Crossing_fin_decomp, ?_⟩
  have hw : c6Crossing_fin_decomp.width = bagSupWidth c6Crossing_bag := by
    dsimp [TreeDecomp.width, c6Crossing_fin_decomp, c6Crossing_bag, bagSupWidth]
    native_decide
  exact hw ▸ c6Crossing_fin_bagSupWidth

/-! ### c7Crossing: tw = 4 -/
def c7Crossing_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 8), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6), (6, 7), (7, 8)]
def c7Crossing_lineGraphFin : SimpleGraph (Fin 9) :=
  graphOfEdgeList9 c7Crossing_lineEdges
def c7Crossing_bag : Fin 9 → Finset (Fin 9)
  | 0 => {6, 7, 8}
  | 1 => {2, 6, 8}
  | 2 => {0, 1, 2, 6}
  | 3 => {0, 1, 3, 4, 6}
  | 4 => {1, 3, 4, 5, 6}
  | 5 => {3, 4, 5, 6}
  | 6 => {4, 5, 6}
  | 7 => {5, 6}
  | 8 => {6}
theorem c7Crossing_edgeCover :
    ∀ ⦃a b : Fin 9⦄, c7Crossing_lineGraphFin.Adj a b →
      ∃ w : Fin 9, a ∈ c7Crossing_bag w ∧ b ∈ c7Crossing_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c7Crossing_lineGraphFin, graphOfEdgeList9, graphOfEdgeList9Adj, c7Crossing_lineEdges, c7Crossing_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c7Crossing_preconnected_bag (x : Fin 9) (a b : Nat)
    (ha : a < 9) (hb : b < 9) (hab : a ≤ b)
    (hset : {w : Fin 9 | x ∈ c7Crossing_bag w} = certPathGraphInterval 9 a b) :
    (certPathGraph 9).induce {w : Fin 9 | x ∈ c7Crossing_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 9 a b ha hb hab

noncomputable def c7Crossing_fin_decomp : TreeDecomp c7Crossing_lineGraphFin 9 where
  bag := c7Crossing_bag
  tree := certPathGraph 9
  isTree := certPathGraph9_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c7Crossing_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c7Crossing_preconnected_bag 0 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 1 2 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 2 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 3 3 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 4 3 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 5 4 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 6 0 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 7 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
    · exact c7Crossing_preconnected_bag 8 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Crossing_bag] <;> decide)
theorem c7Crossing_fin_bagSupWidth : bagSupWidth c7Crossing_bag ≤ 4 := by native_decide

theorem c7Crossing_fin_hasTreeDecomp_4 : HasTreeDecomp c7Crossing_lineGraphFin 4 := by
  refine ⟨9, c7Crossing_fin_decomp, ?_⟩
  have hw : c7Crossing_fin_decomp.width = bagSupWidth c7Crossing_bag := by
    dsimp [TreeDecomp.width, c7Crossing_fin_decomp, c7Crossing_bag, bagSupWidth]
    native_decide
  exact hw ▸ c7Crossing_fin_bagSupWidth

/-! ### c7Nested: tw = 3 -/
def c7Nested_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (1, 5), (2, 7), (3, 4), (4, 5), (5, 6), (6, 7)]
def c7Nested_lineGraphFin : SimpleGraph (Fin 8) :=
  graphOfEdgeList8 c7Nested_lineEdges
def c7Nested_bag : Fin 8 → Finset (Fin 8)
  | 0 => {5, 6, 7}
  | 1 => {2, 5, 7}
  | 2 => {1, 2, 4, 5}
  | 3 => {1, 2, 3, 4}
  | 4 => {0, 1, 2, 3}
  | 5 => {0, 1, 2}
  | 6 => {0, 1}
  | 7 => {1}
theorem c7Nested_edgeCover :
    ∀ ⦃a b : Fin 8⦄, c7Nested_lineGraphFin.Adj a b →
      ∃ w : Fin 8, a ∈ c7Nested_bag w ∧ b ∈ c7Nested_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c7Nested_lineGraphFin, graphOfEdgeList8, graphOfEdgeList8Adj, c7Nested_lineEdges, c7Nested_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c7Nested_preconnected_bag (x : Fin 8) (a b : Nat)
    (ha : a < 8) (hb : b < 8) (hab : a ≤ b)
    (hset : {w : Fin 8 | x ∈ c7Nested_bag w} = certPathGraphInterval 8 a b) :
    (certPathGraph 8).induce {w : Fin 8 | x ∈ c7Nested_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 8 a b ha hb hab

noncomputable def c7Nested_fin_decomp : TreeDecomp c7Nested_lineGraphFin 8 where
  bag := c7Nested_bag
  tree := certPathGraph 8
  isTree := certPathGraph8_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c7Nested_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c7Nested_preconnected_bag 0 4 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 1 2 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 2 1 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 3 3 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 4 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 5 0 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 6 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
    · exact c7Nested_preconnected_bag 7 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c7Nested_bag] <;> decide)
theorem c7Nested_fin_bagSupWidth : bagSupWidth c7Nested_bag ≤ 3 := by native_decide

theorem c7Nested_fin_hasTreeDecomp_3 : HasTreeDecomp c7Nested_lineGraphFin 3 := by
  refine ⟨8, c7Nested_fin_decomp, ?_⟩
  have hw : c7Nested_fin_decomp.width = bagSupWidth c7Nested_bag := by
    dsimp [TreeDecomp.width, c7Nested_fin_decomp, c7Nested_bag, bagSupWidth]
    native_decide
  exact hw ▸ c7Nested_fin_bagSupWidth

/-! ### c8Crossing: tw = 4 -/
def c8Crossing_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 9), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6), (6, 7), (7, 8), (8, 9)]
def c8Crossing_lineGraphFin : SimpleGraph (Fin 10) :=
  graphOfEdgeList10 c8Crossing_lineEdges
def c8Crossing_bag : Fin 10 → Finset (Fin 10)
  | 0 => {6, 7, 8}
  | 1 => {6, 8, 9}
  | 2 => {2, 6, 9}
  | 3 => {0, 1, 2, 6}
  | 4 => {0, 1, 3, 4, 6}
  | 5 => {1, 3, 4, 5, 6}
  | 6 => {3, 4, 5, 6}
  | 7 => {4, 5, 6}
  | 8 => {5, 6}
  | 9 => {6}
theorem c8Crossing_edgeCover :
    ∀ ⦃a b : Fin 10⦄, c8Crossing_lineGraphFin.Adj a b →
      ∃ w : Fin 10, a ∈ c8Crossing_bag w ∧ b ∈ c8Crossing_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c8Crossing_lineGraphFin, graphOfEdgeList10, graphOfEdgeList10Adj, c8Crossing_lineEdges, c8Crossing_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c8Crossing_preconnected_bag (x : Fin 10) (a b : Nat)
    (ha : a < 10) (hb : b < 10) (hab : a ≤ b)
    (hset : {w : Fin 10 | x ∈ c8Crossing_bag w} = certPathGraphInterval 10 a b) :
    (certPathGraph 10).induce {w : Fin 10 | x ∈ c8Crossing_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 10 a b ha hb hab

noncomputable def c8Crossing_fin_decomp : TreeDecomp c8Crossing_lineGraphFin 10 where
  bag := c8Crossing_bag
  tree := certPathGraph 10
  isTree := certPathGraph10_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c8Crossing_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c8Crossing_preconnected_bag 0 3 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 1 3 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 2 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 3 4 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 4 4 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 5 5 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 6 0 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 7 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 8 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
    · exact c8Crossing_preconnected_bag 9 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c8Crossing_bag] <;> decide)
theorem c8Crossing_fin_bagSupWidth : bagSupWidth c8Crossing_bag ≤ 4 := by native_decide

theorem c8Crossing_fin_hasTreeDecomp_4 : HasTreeDecomp c8Crossing_lineGraphFin 4 := by
  refine ⟨10, c8Crossing_fin_decomp, ?_⟩
  have hw : c8Crossing_fin_decomp.width = bagSupWidth c8Crossing_bag := by
    dsimp [TreeDecomp.width, c8Crossing_fin_decomp, c8Crossing_bag, bagSupWidth]
    native_decide
  exact hw ▸ c8Crossing_fin_bagSupWidth

/-! ### c9Crossing: tw = 4 -/
def c9Crossing_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 10), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10)]
def c9Crossing_lineGraphFin : SimpleGraph (Fin 11) :=
  graphOfEdgeList11 c9Crossing_lineEdges
def c9Crossing_bag : Fin 11 → Finset (Fin 11)
  | 0 => {6, 7, 8}
  | 1 => {6, 8, 9}
  | 2 => {6, 9, 10}
  | 3 => {2, 6, 10}
  | 4 => {0, 1, 2, 6}
  | 5 => {0, 1, 3, 4, 6}
  | 6 => {1, 3, 4, 5, 6}
  | 7 => {3, 4, 5, 6}
  | 8 => {4, 5, 6}
  | 9 => {5, 6}
  | 10 => {6}
theorem c9Crossing_edgeCover :
    ∀ ⦃a b : Fin 11⦄, c9Crossing_lineGraphFin.Adj a b →
      ∃ w : Fin 11, a ∈ c9Crossing_bag w ∧ b ∈ c9Crossing_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c9Crossing_lineGraphFin, graphOfEdgeList11, graphOfEdgeList11Adj, c9Crossing_lineEdges, c9Crossing_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c9Crossing_preconnected_bag (x : Fin 11) (a b : Nat)
    (ha : a < 11) (hb : b < 11) (hab : a ≤ b)
    (hset : {w : Fin 11 | x ∈ c9Crossing_bag w} = certPathGraphInterval 11 a b) :
    (certPathGraph 11).induce {w : Fin 11 | x ∈ c9Crossing_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 11 a b ha hb hab

noncomputable def c9Crossing_fin_decomp : TreeDecomp c9Crossing_lineGraphFin 11 where
  bag := c9Crossing_bag
  tree := certPathGraph 11
  isTree := certPathGraph11_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c9Crossing_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c9Crossing_preconnected_bag 0 4 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 1 4 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 2 3 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 3 5 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 4 5 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 5 6 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 6 0 10 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 7 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 8 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 9 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
    · exact c9Crossing_preconnected_bag 10 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Crossing_bag] <;> decide)
theorem c9Crossing_fin_bagSupWidth : bagSupWidth c9Crossing_bag ≤ 4 := by native_decide

theorem c9Crossing_fin_hasTreeDecomp_4 : HasTreeDecomp c9Crossing_lineGraphFin 4 := by
  refine ⟨11, c9Crossing_fin_decomp, ?_⟩
  have hw : c9Crossing_fin_decomp.width = bagSupWidth c9Crossing_bag := by
    dsimp [TreeDecomp.width, c9Crossing_fin_decomp, c9Crossing_bag, bagSupWidth]
    native_decide
  exact hw ▸ c9Crossing_fin_bagSupWidth

/-! ### c9Nested: tw = 3 -/
def c9Nested_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 6), (1, 7), (2, 9), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]
def c9Nested_lineGraphFin : SimpleGraph (Fin 10) :=
  graphOfEdgeList10 c9Nested_lineEdges
def c9Nested_bag : Fin 10 → Finset (Fin 10)
  | 0 => {0, 1, 2, 3}
  | 1 => {1, 2, 3, 4}
  | 2 => {1, 2, 4, 5}
  | 3 => {1, 2, 5, 6}
  | 4 => {1, 2, 6, 9}
  | 5 => {1, 6, 8, 9}
  | 6 => {1, 6, 7, 8}
  | 7 => {1, 6, 7}
  | 8 => {1, 6}
  | 9 => {6}
theorem c9Nested_edgeCover :
    ∀ ⦃a b : Fin 10⦄, c9Nested_lineGraphFin.Adj a b →
      ∃ w : Fin 10, a ∈ c9Nested_bag w ∧ b ∈ c9Nested_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c9Nested_lineGraphFin, graphOfEdgeList10, graphOfEdgeList10Adj, c9Nested_lineEdges, c9Nested_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c9Nested_preconnected_bag (x : Fin 10) (a b : Nat)
    (ha : a < 10) (hb : b < 10) (hab : a ≤ b)
    (hset : {w : Fin 10 | x ∈ c9Nested_bag w} = certPathGraphInterval 10 a b) :
    (certPathGraph 10).induce {w : Fin 10 | x ∈ c9Nested_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 10 a b ha hb hab

noncomputable def c9Nested_fin_decomp : TreeDecomp c9Nested_lineGraphFin 10 where
  bag := c9Nested_bag
  tree := certPathGraph 10
  isTree := certPathGraph10_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c9Nested_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c9Nested_preconnected_bag 0 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 1 0 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 2 0 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 3 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 4 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 5 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 6 3 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 7 6 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 8 5 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
    · exact c9Nested_preconnected_bag 9 4 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c9Nested_bag] <;> decide)
theorem c9Nested_fin_bagSupWidth : bagSupWidth c9Nested_bag ≤ 3 := by native_decide

theorem c9Nested_fin_hasTreeDecomp_3 : HasTreeDecomp c9Nested_lineGraphFin 3 := by
  refine ⟨10, c9Nested_fin_decomp, ?_⟩
  have hw : c9Nested_fin_decomp.width = bagSupWidth c9Nested_bag := by
    dsimp [TreeDecomp.width, c9Nested_fin_decomp, c9Nested_bag, bagSupWidth]
    native_decide
  exact hw ▸ c9Nested_fin_bagSupWidth

/-! ### c10Crossing: tw = 4 -/
def c10Crossing_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (2, 11), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11)]
def c10Crossing_lineGraphFin : SimpleGraph (Fin 12) :=
  graphOfEdgeList12 c10Crossing_lineEdges
def c10Crossing_bag : Fin 12 → Finset (Fin 12)
  | 0 => {6, 7, 8}
  | 1 => {6, 8, 9}
  | 2 => {6, 9, 10}
  | 3 => {6, 10, 11}
  | 4 => {2, 6, 11}
  | 5 => {0, 1, 2, 6}
  | 6 => {0, 1, 3, 4, 6}
  | 7 => {1, 3, 4, 5, 6}
  | 8 => {3, 4, 5, 6}
  | 9 => {4, 5, 6}
  | 10 => {5, 6}
  | 11 => {6}
theorem c10Crossing_edgeCover :
    ∀ ⦃a b : Fin 12⦄, c10Crossing_lineGraphFin.Adj a b →
      ∃ w : Fin 12, a ∈ c10Crossing_bag w ∧ b ∈ c10Crossing_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c10Crossing_lineGraphFin, graphOfEdgeList12, graphOfEdgeList12Adj, c10Crossing_lineEdges, c10Crossing_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c10Crossing_preconnected_bag (x : Fin 12) (a b : Nat)
    (ha : a < 12) (hb : b < 12) (hab : a ≤ b)
    (hset : {w : Fin 12 | x ∈ c10Crossing_bag w} = certPathGraphInterval 12 a b) :
    (certPathGraph 12).induce {w : Fin 12 | x ∈ c10Crossing_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 12 a b ha hb hab

noncomputable def c10Crossing_fin_decomp : TreeDecomp c10Crossing_lineGraphFin 12 where
  bag := c10Crossing_bag
  tree := certPathGraph 12
  isTree := certPathGraph12_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c10Crossing_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c10Crossing_preconnected_bag 0 5 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 1 5 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 2 4 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 3 6 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 4 6 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 5 7 10 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 6 0 11 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 7 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 8 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 9 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 10 2 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
    · exact c10Crossing_preconnected_bag 11 3 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Crossing_bag] <;> decide)
theorem c10Crossing_fin_bagSupWidth : bagSupWidth c10Crossing_bag ≤ 4 := by native_decide

theorem c10Crossing_fin_hasTreeDecomp_4 : HasTreeDecomp c10Crossing_lineGraphFin 4 := by
  refine ⟨12, c10Crossing_fin_decomp, ?_⟩
  have hw : c10Crossing_fin_decomp.width = bagSupWidth c10Crossing_bag := by
    dsimp [TreeDecomp.width, c10Crossing_fin_decomp, c10Crossing_bag, bagSupWidth]
    native_decide
  exact hw ▸ c10Crossing_fin_bagSupWidth

/-! ### c10Nested: tw = 3 -/
def c10Nested_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (1, 5), (2, 10), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10)]
def c10Nested_lineGraphFin : SimpleGraph (Fin 11) :=
  graphOfEdgeList11 c10Nested_lineEdges
def c10Nested_bag : Fin 11 → Finset (Fin 11)
  | 0 => {5, 6, 7}
  | 1 => {1, 4, 5, 7}
  | 2 => {1, 3, 4, 7}
  | 3 => {1, 3, 7, 8}
  | 4 => {0, 1, 3, 8}
  | 5 => {0, 1, 2, 8}
  | 6 => {1, 2, 8, 10}
  | 7 => {1, 8, 9, 10}
  | 8 => {1, 9, 10}
  | 9 => {1, 9}
  | 10 => {9}
theorem c10Nested_edgeCover :
    ∀ ⦃a b : Fin 11⦄, c10Nested_lineGraphFin.Adj a b →
      ∃ w : Fin 11, a ∈ c10Nested_bag w ∧ b ∈ c10Nested_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [c10Nested_lineGraphFin, graphOfEdgeList11, graphOfEdgeList11Adj, c10Nested_lineEdges, c10Nested_bag] at h ⊢ <;>
    first | contradiction | decide

theorem c10Nested_preconnected_bag (x : Fin 11) (a b : Nat)
    (ha : a < 11) (hb : b < 11) (hab : a ≤ b)
    (hset : {w : Fin 11 | x ∈ c10Nested_bag w} = certPathGraphInterval 11 a b) :
    (certPathGraph 11).induce {w : Fin 11 | x ∈ c10Nested_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 11 a b ha hb hab

noncomputable def c10Nested_fin_decomp : TreeDecomp c10Nested_lineGraphFin 11 where
  bag := c10Nested_bag
  tree := certPathGraph 11
  isTree := certPathGraph11_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := c10Nested_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact c10Nested_preconnected_bag 0 4 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 1 1 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 2 5 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 3 2 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 4 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 5 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 6 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 7 0 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 8 3 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 9 7 10 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
    · exact c10Nested_preconnected_bag 10 6 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, c10Nested_bag] <;> decide)
theorem c10Nested_fin_bagSupWidth : bagSupWidth c10Nested_bag ≤ 3 := by native_decide

theorem c10Nested_fin_hasTreeDecomp_3 : HasTreeDecomp c10Nested_lineGraphFin 3 := by
  refine ⟨11, c10Nested_fin_decomp, ?_⟩
  have hw : c10Nested_fin_decomp.width = bagSupWidth c10Nested_bag := by
    dsimp [TreeDecomp.width, c10Nested_fin_decomp, c10Nested_bag, bagSupWidth]
    native_decide
  exact hw ▸ c10Nested_fin_bagSupWidth

def certificatesSmokesDoc : String :=
  "Auto-generated HasTreeDecomp for c6–c10 + c8Crossing smokes."
end SmokeLineGraphCert

end PNPLab.ChordWidth
