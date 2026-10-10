/-
  Auto-generated Fin-indexed tree-decomposition certificates for the cubic
  Hamiltonian asymptotic family D_n (n = 6, 8, 10 Lean-certified; n ≥ 12 JSON-only).

  Regenerate: `PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_asymptotic.py`
-/

import PNPLab.ChordWidth.TreeDecomp.Certificates
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphAsymptotic

set_option maxHeartbeats 1600000

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace AsymptoticLineGraphCert

open SmokeLineGraphCert (bagSupWidth certPathGraph certPathGraphInterval
  certPathGraph_induce_interval_preconnected)

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

def graphOfEdgeList15Adj (edges : List (Nat × Nat)) (i j : Fin 15) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList15Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList15Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList15Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList15Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList15 (edges : List (Nat × Nat)) : SimpleGraph (Fin 15) where
  Adj := graphOfEdgeList15Adj edges
  symm := inferInstance
  loopless := inferInstance
/-! ### D_6: tw(L(G)) = 5, |V(L)| = 9 -/
def cubicHam6_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (1, 7), (2, 6), (2, 8), (3, 4), (3, 5), (3, 6), (4, 7), (4, 8), (5, 6), (5, 7), (6, 8), (7, 8)]
def cubicHam6_lineGraphFin : SimpleGraph (Fin 9) :=
  graphOfEdgeList9 cubicHam6_lineEdges
def cubicHam6_bag : Fin 9 → Finset (Fin 9)
  | 0 => {1, 3, 5, 6, 7}
  | 1 => {0, 1, 3, 4, 6, 7}
  | 2 => {0, 1, 4, 6, 7, 8}
  | 3 => {0, 1, 2, 6, 7, 8}
  | 4 => {0, 2, 6, 7, 8}
  | 5 => {0, 6, 7, 8}
  | 6 => {0, 6, 7}
  | 7 => {6, 7}
  | 8 => {6}
theorem cubicHam6_edgeCover :
    ∀ ⦃a b : Fin 9⦄, cubicHam6_lineGraphFin.Adj a b →
      ∃ w : Fin 9, a ∈ cubicHam6_bag w ∧ b ∈ cubicHam6_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [cubicHam6_lineGraphFin, graphOfEdgeList9, graphOfEdgeList9Adj, cubicHam6_lineEdges, cubicHam6_bag] at h ⊢ <;>
    first | contradiction | decide

theorem cubicHam6_preconnected_bag (x : Fin 9) (a b : Nat)
    (ha : a < 9) (hb : b < 9) (hab : a ≤ b)
    (hset : {w : Fin 9 | x ∈ cubicHam6_bag w} = certPathGraphInterval 9 a b) :
    (certPathGraph 9).induce {w : Fin 9 | x ∈ cubicHam6_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 9 a b ha hb hab

noncomputable def cubicHam6_fin_decomp : TreeDecomp cubicHam6_lineGraphFin 9 where
  bag := cubicHam6_bag
  tree := certPathGraph 9
  isTree := SmokeLineGraphCert.certPathGraph9_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := cubicHam6_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact cubicHam6_preconnected_bag 0 1 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 1 0 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 2 3 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 3 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 4 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 5 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 6 0 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 7 0 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
    · exact cubicHam6_preconnected_bag 8 2 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam6_bag] <;> decide)
theorem cubicHam6_fin_bagSupWidth : bagSupWidth cubicHam6_bag ≤ 5 := by native_decide

theorem cubicHam6_fin_hasTreeDecomp_5 : HasTreeDecomp cubicHam6_lineGraphFin 5 := by
  refine ⟨9, cubicHam6_fin_decomp, ?_⟩
  have hw : cubicHam6_fin_decomp.width = bagSupWidth cubicHam6_bag := by
    dsimp [TreeDecomp.width, cubicHam6_fin_decomp, cubicHam6_bag, bagSupWidth]
    native_decide
  exact hw ▸ cubicHam6_fin_bagSupWidth

/-! ### D_8: tw(L(G)) = 5, |V(L)| = 12 -/
def cubicHam8_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 7), (1, 9), (2, 8), (2, 11), (3, 4), (3, 5), (3, 6), (4, 9), (4, 10), (5, 6), (5, 7), (5, 8), (6, 10), (6, 11), (7, 8), (7, 9), (8, 11), (9, 10), (10, 11)]
def cubicHam8_lineGraphFin : SimpleGraph (Fin 12) :=
  graphOfEdgeList12 cubicHam8_lineEdges
def cubicHam8_bag : Fin 12 → Finset (Fin 12)
  | 0 => {2, 5, 7, 8, 11}
  | 1 => {2, 5, 6, 7, 10, 11}
  | 2 => {2, 3, 5, 6, 7, 10}
  | 3 => {2, 3, 5, 7, 10}
  | 4 => {1, 2, 3, 7, 9, 10}
  | 5 => {1, 2, 3, 4, 9, 10}
  | 6 => {0, 1, 2, 3, 4, 9}
  | 7 => {0, 1, 3, 4, 9}
  | 8 => {1, 3, 4, 9}
  | 9 => {1, 3, 4}
  | 10 => {3, 4}
  | 11 => {3}
theorem cubicHam8_edgeCover :
    ∀ ⦃a b : Fin 12⦄, cubicHam8_lineGraphFin.Adj a b →
      ∃ w : Fin 12, a ∈ cubicHam8_bag w ∧ b ∈ cubicHam8_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [cubicHam8_lineGraphFin, graphOfEdgeList12, graphOfEdgeList12Adj, cubicHam8_lineEdges, cubicHam8_bag] at h ⊢ <;>
    first | contradiction | decide

theorem cubicHam8_preconnected_bag (x : Fin 12) (a b : Nat)
    (ha : a < 12) (hb : b < 12) (hab : a ≤ b)
    (hset : {w : Fin 12 | x ∈ cubicHam8_bag w} = certPathGraphInterval 12 a b) :
    (certPathGraph 12).induce {w : Fin 12 | x ∈ cubicHam8_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 12 a b ha hb hab

noncomputable def cubicHam8_fin_decomp : TreeDecomp cubicHam8_lineGraphFin 12 where
  bag := cubicHam8_bag
  tree := certPathGraph 12
  isTree := SmokeLineGraphCert.certPathGraph12_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := cubicHam8_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact cubicHam8_preconnected_bag 0 6 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 1 4 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 2 0 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 3 2 11 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 4 5 10 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 5 0 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 6 1 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 7 0 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 8 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 9 4 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 10 1 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
    · exact cubicHam8_preconnected_bag 11 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam8_bag] <;> decide)
theorem cubicHam8_fin_bagSupWidth : bagSupWidth cubicHam8_bag ≤ 5 := by native_decide

theorem cubicHam8_fin_hasTreeDecomp_5 : HasTreeDecomp cubicHam8_lineGraphFin 5 := by
  refine ⟨12, cubicHam8_fin_decomp, ?_⟩
  have hw : cubicHam8_fin_decomp.width = bagSupWidth cubicHam8_bag := by
    dsimp [TreeDecomp.width, cubicHam8_fin_decomp, cubicHam8_bag, bagSupWidth]
    native_decide
  exact hw ▸ cubicHam8_fin_bagSupWidth

/-! ### D_10: tw(L(G)) = 5, |V(L)| = 15 -/
def cubicHam10_lineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 9), (1, 11), (2, 10), (2, 14), (3, 4), (3, 5), (3, 6), (4, 11), (4, 12), (5, 6), (5, 7), (5, 8), (6, 12), (6, 13), (7, 8), (7, 9), (7, 10), (8, 13), (8, 14), (9, 10), (9, 11), (10, 14), (11, 12), (12, 13), (13, 14)]
def cubicHam10_lineGraphFin : SimpleGraph (Fin 15) :=
  graphOfEdgeList15 cubicHam10_lineEdges
def cubicHam10_bag : Fin 15 → Finset (Fin 15)
  | 0 => {3, 5, 6, 7, 8}
  | 1 => {3, 6, 7, 8, 12, 13}
  | 2 => {3, 7, 8, 12, 13, 14}
  | 3 => {3, 7, 12, 13, 14}
  | 4 => {3, 7, 9, 10, 12, 14}
  | 5 => {2, 3, 9, 10, 12, 14}
  | 6 => {2, 3, 9, 10, 12}
  | 7 => {1, 2, 3, 9, 11, 12}
  | 8 => {0, 1, 2, 3, 11, 12}
  | 9 => {0, 2, 3, 4, 11, 12}
  | 10 => {0, 2, 3, 4, 12}
  | 11 => {0, 2, 3, 4}
  | 12 => {0, 2, 3}
  | 13 => {0, 2}
  | 14 => {0}
theorem cubicHam10_edgeCover :
    ∀ ⦃a b : Fin 15⦄, cubicHam10_lineGraphFin.Adj a b →
      ∃ w : Fin 15, a ∈ cubicHam10_bag w ∧ b ∈ cubicHam10_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [cubicHam10_lineGraphFin, graphOfEdgeList15, graphOfEdgeList15Adj, cubicHam10_lineEdges, cubicHam10_bag] at h ⊢ <;>
    first | contradiction | decide

theorem cubicHam10_preconnected_bag (x : Fin 15) (a b : Nat)
    (ha : a < 15) (hb : b < 15) (hab : a ≤ b)
    (hset : {w : Fin 15 | x ∈ cubicHam10_bag w} = certPathGraphInterval 15 a b) :
    (certPathGraph 15).induce {w : Fin 15 | x ∈ cubicHam10_bag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected 15 a b ha hb hab

noncomputable def cubicHam10_fin_decomp : TreeDecomp cubicHam10_lineGraphFin 15 where
  bag := cubicHam10_bag
  tree := certPathGraph 15
  isTree := certPathGraph15_isTree
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := cubicHam10_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
    · exact cubicHam10_preconnected_bag 0 8 14 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 1 7 8 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 2 5 13 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 3 0 12 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 4 9 11 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 5 0 0 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 6 0 1 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 7 0 4 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 8 0 2 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 9 4 7 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 10 4 6 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 11 7 9 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 12 1 10 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 13 1 3 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
    · exact cubicHam10_preconnected_bag 14 2 5 (by decide) (by decide) (by decide)
        (by ext w; fin_cases w <;> simp [certPathGraphInterval, cubicHam10_bag] <;> decide)
theorem cubicHam10_fin_bagSupWidth : bagSupWidth cubicHam10_bag ≤ 5 := by native_decide

theorem cubicHam10_fin_hasTreeDecomp_5 : HasTreeDecomp cubicHam10_lineGraphFin 5 := by
  refine ⟨15, cubicHam10_fin_decomp, ?_⟩
  have hw : cubicHam10_fin_decomp.width = bagSupWidth cubicHam10_bag := by
    dsimp [TreeDecomp.width, cubicHam10_fin_decomp, cubicHam10_bag, bagSupWidth]
    native_decide
  exact hw ▸ cubicHam10_fin_bagSupWidth

def certificatesAsymptoticDoc : String :=
  "HasTreeDecomp Lean-certified for cubic Hamiltonian D_n (n=6,8,10); n=12,14 JSON verified in reports/tree_decomp_certificates/asymptotic/."
end AsymptoticLineGraphCert

end PNPLab.ChordWidth
