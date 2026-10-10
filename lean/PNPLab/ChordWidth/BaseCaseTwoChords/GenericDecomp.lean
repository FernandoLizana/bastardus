/-
  Route F+A generic decomposition tree: node-kind sum type + pairing/gap-dependent adjacency.

  Replaces fixed `Fin (longArcLen + 5)` scaffold with parametric `GenericDecompNode g`.
  Bag families wired from `NoncrossingPathDecompAssumptions` (long/short arc + enriched junction).
  Hub nodes reserved (empty kind for nested/disjoint pilot); unconditional `IsTree` from
  `GenericDecompTreeShape` + combinatorial card; Fin transport toward `HasTreeDecomp`.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import PNPLab.ChordWidth.BaseCaseTwoChords.NoncrossingPathDecomp
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.Basic

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp
open SmokeLineGraphCert

/-!
  ## Node kinds (design: CHORDWIDTH_GENERIC_DECOMP_DESIGN.md)
-/

/-- Hub relay kinds (empty for nested/disjoint pilot; crossing may add constructors later). -/
inductive GenericHubKind (_g : CycleTwoChordGraph) where
  deriving DecidableEq

/-- Parametric decomposition tree vertex (disjoint union of arc segments + junctions + hubs). -/
inductive GenericDecompNode (g : CycleTwoChordGraph) (arcIdx : Fin 4) : Type where
  | longSeg (j : Fin (g.cyclicGap arcIdx))
  | shortSeg (a : Fin 4) (hne : a ≠  arcIdx) (j : Fin (g.cyclicGap a))
  | junction (e : Fin 4)
  | hub (kind : GenericHubKind g)
  deriving DecidableEq

namespace GenericDecompNode

variable {g : CycleTwoChordGraph} {arcIdx : Fin 4}

theorem shortSeg_eq_of_arcIdxVal {a a' : Fin 4} {hne : a ≠ arcIdx} {hne' : a' ≠ arcIdx}
    {j : Fin (g.cyclicGap a)} {j' : Fin (g.cyclicGap a')} (ha : a' = a) (hj : j'.val = j.val) :
    GenericDecompNode.shortSeg a' hne' j' = GenericDecompNode.shortSeg a hne j := by
  subst ha
  rw [Fin.ext hj]

def longArcIdx (node : GenericDecompNode g arcIdx) : Option (Fin 4) :=
  match node with
  | .longSeg _ => some arcIdx
  | .shortSeg a _ _ => some a
  | .junction _ | .hub _ => none

end GenericDecompNode

namespace GenericDecomp

/-!
  ## Pairing/gap-dependent adjacency (combinatorial, not fixed Fin length)
-/

def longArcStartJunctions : Fin 4 → Prop
  | 0 => True
  | 1 => False
  | 2 => True
  | 3 => False

def longArcEndJunctions : Fin 4 → Prop
  | 0 => False
  | 1 => True
  | 2 => False
  | 3 => True

def shortArcZeroJunction (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (shortArc endpoint : Fin 4) : Prop :=
  g.junctionShortArcAt hyp.arcIdx endpoint = some shortArc

def genericDecompAdj (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (u v : GenericDecompNode g hyp.arcIdx) : Prop :=
  match u, v with
  | .longSeg j, .longSeg j' =>
    (j.val + 1 = j'.val ∧ j.val + 1 < hyp.longArcLen) ∨
      (j'.val + 1 = j.val ∧ j'.val + 1 < hyp.longArcLen)
  | .longSeg j, .junction e =>
    (j.val = 0 ∧ longArcStartJunctions e) ∨
      (j.val + 1 = hyp.longArcLen ∧ longArcEndJunctions e)
  | .junction e, .longSeg j =>
    (j.val = 0 ∧ longArcStartJunctions e) ∨
      (j.val + 1 = hyp.longArcLen ∧ longArcEndJunctions e)
  | .shortSeg a _ j, .junction e =>
    j.val = 0 ∧ shortArcZeroJunction g hyp a e
  | .junction e, .shortSeg a _ j =>
    j.val = 0 ∧ shortArcZeroJunction g hyp a e
  | .shortSeg a _ j, .shortSeg a' _ j' =>
    a = a' ∧
      ((j.val + 1 = j'.val ∧ j.val + 1 < g.cyclicGap a) ∨
        (j'.val + 1 = j.val ∧ j'.val + 1 < g.cyclicGap a))
  | .junction _, .junction _ => False
  | _, _ => False

theorem genericDecompAdj_symm (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    {u v : GenericDecompNode g hyp.arcIdx} (h : genericDecompAdj g hyp u v) :
    genericDecompAdj g hyp v u := by
  rcases u with _ | ⟨a, _, j⟩ | e | _ <;> rcases v with _ | ⟨a', _, j'⟩ | e' | _ <;>
    simp [genericDecompAdj] at h ⊢ <;>
    first
    | tauto
    | (rcases h with ⟨h1, h2⟩; exact ⟨h1, h2⟩)
    | (rcases h with h | h; exact Or.inr h <|> exact Or.inl h)
    | (rcases h with ⟨ha, hstep | hstep⟩
       · subst ha; exact ⟨rfl, Or.inr hstep⟩
       · subst ha; exact ⟨rfl, Or.inl hstep⟩)

theorem genericDecompAdj_irrefl (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (u : GenericDecompNode g hyp.arcIdx) (h : genericDecompAdj g hyp u u) : False := by
  cases u <;> simp [genericDecompAdj] at h <;>
    first | omega | tauto | (fin_cases h) | (cases h)

instance genericDecompAdj_symmInst (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Std.Symm (genericDecompAdj g hyp) where
  symm a b h := genericDecompAdj_symm g hyp h

instance genericDecompAdj_irreflInst (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Std.Irrefl (genericDecompAdj g hyp) where
  irrefl := genericDecompAdj_irrefl g hyp

def genericDecompGraph (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    SimpleGraph (GenericDecompNode g hyp.arcIdx) where
  Adj := genericDecompAdj g hyp
  symm := inferInstance
  loopless := inferInstance

/-!
  ## Segment chains ↔ `certPathGraph` (reuse path `IsTree` on arc segments)
-/

def genericShortArcGapSum (g : CycleTwoChordGraph) (longIdx : Fin 4) : Nat :=
  (Finset.univ : Finset (Fin 4)).filter (fun a => a ≠  longIdx) |>.sum (fun a => g.cyclicGap a)

def shortArcEndpointCount (g : CycleTwoChordGraph) (longIdx : Fin 4) : Nat :=
  (Finset.univ : Finset (Fin 4)).filter (fun e => (g.junctionShortArcAt longIdx e).isSome) |>.card

def genericDecompNodeCount (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen + 4 + genericShortArcGapSum g hyp.arcIdx

def genericDecompEdgeCount (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  (hyp.longArcLen - 1) + 4 + genericShortArcGapSum g hyp.arcIdx

theorem genericDecomp_card_balance (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    genericDecompEdgeCount g hyp + 1 = genericDecompNodeCount g hyp := by
  dsimp [genericDecompEdgeCount, genericDecompNodeCount, NoncrossingPathDecompAssumptions.longArcLen]
  have h1 : g.cyclicGap hyp.arcIdx - 1 + 1 = g.cyclicGap hyp.arcIdx :=
    Nat.sub_add_cancel (Nat.one_le_of_lt hyp.hlen)
  omega

theorem longSeg_adj_iff (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j j' : Fin hyp.longArcLen) :
    (genericDecompGraph g hyp).Adj (.longSeg j) (.longSeg j') ↔
      certPathGraphAdj hyp.longArcLen j j' := by
  simp only [genericDecompGraph, genericDecompAdj, certPathGraphAdj, NoncrossingPathDecompAssumptions.longArcLen]
  constructor
  · intro h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr ⟨h, by omega⟩

theorem shortSeg_adj_iff (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (_hne : a ≠  hyp.arcIdx) (j j' : Fin (g.cyclicGap a)) :
    (genericDecompGraph g hyp).Adj (.shortSeg a _hne j) (.shortSeg a _hne j') ↔
      certPathGraphAdj (g.cyclicGap a) j j' := by
  simp only [genericDecompGraph, genericDecompAdj, certPathGraphAdj]
  constructor
  · intro h
    rcases h with ⟨_, hstep⟩
    rcases hstep with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro h
    rcases h with h | h
    · simp only [eq_self_iff_true, true_and]
      exact Or.inl ⟨h, by omega⟩
    · simp only [eq_self_iff_true, true_and]
      exact Or.inr ⟨h, by omega⟩

/-- Combinatorial shape for nested/disjoint pilot trees (three endpoints on short arcs). -/
structure GenericDecompTreeShape (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  shortArc_attached :
    ∀ (a : Fin 4) (hne : a ≠  hyp.arcIdx),
      ∃ e : Fin 4, g.junctionShortArcAt hyp.arcIdx e = some a
  shortArc_junction_unique :
    ∀ (a : Fin 4) (hne : a ≠ hyp.arcIdx) (e e' : Fin 4),
      shortArcZeroJunction g hyp a e → shortArcZeroJunction g hyp a e' → e = e'
  shortArc_gap_pos :
    ∀ (a : Fin 4) (hne : a ≠ hyp.arcIdx), 0 < g.cyclicGap a
  three_short_arc_endpoints : shortArcEndpointCount g hyp.arcIdx = 3
  longArc_isTree : hyp.longArcCertPathGraph.IsTree

theorem longSeg_adj_succ (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) (h : j.val + 1 < hyp.longArcLen) :
    (genericDecompGraph g hyp).Adj (.longSeg j) (.longSeg ⟨j.val + 1, h⟩) := by
  rw [longSeg_adj_iff]
  exact certPathGraph_adj_succ j h

theorem shortSeg_adj_succ (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠  hyp.arcIdx) (j : Fin (g.cyclicGap a)) (h : j.val + 1 < g.cyclicGap a) :
    (genericDecompGraph g hyp).Adj (.shortSeg a hne j) (.shortSeg a hne ⟨j.val + 1, h⟩) := by
  rw [shortSeg_adj_iff]
  exact certPathGraph_adj_succ j h

theorem longSeg_zero_adj_junction_start (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : Fin 4) (he : longArcStartJunctions e) :
    (genericDecompGraph g hyp).Adj (.longSeg ⟨0, hyp.hlen⟩) (.junction e) := by
  simp [genericDecompGraph, genericDecompAdj, he]

theorem shortSeg_zero_adj_junction (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠  hyp.arcIdx) (e : Fin 4) (hgap : 0 < g.cyclicGap a)
    (hown : shortArcZeroJunction g hyp a e) :
    (genericDecompGraph g hyp).Adj (.shortSeg a hne ⟨0, hgap⟩) (.junction e) := by
  simp [genericDecompGraph, genericDecompAdj, hown]

theorem longSeg_last_adj_junction_end (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : Fin 4) (he : longArcEndJunctions e) :
    (genericDecompGraph g hyp).Adj (.longSeg ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen Nat.one_pos⟩)
      (.junction e) := by
  dsimp [genericDecompGraph, genericDecompAdj, longArcEndJunctions, NoncrossingPathDecompAssumptions.longArcLen]
  refine Or.inr ⟨?_, he⟩
  exact Nat.sub_add_cancel (Nat.one_le_of_lt hyp.hlen)

/-!
  ## Reachability + `Connected` from pairing/gap shape (junction glue)
-/

section Reachability

variable {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}

def longSegRoot : GenericDecompNode g hyp.arcIdx :=
  .longSeg ⟨0, hyp.hlen⟩

theorem longArcStartJunctions_or_end (e : Fin 4) :
    longArcStartJunctions e ∨ longArcEndJunctions e := by
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions]

theorem longArcEndJunctions_of_not_start (e : Fin 4) (h : ¬ longArcStartJunctions e) :
    longArcEndJunctions e := by
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at h ⊢ <;> tauto

theorem longSeg_reachable_from_root (j : Fin hyp.longArcLen) :
    (genericDecompGraph g hyp).Reachable longSegRoot (.longSeg j) := by
  suffices h : ∀ k (hk : k < hyp.longArcLen),
      (genericDecompGraph g hyp).Reachable longSegRoot (.longSeg ⟨k, hk⟩) by
    exact h j.val j.isLt
  intro k hk
  revert hk
  induction k with
  | zero =>
    intro hk
    dsimp only [longSegRoot]
    have hvert : (⟨0, hyp.hlen⟩ : Fin hyp.longArcLen) = ⟨0, hk⟩ := Fin.ext rfl
    exact hvert ▸ Reachable.rfl
  | succ k ih =>
    intro hk
    have hk' : k < hyp.longArcLen := by omega
    exact (ih hk').trans (longSeg_adj_succ g hyp ⟨k, hk'⟩ (by omega)).reachable

theorem junction_reachable_from_root (e : Fin 4) :
    (genericDecompGraph g hyp).Reachable longSegRoot (.junction e) := by
  fin_cases e
  · exact (longSeg_zero_adj_junction_start g hyp 0 (by simp [longArcStartJunctions])).reachable
  · have hlen' : hyp.longArcLen - 1 < hyp.longArcLen := Nat.sub_lt hyp.hlen Nat.one_pos
    have hto_last := longSeg_reachable_from_root ⟨hyp.longArcLen - 1, hlen'⟩
    exact hto_last.trans
      ((longSeg_last_adj_junction_end g hyp 1 (by simp [longArcEndJunctions])).reachable)
  · exact (longSeg_zero_adj_junction_start g hyp 2 (by simp [longArcStartJunctions])).reachable
  · have hlast := (longSeg_last_adj_junction_end g hyp 3 (by simp [longArcEndJunctions])).reachable
    have hlen' : hyp.longArcLen - 1 < hyp.longArcLen := Nat.sub_lt hyp.hlen Nat.one_pos
    have hto_last := longSeg_reachable_from_root ⟨hyp.longArcLen - 1, hlen'⟩
    exact hto_last.trans hlast

theorem shortSeg_reachable_from_zero (a : Fin 4) (hne : a ≠  hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    (genericDecompGraph g hyp).Reachable (.shortSeg a hne ⟨0, Nat.zero_lt_of_lt j.isLt⟩) (.shortSeg a hne j) := by
  suffices h : ∀ k (hk : k < g.cyclicGap a),
      (genericDecompGraph g hyp).Reachable (.shortSeg a hne ⟨0, Nat.zero_lt_of_lt j.isLt⟩)
        (.shortSeg a hne ⟨k, hk⟩) by
    exact h j.val j.isLt
  intro k hk
  revert hk
  induction k with
  | zero => intro _; exact Reachable.rfl
  | succ k ih =>
    intro hk
    have hk' : k < g.cyclicGap a := by omega
    exact (ih hk').trans (shortSeg_adj_succ g hyp a hne ⟨k, hk'⟩ (by omega)).reachable

theorem shortSeg_reachable_from_root (shape : GenericDecompTreeShape g hyp)
    (a : Fin 4) (hne : a ≠  hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    (genericDecompGraph g hyp).Reachable longSegRoot (.shortSeg a hne j) := by
  obtain ⟨e, he⟩ := shape.shortArc_attached a hne
  have hgap : 0 < g.cyclicGap a := shape.shortArc_gap_pos a hne
  have hown : shortArcZeroJunction g hyp a e := by simp [shortArcZeroJunction, he]
  have hjunc := junction_reachable_from_root (g := g) (hyp := hyp) e
  have hzero := (shortSeg_zero_adj_junction g hyp a hne e hgap hown).reachable
  have hchain := shortSeg_reachable_from_zero a hne j
  exact hjunc.trans (hzero.symm.trans hchain)

theorem genericDecompGraph_connected_of_shape (shape : GenericDecompTreeShape g hyp) :
    (genericDecompGraph g hyp).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨longSegRoot, ?_⟩
  intro v
  cases v with
  | longSeg j => exact longSeg_reachable_from_root j
  | shortSeg a hne j => exact shortSeg_reachable_from_root shape a hne j
  | junction e => exact junction_reachable_from_root e
  | hub kind => cases kind

theorem genericDecompGraph_isTree_of_shape_and_card [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp)
    (hcard : Nat.card (genericDecompGraph g hyp).edgeSet + 1 =
      Nat.card (GenericDecompNode g hyp.arcIdx)) :
    (genericDecompGraph g hyp).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  exact ⟨genericDecompGraph_connected_of_shape shape, hcard⟩

theorem genericDecompGraph_isTree_of_shape (shape : GenericDecompTreeShape g hyp)
    (hacyc : (genericDecompGraph g hyp).IsAcyclic) :
    (genericDecompGraph g hyp).IsTree :=
  ⟨genericDecompGraph_connected_of_shape shape, hacyc⟩

theorem genericDecompGraph_isTree_of_shape_and_combinatorial_card
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp)
    (hedges : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp)
    (hnodes : Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp) :
    (genericDecompGraph g hyp).IsTree := by
  refine genericDecompGraph_isTree_of_shape_and_card shape ?_
  rw [hedges, hnodes, genericDecomp_card_balance]

/-! ### ALT route scaffolding (acyclic / edge-upper-bound); discharge theorems below `nodeCard`. -/

end Reachability

/-!
  ## Fin encoding + combinatorial card (toward `HasTreeDecomp` transport)
-/

def shortArcBlockOffset (g : CycleTwoChordGraph) (longIdx : Fin 4) (a : Fin 4) (_hne : a ≠  longIdx) :
    Nat :=
  ((Finset.univ : Finset (Fin 4)).filter (fun b => b ≠  longIdx ∧ b.val < a.val)).sum (fun b => g.cyclicGap b)

noncomputable def genericDecompNodeEncode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (node : GenericDecompNode g hyp.arcIdx) : Nat :=
  match node with
  | .longSeg j => j.val
  | .shortSeg a hne j =>
    hyp.longArcLen + shortArcBlockOffset g hyp.arcIdx a hne + j.val
  | .junction e => hyp.longArcLen + genericShortArcGapSum g hyp.arcIdx + e.val
  | .hub kind => nomatch kind

def genericDecompJunctionBase (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen + genericShortArcGapSum g hyp.arcIdx

theorem longArcLen_eq (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    hyp.longArcLen = g.cyclicGap hyp.arcIdx :=
  rfl

structure ShortArcGapDecode (g : CycleTwoChordGraph) (longIdx : Fin 4) where
  a : Fin 4
  hne : a ≠ longIdx
  j : Fin (g.cyclicGap a)

theorem genericShortArcGapSum_zero (g : CycleTwoChordGraph) :
    genericShortArcGapSum g 0 = g.cyclicGap 1 + g.cyclicGap 2 + g.cyclicGap 3 := by
  simp [genericShortArcGapSum]
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun a => a ≠ (0 : Fin 4)) = ({1, 2, 3} : Finset (Fin 4)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    fin_cases a <;> simp
  rw [hset]
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp [Finset.sum_insert, Finset.sum_singleton, h12, h13, h23]
  ac_rfl

theorem genericShortArcGapSum_one (g : CycleTwoChordGraph) :
    genericShortArcGapSum g 1 = g.cyclicGap 0 + g.cyclicGap 2 + g.cyclicGap 3 := by
  simp [genericShortArcGapSum]
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun a => a ≠ (1 : Fin 4)) = ({0, 2, 3} : Finset (Fin 4)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    fin_cases a <;> simp
  rw [hset]
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp [Finset.sum_insert, Finset.sum_singleton, h02, h03, h23]
  ac_rfl

theorem genericShortArcGapSum_two (g : CycleTwoChordGraph) :
    genericShortArcGapSum g 2 = g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 3 := by
  simp [genericShortArcGapSum]
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun a => a ≠ (2 : Fin 4)) = ({0, 1, 3} : Finset (Fin 4)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    fin_cases a <;> simp
  rw [hset]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  simp [Finset.sum_insert, Finset.sum_singleton, h01, h03, h13]
  ac_rfl

theorem genericShortArcGapSum_three (g : CycleTwoChordGraph) :
    genericShortArcGapSum g 3 = g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 2 := by
  simp [genericShortArcGapSum]
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun a => a ≠ (3 : Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    fin_cases a <;> simp
  rw [hset]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  simp [Finset.sum_insert, Finset.sum_singleton, h01, h02, h12]
  ac_rfl

theorem genericShortArcGapSum_fin (g : CycleTwoChordGraph) (longIdx : Fin 4) :
    genericShortArcGapSum g longIdx =
      match longIdx with
      | 0 => g.cyclicGap 1 + g.cyclicGap 2 + g.cyclicGap 3
      | 1 => g.cyclicGap 0 + g.cyclicGap 2 + g.cyclicGap 3
      | 2 => g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 3
      | 3 => g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 2 := by
  fin_cases longIdx <;>
    first
    | exact genericShortArcGapSum_zero g
    | exact genericShortArcGapSum_one g
    | exact genericShortArcGapSum_two g
    | exact genericShortArcGapSum_three g

theorem shortArcBlockOffset_zero_one (g : CycleTwoChordGraph) (h : (1 : Fin 4) ≠ 0) :
    shortArcBlockOffset g 0 1 h = 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (0 : Fin 4) ∧ b.val < 1) = (∅ : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_empty]

theorem shortArcBlockOffset_zero_two (g : CycleTwoChordGraph) (h : (2 : Fin 4) ≠ 0) :
    shortArcBlockOffset g 0 2 h = g.cyclicGap 1 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (0 : Fin 4) ∧ b.val < 2) = ({1} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_singleton]
  rfl

theorem shortArcBlockOffset_zero_three (g : CycleTwoChordGraph) (h : (3 : Fin 4) ≠ 0) :
    shortArcBlockOffset g 0 3 h = g.cyclicGap 1 + g.cyclicGap 2 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (0 : Fin 4) ∧ b.val < 3) = ({1, 2} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  simp [shortArcBlockOffset, hset, Finset.sum_insert, Finset.sum_singleton, h12]

theorem shortArcBlockOffset_one_zero (g : CycleTwoChordGraph) (h : (0 : Fin 4) ≠ 1) :
    shortArcBlockOffset g 1 0 h = 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (1 : Fin 4) ∧ b.val < 0) = (∅ : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_empty]

theorem shortArcBlockOffset_one_two (g : CycleTwoChordGraph) (h : (2 : Fin 4) ≠ 1) :
    shortArcBlockOffset g 1 2 h = g.cyclicGap 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (1 : Fin 4) ∧ b.val < 2) = ({0} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_singleton]
  rfl

theorem shortArcBlockOffset_one_three (g : CycleTwoChordGraph) (h : (3 : Fin 4) ≠ 1) :
    shortArcBlockOffset g 1 3 h = g.cyclicGap 0 + g.cyclicGap 2 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (1 : Fin 4) ∧ b.val < 3) = ({0, 2} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  simp [shortArcBlockOffset, hset, Finset.sum_insert, Finset.sum_singleton, h02]

theorem shortArcBlockOffset_two_zero (g : CycleTwoChordGraph) (h : (0 : Fin 4) ≠ 2) :
    shortArcBlockOffset g 2 0 h = 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (2 : Fin 4) ∧ b.val < 0) = (∅ : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_empty]

theorem shortArcBlockOffset_two_one (g : CycleTwoChordGraph) (h : (1 : Fin 4) ≠ 2) :
    shortArcBlockOffset g 2 1 h = g.cyclicGap 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (2 : Fin 4) ∧ b.val < 1) = ({0} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_singleton]
  rfl

theorem shortArcBlockOffset_two_three (g : CycleTwoChordGraph) (h : (3 : Fin 4) ≠ 2) :
    shortArcBlockOffset g 2 3 h = g.cyclicGap 0 + g.cyclicGap 1 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (2 : Fin 4) ∧ b.val < 3) = ({0, 1} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  simp [shortArcBlockOffset, hset, Finset.sum_insert, Finset.sum_singleton, h01]

theorem shortArcBlockOffset_three_zero (g : CycleTwoChordGraph) (h : (0 : Fin 4) ≠ 3) :
    shortArcBlockOffset g 3 0 h = 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (3 : Fin 4) ∧ b.val < 0) = (∅ : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_empty]

theorem shortArcBlockOffset_three_one (g : CycleTwoChordGraph) (h : (1 : Fin 4) ≠ 3) :
    shortArcBlockOffset g 3 1 h = g.cyclicGap 0 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (3 : Fin 4) ∧ b.val < 1) = ({0} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  simp [shortArcBlockOffset, hset, Finset.sum_singleton]
  rfl

theorem shortArcBlockOffset_three_two (g : CycleTwoChordGraph) (h : (2 : Fin 4) ≠ 3) :
    shortArcBlockOffset g 3 2 h = g.cyclicGap 0 + g.cyclicGap 1 := by
  have hset : (Finset.univ : Finset (Fin 4)).filter (fun b => b ≠ (3 : Fin 4) ∧ b.val < 2) = ({0, 1} : Finset (Fin 4)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, Finset.mem_insert, Finset.mem_singleton]
    fin_cases b <;> simp
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  simp [shortArcBlockOffset, hset, Finset.sum_insert, Finset.sum_singleton, h01]
  ac_rfl

theorem shortArcBlockOffset_fin (g : CycleTwoChordGraph) (longIdx a : Fin 4) (hne : a ≠ longIdx) :
    shortArcBlockOffset g longIdx a hne =
      match longIdx, a with
      | 0, 1 => 0
      | 0, 2 => g.cyclicGap 1
      | 0, 3 => g.cyclicGap 1 + g.cyclicGap 2
      | 1, 0 => 0
      | 1, 2 => g.cyclicGap 0
      | 1, 3 => g.cyclicGap 0 + g.cyclicGap 2
      | 2, 0 => 0
      | 2, 1 => g.cyclicGap 0
      | 2, 3 => g.cyclicGap 0 + g.cyclicGap 1
      | 3, 0 => 0
      | 3, 1 => g.cyclicGap 0
      | 3, 2 => g.cyclicGap 0 + g.cyclicGap 1
      | _, _ => 0 := by
  fin_cases longIdx <;> fin_cases a <;>
    first
    | exact absurd rfl hne
    | rfl
    | exact shortArcBlockOffset_zero_one g (by decide)
    | exact shortArcBlockOffset_zero_two g (by decide)
    | exact shortArcBlockOffset_zero_three g (by decide)
    | exact shortArcBlockOffset_one_zero g (by decide)
    | exact shortArcBlockOffset_one_two g (by decide)
    | exact shortArcBlockOffset_one_three g (by decide)
    | exact shortArcBlockOffset_two_zero g (by decide)
    | exact shortArcBlockOffset_two_one g (by decide)
    | exact shortArcBlockOffset_two_three g (by decide)
    | exact shortArcBlockOffset_three_zero g (by decide)
    | exact shortArcBlockOffset_three_one g (by decide)
    | exact shortArcBlockOffset_three_two g (by decide)

theorem shortArcBlockOffset_add_gap_le_sum (g : CycleTwoChordGraph) (longIdx : Fin 4) (a : Fin 4)
    (hne : a ≠ longIdx) :
    shortArcBlockOffset g longIdx a hne + g.cyclicGap a ≤ genericShortArcGapSum g longIdx := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rw [shortArcBlockOffset_fin, genericShortArcGapSum_fin]
  fin_cases longIdx <;> fin_cases a <;>
    first
    | exact absurd rfl hne
    | simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n]; first | done | omega

theorem genericDecompNodeEncode_lt (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (node : GenericDecompNode g hyp.arcIdx) :
    genericDecompNodeEncode g hyp node < genericDecompNodeCount g hyp := by
  cases node with
  | longSeg j =>
    have hj := j.isLt
    dsimp [genericDecompNodeEncode, genericDecompNodeCount, NoncrossingPathDecompAssumptions.longArcLen]
    omega
  | shortSeg a hne j =>
    dsimp [genericDecompNodeEncode, genericDecompNodeCount]
    have hoff := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
    have hj : j.val + 1 ≤ g.cyclicGap a := Nat.succ_le_of_lt j.isLt
    omega
  | junction e =>
    dsimp [genericDecompNodeEncode, genericDecompNodeCount, genericDecompJunctionBase]
    have he := e.isLt
    omega
  | hub kind => nomatch kind

/-- Fin transport toward HasTreeDecomp. -/
structure GenericDecompFinTransport (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  finEquiv : GenericDecompNode g hyp.arcIdx ≃ Fin (genericDecompNodeCount g hyp)

theorem shortArcGapOffsetDecode_exists (g : CycleTwoChordGraph) (longIdx : Fin 4) (k : Nat)
    (hk : k < genericShortArcGapSum g longIdx) :
    ∃ p : ShortArcGapDecode g longIdx,
      shortArcBlockOffset g longIdx p.a p.hne + p.j.val = k := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rw [genericShortArcGapSum_fin] at hk
  fin_cases longIdx
  · simp only [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
    by_cases hk1 : k < g.cyclicGap 1
    · exact ⟨⟨1, by decide, ⟨k, hk1⟩⟩, by
        simpa [shortArcBlockOffset_zero_one g (by decide), Nat.zero_add]⟩
    · by_cases hk2 : k < g.cyclicGap 1 + g.cyclicGap 2
      · exact ⟨⟨2, by decide, ⟨k - g.cyclicGap 1, by omega⟩⟩, by
          simpa [shortArcBlockOffset_zero_two g (by decide)] using
            Nat.add_sub_cancel' (le_of_not_gt hk1)⟩
      · have hj : k - g.cyclicGap 1 - g.cyclicGap 2 < g.cyclicGap 3 := by
          simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
          omega
        exact ⟨⟨3, by decide, ⟨k - g.cyclicGap 1 - g.cyclicGap 2, hj⟩⟩, by
          simp only [shortArcBlockOffset_zero_three g (by decide)]
          calc (g.cyclicGap 1 + g.cyclicGap 2) + (k - g.cyclicGap 1 - g.cyclicGap 2)
            _ = (g.cyclicGap 1 + g.cyclicGap 2) + (k - (g.cyclicGap 1 + g.cyclicGap 2)) := by omega
            _ = k := Nat.add_sub_cancel' (le_of_not_gt hk2)⟩
  · simp only [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
    by_cases hk0 : k < g.cyclicGap 0
    · exact ⟨⟨0, by decide, ⟨k, hk0⟩⟩, by
        simpa [shortArcBlockOffset_one_zero g (by decide), Nat.zero_add]⟩
    · by_cases hk2 : k < g.cyclicGap 0 + g.cyclicGap 2
      · exact ⟨⟨2, by decide, ⟨k - g.cyclicGap 0, by omega⟩⟩, by
          simpa [shortArcBlockOffset_one_two g (by decide)] using
            Nat.add_sub_cancel' (le_of_not_gt hk0)⟩
      · have hj : k - g.cyclicGap 0 - g.cyclicGap 2 < g.cyclicGap 3 := by
          simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
          omega
        exact ⟨⟨3, by decide, ⟨k - g.cyclicGap 0 - g.cyclicGap 2, hj⟩⟩, by
          simp only [shortArcBlockOffset_one_three g (by decide)]
          calc (g.cyclicGap 0 + g.cyclicGap 2) + (k - g.cyclicGap 0 - g.cyclicGap 2)
            _ = (g.cyclicGap 0 + g.cyclicGap 2) + (k - (g.cyclicGap 0 + g.cyclicGap 2)) := by omega
            _ = k := Nat.add_sub_cancel' (le_of_not_gt hk2)⟩
  · simp only [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
    by_cases hk0 : k < g.cyclicGap 0
    · exact ⟨⟨0, by decide, ⟨k, hk0⟩⟩, by
        simpa [shortArcBlockOffset_two_zero g (by decide), Nat.zero_add]⟩
    · by_cases hk1 : k < g.cyclicGap 0 + g.cyclicGap 1
      · exact ⟨⟨1, by decide, ⟨k - g.cyclicGap 0, by omega⟩⟩, by
          simpa [shortArcBlockOffset_two_one g (by decide)] using
            Nat.add_sub_cancel' (le_of_not_gt hk0)⟩
      · have hj : k - g.cyclicGap 0 - g.cyclicGap 1 < g.cyclicGap 3 := by
          simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
          omega
        exact ⟨⟨3, by decide, ⟨k - g.cyclicGap 0 - g.cyclicGap 1, hj⟩⟩, by
          simp only [shortArcBlockOffset_two_three g (by decide)]
          calc (g.cyclicGap 0 + g.cyclicGap 1) + (k - g.cyclicGap 0 - g.cyclicGap 1)
            _ = (g.cyclicGap 0 + g.cyclicGap 1) + (k - (g.cyclicGap 0 + g.cyclicGap 1)) := by omega
            _ = k := Nat.add_sub_cancel' (le_of_not_gt hk1)⟩
  · simp only [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
    by_cases hk0 : k < g.cyclicGap 0
    · exact ⟨⟨0, by decide, ⟨k, hk0⟩⟩, by
        simpa [shortArcBlockOffset_three_zero g (by decide), Nat.zero_add]⟩
    · by_cases hk1 : k < g.cyclicGap 0 + g.cyclicGap 1
      · exact ⟨⟨1, by decide, ⟨k - g.cyclicGap 0, by omega⟩⟩, by
          simpa [shortArcBlockOffset_three_one g (by decide)] using
            Nat.add_sub_cancel' (le_of_not_gt hk0)⟩
      · have hj : k - g.cyclicGap 0 - g.cyclicGap 1 < g.cyclicGap 2 := by
          simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hk ⊢
          omega
        exact ⟨⟨2, by decide, ⟨k - g.cyclicGap 0 - g.cyclicGap 1, hj⟩⟩, by
          simp only [shortArcBlockOffset_three_two g (by decide)]
          calc (g.cyclicGap 0 + g.cyclicGap 1) + (k - g.cyclicGap 0 - g.cyclicGap 1)
            _ = (g.cyclicGap 0 + g.cyclicGap 1) + (k - (g.cyclicGap 0 + g.cyclicGap 1)) := by omega
            _ = k := Nat.add_sub_cancel' (le_of_not_gt hk1)⟩

noncomputable def shortArcGapOffsetDecode (g : CycleTwoChordGraph) (longIdx : Fin 4) (k : Nat)
    (hk : k < genericShortArcGapSum g longIdx) : ShortArcGapDecode g longIdx :=
  (shortArcGapOffsetDecode_exists g longIdx k hk).choose

theorem shortArcGapOffsetDecode_spec (g : CycleTwoChordGraph) (longIdx : Fin 4) (k : Nat)
    (hk : k < genericShortArcGapSum g longIdx) :
    shortArcBlockOffset g longIdx (shortArcGapOffsetDecode g longIdx k hk).a
        (shortArcGapOffsetDecode g longIdx k hk).hne +
      (shortArcGapOffsetDecode g longIdx k hk).j.val = k :=
  (shortArcGapOffsetDecode_exists g longIdx k hk).choose_spec

theorem shortArcBlockOffset_lt_of_lt (g : CycleTwoChordGraph) (longIdx a a' : Fin 4)
    (hne : a ≠ longIdx) (hne' : a' ≠ longIdx) (hlt : a.val < a'.val) :
    shortArcBlockOffset g longIdx a hne + g.cyclicGap a ≤ shortArcBlockOffset g longIdx a' hne' := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rw [shortArcBlockOffset_fin, shortArcBlockOffset_fin]
  fin_cases longIdx <;> fin_cases a <;> fin_cases a' <;>
    first
    | exact absurd rfl hne
    | exact absurd rfl hne'
    | simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] at hlt ⊢; first | done | omega

theorem shortArcGapOffsetDecode_unique (g : CycleTwoChordGraph) (longIdx : Fin 4) (k : Nat)
    (_hk : k < genericShortArcGapSum g longIdx)
    {a a' : Fin 4} {hne : a ≠ longIdx} {hne' : a' ≠ longIdx}
    {j : Fin (g.cyclicGap a)} {j' : Fin (g.cyclicGap a')}
    (h1 : shortArcBlockOffset g longIdx a hne + j.val = k)
    (h2 : shortArcBlockOffset g longIdx a' hne' + j'.val = k) :
    a = a' ∧ j.val = j'.val := by
  by_cases heq : a = a'
  · subst heq
    exact ⟨rfl, by omega⟩
  · exfalso
    have hlt' : a.val < a'.val ∨ a'.val < a.val :=
      Nat.lt_or_gt_of_ne (Fin.val_ne_iff.mpr heq)
    rcases hlt' with hlt | hlt
    · have hbound := shortArcBlockOffset_lt_of_lt g longIdx a a' hne hne' hlt
      have hj : j.val + 1 ≤ g.cyclicGap a := Nat.succ_le_of_lt j.isLt
      omega
    · have hbound := shortArcBlockOffset_lt_of_lt g longIdx a' a hne' hne hlt
      have hj' : j'.val + 1 ≤ g.cyclicGap a' := Nat.succ_le_of_lt j'.isLt
      omega

noncomputable def genericDecompNodeDecode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (n : Nat) (hn : n < genericDecompNodeCount g hyp) : GenericDecompNode g hyp.arcIdx :=
  if h0 : n < hyp.longArcLen then
    .longSeg (Fin.cast (longArcLen_eq g hyp) ⟨n, h0⟩)
  else if h1 : n < genericDecompJunctionBase g hyp then
    let k := n - hyp.longArcLen
    have hk : k < genericShortArcGapSum g hyp.arcIdx := by
      dsimp [genericDecompJunctionBase] at h1
      omega
    let decoded := shortArcGapOffsetDecode g hyp.arcIdx k hk
    .shortSeg decoded.a decoded.hne decoded.j
  else
    .junction ⟨(n - genericDecompJunctionBase g hyp), by
      dsimp [genericDecompNodeCount, genericDecompJunctionBase] at hn h1 ⊢
      omega⟩

theorem genericDecompNodeDecode_encode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (node : GenericDecompNode g hyp.arcIdx) :
    genericDecompNodeDecode g hyp (genericDecompNodeEncode g hyp node)
      (genericDecompNodeEncode_lt g hyp node) = node := by
  cases node with
  | longSeg j =>
    have hlt' : j.val < hyp.longArcLen := j.isLt
    dsimp [genericDecompNodeDecode, genericDecompNodeEncode]
    rw [dif_pos hlt']
    rfl
  | shortSeg a hne j =>
    set enc := hyp.longArcLen + shortArcBlockOffset g hyp.arcIdx a hne + j.val
    have h0 : ¬ enc < hyp.longArcLen := by dsimp [enc]; omega
    have h1 : enc < genericDecompJunctionBase g hyp := by
      dsimp [enc, genericDecompJunctionBase]
      have _hoff := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
      have _hj : j.val + 1 ≤ g.cyclicGap a := Nat.succ_le_of_lt j.isLt
      omega
    have hk : enc - hyp.longArcLen < genericShortArcGapSum g hyp.arcIdx := by
      dsimp [enc, genericDecompJunctionBase] at h1
      omega
    set dec := shortArcGapOffsetDecode g hyp.arcIdx (enc - hyp.longArcLen) hk
    have hspec := shortArcGapOffsetDecode_spec g hyp.arcIdx (enc - hyp.longArcLen) hk
    have hself : shortArcBlockOffset g hyp.arcIdx a hne + j.val = enc - hyp.longArcLen := by
      dsimp [enc]
      omega
    have huniq := shortArcGapOffsetDecode_unique g hyp.arcIdx _ hk hself hspec
    obtain ⟨ha, hjval⟩ := huniq
    simp only [genericDecompNodeDecode, genericDecompNodeEncode, enc, dec, h0, h1, if_neg, if_pos, ↓reduceDIte]
    exact GenericDecompNode.shortSeg_eq_of_arcIdxVal ha.symm hjval.symm
  | junction e =>
    set enc := hyp.longArcLen + genericShortArcGapSum g hyp.arcIdx + e.val
    have h0 : ¬ enc < hyp.longArcLen := by dsimp [enc]; omega
    have h1 : ¬ enc < genericDecompJunctionBase g hyp := by
      dsimp [enc, genericDecompJunctionBase]
      omega
    have h2 : ¬ enc < hyp.longArcLen + genericShortArcGapSum g hyp.arcIdx := by dsimp [enc]; omega
    simp only [genericDecompNodeDecode, genericDecompNodeEncode, enc, h0, h1, h2, if_neg, ↓reduceDIte]
    congr 1
    exact Fin.ext (by dsimp [enc, genericDecompJunctionBase]; omega)
  | hub kind => nomatch kind

theorem genericDecompNodeEncode_decode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (i : Fin (genericDecompNodeCount g hyp)) :
    genericDecompNodeEncode g hyp (genericDecompNodeDecode g hyp i.val i.2) = i.val := by
  by_cases h0 : i.val < hyp.longArcLen
  · have hdec : genericDecompNodeDecode g hyp i.val i.2 =
      .longSeg (Fin.cast (longArcLen_eq g hyp) ⟨i.val, h0⟩) := by
      simp [genericDecompNodeDecode, h0]
    rw [hdec, genericDecompNodeEncode]
    simp
  · by_cases h1 : i.val < genericDecompJunctionBase g hyp
    · have hk : i.val - hyp.longArcLen < genericShortArcGapSum g hyp.arcIdx := by
        dsimp [genericDecompJunctionBase] at h1
        omega
      have hdec : genericDecompNodeDecode g hyp i.val i.2 =
          .shortSeg (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).a
            (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).hne
            (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).j := by
        simp [genericDecompNodeDecode, h0, h1, if_neg, if_pos]
      have hspec := shortArcGapOffsetDecode_spec g hyp.arcIdx (i.val - hyp.longArcLen) hk
      have hle : hyp.longArcLen ≤ i.val := Nat.le_of_not_lt h0
      rw [hdec, genericDecompNodeEncode]
      calc hyp.longArcLen +
            shortArcBlockOffset g hyp.arcIdx (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).a
              (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).hne +
          ↑(shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).j
          _ = (hyp.longArcLen +
              shortArcBlockOffset g hyp.arcIdx (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).a
                (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).hne) +
              ↑(shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).j := rfl
          _ = hyp.longArcLen +
              (shortArcBlockOffset g hyp.arcIdx (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).a
                  (shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).hne +
                ↑(shortArcGapOffsetDecode g hyp.arcIdx (i.val - hyp.longArcLen) hk).j) := Nat.add_assoc _ _ _
          _ = i.val := by rw [hspec, Nat.add_sub_of_le hle]
    · have hdec : genericDecompNodeDecode g hyp i.val i.2 =
        .junction ⟨i.val - genericDecompJunctionBase g hyp,
          by
            have hbase : genericDecompJunctionBase g hyp ≤ i.val := Nat.le_of_not_lt h1
            have hi' : i.val < genericDecompJunctionBase g hyp + 4 := by
              have hcnt : genericDecompNodeCount g hyp = genericDecompJunctionBase g hyp + 4 := by
                dsimp [genericDecompNodeCount, genericDecompJunctionBase]
                omega
              simpa [hcnt] using i.isLt
            omega⟩ := by
        simp [genericDecompNodeDecode, h0, h1, if_neg]
      rw [hdec, genericDecompNodeEncode]
      dsimp [genericDecompJunctionBase]
      exact Nat.add_sub_of_le (Nat.le_of_not_lt h1)

noncomputable def genericDecompNodeFinEquiv (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    GenericDecompNode g hyp.arcIdx ≃ Fin (genericDecompNodeCount g hyp) where
  toFun node := ⟨genericDecompNodeEncode g hyp node, genericDecompNodeEncode_lt g hyp node⟩
  invFun i := genericDecompNodeDecode g hyp i.val i.2
  left_inv node := genericDecompNodeDecode_encode g hyp node
  right_inv i := Fin.ext (genericDecompNodeEncode_decode g hyp i)

noncomputable def mkGenericDecompFinTransport (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    GenericDecompFinTransport g hyp where
  finEquiv := genericDecompNodeFinEquiv g hyp

theorem genericDecompNodeCount_eq_card (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp := by
  classical
  rw [← Nat.card_fin (genericDecompNodeCount g hyp), Nat.card_congr (genericDecompNodeFinEquiv g hyp).symm]

noncomputable instance genericDecompNodeFinite (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Finite (GenericDecompNode g hyp.arcIdx) :=
  Finite.of_equiv _ (genericDecompNodeFinEquiv g hyp).symm

noncomputable instance genericDecompNodeFintype (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Fintype (GenericDecompNode g hyp.arcIdx) :=
  Fintype.ofFinite _

/-! ## Tagged-edge Fin encoding (toward `edgeCard`) -/

def genericDecompLongChainBound (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen - 1

def genericDecompLongStartBase (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen - 1

def genericDecompLongEndBase (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen + 1

def genericDecompShortEdgeBase (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  hyp.longArcLen + 3

theorem genericDecompShortEdgeBase_eq (hyp : NoncrossingPathDecompAssumptions g) :
    genericDecompShortEdgeBase hyp =
      genericDecompLongChainBound hyp + 4 := by
  have _hlen := hyp.hlen
  dsimp [genericDecompShortEdgeBase, genericDecompLongChainBound,
    NoncrossingPathDecompAssumptions.longArcLen]
  omega

theorem genericDecompEdgeCount_eq_shortBase (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    genericDecompEdgeCount g hyp =
      genericDecompShortEdgeBase hyp + genericShortArcGapSum g hyp.arcIdx := by
  have _hlen := hyp.hlen
  dsimp [genericDecompEdgeCount, genericDecompShortEdgeBase, genericDecompLongChainBound,
    NoncrossingPathDecompAssumptions.longArcLen]
  omega

def longStartEndpoint (k : Fin 2) : Fin 4 :=
  if k = 0 then 0 else 2

def longEndEndpoint (k : Fin 2) : Fin 4 :=
  if k = 0 then 1 else 3

theorem longStartEndpoint_start (k : Fin 2) : longArcStartJunctions (longStartEndpoint k) := by
  fin_cases k <;> simp [longStartEndpoint, longArcStartJunctions]

theorem longEndEndpoint_end (k : Fin 2) : longArcEndJunctions (longEndEndpoint k) := by
  fin_cases k <;> simp [longEndEndpoint, longArcEndJunctions]

noncomputable def shortArcJunctionEndpoint (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (shape : GenericDecompTreeShape g hyp) (a : Fin 4) (hne : a ≠ hyp.arcIdx) : Fin 4 :=
  (shape.shortArc_attached a hne).choose

theorem shortArcJunctionEndpoint_spec (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (shape : GenericDecompTreeShape g hyp) (a : Fin 4) (hne : a ≠ hyp.arcIdx) :
    g.junctionShortArcAt hyp.arcIdx (shortArcJunctionEndpoint g hyp shape a hne) = some a :=
  (shape.shortArc_attached a hne).choose_spec

theorem shortArcZeroJunction_shortArcJunctionEndpoint (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (shape : GenericDecompTreeShape g hyp)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) :
    shortArcZeroJunction g hyp a (shortArcJunctionEndpoint g hyp shape a hne) := by
  simp [shortArcZeroJunction, shortArcJunctionEndpoint_spec]

theorem shortArcJunctionEndpoint_eq_of_shortArcZeroJunction (shape : GenericDecompTreeShape g hyp)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) (e : Fin 4)
    (he : shortArcZeroJunction g hyp a e) :
    e = shortArcJunctionEndpoint g hyp shape a hne := by
  classical
  dsimp [shortArcJunctionEndpoint, shortArcZeroJunction] at he ⊢
  have he' : shortArcZeroJunction g hyp a (shortArcJunctionEndpoint g hyp shape a hne) :=
    shortArcZeroJunction_shortArcJunctionEndpoint g hyp shape a hne
  exact shape.shortArc_junction_unique a hne e _ he he'

/-! ## Route B: tagged endpoint classification (upper bound on |E|) -/

section EdgeTag

variable {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}

/-- Combinatorial edge tag from endpoint kinds (no Fin↔`Sym2` bijection). -/
inductive GenericDecompEdgeTag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  | longChain (j : Fin (hyp.longArcLen - 1))
  | longStartJunc (k : Fin 2)
  | longEndJunc (k : Fin 2)
  | shortChain (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Fin (g.cyclicGap a - 1))
  | shortBase (a : Fin 4) (hne : a ≠ hyp.arcIdx)

noncomputable instance genericDecompAdj_decidableRel : DecidableRel (genericDecompAdj g hyp) :=
  Classical.decRel _

noncomputable instance genericDecompGraph_adjDecidable :
    DecidableRel (genericDecompGraph g hyp).Adj :=
  genericDecompAdj_decidableRel

noncomputable instance genericDecompGraph_fintypeEdgeSet :
    Fintype (genericDecompGraph g hyp).edgeSet :=
  SimpleGraph.fintypeEdgeSet (genericDecompGraph g hyp)

def longStartEndpointInv (e : Fin 4) (_he : longArcStartJunctions e) : Fin 2 :=
  if _ : e = 0 then 0 else 1

def longEndEndpointInv (e : Fin 4) (_he : longArcEndJunctions e) : Fin 2 :=
  if _ : e = 1 then 0 else 1

theorem longStartEndpoint_inv (k : Fin 2) :
    longStartEndpointInv (longStartEndpoint k) (longStartEndpoint_start k) = k := by
  fin_cases k <;> simp [longStartEndpoint, longStartEndpointInv, longArcStartJunctions]

theorem longEndEndpoint_inv (k : Fin 2) :
    longEndEndpointInv (longEndEndpoint k) (longEndEndpoint_end k) = k := by
  fin_cases k <;> simp [longEndEndpoint, longEndEndpointInv, longArcEndJunctions]

theorem longStartEndpointInv_spec (e : Fin 4) (he : longArcStartJunctions e) :
    longStartEndpoint (longStartEndpointInv e he) = e := by
  fin_cases e <;> simp [longArcStartJunctions] at he <;> simp [longStartEndpoint, longStartEndpointInv]

theorem longEndEndpointInv_spec (e : Fin 4) (he : longArcEndJunctions e) :
    longEndEndpoint (longEndEndpointInv e he) = e := by
  fin_cases e <;> simp [longArcEndJunctions] at he <;> simp [longEndEndpoint, longEndEndpointInv]

theorem shortArc_gap_pos (shape : GenericDecompTreeShape g hyp)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) : 0 < g.cyclicGap a :=
  shape.shortArc_gap_pos a hne

noncomputable def genericDecompEdgeOfTag (shape : GenericDecompTreeShape g hyp)
    (tag : GenericDecompEdgeTag g hyp) : Sym2 (GenericDecompNode g hyp.arcIdx) :=
  match tag with
  | .longChain j =>
    s(.longSeg ⟨j.val, Nat.lt_trans j.isLt (Nat.sub_lt hyp.hlen Nat.one_pos)⟩,
      .longSeg ⟨j.val + 1, by
        dsimp [NoncrossingPathDecompAssumptions.longArcLen]
        omega⟩)
  | .longStartJunc k =>
    s(.longSeg ⟨0, hyp.hlen⟩, .junction (longStartEndpoint k))
  | .longEndJunc k =>
    s(.longSeg ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen Nat.one_pos⟩,
      .junction (longEndEndpoint k))
  | .shortChain a hne j =>
    s(.shortSeg a hne ⟨j.val, by omega⟩, .shortSeg a hne ⟨j.val + 1, by omega⟩)
  | .shortBase a hne =>
    let hgap := shortArc_gap_pos shape a hne
    s(.shortSeg a hne ⟨0, hgap⟩, .junction (shortArcJunctionEndpoint g hyp shape a hne))

theorem genericDecompEdgeOfTag_mem_edgeSet (shape : GenericDecompTreeShape g hyp)
    (tag : GenericDecompEdgeTag g hyp) :
    genericDecompEdgeOfTag shape tag ∈ (genericDecompGraph g hyp).edgeSet := by
  cases tag with
  | longChain j =>
    apply (SimpleGraph.mem_edgeSet _).mpr
    have hj : j.val + 1 < hyp.longArcLen := by
      dsimp [NoncrossingPathDecompAssumptions.longArcLen]
      omega
    have hjlt : j.val < hyp.longArcLen :=
      Nat.lt_trans j.isLt (Nat.sub_lt hyp.hlen Nat.one_pos)
    exact longSeg_adj_succ g hyp (Fin.cast (longArcLen_eq g hyp).symm ⟨j.val, hjlt⟩) hj
  | longStartJunc k =>
    fin_cases k
    · exact (SimpleGraph.mem_edgeSet _).mpr
        (longSeg_zero_adj_junction_start g hyp 0 (by simp [longArcStartJunctions]))
    · exact (SimpleGraph.mem_edgeSet _).mpr
        (longSeg_zero_adj_junction_start g hyp 2 (by simp [longArcStartJunctions]))
  | longEndJunc k =>
    fin_cases k
    · exact (SimpleGraph.mem_edgeSet _).mpr
        (longSeg_last_adj_junction_end g hyp 1 (by simp [longArcEndJunctions]))
    · exact (SimpleGraph.mem_edgeSet _).mpr
        (longSeg_last_adj_junction_end g hyp 3 (by simp [longArcEndJunctions]))
  | shortChain a hne j =>
    apply (SimpleGraph.mem_edgeSet _).mpr
    dsimp [genericDecompEdgeOfTag, genericDecompGraph, genericDecompAdj]
    refine And.intro rfl (Or.inl ⟨rfl, by omega⟩)
  | shortBase a hne =>
    apply (SimpleGraph.mem_edgeSet _).mpr
    exact shortSeg_zero_adj_junction g hyp a hne (shortArcJunctionEndpoint g hyp shape a hne)
      (shortArc_gap_pos shape a hne)
      (shortArcZeroJunction_shortArcJunctionEndpoint g hyp shape a hne)

noncomputable def genericDecompSym2Unpair {α} (s : Sym2 α) : α × α :=
  let hex := (Sym2.exists).1 ⟨s, rfl⟩
  let u := Classical.choose hex
  let v := Classical.choose (Classical.choose_spec hex)
  (u, v)

theorem genericDecompSym2Unpair_spec {α} (s : Sym2 α) :
    s = Sym2.mk (genericDecompSym2Unpair s).1 (genericDecompSym2Unpair s).2 := by
  classical
  dsimp [genericDecompSym2Unpair]
  exact Classical.choose_spec (Classical.choose_spec ((Sym2.exists).1 ⟨s, rfl⟩))

theorem genericDecompAdj_hub_left (k : GenericHubKind g) (v : GenericDecompNode g hyp.arcIdx)
    (h : genericDecompAdj g hyp (.hub k) v) : False := by
  cases v <;> simp [genericDecompAdj] at h

theorem genericDecompAdj_hub_right (u : GenericDecompNode g hyp.arcIdx) (k : GenericHubKind g)
    (h : genericDecompAdj g hyp u (.hub k)) : False := by
  cases u <;> simp [genericDecompAdj] at h

def decLongArcStartJunctions : (e : Fin 4) → Decidable (longArcStartJunctions e)
  | 0 => isTrue (by simp [longArcStartJunctions])
  | 1 => isFalse (by simp [longArcStartJunctions])
  | 2 => isTrue (by simp [longArcStartJunctions])
  | 3 => isFalse (by simp [longArcStartJunctions])

def decLongArcEndJunctions : (e : Fin 4) → Decidable (longArcEndJunctions e)
  | 0 => isFalse (by simp [longArcEndJunctions])
  | 1 => isTrue (by simp [longArcEndJunctions])
  | 2 => isFalse (by simp [longArcEndJunctions])
  | 3 => isTrue (by simp [longArcEndJunctions])

instance (e : Fin 4) : Decidable (longArcStartJunctions e) :=
  decLongArcStartJunctions e

instance (e : Fin 4) : Decidable (longArcEndJunctions e) :=
  decLongArcEndJunctions e

theorem genericDecompAdj_longSeg_longSeg_succ {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : j.val + 1 = j'.val) :
    j.val + 1 < hyp.longArcLen := by
  simp [genericDecompAdj, hcond] at h
  omega

theorem genericDecompAdj_longSeg_longSeg_pred {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : ¬ j.val + 1 = j'.val) :
    j'.val + 1 = j.val ∧ j'.val + 1 < hyp.longArcLen := by
  simp [genericDecompAdj, hcond] at h
  omega

theorem genericDecompAdj_longSeg_junction_end {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e)) (hstart : ¬ longArcStartJunctions e) :
    longArcEndJunctions e := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

theorem genericDecompAdj_junction_longSeg_end {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j)) (hstart : ¬ longArcStartJunctions e) :
    longArcEndJunctions e := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

theorem genericDecompAdj_shortSeg_shortSeg_succ {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : j.val + 1 = j'.val) : j.val + 1 < g.cyclicGap a := by
  simp [genericDecompAdj, hcond] at h
  omega

theorem genericDecompAdj_shortSeg_shortSeg_pred {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : ¬ j.val + 1 = j'.val) : j'.val + 1 = j.val ∧ j'.val + 1 < g.cyclicGap a := by
  simp [genericDecompAdj, hcond] at h
  omega

theorem genericDecompAdj_longSeg_junction_start_components {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e)) (hstart : longArcStartJunctions e) :
    j.val = 0 := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

theorem genericDecompAdj_longSeg_junction_end_components {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e)) (hstart : ¬ longArcStartJunctions e) :
    j.val + 1 = hyp.longArcLen := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

theorem genericDecompAdj_junction_longSeg_start_components {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j)) (hstart : longArcStartJunctions e) :
    j.val = 0 := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

theorem genericDecompAdj_junction_longSeg_end_components {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j)) (hstart : ¬ longArcStartJunctions e) :
    j.val + 1 = hyp.longArcLen := by
  simp [genericDecompAdj] at h
  fin_cases e <;> simp [longArcStartJunctions, longArcEndJunctions] at hstart h ⊢ <;> tauto

def genericDecompEdgeTagOfAdj_longSeg_succ {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j'))
    (hcond : j.val + 1 = j'.val) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longChain ⟨j.val, by
    have hlt := genericDecompAdj_longSeg_longSeg_succ h hcond
    omega⟩

def genericDecompEdgeTagOfAdj_longSeg_pred {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j'))
    (hcond : ¬ j.val + 1 = j'.val) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longChain ⟨j'.val, by
    have hright := genericDecompAdj_longSeg_longSeg_pred h hcond
    omega⟩

def genericDecompEdgeTagOfAdj_longSeg_junction_start {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e))
    (hstart : longArcStartJunctions e) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longStartJunc (longStartEndpointInv e hstart)

def genericDecompEdgeTagOfAdj_longSeg_junction_end {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e))
    (hstart : ¬ longArcStartJunctions e) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longEndJunc (longEndEndpointInv e
    (genericDecompAdj_longSeg_junction_end h hstart))

def genericDecompEdgeTagOfAdj_shortSeg_succ {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : j.val + 1 = j'.val) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.shortChain a hne ⟨j.val, by
    have hlt := genericDecompAdj_shortSeg_shortSeg_succ h hcond
    omega⟩

def genericDecompEdgeTagOfAdj_shortSeg_pred {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : ¬ j.val + 1 = j'.val) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.shortChain a hne ⟨j'.val, by
    have hright := genericDecompAdj_shortSeg_shortSeg_pred h hcond
    omega⟩

def genericDecompEdgeTagOfAdj_junction_longSeg_start {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j))
    (hstart : longArcStartJunctions e) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longStartJunc (longStartEndpointInv e hstart)

def genericDecompEdgeTagOfAdj_junction_longSeg_end {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j))
    (hstart : ¬ longArcStartJunctions e) : GenericDecompEdgeTag g hyp :=
  GenericDecompEdgeTag.longEndJunc (longEndEndpointInv e
    (genericDecompAdj_junction_longSeg_end h hstart))

noncomputable def genericDecompEdgeTagOfAdj_junction_bridge (e e' : Fin 4)
    (_h : hyp.genericJunctionBridge e e') : GenericDecompEdgeTag g hyp :=
  if _ : e = 0 ∧ e' = 2 then .longStartJunc 1
  else if _ : e = 2 ∧ e' = 0 then .longStartJunc 1
  else if _ : e = 2 ∧ e' = 3 then .longEndJunc 1
  else if _ : e = 3 ∧ e' = 2 then .longEndJunc 1
  else if _ : e = 0 ∧ e' = 1 then .longEndJunc 0
  else if _ : e = 1 ∧ e' = 0 then .longEndJunc 0
  else .longStartJunc 0

/-!
  OPEN (Route B bridge): `genericDecompEdgeTagOfAdj_junction_bridge` parked until
  `genericDecompAdj` gains junction-bridge edges + `genericDecompEdgeOfTag` bridge ite.
-/

/-
theorem genericDecompEdgeTagOfAdj_junction_bridge_spec (shape : GenericDecompTreeShape g hyp)
    {e e' : Fin 4} (hbr : hyp.genericJunctionBridge e e') :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_junction_bridge e e' hbr) =
      s(.junction e, .junction e') := by
  sorry
-/

noncomputable def genericDecompEdgeTagOfAdj (u v : GenericDecompNode g hyp.arcIdx)
    (h : genericDecompAdj g hyp u v) : GenericDecompEdgeTag g hyp := by
  cases u with
  | longSeg j =>
    cases v with
    | longSeg j' =>
      by_cases hcond : j.val + 1 = j'.val
      · exact genericDecompEdgeTagOfAdj_longSeg_succ h hcond
      · exact genericDecompEdgeTagOfAdj_longSeg_pred h hcond
    | junction e =>
      by_cases hstart : longArcStartJunctions e
      · exact genericDecompEdgeTagOfAdj_longSeg_junction_start h hstart
      · exact genericDecompEdgeTagOfAdj_longSeg_junction_end h hstart
    | shortSeg _ _ _ | hub _ => exact False.elim (by simp [genericDecompAdj] at h)
  | shortSeg a hne j =>
    cases v with
    | longSeg _ | hub _ => exact False.elim (by simp [genericDecompAdj] at h)
    | junction _ => exact GenericDecompEdgeTag.shortBase a hne
    | shortSeg a' hne' j' =>
      by_cases hcond : j.val + 1 = j'.val
      · exact genericDecompEdgeTagOfAdj_shortSeg_succ h hcond
      · exact genericDecompEdgeTagOfAdj_shortSeg_pred h hcond
  | junction e =>
    cases v with
    | longSeg _ =>
      by_cases hstart : longArcStartJunctions e
      · exact genericDecompEdgeTagOfAdj_junction_longSeg_start h hstart
      · exact genericDecompEdgeTagOfAdj_junction_longSeg_end h hstart
    | shortSeg a hne _ => exact GenericDecompEdgeTag.shortBase a hne
    | junction _ => exact False.elim (by simp [genericDecompAdj] at h)
    | hub _ => exact False.elim (by simp [genericDecompAdj] at h)
  | hub _ =>
    exact False.elim (by simp [genericDecompAdj] at h)

noncomputable def genericDecompEdgeTagOfEdge (shape : GenericDecompTreeShape g hyp)
    (e : (genericDecompGraph g hyp).edgeSet) : GenericDecompEdgeTag g hyp :=
  let uv := genericDecompSym2Unpair e.val
  genericDecompEdgeTagOfAdj uv.1 uv.2 ((SimpleGraph.mem_edgeSet _).1 (by
    rw [← genericDecompSym2Unpair_spec e.val]
    exact e.property))

def genericDecompEdgeTagIndex (tag : GenericDecompEdgeTag g hyp) : Nat :=
  match tag with
  | .longChain j => j.val
  | .longStartJunc k => genericDecompLongStartBase hyp + k.val
  | .longEndJunc k => genericDecompLongEndBase hyp + k.val
  | .shortChain a hne j =>
    genericDecompShortEdgeBase hyp + shortArcBlockOffset g hyp.arcIdx a hne + j.val
  | .shortBase a hne =>
    genericDecompShortEdgeBase hyp + shortArcBlockOffset g hyp.arcIdx a hne +
      (g.cyclicGap a - 1)

theorem genericDecompEdgeTagIndex_lt (shape : GenericDecompTreeShape g hyp)
    (tag : GenericDecompEdgeTag g hyp) :
    genericDecompEdgeTagIndex tag < genericDecompEdgeCount g hyp := by
  cases tag with
  | longChain j =>
    dsimp [genericDecompEdgeTagIndex, genericDecompEdgeCount, NoncrossingPathDecompAssumptions.longArcLen]
    omega
  | longStartJunc k =>
    dsimp [genericDecompEdgeTagIndex, genericDecompEdgeCount, genericDecompLongStartBase,
      NoncrossingPathDecompAssumptions.longArcLen]
    fin_cases k <;> omega
  | longEndJunc k =>
    dsimp [genericDecompEdgeTagIndex, genericDecompEdgeCount, genericDecompLongEndBase,
      NoncrossingPathDecompAssumptions.longArcLen]
    fin_cases k <;> omega
  | shortChain a hne j =>
    dsimp [genericDecompEdgeTagIndex, genericDecompEdgeCount, genericDecompShortEdgeBase]
    have hsum := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
    omega
  | shortBase a hne =>
    dsimp [genericDecompEdgeTagIndex, genericDecompEdgeCount, genericDecompShortEdgeBase]
    have hsum := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
    have hgap1 : 1 ≤ g.cyclicGap a := Nat.succ_le_of_lt (shortArc_gap_pos shape a hne)
    omega

theorem shortArcChainTagOffset_ne_shortBaseOffset (g : CycleTwoChordGraph) (longIdx a a' : Fin 4)
    (hne : a ≠ longIdx) (hne' : a' ≠ longIdx) (ha : a ≠ a') (j : Fin (g.cyclicGap a - 1)) :
    shortArcBlockOffset g longIdx a hne + j.val ≠
      shortArcBlockOffset g longIdx a' hne' + (g.cyclicGap a' - 1) := by
  intro heq
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  have hgap' : 1 ≤ g.cyclicGap a' := by
    fin_cases a' <;> simp [CycleTwoChordGraph.cyclicGap, h01, h12, h23, h3n] <;> omega
  by_cases hlt : a.val < a'.val
  · have hbound := shortArcBlockOffset_lt_of_lt g longIdx a a' hne hne' hlt
    have hj := j.isLt
    omega
  · by_cases hlt' : a'.val < a.val
    · have hbound := shortArcBlockOffset_lt_of_lt g longIdx a' a hne' hne hlt'
      have hj := j.isLt
      omega
    · exact ha (Fin.ext (Nat.le_antisymm (Nat.not_lt.mp hlt') (Nat.not_lt.mp hlt)))

theorem genericDecompEdgeTagIndex_shortChain_ne_shortBase (shape : GenericDecompTreeShape g hyp)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Fin (g.cyclicGap a - 1))
    (a' : Fin 4) (hne' : a' ≠ hyp.arcIdx) :
    genericDecompEdgeTagIndex (.shortChain a hne j) ≠
      genericDecompEdgeTagIndex (.shortBase a' hne') := by
  intro h
  have hoff :
      shortArcBlockOffset g hyp.arcIdx a hne + j.val =
        shortArcBlockOffset g hyp.arcIdx a' hne' + (g.cyclicGap a' - 1) := by
    dsimp [genericDecompEdgeTagIndex] at h
    simp only [genericDecompShortEdgeBase] at h
    omega
  by_cases heq : a = a'
  · subst heq
    have hj : j.val < g.cyclicGap a - 1 := j.isLt
    omega
  · exact absurd hoff (shortArcChainTagOffset_ne_shortBaseOffset g hyp.arcIdx a a' hne hne' heq j)

theorem genericDecompEdgeTagIndex_injective (shape : GenericDecompTreeShape g hyp) :
    Function.Injective (@genericDecompEdgeTagIndex g hyp) := by
  intro t1 t2 h
  match t1, t2 with
  | .longChain j1, .longChain j2 =>
    simp [genericDecompEdgeTagIndex] at h
    exact congrArg GenericDecompEdgeTag.longChain (Fin.ext h)
  | .longStartJunc k1, .longStartJunc k2 =>
    simp [genericDecompEdgeTagIndex, genericDecompLongStartBase] at h
    exact congrArg GenericDecompEdgeTag.longStartJunc (Fin.ext h)
  | .longEndJunc k1, .longEndJunc k2 =>
    simp [genericDecompEdgeTagIndex, genericDecompLongEndBase] at h
    exact congrArg GenericDecompEdgeTag.longEndJunc (Fin.ext h)
  | .shortChain a hne j, .shortChain a' hne' j' =>
    simp [genericDecompEdgeTagIndex, genericDecompShortEdgeBase] at h
    have hoff :
        shortArcBlockOffset g hyp.arcIdx a hne + j.val =
          shortArcBlockOffset g hyp.arcIdx a' hne' + j'.val := by omega
    set k := shortArcBlockOffset g hyp.arcIdx a hne + j.val
    let jup : Fin (g.cyclicGap a) := ⟨j.val, by omega⟩
    let j'up : Fin (g.cyclicGap a') := ⟨j'.val, by omega⟩
    have hk : k < genericShortArcGapSum g hyp.arcIdx := by
      dsimp [k]
      have hsum := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
      omega
    have h1 : shortArcBlockOffset g hyp.arcIdx a hne + jup.val = k := rfl
    have h2 : shortArcBlockOffset g hyp.arcIdx a' hne' + j'up.val = k :=
      hoff.symm.trans h1
    have huniq := shortArcGapOffsetDecode_unique g hyp.arcIdx k hk h1 h2
    obtain ⟨ha, hjval⟩ := huniq
    subst ha
    exact congrArg (GenericDecompEdgeTag.shortChain a hne) (Fin.ext hjval)
  | .shortBase a hne, .shortBase a' hne' =>
    simp [genericDecompEdgeTagIndex, genericDecompShortEdgeBase] at h
    have hgap : 0 < g.cyclicGap a := shortArc_gap_pos shape a hne
    have hgap' : 0 < g.cyclicGap a' := shortArc_gap_pos shape a' hne'
    let k := shortArcBlockOffset g hyp.arcIdx a hne + (g.cyclicGap a - 1)
    have hk : k < genericShortArcGapSum g hyp.arcIdx := by
      have hsum := shortArcBlockOffset_add_gap_le_sum g hyp.arcIdx a hne
      omega
    have hoff :
        shortArcBlockOffset g hyp.arcIdx a hne + (g.cyclicGap a - 1) =
          shortArcBlockOffset g hyp.arcIdx a' hne' + (g.cyclicGap a' - 1) := by omega
    let jlast : Fin (g.cyclicGap a) := ⟨g.cyclicGap a - 1, Nat.pred_lt (Nat.ne_of_gt hgap)⟩
    let jlast' : Fin (g.cyclicGap a') := ⟨g.cyclicGap a' - 1, Nat.pred_lt (Nat.ne_of_gt hgap')⟩
    have h1 : shortArcBlockOffset g hyp.arcIdx a hne + jlast.val = k := by
      dsimp [jlast, k]
    have h2 : shortArcBlockOffset g hyp.arcIdx a' hne' + jlast'.val = k := by
      dsimp [jlast, jlast', k]
      exact hoff.symm
    have ha : a = a' :=
      (shortArcGapOffsetDecode_unique g hyp.arcIdx k hk h1 h2).1
    subst ha
    rfl
  | .longChain j, .longStartJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longStartJunc k, .longChain j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longChain j, .longEndJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longEndJunc k, .longChain j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longChain j, .shortChain a hne j' =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompShortEdgeBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    have := hyp.hlen
    omega
  | .shortChain a hne j', .longChain j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompShortEdgeBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    have := hyp.hlen
    omega
  | .longChain j, .shortBase a hne =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompShortEdgeBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    have := hyp.hlen
    omega
  | .shortBase a hne, .longChain j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompShortEdgeBase, NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    have := hyp.hlen
    omega
  | .longStartJunc k, .longEndJunc k' =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompLongEndBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> fin_cases k' <;> have := hyp.hlen <;> omega
  | .longEndJunc k', .longStartJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompLongEndBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> fin_cases k' <;> have := hyp.hlen <;> omega
  | .longStartJunc k, .shortChain a hne j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .shortChain a hne j, .longStartJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longStartJunc k, .shortBase a hne =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .shortBase a hne, .longStartJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongStartBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longEndJunc k, .shortChain a hne j =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .shortChain a hne j, .longEndJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .longEndJunc k, .shortBase a hne =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .shortBase a hne, .longEndJunc k =>
    unfold genericDecompEdgeTagIndex at h
    simp [genericDecompLongEndBase, genericDecompShortEdgeBase,
      NoncrossingPathDecompAssumptions.longArcLen] at h
    exfalso
    fin_cases k <;> have := hyp.hlen <;> omega
  | .shortChain a hne j, .shortBase a' hne' =>
    exact absurd h (genericDecompEdgeTagIndex_shortChain_ne_shortBase shape a hne j a' hne')
  | .shortBase a hne, .shortChain a' hne' j' =>
    exact absurd h (Ne.symm (genericDecompEdgeTagIndex_shortChain_ne_shortBase shape a' hne' j' a hne))

theorem genericDecompEdgeTagOfAdj_longSeg_of_succ {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : j.val + 1 = j'.val) :
    genericDecompEdgeTagOfAdj (.longSeg j) (.longSeg j') h =
      genericDecompEdgeTagOfAdj_longSeg_succ h hcond := by
  simp [genericDecompEdgeTagOfAdj, hcond, genericDecompEdgeTagOfAdj_longSeg_succ]

theorem genericDecompEdgeTagOfAdj_longSeg_of_pred {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : ¬ j.val + 1 = j'.val) :
    genericDecompEdgeTagOfAdj (.longSeg j) (.longSeg j') h =
      genericDecompEdgeTagOfAdj_longSeg_pred h hcond := by
  simp [genericDecompEdgeTagOfAdj, hcond, genericDecompEdgeTagOfAdj_longSeg_pred]

theorem genericDecompEdgeTagOfAdj_longSeg_junction_of_start {j : Fin (g.cyclicGap hyp.arcIdx)}
    {e : Fin 4} (h : genericDecompAdj g hyp (.longSeg j) (.junction e))
    (hstart : longArcStartJunctions e) :
    genericDecompEdgeTagOfAdj (.longSeg j) (.junction e) h =
      genericDecompEdgeTagOfAdj_longSeg_junction_start h hstart := by
  simp [genericDecompEdgeTagOfAdj, hstart, genericDecompEdgeTagOfAdj_longSeg_junction_start]

theorem genericDecompEdgeTagOfAdj_longSeg_junction_of_end {j : Fin (g.cyclicGap hyp.arcIdx)}
    {e : Fin 4} (h : genericDecompAdj g hyp (.longSeg j) (.junction e))
    (hstart : ¬ longArcStartJunctions e) :
    genericDecompEdgeTagOfAdj (.longSeg j) (.junction e) h =
      genericDecompEdgeTagOfAdj_longSeg_junction_end h hstart := by
  simp [genericDecompEdgeTagOfAdj, hstart, genericDecompEdgeTagOfAdj_longSeg_junction_end]

theorem genericDecompEdgeTagOfAdj_shortSeg_of_succ {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : j.val + 1 = j'.val) :
    genericDecompEdgeTagOfAdj (.shortSeg a hne j) (.shortSeg a' hne' j') h =
      genericDecompEdgeTagOfAdj_shortSeg_succ h hcond := by
  simp [genericDecompEdgeTagOfAdj, hcond, genericDecompEdgeTagOfAdj_shortSeg_succ]

theorem genericDecompEdgeTagOfAdj_shortSeg_of_pred {a : Fin 4} {hne : a ≠ hyp.arcIdx}
    {j : Fin (g.cyclicGap a)} {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : ¬ j.val + 1 = j'.val) :
    genericDecompEdgeTagOfAdj (.shortSeg a hne j) (.shortSeg a' hne' j') h =
      genericDecompEdgeTagOfAdj_shortSeg_pred h hcond := by
  simp [genericDecompEdgeTagOfAdj, hcond, genericDecompEdgeTagOfAdj_shortSeg_pred]

theorem genericDecompEdgeTagOfAdj_junction_longSeg_of_start {e : Fin 4}
    {j : Fin (g.cyclicGap hyp.arcIdx)} (h : genericDecompAdj g hyp (.junction e) (.longSeg j))
    (hstart : longArcStartJunctions e) :
    genericDecompEdgeTagOfAdj (.junction e) (.longSeg j) h =
      genericDecompEdgeTagOfAdj_junction_longSeg_start h hstart := by
  simp [genericDecompEdgeTagOfAdj, hstart, genericDecompEdgeTagOfAdj_junction_longSeg_start]

theorem genericDecompEdgeTagOfAdj_junction_longSeg_of_end {e : Fin 4}
    {j : Fin (g.cyclicGap hyp.arcIdx)} (h : genericDecompAdj g hyp (.junction e) (.longSeg j))
    (hstart : ¬ longArcStartJunctions e) :
    genericDecompEdgeTagOfAdj (.junction e) (.longSeg j) h =
      genericDecompEdgeTagOfAdj_junction_longSeg_end h hstart := by
  simp [genericDecompEdgeTagOfAdj, hstart, genericDecompEdgeTagOfAdj_junction_longSeg_end]

theorem genericDecompEdgeTagOfAdj_longSeg_succ_spec (shape : GenericDecompTreeShape g hyp)
    {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : j.val + 1 = j'.val) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_longSeg_succ h hcond) =
      s(.longSeg j, .longSeg j') := by
  dsimp [genericDecompEdgeTagOfAdj_longSeg_succ, genericDecompEdgeOfTag]
  have hj' : j' = ⟨j.val + 1, genericDecompAdj_longSeg_longSeg_succ h hcond⟩ :=
    Fin.ext (Eq.symm hcond)
  exact (Sym2.eq_iff).2 (Or.inl ⟨rfl, congrArg GenericDecompNode.longSeg hj'.symm⟩)

theorem genericDecompEdgeTagOfAdj_longSeg_pred_spec (shape : GenericDecompTreeShape g hyp)
    {j j' : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.longSeg j) (.longSeg j')) (hcond : ¬ j.val + 1 = j'.val) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_longSeg_pred h hcond) =
      s(.longSeg j, .longSeg j') := by
  have hright := genericDecompAdj_longSeg_longSeg_pred h hcond
  have hj : j = ⟨j'.val + 1, hright.2⟩ := Fin.ext (Eq.symm hright.1)
  dsimp [genericDecompEdgeTagOfAdj_longSeg_pred, genericDecompEdgeOfTag]
  exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, congrArg GenericDecompNode.longSeg hj.symm⟩)

theorem genericDecompEdgeTagOfAdj_longSeg_junction_start_spec (shape : GenericDecompTreeShape g hyp)
    {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e)) (hstart : longArcStartJunctions e) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_longSeg_junction_start h hstart) =
      s(.longSeg j, .junction e) := by
  have hj0 := genericDecompAdj_longSeg_junction_start_components h hstart
  have hj : j = ⟨0, hyp.hlen⟩ := Fin.ext hj0
  dsimp [genericDecompEdgeTagOfAdj_longSeg_junction_start, genericDecompEdgeOfTag]
  rw [longStartEndpointInv_spec e hstart]
  simp [longStartEndpoint, hj]

theorem genericDecompEdgeTagOfAdj_longSeg_junction_end_spec (shape : GenericDecompTreeShape g hyp)
    {j : Fin (g.cyclicGap hyp.arcIdx)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.longSeg j) (.junction e)) (hstart : ¬ longArcStartJunctions e) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_longSeg_junction_end h hstart) =
      s(.longSeg j, .junction e) := by
  have hj1 := genericDecompAdj_longSeg_junction_end_components h hstart
  have hend := genericDecompAdj_longSeg_junction_end h hstart
  have hjval : j.val = hyp.longArcLen - 1 := by
    dsimp [NoncrossingPathDecompAssumptions.longArcLen] at hj1 ⊢
    omega
  have hj : j = ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen Nat.one_pos⟩ := Fin.ext hjval
  dsimp [genericDecompEdgeTagOfAdj_longSeg_junction_end, genericDecompEdgeOfTag]
  rw [longEndEndpointInv_spec e hend]
  simp [longEndEndpoint, hj, NoncrossingPathDecompAssumptions.longArcLen]

theorem genericDecompEdgeTagOfAdj_shortSeg_succ_spec (shape : GenericDecompTreeShape g hyp)
    {a : Fin 4} {hne : a ≠ hyp.arcIdx} {j : Fin (g.cyclicGap a)}
    {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : j.val + 1 = j'.val) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_shortSeg_succ h hcond) =
      s(.shortSeg a hne j, .shortSeg a' hne' j') := by
  have hsucc := genericDecompAdj_shortSeg_shortSeg_succ h hcond
  obtain ⟨ha, _⟩ := h
  subst ha
  rw [show hne' = hne from Subsingleton.elim _ _]
  have hj' : j' = ⟨j.val + 1, hsucc⟩ := Fin.ext (Eq.symm hcond)
  dsimp [genericDecompEdgeTagOfAdj_shortSeg_succ, genericDecompEdgeOfTag]
  exact (Sym2.eq_iff).2 (Or.inl ⟨rfl, congrArg (GenericDecompNode.shortSeg a hne) hj'.symm⟩)

theorem genericDecompEdgeTagOfAdj_shortSeg_pred_spec (shape : GenericDecompTreeShape g hyp)
    {a : Fin 4} {hne : a ≠ hyp.arcIdx} {j : Fin (g.cyclicGap a)}
    {a' : Fin 4} {hne' : a' ≠ hyp.arcIdx} {j' : Fin (g.cyclicGap a')}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.shortSeg a' hne' j'))
    (hcond : ¬ j.val + 1 = j'.val) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_shortSeg_pred h hcond) =
      s(.shortSeg a hne j, .shortSeg a' hne' j') := by
  have hright := genericDecompAdj_shortSeg_shortSeg_pred h hcond
  obtain ⟨ha, _⟩ := h
  subst ha
  rw [show hne' = hne from Subsingleton.elim _ _]
  have hj : j = ⟨j'.val + 1, hright.2⟩ := Fin.ext (Eq.symm hright.1)
  dsimp [genericDecompEdgeTagOfAdj_shortSeg_pred, genericDecompEdgeOfTag]
  exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, congrArg (GenericDecompNode.shortSeg a hne) hj.symm⟩)

theorem genericDecompEdgeTagOfAdj_shortSeg_junction_spec (shape : GenericDecompTreeShape g hyp)
    {a : Fin 4} {hne : a ≠ hyp.arcIdx} {j : Fin (g.cyclicGap a)} {e : Fin 4}
    (h : genericDecompAdj g hyp (.shortSeg a hne j) (.junction e)) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj (.shortSeg a hne j) (.junction e) h) =
      s(.shortSeg a hne j, .junction e) := by
  dsimp [genericDecompEdgeTagOfAdj, genericDecompEdgeOfTag]
  obtain ⟨hj0, heown⟩ := h
  have heJ := shortArcJunctionEndpoint_eq_of_shortArcZeroJunction shape a hne e heown
  have hgap := shortArc_gap_pos shape a hne
  have hj : j = ⟨0, hgap⟩ := Fin.ext hj0
  rw [hj, heJ]

theorem genericDecompEdgeTagOfAdj_junction_shortSeg_spec (shape : GenericDecompTreeShape g hyp)
    {e : Fin 4} {a : Fin 4} {hne : a ≠ hyp.arcIdx} {j : Fin (g.cyclicGap a)}
    (h : genericDecompAdj g hyp (.junction e) (.shortSeg a hne j)) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj (.junction e) (.shortSeg a hne j) h) =
      s(.junction e, .shortSeg a hne j) := by
  dsimp [genericDecompEdgeTagOfAdj, genericDecompEdgeOfTag]
  obtain ⟨hj0, heown⟩ := h
  have heJ := shortArcJunctionEndpoint_eq_of_shortArcZeroJunction shape a hne e heown
  have hgap := shortArc_gap_pos shape a hne
  have hj : j = ⟨0, hgap⟩ := Fin.ext hj0
  rw [Sym2.eq_iff, heJ, hj]
  exact Or.inr ⟨rfl, rfl⟩

theorem genericDecompEdgeTagOfAdj_junction_longSeg_start_spec (shape : GenericDecompTreeShape g hyp)
    {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j)) (hstart : longArcStartJunctions e) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_junction_longSeg_start h hstart) =
      s(.junction e, .longSeg j) := by
  have hj0 := genericDecompAdj_junction_longSeg_start_components h hstart
  have hj : j = ⟨0, hyp.hlen⟩ := Fin.ext hj0
  dsimp [genericDecompEdgeTagOfAdj_junction_longSeg_start, genericDecompEdgeOfTag]
  rw [longStartEndpointInv_spec e hstart]
  simp [longStartEndpoint, hj]

theorem genericDecompEdgeTagOfAdj_junction_longSeg_end_spec (shape : GenericDecompTreeShape g hyp)
    {e : Fin 4} {j : Fin (g.cyclicGap hyp.arcIdx)}
    (h : genericDecompAdj g hyp (.junction e) (.longSeg j)) (hstart : ¬ longArcStartJunctions e) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_junction_longSeg_end h hstart) =
      s(.junction e, .longSeg j) := by
  have hj1 := genericDecompAdj_junction_longSeg_end_components h hstart
  have hend := genericDecompAdj_junction_longSeg_end h hstart
  have hjval : j.val = hyp.longArcLen - 1 := by
    dsimp [NoncrossingPathDecompAssumptions.longArcLen] at hj1 ⊢
    omega
  have hj : j = ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen Nat.one_pos⟩ := Fin.ext hjval
  dsimp [genericDecompEdgeTagOfAdj_junction_longSeg_end, genericDecompEdgeOfTag]
  rw [longEndEndpointInv_spec e hend]
  simp [longEndEndpoint, hj, NoncrossingPathDecompAssumptions.longArcLen]

/-
theorem genericDecompEdgeTagOfAdj_junction_bridge_spec (shape : GenericDecompTreeShape g hyp)
    {e e' : Fin 4} (hbr : hyp.genericJunctionBridge e e') :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj_junction_bridge e e' hbr) =
      s(.junction e, .junction e') := by
  dsimp [genericDecompEdgeTagOfAdj_junction_bridge, genericDecompEdgeOfTag]
  fin_cases e <;> fin_cases e' <;>
    first
    | (simp [genericDecompEdgeOfTag]; split_ifs <;> simp [genericDecompEdgeOfTag] <;>
        exact (Sym2.eq_iff).2 (Or.inl ⟨rfl, rfl⟩))
    | (simp [genericDecompEdgeOfTag]; exact (Sym2.eq_iff).2 (Or.inl ⟨rfl, rfl⟩))
-/

theorem genericDecompEdgeOfTag_tagOfEdge (shape : GenericDecompTreeShape g hyp)
    (e : (genericDecompGraph g hyp).edgeSet) :
    genericDecompEdgeOfTag shape (genericDecompEdgeTagOfEdge shape e) = e.val := by
  classical
  dsimp [genericDecompEdgeTagOfEdge]
  have heq := genericDecompSym2Unpair_spec e.val
  have hadj : genericDecompAdj g hyp (genericDecompSym2Unpair e.val).1
      (genericDecompSym2Unpair e.val).2 :=
    (SimpleGraph.mem_edgeSet _).1 (heq ▸ e.property)
  have hmain :
      genericDecompEdgeOfTag shape
          (genericDecompEdgeTagOfAdj (genericDecompSym2Unpair e.val).1
            (genericDecompSym2Unpair e.val).2 hadj) =
        s((genericDecompSym2Unpair e.val).1, (genericDecompSym2Unpair e.val).2) := by
    suffices ∀ (u v : GenericDecompNode g hyp.arcIdx) (adj : genericDecompAdj g hyp u v),
        genericDecompEdgeOfTag shape (genericDecompEdgeTagOfAdj u v adj) = s(u, v) by
      exact this _ _ hadj
    intro u v adj
    match u, v with
    | .longSeg j, .longSeg j' =>
      by_cases hcond : j.val + 1 = j'.val
      · rw [genericDecompEdgeTagOfAdj_longSeg_of_succ adj hcond]
        exact genericDecompEdgeTagOfAdj_longSeg_succ_spec shape adj hcond
      · rw [genericDecompEdgeTagOfAdj_longSeg_of_pred adj hcond]
        exact genericDecompEdgeTagOfAdj_longSeg_pred_spec shape adj hcond
    | .longSeg j, .junction eJ =>
      by_cases hstart : longArcStartJunctions eJ
      · rw [genericDecompEdgeTagOfAdj_longSeg_junction_of_start adj hstart]
        exact genericDecompEdgeTagOfAdj_longSeg_junction_start_spec shape adj hstart
      · rw [genericDecompEdgeTagOfAdj_longSeg_junction_of_end adj hstart]
        exact genericDecompEdgeTagOfAdj_longSeg_junction_end_spec shape adj hstart
    | .shortSeg a hne j, .junction eJ =>
      exact genericDecompEdgeTagOfAdj_shortSeg_junction_spec shape adj
    | .shortSeg a hne j, .shortSeg a' hne' j' =>
      by_cases hcond : j.val + 1 = j'.val
      · rw [genericDecompEdgeTagOfAdj_shortSeg_of_succ adj hcond]
        exact genericDecompEdgeTagOfAdj_shortSeg_succ_spec shape adj hcond
      · rw [genericDecompEdgeTagOfAdj_shortSeg_of_pred adj hcond]
        exact genericDecompEdgeTagOfAdj_shortSeg_pred_spec shape adj hcond
    | .junction eJ, .longSeg j =>
      by_cases hstart : longArcStartJunctions eJ
      · rw [genericDecompEdgeTagOfAdj_junction_longSeg_of_start adj hstart]
        exact genericDecompEdgeTagOfAdj_junction_longSeg_start_spec shape adj hstart
      · rw [genericDecompEdgeTagOfAdj_junction_longSeg_of_end adj hstart]
        exact genericDecompEdgeTagOfAdj_junction_longSeg_end_spec shape adj hstart
    | .junction eJ, .shortSeg a hne j =>
      exact genericDecompEdgeTagOfAdj_junction_shortSeg_spec shape adj
    | .junction _, .junction _ =>
      exfalso; simp [genericDecompAdj] at adj
    | .longSeg _, .shortSeg _ _ _ | .longSeg _, .hub _
    | .shortSeg _ _ _, .longSeg _ | .shortSeg _ _ _, .hub _
    | .junction _, .hub _
    | .hub _, _ =>
      exfalso; simp [genericDecompAdj] at adj
  exact hmain.trans heq.symm

noncomputable def genericDecompEdgeFinIndex (shape : GenericDecompTreeShape g hyp)
    (e : (genericDecompGraph g hyp).edgeSet) : Fin (genericDecompEdgeCount g hyp) :=
  ⟨genericDecompEdgeTagIndex (genericDecompEdgeTagOfEdge shape e),
    genericDecompEdgeTagIndex_lt shape _⟩

theorem genericDecompEdgeFinIndex_injective (shape : GenericDecompTreeShape g hyp) :
    Function.Injective (genericDecompEdgeFinIndex shape) := by
  intro e1 e2 h
  apply Subtype.ext
  simp [genericDecompEdgeFinIndex] at h
  have htag :
      genericDecompEdgeTagOfEdge shape e1 = genericDecompEdgeTagOfEdge shape e2 := by
    apply genericDecompEdgeTagIndex_injective shape
    exact h
  calc e1.val
      _ = genericDecompEdgeOfTag shape (genericDecompEdgeTagOfEdge shape e1) :=
        (genericDecompEdgeOfTag_tagOfEdge shape e1).symm
      _ = genericDecompEdgeOfTag shape (genericDecompEdgeTagOfEdge shape e2) := by rw [htag]
      _ = e2.val := genericDecompEdgeOfTag_tagOfEdge shape e2

theorem genericDecomp_card_edgeSet_le_edgeCount (shape : GenericDecompTreeShape g hyp) :
    Nat.card (genericDecompGraph g hyp).edgeSet ≤ genericDecompEdgeCount g hyp := by
  classical
  have hle := Fintype.card_le_of_injective (genericDecompEdgeFinIndex shape)
    (genericDecompEdgeFinIndex_injective shape)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at hle
  simpa [SimpleGraph.card_edgeSet] using hle

end EdgeTag

/-- Combinatorial node/edge counts (`edgeCard` OPEN — Fin↔edgeSet bijection in progress). -/
structure GenericDecompCombinatorialCard (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  nodeCard : Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp
  edgeCard : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp

/-!
  OPEN (`edgeCard` / `isTree`): two ALT routes to close `GenericDecompOpenGoals.isTree` without
  the blocked Fin↔`edgeSet` bijection (`genericDecompIndexOfEdgeAux_swap`, `Sym2.recOn`).

  **Route A (acyclic):** prove `genericDecompGraph_isAcyclic_of_shape`, then
  `GenericDecompOpenGoals.isTree_of_shape_and_acyclic` (connected already PROVED).
  Planned proof: fold `⊔ edge` in reachability order (`IsAcyclic.sup_edge_of_not_reachable`).

  **Route B (card upper bound):** `genericDecompEdgeOfTag_tagOfEdge` PROVED via `by_cases`
  helper defs in `genericDecompEdgeTagOfAdj`; `Nat.card edgeSet ≤ genericDecompEdgeCount` via
  `genericDecompEdgeFinIndex_injective`; combine with lower bound in
  `genericDecompGraph_isTree_of_shape_and_edgeCount_upper`.

  Fin↔`edgeSet` bijection remains optional (not required once either route closes).
-/
theorem genericDecompCombinatorialCard_nodeCard (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) :
    Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp :=
  genericDecompNodeCount_eq_card g hyp

theorem genericDecompGraph_isTree_of_combinatorialCard
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp) (card : GenericDecompCombinatorialCard g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape_and_combinatorial_card g hyp shape card.edgeCard card.nodeCard

/-- Connected + `nodeCard` forces `|E| ≥ genericDecompEdgeCount` (no edge lower-bound construction needed). -/
theorem genericDecompEdgeCount_le_card_edgeSet
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (shape : GenericDecompTreeShape g hyp) :
    genericDecompEdgeCount g hyp ≤ Nat.card (genericDecompGraph g hyp).edgeSet := by
  have hle := (genericDecompGraph_connected_of_shape shape).card_vert_le_card_edgeSet_add_one
  have hnodes := genericDecompNodeCount_eq_card g hyp
  have hbal := genericDecomp_card_balance g hyp
  omega

/-- Upper bound on `|E|` (tag classification) + shape closes `IsTree` without Fin↔edgeSet bijection. -/
theorem genericDecompGraph_isTree_of_shape_and_edgeCount_upper
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (shape : GenericDecompTreeShape g hyp)
    (hupper : Nat.card (genericDecompGraph g hyp).edgeSet ≤ genericDecompEdgeCount g hyp) :
    (genericDecompGraph g hyp).IsTree := by
  have hlower := genericDecompEdgeCount_le_card_edgeSet shape
  have hedges : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp := by omega
  exact genericDecompGraph_isTree_of_shape_and_combinatorial_card g hyp shape hedges
    (genericDecompNodeCount_eq_card g hyp)

theorem genericDecompGraph_isTree_of_shape_cardUpper (shape : GenericDecompTreeShape g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape_and_edgeCount_upper shape <|
    genericDecomp_card_edgeSet_le_edgeCount shape

/-!
  ## Bag assignment (image of existing Fin-indexed families)
  -/

noncomputable def genericBagFamily (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (node : GenericDecompNode g hyp.arcIdx) : Finset g.toSimpleGraph.edgeSet :=
  match node with
  | .longSeg j => hyp.longArcLineGraphBag j ∪ hyp.genericLongSegBagExtension j
  | .shortSeg a _ j => hyp.shortArcLineGraphBag a j
  | .junction e => hyp.enrichedJunctionBag e ∪ hyp.genericJunctionBagExtension e \ hyp.genericJunctionBagTrim e
  | .hub _ => ∅

theorem genericBagFamily_longSeg (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) :
    genericBagFamily g hyp (.longSeg j) = hyp.longArcLineGraphBag j ∪ hyp.genericLongSegBagExtension j :=
  rfl

theorem genericBagFamily_shortSeg (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠  hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    genericBagFamily g hyp (.shortSeg a hne j) = hyp.shortArcLineGraphBag a j :=
  rfl

theorem genericBagFamily_longSeg_mem_of_line (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Fin hyp.longArcLen)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcLineGraphBag j) :
    e ∈ genericBagFamily g hyp (.longSeg j) := by
  rw [genericBagFamily_longSeg]
  exact Finset.mem_union_left _ he

theorem genericBagFamily_junction (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : Fin 4) :
    genericBagFamily g hyp (.junction e) =
      hyp.enrichedJunctionBag e ∪ hyp.genericJunctionBagExtension e \ hyp.genericJunctionBagTrim e :=
  rfl

theorem genericBagFamily_junction_mem_of_enrichedUntrimmed (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet}
    (he : e ∈ hyp.enrichedJunctionBag endpoint \ hyp.genericJunctionBagTrim endpoint) :
    e ∈ genericBagFamily g hyp (.junction endpoint) := by
  rw [genericBagFamily_junction]
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1

theorem genericBagFamily_junction_mem_of_enriched (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.enrichedJunctionBag endpoint) :
    e ∈ genericBagFamily g hyp (.junction endpoint) := by
  rw [genericBagFamily_junction]
  exact Finset.mem_union_left _ he

/-!
  ## Segment graph homs (preconnected on long-arc intervals)
-/

def longSegNode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) (j : Fin hyp.longArcLen) :
    GenericDecompNode g hyp.arcIdx :=
  @GenericDecompNode.longSeg g hyp.arcIdx (Fin.cast (longArcLen_eq g hyp).symm j)

theorem genericBagFamily_longSegNode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) :
    genericBagFamily g hyp (longSegNode g hyp j) =
      hyp.longArcLineGraphBag j ∪ hyp.genericLongSegBagExtension j := by
  simp [longSegNode, genericBagFamily_longSeg, longArcLen_eq]

lemma Preconnected.induce_map_image {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    {f : G →g G'} (_hf : Function.Injective f) {s : Set V} {t : Set W} (hst : t = f '' s)
    (h : (G.induce s).Preconnected) : (G'.induce t).Preconnected := by
  have hmapsto : Set.MapsTo f s t := fun _ hv => hst ▸ Set.mem_image_of_mem f hv
  refine Preconnected.map (SimpleGraph.induceHom f hmapsto) (fun w => ?_) h
  have hw : w.val ∈ t := w.2
  obtain ⟨v, hv, heq⟩ := by simpa [hst, Set.mem_image] using hw
  exact ⟨⟨v, hv⟩, Subtype.ext heq⟩

def longSegHom (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    certPathGraph hyp.longArcLen →g genericDecompGraph g hyp where
  toFun := longSegNode g hyp
  map_rel' {i j} h := by
    dsimp [longSegNode]
    exact (longSeg_adj_iff g hyp i j).mpr h

theorem longSegHom_injective (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Function.Injective (longSegHom g hyp) := by
  intro i j h
  dsimp [longSegHom, longSegNode] at h
  injection h

def genericLongSegNodeSet (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Set (GenericDecompNode g hyp.arcIdx) :=
  Set.range (longSegNode g hyp)

theorem genericLongSeg_preconnected_of_interval (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (e : g.toSimpleGraph.edgeSet) (a b : Nat)
    (ha : a < hyp.longArcLen) (hb : b < hyp.longArcLen) (hab : a ≤ b)
    (hset : {j : Fin hyp.longArcLen | e ∈ hyp.longArcSegmentBag j} =
      certPathGraphInterval hyp.longArcLen a b) :
    (genericDecompGraph g hyp).induce
        ({w | e ∈ genericBagFamily g hyp w} ∩ genericLongSegNodeSet g hyp) |>.Preconnected := by
  have hpre := hyp.longArcSegment_preconnected_of_interval e a b ha hb hab hset
  let s : Set (Fin hyp.longArcLen) := {j | e ∈ hyp.longArcSegmentBag j}
  have hs : s = certPathGraphInterval hyp.longArcLen a b := hset
  have hcert : (certPathGraph hyp.longArcLen).induce s |>.Preconnected := by
    simpa [NoncrossingPathDecompAssumptions.longArcCertPathGraph, hs] using hpre
  have hst :
      {w | e ∈ genericBagFamily g hyp w} ∩ genericLongSegNodeSet g hyp =
        (longSegHom g hyp).toFun '' s := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, genericLongSegNodeSet, Set.mem_image,
      longSegHom, s]
    constructor
    · intro ⟨he, ⟨j, hj⟩⟩
      subst hj
      rw [genericBagFamily_longSegNode, hyp.genericLongSegBagExtension_empty j, Finset.union_empty] at he
      exact ⟨j, by dsimp [NoncrossingPathDecompAssumptions.longArcSegmentBag]; exact he, rfl⟩
    · intro ⟨j, hj, hw⟩
      subst hw
      refine ⟨?_, Set.mem_range_self j⟩
      rw [genericBagFamily_longSegNode, hyp.genericLongSegBagExtension_empty j, Finset.union_empty]
      dsimp [NoncrossingPathDecompAssumptions.longArcSegmentBag] at hj
      exact hj
  exact Preconnected.induce_map_image (f := longSegHom g hyp) (longSegHom_injective g hyp) hst hcert

def shortSegNode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    GenericDecompNode g hyp.arcIdx :=
  .shortSeg a hne j

theorem genericBagFamily_shortSegNode (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    genericBagFamily g hyp (shortSegNode g hyp a hne j) = hyp.shortArcLineGraphBag a j := by
  simp [shortSegNode, genericBagFamily_shortSeg]

def shortSegHom (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) :
    certPathGraph (g.cyclicGap a) →g genericDecompGraph g hyp where
  toFun := shortSegNode g hyp a hne
  map_rel' {i j} h := (shortSeg_adj_iff g hyp a hne i j).mpr h

theorem shortSegHom_injective (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) :
    Function.Injective (shortSegHom g hyp a hne) := by
  intro i j h
  dsimp [shortSegHom, shortSegNode] at h
  injection h

def genericShortSegNodeSet (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) :
    Set (GenericDecompNode g hyp.arcIdx) :=
  Set.range (shortSegNode g hyp a hne)

theorem genericShortSeg_preconnected_of_interval (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx)
    (e : g.toSimpleGraph.edgeSet) (a b : Nat)
    (ha : a < g.cyclicGap shortArc) (hb : b < g.cyclicGap shortArc) (hab : a ≤ b)
    (hset : {j : Fin (g.cyclicGap shortArc) | e ∈ hyp.shortArcLineGraphBag shortArc j} =
      certPathGraphInterval (g.cyclicGap shortArc) a b) :
    (genericDecompGraph g hyp).induce
        ({w | e ∈ genericBagFamily g hyp w} ∩ genericShortSegNodeSet g hyp shortArc hne) |>.Preconnected := by
  let s : Set (Fin (g.cyclicGap shortArc)) := {j | e ∈ hyp.shortArcLineGraphBag shortArc j}
  have hs : s = certPathGraphInterval (g.cyclicGap shortArc) a b := hset
  have hcert : (certPathGraph (g.cyclicGap shortArc)).induce s |>.Preconnected := by
    rw [hs]
    exact certPathGraph_induce_interval_preconnected (g.cyclicGap shortArc) a b ha hb hab
  have hst :
      {w | e ∈ genericBagFamily g hyp w} ∩ genericShortSegNodeSet g hyp shortArc hne =
        (shortSegHom g hyp shortArc hne).toFun '' s := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, genericShortSegNodeSet, Set.mem_image,
      shortSegHom, shortSegNode, s]
    constructor
    · intro ⟨he, hj⟩
      obtain ⟨j, rfl⟩ := hj
      rw [genericBagFamily_shortSegNode] at he
      exact ⟨j, he, rfl⟩
    · intro ⟨j, hj, hw⟩
      subst hw
      have hbag : e ∈ genericBagFamily g hyp (shortSegNode g hyp shortArc hne j) := by
        rw [genericBagFamily_shortSegNode]
        exact hj
      exact ⟨hbag, Set.mem_range_self j⟩
  exact Preconnected.induce_map_image (f := shortSegHom g hyp shortArc hne)
    (shortSegHom_injective g hyp shortArc hne) hst hcert

/-!
  ## Cover fragments (long-arc consecutive + same-bag; mixed cases OPEN)
-/

theorem genericLongSeg_edgeCover_sameBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) (e₁ e₂ : g.toSimpleGraph.edgeSet)
    (h1 : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (h2 : e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  ⟨.longSeg j, h1, h2⟩

private theorem genericLongSeg_slidingBag_mem_arcEdge (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Nat) (hj : j < hyp.longArcLen) :
    hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
          exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj)) ∈
      hyp.longArcLineGraphBag ⟨j, hj⟩ := by
  dsimp [NoncrossingPathDecompAssumptions.longArcLineGraphBag, CycleTwoChordGraph.longArcBagFamily]
  refine Finset.mem_image.mpr ⟨g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
    exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj), ?_, rfl⟩
  dsimp [CycleTwoChordGraph.longArcSlidingBag]
  simp [Finset.mem_union, Finset.mem_insert, Option.mem_toFinset]

theorem genericLongSeg_vertexCover_arcEdge (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Nat) (hj : j < hyp.longArcLen) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
            exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj)) ∈
        genericBagFamily g hyp w :=
  ⟨.longSeg ⟨j, hj⟩, by
    rw [genericBagFamily_longSeg]
    exact Finset.mem_union_left _ (genericLongSeg_slidingBag_mem_arcEdge g hyp j hj)⟩

theorem genericLongSeg_edgeCover_arcConsecutive (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Nat) (hj : j < hyp.longArcLen)
    (hj' : j + 1 < hyp.longArcLen) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
            exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj)) ∈
        genericBagFamily g hyp w ∧
        hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j + 1) (by
            exact g.arcEdgeOffset_add_lt hyp.arcIdx (j + 1) hj')) ∈
          genericBagFamily g hyp w := by
  refine ⟨.longSeg ⟨j, hj⟩, ?_, ?_⟩
  · rw [genericBagFamily_longSeg]
    exact Finset.mem_union_left _ (hyp.arcEdgeCoverConsecutive j hj hj').1
  · rw [genericBagFamily_longSeg]
    exact Finset.mem_union_left _ (hyp.arcEdgeCoverConsecutive j hj hj').2

theorem genericLongSeg_lineGraphAdj_arcConsecutive (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Nat) (hj : j < hyp.longArcLen)
    (hj' : j + 1 < hyp.longArcLen) :
    (lineGraph g.toSimpleGraph).Adj
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
          exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj)))
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j + 1) (by
          exact g.arcEdgeOffset_add_lt hyp.arcIdx (j + 1) hj'))) :=
  GraphEdgeBijection.arcConsecutive_lineGraphAdj g hyp.edgeBij hyp.arcIdx j hj hj'

theorem genericLongSeg_lineGraphAdj_consecutive_edgeCover (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (j : Nat) (hj : j < hyp.longArcLen)
    (hj' : j + 1 < hyp.longArcLen) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
            exact g.arcEdgeOffset_add_lt hyp.arcIdx j hj)) ∈
        genericBagFamily g hyp w ∧
        hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j + 1) (by
            exact g.arcEdgeOffset_add_lt hyp.arcIdx (j + 1) hj')) ∈
          genericBagFamily g hyp w :=
  genericLongSeg_edgeCover_arcConsecutive g hyp j hj hj'

/-- Same long-seg bag index already covers both edges (no line-graph hypothesis needed). -/
theorem genericLongSeg_edgeCover_sameBagIndex (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hj :
      ∃ j : Fin hyp.longArcLen,
        e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧ e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ j : Fin hyp.longArcLen,
      e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧ e₂ ∈ genericBagFamily g hyp (.longSeg j) :=
  hj

/-- If both edges lie in long-seg bags at the same index, line-graph adjacency is irrelevant. -/
theorem genericLongSeg_edgeCover_of_commonBagIndex (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (_hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj :
      ∃ j : Fin hyp.longArcLen,
        e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧ e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ j : Fin hyp.longArcLen,
      e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧ e₂ ∈ genericBagFamily g hyp (.longSeg j) :=
  genericLongSeg_edgeCover_sameBagIndex g hyp hj

theorem genericShortSeg_edgeCover_sameBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Fin (g.cyclicGap a))
    (e₁ e₂ : g.toSimpleGraph.edgeSet)
    (h1 : e₁ ∈ genericBagFamily g hyp (.shortSeg a hne j))
    (h2 : e₂ ∈ genericBagFamily g hyp (.shortSeg a hne j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  ⟨.shortSeg a hne j, h1, h2⟩

theorem genericShortSeg_edgeCover_arcConsecutive (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Nat)
    (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j) (by
            exact g.arcEdgeOffset_add_lt a j hj)) ∈
        genericBagFamily g hyp w ∧
        hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j + 1) (by
            exact g.arcEdgeOffset_add_lt a (j + 1) hj')) ∈
          genericBagFamily g hyp w := by
  refine ⟨.shortSeg a hne ⟨j, hj⟩, ?_, ?_⟩
  · rw [genericBagFamily_shortSeg]
    exact (hyp.shortArcEdgeCoverConsecutive a hne j hj hj').1
  · rw [genericBagFamily_shortSeg]
    exact (hyp.shortArcEdgeCoverConsecutive a hne j hj hj').2

theorem genericShortSeg_lineGraphAdj_arcConsecutive (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (_hne : a ≠ hyp.arcIdx) (j : Nat)
    (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    (lineGraph g.toSimpleGraph).Adj
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j) (by
          exact g.arcEdgeOffset_add_lt a j hj)))
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j + 1) (by
          exact g.arcEdgeOffset_add_lt a (j + 1) hj'))) :=
  GraphEdgeBijection.arcConsecutive_lineGraphAdj g hyp.edgeBij a j hj hj'

theorem genericShortSeg_lineGraphAdj_consecutive_edgeCover (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (hne : a ≠ hyp.arcIdx) (j : Nat)
    (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j) (by
            exact g.arcEdgeOffset_add_lt a j hj)) ∈
        genericBagFamily g hyp w ∧
        hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + j + 1) (by
            exact g.arcEdgeOffset_add_lt a (j + 1) hj')) ∈
          genericBagFamily g hyp w :=
  genericShortSeg_edgeCover_arcConsecutive g hyp a hne j hj hj'

/-- Step-0 sliding bag covers consecutive arc edges (mirror `longArcSlidingBag_covers_arc_consecutive`). -/
theorem genericShortSeg_edgeCover_arcConsecutive_zero (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (hne : a ≠ hyp.arcIdx)
    (hgap : 1 < g.cyclicGap a) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a) (by
            exact g.arcEdgeOffset_add_lt a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)))) ∈
        genericBagFamily g hyp w ∧
        hyp.edgeBij.edgeEquiv
          (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + 1) (by
            exact g.arcEdgeOffset_add_lt a 1 hgap)) ∈
          genericBagFamily g hyp w := by
  have hj := Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)
  refine ⟨.shortSeg a hne ⟨0, hj⟩, ?_, ?_⟩
  · rw [genericBagFamily_shortSeg]
    exact (hyp.shortArcEdgeCoverConsecutive_zero a hne hgap).1
  · rw [genericBagFamily_shortSeg]
    exact (hyp.shortArcEdgeCoverConsecutive_zero a hne hgap).2

theorem genericShortSeg_lineGraphAdj_arcConsecutive_zero (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (_hne : a ≠ hyp.arcIdx)
    (hgap : 1 < g.cyclicGap a) :
    (lineGraph g.toSimpleGraph).Adj
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a) (by
          exact g.arcEdgeOffset_add_lt a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)))))
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + 1) (by
          exact g.arcEdgeOffset_add_lt a 1 hgap))) :=
  have hj := Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)
  genericShortSeg_lineGraphAdj_arcConsecutive g hyp a _hne 0 hj hgap

theorem genericShortSeg_slidingBag_zero_adj_junction (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (a : Fin 4) (hne : a ≠ hyp.arcIdx)
    (hgap : 1 < g.cyclicGap a) :
    (lineGraph g.toSimpleGraph).Adj
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a) (by
          exact g.arcEdgeOffset_add_lt a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)))))
      (hyp.edgeBij.edgeEquiv
        (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + 1) (by
          exact g.arcEdgeOffset_add_lt a 1 hgap))) ∧
      ∃ w : GenericDecompNode g hyp.arcIdx,
        hyp.edgeBij.edgeEquiv
            (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a) (by
              exact g.arcEdgeOffset_add_lt a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)))) ∈
          genericBagFamily g hyp w ∧
          hyp.edgeBij.edgeEquiv
            (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + 1) (by
              exact g.arcEdgeOffset_add_lt a 1 hgap)) ∈
            genericBagFamily g hyp w :=
  ⟨genericShortSeg_lineGraphAdj_arcConsecutive_zero g hyp a hne hgap,
    genericShortSeg_edgeCover_arcConsecutive_zero g hyp a hne hgap⟩

theorem genericBagFamily_longSeg_width (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) :
    (genericBagFamily g hyp (longSegNode g hyp j)).card - 1 ≤ 3 := by
  rw [genericBagFamily_longSegNode, hyp.genericLongSegBagExtension_empty j, Finset.union_empty]
  have h := g.longArcBag_width_le_three hyp.arcIdx j
  have hcard := hyp.cardSegmentBagEq j
  dsimp [NoncrossingPathDecompAssumptions.longArcSegmentBag] at hcard
  rw [hcard]
  exact h

theorem genericBagFamily_shortSeg_width (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (a : Fin 4) (hne : a ≠  hyp.arcIdx) (j : Fin (g.cyclicGap a)) :
    (genericBagFamily g hyp (.shortSeg a hne j)).card - 1 ≤ 3 := by
  rw [genericBagFamily_shortSeg]
  have hcard := Finset.card_image_of_injective (g.shortArcBagFamily a j)
    hyp.edgeBij.edgeEquiv.injective
  dsimp [NoncrossingPathDecompAssumptions.shortArcLineGraphBag]
  rw [hcard]
  exact g.shortArcBag_width_le_three a j

theorem genericBagFamily_junction_width (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : Fin 4) :
    (genericBagFamily g hyp (.junction e)).card - 1 ≤ 3 := by
  rw [genericBagFamily_junction]
  simp only [hyp.genericJunctionBagExtension_empty e, hyp.genericJunctionBagTrim_empty e,
    Finset.union_empty, Finset.sdiff_empty]
  exact NoncrossingPathDecompAssumptions.widthThreeEnrichedBag hyp e

noncomputable def genericBagSupWidth (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) : Nat :=
  max
    ((Finset.univ : Finset (Fin hyp.longArcLen)).sup
      fun j => (genericBagFamily g hyp (.longSeg j)).card - 1)
    (max
      ((Finset.univ : Finset (Fin 4)).sup fun a =>
        if hne : a ≠  hyp.arcIdx then
          (Finset.univ : Finset (Fin (g.cyclicGap a))).sup fun j =>
            (genericBagFamily g hyp (.shortSeg a hne j)).card - 1
        else 0)
      ((Finset.univ : Finset (Fin 4)).sup fun e =>
        (genericBagFamily g hyp (.junction e)).card - 1))

theorem genericBagSupWidth_le_three (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    genericBagSupWidth g hyp ≤ 3 := by
  dsimp [genericBagSupWidth]
  refine max_le ?_ (max_le ?_ ?_)
  · exact Finset.sup_le fun j _ => genericBagFamily_longSeg_width g hyp j
  · refine Finset.sup_le fun a _ => ?_
    by_cases hne : a ≠  hyp.arcIdx
    · simp only [hne, ↓reduceIte]
      exact Finset.sup_le fun j _ => genericBagFamily_shortSeg_width g hyp a hne j
    · simp only [hne, ↓reduceIte]
      exact Nat.zero_le 3
  · exact Finset.sup_le fun e _ => genericBagFamily_junction_width g hyp e

theorem genericBagFamily_width_le_sup (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (w : GenericDecompNode g hyp.arcIdx) :
    (genericBagFamily g hyp w).card - 1 ≤ genericBagSupWidth g hyp := by
  cases w with
  | longSeg j =>
    dsimp [genericBagSupWidth]
    exact le_max_of_le_left (Finset.le_sup (f := fun j =>
      (genericBagFamily g hyp (.longSeg j)).card - 1) (show j ∈ Finset.univ by simp))
  | shortSeg a hne j =>
    dsimp only [genericBagSupWidth]
    refine le_max_of_le_right (le_max_of_le_left ?_)
    have hj := Finset.le_sup (f := fun j =>
      (genericBagFamily g hyp (.shortSeg a hne j)).card - 1) (Finset.mem_univ j)
    have ha := Finset.le_sup (f := fun a =>
      if hne' : a ≠  hyp.arcIdx then
        (Finset.univ : Finset (Fin (g.cyclicGap a))).sup fun j =>
          (genericBagFamily g hyp (.shortSeg a hne' j)).card - 1
      else 0) (Finset.mem_univ a)
    rw [dif_pos hne] at ha
    exact le_trans hj ha
  | junction e =>
    dsimp [genericBagSupWidth]
    refine le_max_of_le_right (le_max_of_le_right ?_)
    exact Finset.le_sup (f := fun e => (genericBagFamily g hyp (.junction e)).card - 1)
      (show e ∈ Finset.univ by simp)
  | hub kind => cases kind

/-!
  ## Open goals bundle + conditional generic certificate
  -/

structure GenericDecompOpenGoals (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w
  preconnected :
    ∀ e : g.toSimpleGraph.edgeSet,
      ((genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected)
  isTree : (genericDecompGraph g hyp).IsTree

/-- Cover fragments expected from `NoncrossingPathDecomp` bag lemmas (discharge remains OPEN). -/
structure GenericDecompCoverAssumptions (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  junction_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ endpoint : Fin 4,
          e₁ ∈ genericBagFamily g hyp (.junction endpoint) ∧
            e₂ ∈ genericBagFamily g hyp (.junction endpoint)
  shortArc_edgeCover :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠  hyp.arcIdx),
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        (∃ j : Fin (g.cyclicGap shortArc), e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
        (∃ j : Fin (g.cyclicGap shortArc), e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
          ∃ j : Fin (g.cyclicGap shortArc),
            e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j) ∧
              e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)
  longArc_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
      (∃ j : Fin hyp.longArcLen, e₁ ∈ genericBagFamily g hyp (.longSeg j)) →
      (∃ j : Fin hyp.longArcLen, e₂ ∈ genericBagFamily g hyp (.longSeg j)) →
        ∃ j : Fin hyp.longArcLen,
          e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧
            e₂ ∈ genericBagFamily g hyp (.longSeg j)
  longArc_vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet,
      (∃ j : Fin hyp.longArcLen, e ∈ genericBagFamily g hyp (.longSeg j)) →
        ∃ j : Fin hyp.longArcLen, e ∈ genericBagFamily g hyp (.longSeg j)
  shortArc_vertexCover :
    ∀ (a : Fin 4) (hne : a ≠  hyp.arcIdx) (e : g.toSimpleGraph.edgeSet),
      (∃ j : Fin (g.cyclicGap a), e ∈ genericBagFamily g hyp (.shortSeg a hne j)) →
        ∃ j : Fin (g.cyclicGap a), e ∈ genericBagFamily g hyp (.shortSeg a hne j)
  junction_vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet,
      (∃ endpoint : Fin 4, e ∈ genericBagFamily g hyp (.junction endpoint)) →
        ∃ endpoint : Fin 4, e ∈ genericBagFamily g hyp (.junction endpoint)

theorem GenericDecompOpenGoals.isTree_of_shape_and_combinatorial_card
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp)
    (hedges : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp)
    (hnodes : Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape_and_combinatorial_card g hyp shape hedges hnodes

theorem GenericDecompOpenGoals.isTree_of_shape_and_nodeCard
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp)
    (hedges : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp)
    (hnodes : Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  GenericDecompOpenGoals.isTree_of_shape_and_combinatorial_card shape hedges hnodes

theorem GenericDecompOpenGoals.isTree_of_combinatorialCard
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (shape : GenericDecompTreeShape g hyp) (card : GenericDecompCombinatorialCard g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_combinatorialCard g hyp shape card

theorem GenericDecompOpenGoals.isTree_of_shape_and_acyclic
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (shape : GenericDecompTreeShape g hyp)
    (hacyc : (genericDecompGraph g hyp).IsAcyclic) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape shape hacyc

theorem GenericDecompOpenGoals.isTree_of_shape_and_edgeCount_upper
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (shape : GenericDecompTreeShape g hyp)
    (hupper : Nat.card (genericDecompGraph g hyp).edgeSet ≤ genericDecompEdgeCount g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape_and_edgeCount_upper shape hupper

theorem GenericDecompOpenGoals.isTree_of_shape
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (shape : GenericDecompTreeShape g hyp) :
    (genericDecompGraph g hyp).IsTree :=
  genericDecompGraph_isTree_of_shape_cardUpper shape

theorem GenericDecompOpenGoals.of_cover_shape
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (_cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (edgeCover : ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (vertexCover : ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w)
    (preconnected :
      ∀ e : g.toSimpleGraph.edgeSet,
        (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected) :
    GenericDecompOpenGoals g hyp where
  edgeCover := edgeCover
  vertexCover := vertexCover
  preconnected := preconnected
  isTree := GenericDecompOpenGoals.isTree_of_shape shape

theorem GenericDecompOpenGoals.of_cover_shape_and_acyclic
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (_cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (hacyc : (genericDecompGraph g hyp).IsAcyclic)
    (edgeCover : ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (vertexCover : ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w)
    (preconnected :
      ∀ e : g.toSimpleGraph.edgeSet,
        (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected) :
    GenericDecompOpenGoals g hyp where
  edgeCover := edgeCover
  vertexCover := vertexCover
  preconnected := preconnected
  isTree := GenericDecompOpenGoals.isTree_of_shape_and_acyclic shape hacyc

theorem GenericDecompOpenGoals.junction_edgeCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ endpoint : Fin 4,
          e₁ ∈ genericBagFamily g hyp (.junction endpoint) ∧
            e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
  cover.junction_edgeCover

theorem GenericDecompOpenGoals.shortArc_edgeCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠  hyp.arcIdx),
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        (∃ j : Fin (g.cyclicGap shortArc), e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
        (∃ j : Fin (g.cyclicGap shortArc), e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
          ∃ j : Fin (g.cyclicGap shortArc),
            e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j) ∧
              e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j) :=
  cover.shortArc_edgeCover

theorem GenericDecompOpenGoals.longArc_edgeCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
      (∃ j : Fin hyp.longArcLen, e₁ ∈ genericBagFamily g hyp (.longSeg j)) →
      (∃ j : Fin hyp.longArcLen, e₂ ∈ genericBagFamily g hyp (.longSeg j)) →
        ∃ j : Fin hyp.longArcLen,
          e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧
            e₂ ∈ genericBagFamily g hyp (.longSeg j) :=
  cover.longArc_edgeCover

theorem GenericDecompOpenGoals.longArc_vertexCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ e : g.toSimpleGraph.edgeSet,
      (∃ j : Fin hyp.longArcLen, e ∈ genericBagFamily g hyp (.longSeg j)) →
        ∃ j : Fin hyp.longArcLen, e ∈ genericBagFamily g hyp (.longSeg j) :=
  cover.longArc_vertexCover

theorem GenericDecompOpenGoals.shortArc_vertexCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ (a : Fin 4) (hne : a ≠  hyp.arcIdx) (e : g.toSimpleGraph.edgeSet),
      (∃ j : Fin (g.cyclicGap a), e ∈ genericBagFamily g hyp (.shortSeg a hne j)) →
        ∃ j : Fin (g.cyclicGap a), e ∈ genericBagFamily g hyp (.shortSeg a hne j) :=
  cover.shortArc_vertexCover

theorem GenericDecompOpenGoals.junction_vertexCover_of_cover
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp) :
    ∀ e : g.toSimpleGraph.edgeSet,
      (∃ endpoint : Fin 4, e ∈ genericBagFamily g hyp (.junction endpoint)) →
        ∃ endpoint : Fin 4, e ∈ genericBagFamily g hyp (.junction endpoint) :=
  cover.junction_vertexCover

theorem GenericDecompOpenGoals.of_cover_shape_nodeCard
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (_cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (hedges : Nat.card (genericDecompGraph g hyp).edgeSet = genericDecompEdgeCount g hyp)
    (hnodes : Nat.card (GenericDecompNode g hyp.arcIdx) = genericDecompNodeCount g hyp)
    (edgeCover : ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (vertexCover : ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w)
    (preconnected :
      ∀ e : g.toSimpleGraph.edgeSet,
        (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected) :
    GenericDecompOpenGoals g hyp where
  edgeCover := edgeCover
  vertexCover := vertexCover
  preconnected := preconnected
  isTree := GenericDecompOpenGoals.isTree_of_shape_and_nodeCard shape hedges hnodes

theorem GenericDecompOpenGoals.of_cover_shape_and_combinatorialCard
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    [Finite (GenericDecompNode g hyp.arcIdx)]
    (cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (card : GenericDecompCombinatorialCard g hyp)
    (edgeCover : ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (vertexCover : ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w)
    (preconnected :
      ∀ e : g.toSimpleGraph.edgeSet,
        (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected) :
    GenericDecompOpenGoals g hyp :=
  GenericDecompOpenGoals.of_cover_shape_nodeCard cover shape card.edgeCard card.nodeCard
    edgeCover vertexCover preconnected

/-- Junction + short-arc cover fragments from `NoncrossingPathDecompOpenGoals`. -/
structure GenericDecompCoverFromNoncrossing (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  junction_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ endpoint : Fin 4,
          e₁ ∈ genericBagFamily g hyp (.junction endpoint) ∧
            e₂ ∈ genericBagFamily g hyp (.junction endpoint)
  shortArc_edgeCover :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx),
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        (∃ j : Fin (g.cyclicGap shortArc), e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
        (∃ j : Fin (g.cyclicGap shortArc), e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)) →
          ∃ j : Fin (g.cyclicGap shortArc),
            e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j) ∧
              e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)

theorem GenericDecompCoverFromNoncrossing.of_noncrossingOpenGoals
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (goals : NoncrossingPathDecompAssumptions.NoncrossingPathDecompOpenGoals hyp) :
    GenericDecompCoverFromNoncrossing g hyp where
  junction_edgeCover := fun _ _ hadj => by
    obtain ⟨endpoint, h1, h2⟩ := goals.junction_edgeCover hadj
    exact ⟨endpoint, genericBagFamily_junction_mem_of_enriched g hyp endpoint h1,
      genericBagFamily_junction_mem_of_enriched g hyp endpoint h2⟩
  shortArc_edgeCover := fun shortArc hne _ _ hadj he1 he2 => by
    obtain ⟨j, h1, h2⟩ :=
      goals.shortArc_edgeCover shortArc hne hadj
        (by
          obtain ⟨j, hj⟩ := he1
          exact ⟨j, (genericBagFamily_shortSeg g hyp shortArc hne j).symm ▸ hj⟩)
        (by
          obtain ⟨j, hj⟩ := he2
          exact ⟨j, (genericBagFamily_shortSeg g hyp shortArc hne j).symm ▸ hj⟩)
    exact ⟨j, (genericBagFamily_shortSeg g hyp shortArc hne j).symm ▸ h1,
      (genericBagFamily_shortSeg g hyp shortArc hne j).symm ▸ h2⟩

/-- Long-arc edge cover fragment (not in `NoncrossingPathDecompOpenGoals`; discharge OPEN).

  Target: from `lineGraph` adjacency + membership in (possibly distinct) long-seg bags, extract a
  common sliding-bag index. Intended proof route (see `NoncrossingPathDecomp.arcEdgeCoverConsecutive`):
  invert `edgeBij` to arc-local positions, use shared-vertex ⇒ consecutive positions, then
  `arcEdgeCoverConsecutive`. Partial discharge: `genericLongSeg_edgeCover_sameBagIndex`,
  `genericLongSeg_lineGraphAdj_consecutive_edgeCover`. -/
structure GenericDecompLongArcCoverAssumptions (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  longArc_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
      (∃ j : Fin hyp.longArcLen, e₁ ∈ genericBagFamily g hyp (.longSeg j)) →
      (∃ j : Fin hyp.longArcLen, e₂ ∈ genericBagFamily g hyp (.longSeg j)) →
        ∃ j : Fin hyp.longArcLen,
          e₁ ∈ genericBagFamily g hyp (.longSeg j) ∧
            e₂ ∈ genericBagFamily g hyp (.longSeg j)

/-- Specialize long-arc lineGraph bag cover from `NoncrossingPathDecomp`. -/
theorem GenericDecompLongArcCoverAssumptions.of_noncrossingLineGraphBag
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g} :
    GenericDecompLongArcCoverAssumptions g hyp where
  longArc_edgeCover := fun {e₁ e₂} hadj hj₁ hj₂ => by
    obtain ⟨j₁, hj₁'⟩ := hj₁
    obtain ⟨j₂, hj₂'⟩ := hj₂
    have hj₁'' : e₁ ∈ hyp.longArcLineGraphBag j₁ := by
      rw [genericBagFamily_longSeg, hyp.genericLongSegBagExtension_empty j₁] at hj₁'
      simpa using hj₁'
    have hj₂'' : e₂ ∈ hyp.longArcLineGraphBag j₂ := by
      rw [genericBagFamily_longSeg, hyp.genericLongSegBagExtension_empty j₂] at hj₂'
      simpa using hj₂'
    obtain ⟨j, h1, h2⟩ :=
      NoncrossingPathDecompAssumptions.longArcLineGraphBag_edgeCover hyp hadj
        ⟨j₁, hj₁''⟩ ⟨j₂, hj₂''⟩
    exact ⟨j, genericBagFamily_longSeg_mem_of_line g hyp j h1,
      genericBagFamily_longSeg_mem_of_line g hyp j h2⟩

theorem GenericDecompCoverAssumptions.of_coverFragments
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (frag : GenericDecompCoverFromNoncrossing g hyp)
    (longArc : GenericDecompLongArcCoverAssumptions g hyp) :
    GenericDecompCoverAssumptions g hyp where
  junction_edgeCover := frag.junction_edgeCover
  shortArc_edgeCover := frag.shortArc_edgeCover
  longArc_edgeCover := longArc.longArc_edgeCover
  longArc_vertexCover := fun _ h => h
  shortArc_vertexCover := fun _ _ _ h => h
  junction_vertexCover := fun _ h => h

theorem GenericDecompCoverAssumptions.of_noncrossingOpenGoals
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (goals : NoncrossingPathDecompAssumptions.NoncrossingPathDecompOpenGoals hyp)
    (longArc : GenericDecompLongArcCoverAssumptions g hyp) :
    GenericDecompCoverAssumptions g hyp :=
  GenericDecompCoverAssumptions.of_coverFragments
    (GenericDecompCoverFromNoncrossing.of_noncrossingOpenGoals goals) longArc

/-!
  ## Mixed edgeCover fragments (long↔junction, short↔junction, long↔short)
  -/

def edgeInLongSegBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : g.toSimpleGraph.edgeSet) : Prop :=
  ∃ j : Fin hyp.longArcLen, e ∈ genericBagFamily g hyp (.longSeg j)

def edgeInJunctionBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : g.toSimpleGraph.edgeSet) : Prop :=
  ∃ endpoint : Fin 4, e ∈ genericBagFamily g hyp (.junction endpoint)

def edgeInShortSegBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx) (e : g.toSimpleGraph.edgeSet) : Prop :=
  ∃ j : Fin (g.cyclicGap shortArc), e ∈ genericBagFamily g hyp (.shortSeg shortArc hne j)

def edgeInSomeShortSegBag (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (e : g.toSimpleGraph.edgeSet) : Prop :=
  ∃ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx), edgeInShortSegBag g hyp shortArc hne e

theorem genericMixed_edgeCover_junction (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨endpoint, h1, h2⟩ := cover.junction_edgeCover hadj
  exact ⟨.junction endpoint, h1, h2⟩

theorem genericMixed_edgeCover_longArc (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hL1 : edgeInLongSegBag g hyp e₁) (hL2 : edgeInLongSegBag g hyp e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨j₁, hj₁⟩ := hL1
  obtain ⟨j₂, hj₂⟩ := hL2
  obtain ⟨j, h1, h2⟩ := cover.longArc_edgeCover hadj ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩
  exact ⟨.longSeg j, h1, h2⟩

theorem genericMixed_edgeCover_shortArc (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hS1 : edgeInShortSegBag g hyp shortArc hne e₁)
    (hS2 : edgeInShortSegBag g hyp shortArc hne e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨j₁, hj₁⟩ := hS1
  obtain ⟨j₂, hj₂⟩ := hS2
  obtain ⟨j, h1, h2⟩ := cover.shortArc_edgeCover shortArc hne hadj ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩
  exact ⟨.shortSeg shortArc hne j, h1, h2⟩

theorem genericMixed_longSeg_junction_end_of_tail (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.longArcJunctionTailBag endpoint)
    (h2 : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint
      (hyp.enrichedJunctionBag_mem_longArcTail endpoint hnone h1)
  have h2' : e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint h2
  exact ⟨.junction endpoint, h1', h2'⟩

theorem genericMixed_longSeg_junction_start_of_head (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.longArcJunctionHeadBag endpoint)
    (h2 : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint
      (hyp.enrichedJunctionBag_mem_longArcHead endpoint hstep h1)
  have h2' : e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint h2
  exact ⟨.junction endpoint, h1', h2'⟩

theorem genericMixed_junction_longSeg_start_of_head (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (h2 : e₂ ∈ hyp.longArcJunctionHeadBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint h1
  have h2' : e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint
      (hyp.enrichedJunctionBag_mem_longArcHead endpoint hstep h2)
  exact ⟨.junction endpoint, h1', h2'⟩

theorem genericMixed_longSeg_junction_of_bothLongArc (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hL1 : edgeInLongSegBag g hyp e₁) (hL2 : edgeInLongSegBag g hyp e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_edgeCover_longArc g hyp cover hadj hL1 hL2

theorem genericMixed_longSeg_junction_start_of_head_longSegZero (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.longArcJunctionHeadBag endpoint)
    (h2 : e₂ ∈ genericBagFamily g hyp (.longSeg ⟨0, hyp.hlen⟩)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.longSeg ⟨0, hyp.hlen⟩) :=
    genericBagFamily_longSeg_mem_of_line g hyp ⟨0, hyp.hlen⟩
      (hyp.longArcJunctionHeadBag_mem_longArcLineGraphBag endpoint h1)
  exact genericLongSeg_edgeCover_sameBag g hyp ⟨0, hyp.hlen⟩ e₁ e₂ h1' h2

def longSegLast (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    Fin hyp.longArcLen :=
  ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen Nat.one_pos⟩

def longSegZeroIdx (hyp : NoncrossingPathDecompAssumptions g) : Fin hyp.longArcLen :=
  ⟨0, hyp.hlen⟩

theorem genericMixed_junction_longSeg_end_of_tail (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (h2 : e₂ ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint h1
  have h2' : e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint
      (hyp.enrichedJunctionBag_mem_longArcTail endpoint hnone h2)
  exact ⟨.junction endpoint, h1', h2'⟩

theorem genericMixed_longSeg_junction_end_of_tail_longSegLast (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    (cover : GenericDecompCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (h1 : e₁ ∈ hyp.longArcJunctionTailBag endpoint)
    (h2 : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨j, hj₁⟩ := hyp.longArcJunctionTailBag_mem_longArcLineGraphBag endpoint h1
  have h1' : e₁ ∈ genericBagFamily g hyp (.longSeg j) :=
    genericBagFamily_longSeg_mem_of_line g hyp j hj₁
  obtain ⟨j', hc1, hc2⟩ :=
    cover.longArc_edgeCover hadj ⟨j, h1'⟩ ⟨longSegLast g hyp, h2⟩
  exact ⟨.longSeg j', hc1, hc2⟩

theorem edgeInJunctionBag_at (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endpoint : Fin 4) (e : g.toSimpleGraph.edgeSet) :
    e ∈ genericBagFamily g hyp (.junction endpoint) ↔ e ∈ hyp.enrichedJunctionBag endpoint := by
  rw [genericBagFamily_junction]
  simp only [hyp.genericJunctionBagExtension_empty endpoint, hyp.genericJunctionBagTrim_empty endpoint,
    Finset.union_empty, Finset.sdiff_empty]

theorem genericMixed_shortSeg_junction_of_extra (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4) (shortArc : Fin 4)
    (hshort : g.junctionShortArcAt hyp.arcIdx endpoint = some shortArc)
    (hne : shortArc ≠ hyp.arcIdx) (_hgap : 1 < g.cyclicGap shortArc)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ hyp.shortArcJunctionExtraBag endpoint shortArc)
    (h2 : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have h1' : e₁ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint
      (hyp.enrichedJunctionBag_mem_shortArcExtra endpoint shortArc hshort h1)
  have h2' : e₂ ∈ genericBagFamily g hyp (.junction endpoint) :=
    genericBagFamily_junction_mem_of_enriched g hyp endpoint h2
  exact ⟨.junction endpoint, h1', h2'⟩

/-- Cross-region edgeCover fragments (long↔junction, short↔junction, long↔short). -/
structure GenericDecompMixedCoverAssumptions (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  longSeg_junction :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        edgeInLongSegBag g hyp e₁ → edgeInJunctionBag g hyp e₂ →
          ∃ w : GenericDecompNode g hyp.arcIdx,
            e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  junction_longSeg :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        edgeInJunctionBag g hyp e₁ → edgeInLongSegBag g hyp e₂ →
          ∃ w : GenericDecompNode g hyp.arcIdx,
            e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  shortSeg_junction :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx),
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          edgeInShortSegBag g hyp shortArc hne e₁ → edgeInJunctionBag g hyp e₂ →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  junction_shortSeg :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx),
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          edgeInJunctionBag g hyp e₁ → edgeInShortSegBag g hyp shortArc hne e₂ →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  longSeg_shortSeg :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        edgeInLongSegBag g hyp e₁ → edgeInSomeShortSegBag g hyp e₂ →
          ∃ w : GenericDecompNode g hyp.arcIdx,
            e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  shortSeg_longSeg :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        edgeInSomeShortSegBag g hyp e₁ → edgeInLongSegBag g hyp e₂ →
          ∃ w : GenericDecompNode g hyp.arcIdx,
            e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w

/-- Start-junction geometry: long-arc local step 0 aligns with junction cycle step. -/
structure GenericDecompMixedCoverStartGeometry (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  junctionStep_eq_arcOffset :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint),
      g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx

/-- End-junction geometry (mirror of start; used for tail-bag discharge). -/
structure GenericDecompMixedCoverEndGeometry (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  junctionStep_eq_arcOffset :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint),
      g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx

/-- Explicit line-graph routing at start endpoints (incoming/chord ↔ longSeg 0). -/
structure GenericDecompMixedCoverStartRouting (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  longSegZero_incoming :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
          e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  incoming_longSegZero :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  longSegZero_junctionLineGraph :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
          e₂ ∈ hyp.junctionLineGraphBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  junctionLineGraph_longSegZero :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.junctionLineGraphBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  residual_longSeg_junction :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg j) →
          e₂ ∈ hyp.enrichedJunctionBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  residual_junction_longSeg :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.enrichedJunctionBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg j) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w

/-- Explicit line-graph routing at end endpoints (incoming/chord ↔ longSeg last). -/
structure GenericDecompMixedCoverEndRouting (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  longSegLast_incoming :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
          e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  incoming_longSegLast :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  longSegLast_junctionLineGraph :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
          e₂ ∈ hyp.junctionLineGraphBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  junctionLineGraph_longSegLast :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.junctionLineGraphBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  residual_longSeg_junction :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ genericBagFamily g hyp (.longSeg j) →
          e₂ ∈ hyp.enrichedJunctionBag endpoint →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  residual_junction_longSeg :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
      (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
      (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        e₁ ∈ hyp.enrichedJunctionBag endpoint →
          e₂ ∈ genericBagFamily g hyp (.longSeg j) →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w

/-!
  ### Instance-level start/end routing discharge (step 3)

  Primary fields (`longSegZero_*`, `incoming_longSegZero`, `longSegLast_*`, …) discharge from
  `GenericDecompCoverAssumptions.junction_edgeCover` when both edges lie in the same
  `enrichedJunctionBag`, or from same-segment bag when both lie in `longSegZero` / `longSegLast`.
  Residual fields catch enriched tail/extra-only and interior long-seg indices; full parametric
  closure remains OPEN on general topology.
-/

private theorem junctionLineGraphBag_subset_enrichedJunctionBag
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.junctionLineGraphBag endpoint) :
    e ∈ hyp.enrichedJunctionBag endpoint :=
  hyp.enrichedJunctionBag_mem_junction endpoint e he

private theorem incomingJunctionLineGraphBag_subset_enrichedJunctionBag
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.incomingJunctionLineGraphBag endpoint) :
    e ∈ hyp.enrichedJunctionBag endpoint := by
  simp [NoncrossingPathDecompAssumptions.incomingJunctionLineGraphBag] at he
  obtain rfl := he
  exact hyp.enrichedJunctionBag_mem_incoming endpoint

/-- Adjacent pair both in some enriched junction bag → junction node cover (via `cover`). -/
theorem genericMixed_routing_of_enrichedJunction
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (endpoint : Fin 4)
    (_h₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (_h₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_edgeCover_junction g hyp cover hadj

theorem genericMixed_startRouting_longSegZero_incoming_of_head
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj0 : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hin : e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint)
    (hhead : e₁ ∈ hyp.longArcJunctionHeadBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint
    (hyp.enrichedJunctionBag_mem_longArcHead endpoint hstep hhead)
    (incomingJunctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hin)

theorem genericMixed_startRouting_incoming_longSegZero_of_head
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hin : e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint)
    (hj0 : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hhead : e₂ ∈ hyp.longArcJunctionHeadBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint
    (incomingJunctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hin)
    (hyp.enrichedJunctionBag_mem_longArcHead endpoint hstep hhead)

theorem genericMixed_startRouting_longSegZero_junctionLineGraph_of_head
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endpoint : Fin 4) (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hj0 : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hjunc : e₂ ∈ hyp.junctionLineGraphBag endpoint)
    (hhead : e₁ ∈ hyp.longArcJunctionHeadBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_longSeg_junction_start_of_head g hyp endpoint hstep hhead
    (junctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hjunc)

theorem genericMixed_startRouting_junctionLineGraph_longSegZero_of_head
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endpoint : Fin 4) (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hjunc : e₁ ∈ hyp.junctionLineGraphBag endpoint)
    (hj0 : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hhead : e₂ ∈ hyp.longArcJunctionHeadBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_junction_longSeg_start_of_head g hyp endpoint hstep
    (junctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hjunc) hhead

theorem genericMixed_startRouting_longSegZero_junctionLineGraph_of_sameLongSegZero
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hj0₁ : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hj0₂ : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp))) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericLongSeg_edgeCover_sameBag g hyp (longSegZeroIdx hyp) e₁ e₂ hj0₁ hj0₂

theorem genericMixed_startRouting_junctionLineGraph_longSegZero_of_sameLongSegZero
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hj0₁ : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)))
    (hj0₂ : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp))) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_startRouting_longSegZero_junctionLineGraph_of_sameLongSegZero g hyp hj0₁ hj0₂

theorem genericMixed_endRouting_longSegLast_incoming_of_tail
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    (_hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hjlast : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)))
    (hin : e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint)
    (htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint
    (hyp.enrichedJunctionBag_mem_longArcTail endpoint hnone htail)
    (incomingJunctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hin)

theorem genericMixed_endRouting_incoming_longSegLast_of_tail
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    (_hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hin : e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint)
    (hjlast : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)))
    (htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint
    (incomingJunctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hin)
    (hyp.enrichedJunctionBag_mem_longArcTail endpoint hnone htail)

theorem genericMixed_endRouting_longSegLast_junctionLineGraph_of_tail
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endpoint : Fin 4) (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hjlast : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)))
    (hjunc : e₂ ∈ hyp.junctionLineGraphBag endpoint)
    (htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_longSeg_junction_end_of_tail g hyp endpoint hnone htail
    (junctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hjunc)

theorem genericMixed_endRouting_junctionLineGraph_longSegLast_of_tail
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endpoint : Fin 4) (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hjunc : e₁ ∈ hyp.junctionLineGraphBag endpoint)
    (hjlast : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)))
    (htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_junction_longSeg_end_of_tail g hyp endpoint hnone
    (junctionLineGraphBag_subset_enrichedJunctionBag g hyp endpoint hjunc) htail

theorem genericMixed_endRouting_longSegLast_junctionLineGraph_of_sameLongSegLast
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hj₁ : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)))
    (hj₂ : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericLongSeg_edgeCover_sameBag g hyp (longSegLast g hyp) e₁ e₂ hj₁ hj₂

/-- Build start routing: primary fields from cover/head/same-bag; pass OPEN hooks for residual. -/
noncomputable def GenericDecompMixedCoverStartRouting.of_cover_primary
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (longSegZero_incoming_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (incoming_longSegZero_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (longSegZero_junctionLineGraph_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            e₂ ∈ hyp.junctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (junctionLineGraph_longSegZero_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.junctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_longSeg_junction :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_junction_longSeg :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    GenericDecompMixedCoverStartRouting g hyp where
  longSegZero_incoming := fun endpoint hstart hstep e₁ e₂ hadj hj0 hin => by
    by_cases hhead : e₁ ∈ hyp.longArcJunctionHeadBag endpoint
    · exact genericMixed_startRouting_longSegZero_incoming_of_head g hyp cover endpoint hstart
        hstep hadj hj0 hin hhead
    · exact longSegZero_incoming_open endpoint hstart hstep hadj hj0 hin
  incoming_longSegZero := fun endpoint hstart hstep e₁ e₂ hadj hin hj0 => by
    by_cases hhead : e₂ ∈ hyp.longArcJunctionHeadBag endpoint
    · exact genericMixed_startRouting_incoming_longSegZero_of_head g hyp cover endpoint hstart
        hstep hadj hin hj0 hhead
    · exact incoming_longSegZero_open endpoint hstart hstep hadj hin hj0
  longSegZero_junctionLineGraph := fun endpoint hstart hstep e₁ e₂ hadj hj0 hjunc => by
    by_cases hhead : e₁ ∈ hyp.longArcJunctionHeadBag endpoint
    · exact genericMixed_startRouting_longSegZero_junctionLineGraph_of_head g hyp endpoint hstep
        hj0 hjunc hhead
    · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp))
      · exact genericMixed_startRouting_longSegZero_junctionLineGraph_of_sameLongSegZero g hyp hj0 hsame
      · exact longSegZero_junctionLineGraph_open endpoint hstart hstep hadj hj0 hjunc
  junctionLineGraph_longSegZero := fun endpoint hstart hstep e₁ e₂ hadj hjunc hj0 => by
    by_cases hhead : e₂ ∈ hyp.longArcJunctionHeadBag endpoint
    · exact genericMixed_startRouting_junctionLineGraph_longSegZero_of_head g hyp endpoint hstep
        hjunc hj0 hhead
    · by_cases hsame : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp))
      · exact genericMixed_startRouting_junctionLineGraph_longSegZero_of_sameLongSegZero g hyp hsame hj0
      · exact junctionLineGraph_longSegZero_open endpoint hstart hstep hadj hjunc hj0
  residual_longSeg_junction := residual_longSeg_junction
  residual_junction_longSeg := residual_junction_longSeg

/-- Build end routing: primary fields from cover/tail/same-bag; pass OPEN hooks for residual. -/
noncomputable def GenericDecompMixedCoverEndRouting.of_cover_primary
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (longSegLast_incoming_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (incoming_longSegLast_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (longSegLast_junctionLineGraph_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            e₂ ∈ hyp.junctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (junctionLineGraph_longSegLast_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.junctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_longSeg_junction :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_junction_longSeg :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    GenericDecompMixedCoverEndRouting g hyp where
  longSegLast_incoming := fun endpoint hend hstep e₁ e₂ hadj hjlast hin => by
    by_cases hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none
    · by_cases htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint
      · exact genericMixed_endRouting_longSegLast_incoming_of_tail g hyp cover endpoint hnone hend
          hstep hadj hjlast hin htail
      · exact longSegLast_incoming_open endpoint hend hstep hadj hjlast hin
    · exact longSegLast_incoming_open endpoint hend hstep hadj hjlast hin
  incoming_longSegLast := fun endpoint hend hstep e₁ e₂ hadj hin hjlast => by
    by_cases hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none
    · by_cases htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint
      · exact genericMixed_endRouting_incoming_longSegLast_of_tail g hyp cover endpoint hnone hend
          hstep hadj hin hjlast htail
      · exact incoming_longSegLast_open endpoint hend hstep hadj hin hjlast
    · exact incoming_longSegLast_open endpoint hend hstep hadj hin hjlast
  longSegLast_junctionLineGraph := fun endpoint hend hstep e₁ e₂ hadj hjlast hjunc => by
    by_cases hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none
    · by_cases htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint
      · exact genericMixed_endRouting_longSegLast_junctionLineGraph_of_tail g hyp endpoint hnone
          hjlast hjunc htail
      · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))
        · exact genericMixed_endRouting_longSegLast_junctionLineGraph_of_sameLongSegLast g hyp hjlast hsame
        · exact longSegLast_junctionLineGraph_open endpoint hend hstep hadj hjlast hjunc
    · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))
      · exact genericMixed_endRouting_longSegLast_junctionLineGraph_of_sameLongSegLast g hyp hjlast hsame
      · exact longSegLast_junctionLineGraph_open endpoint hend hstep hadj hjlast hjunc
  junctionLineGraph_longSegLast := fun endpoint hend hstep e₁ e₂ hadj hjunc hjlast => by
    by_cases hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none
    · by_cases htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint
      · exact genericMixed_endRouting_junctionLineGraph_longSegLast_of_tail g hyp endpoint hnone
          hjunc hjlast htail
      · by_cases hsame : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))
        · exact genericMixed_endRouting_longSegLast_junctionLineGraph_of_sameLongSegLast g hyp hsame hjlast
        · exact junctionLineGraph_longSegLast_open endpoint hend hstep hadj hjunc hjlast
    · by_cases hsame : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp))
      · exact genericMixed_endRouting_longSegLast_junctionLineGraph_of_sameLongSegLast g hyp hsame hjlast
      · exact junctionLineGraph_longSegLast_open endpoint hend hstep hadj hjunc hjlast
  residual_longSeg_junction := residual_longSeg_junction
  residual_junction_longSeg := residual_junction_longSeg

/-- `shortSeg_junction` at local step 0 when the short-arc extra edge also lies in the j=0 sliding bag. -/
theorem genericMixed_shortSeg_junction_of_zero_and_extra
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) (endpoint : Fin 4)
    (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx)
    (hshort : g.junctionShortArcAt hyp.arcIdx endpoint = some shortArc)
    (hgap : 1 < g.cyclicGap shortArc) (j0 : Fin (g.cyclicGap shortArc)) (hj0 : j0.val = 0)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0))
    (h1extra : e₁ ∈ hyp.shortArcJunctionExtraBag endpoint shortArc)
    (h2 : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_shortSeg_junction_of_extra g hyp endpoint shortArc hshort hne hgap h1extra h2

/-- Both endpoints in enriched junction at a `shortArcZeroJunction` endpoint (line-graph OPEN). -/
theorem genericMixed_shortSeg_junction_of_zero_enriched
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (shortArc endpoint : Fin 4)
    (hne : shortArc ≠ hyp.arcIdx) (_hown : shortArcZeroJunction g hyp shortArc endpoint)
    (hgap : 0 < g.cyclicGap shortArc) (j0 : Fin (g.cyclicGap shortArc)) (hj0 : j0.val = 0)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (h1 : e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0))
    (h1J : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (h2 : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint h1J h2

/-- `shortSeg_junction` at j=0 when both endpoints lie in the same step-0 sliding bag. -/
theorem genericMixed_shortSeg_junction_of_zero_sameBag
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx)
    (hgap : 0 < g.cyclicGap shortArc) (j0 : Fin (g.cyclicGap shortArc)) (hj0 : j0.val = 0)
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0))
    (h2 : e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericShortSeg_edgeCover_sameBag g hyp shortArc hne j0 e₁ e₂ h1 h2

/-- Route `shortSeg_junction` at j=0: extra overlap, enriched overlap, same-bag, or OPEN hook. -/
theorem genericMixed_shortSeg_junction_of_zero_route
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (shortArc juncEp : Fin 4)
    (hne : shortArc ≠ hyp.arcIdx) (hown : shortArcZeroJunction g hyp shortArc juncEp)
    (hshort : g.junctionShortArcAt hyp.arcIdx juncEp = some shortArc)
    (hgap : 0 < g.cyclicGap shortArc) (j0 : Fin (g.cyclicGap shortArc)) (hj0 : j0.val = 0)
    (shortSeg_junction_open :
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0) →
            edgeInJunctionBag g hyp e₂ →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (h1 : e₁ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0)) (hJ2 : edgeInJunctionBag g hyp e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  have hJunc2 := hJ2
  obtain ⟨endpoint', he₂⟩ := hJ2
  have he₂' : e₂ ∈ hyp.enrichedJunctionBag endpoint' :=
    (edgeInJunctionBag_at g hyp endpoint' e₂).mp he₂
  by_cases hextra : e₁ ∈ hyp.shortArcJunctionExtraBag juncEp shortArc
  · by_cases heq : endpoint' = juncEp
    · have he₂J : e₂ ∈ hyp.enrichedJunctionBag juncEp := heq ▸ he₂'
      by_cases hgap1 : 1 < g.cyclicGap shortArc
      · exact genericMixed_shortSeg_junction_of_zero_and_extra g hyp juncEp shortArc hne hshort
          hgap1 j0 hj0 h1 hextra he₂J
      · exact shortSeg_junction_open hadj h1 hJunc2
    · exact shortSeg_junction_open hadj h1 hJunc2
  · by_cases h1J : e₁ ∈ hyp.enrichedJunctionBag juncEp
    · by_cases heq : endpoint' = juncEp
      · have he₂J : e₂ ∈ hyp.enrichedJunctionBag juncEp := heq ▸ he₂'
        exact genericMixed_shortSeg_junction_of_zero_enriched g hyp cover shortArc juncEp hne hown
          hgap j0 hj0 hadj h1 h1J he₂J
      · exact shortSeg_junction_open hadj h1 hJunc2
    · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.shortSeg shortArc hne j0)
      · exact genericMixed_shortSeg_junction_of_zero_sameBag g hyp shortArc hne hgap j0 hj0 h1 hsame
      · exact shortSeg_junction_open hadj h1 hJunc2

/-!
  ### Step 4–5: geometry open goals + residual enriched discharge

  Full parametric `junctionStep_eq_arcOffset` on all start/end endpoints remains OPEN on general
  noncrossing topology (pairing + gap vector determines endpoint cycle steps vs `arcEdgeOffset`).
  Partial discharge: endpoint `0` when `hyp.arcIdx = 0` (`junctionStep_eq_arcOffset_at_zero_iff`);
  nested pairing when `endpointArcIdx = arcIdx` / `junctionShortArcAt = none`
  (`junctionEndpointStep_eq_arcEdgeOffset_endpointArcIdx_nested`).
-/

/-- Geometry fields not derived from pairing/gap alone on general noncrossing instances. -/
structure GenericDecompMixedCoverGeometryOpenGoals (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  start_junctionStep_eq_arcOffset :
    ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint),
      g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx
  end_junctionStep_eq_arcOffset :
    ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint),
      g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx

def genericDecompMixedCoverGeometryOpenGoalsDoc : String :=
  "OPEN: full parametric start/end junctionStep_eq_arcOffset on general pairing+gap topology; " ++
  "PARTIAL: endpoint 0 when hyp.arcIdx = 0 (junctionStep_eq_arcOffset_at_zero_iff in NCP); " ++
  "nested pairing when endpoint on long arc (endpointArcIdx=arcIdx / junctionShortArcAt=none via " ++
  "junctionEndpointStep_eq_arcEdgeOffset_endpointArcIdx_nested); " ++
  "builders GenericDecompMixedCoverStartGeometry.of_openGoals / EndGeometry.of_openGoals / " ++
  "of_nested_with_offLongArc_open."

noncomputable def GenericDecompMixedCoverStartGeometry.of_openGoals
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (goals : GenericDecompMixedCoverGeometryOpenGoals g hyp) :
    GenericDecompMixedCoverStartGeometry g hyp where
  junctionStep_eq_arcOffset := goals.start_junctionStep_eq_arcOffset

noncomputable def GenericDecompMixedCoverEndGeometry.of_openGoals
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (goals : GenericDecompMixedCoverGeometryOpenGoals g hyp) :
    GenericDecompMixedCoverEndGeometry g hyp where
  junctionStep_eq_arcOffset := goals.end_junctionStep_eq_arcOffset

/-- Partial: endpoint `0` start geometry when the long arc is arc `0`. -/
theorem genericDecomp_startGeometry_endpoint_zero_of_arcIdx_zero
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (harc : hyp.arcIdx = 0) :
    g.junctionEndpointStep 0 = g.arcEdgeOffset hyp.arcIdx := by
  rw [g.junctionEndpointStep_zero, harc, CycleTwoChordGraph.arcEdgeOffset]

/-- Nested pairing + endpoint on the long arc (`endpointArcIdx = arcIdx`). -/
theorem genericDecomp_geometry_endpoint_of_endpointArcIdx_nested
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (hn : g.pairing = ChordPairing.nested) (endpoint : Fin 4)
    (h : g.endpointArcIdx endpoint = hyp.arcIdx) :
    g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx := by
  rw [CycleTwoChordGraph.junctionEndpointStep_eq_arcEdgeOffset_endpointArcIdx_nested g hn endpoint, h]

theorem genericDecomp_startGeometry_endpoint_of_endpointArcIdx_nested
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (hn : g.pairing = ChordPairing.nested) (endpoint : Fin 4)
    (_hstart : longArcStartJunctions endpoint)
    (h : g.endpointArcIdx endpoint = hyp.arcIdx) :
    g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx :=
  genericDecomp_geometry_endpoint_of_endpointArcIdx_nested hn endpoint h

/-- Nested pairing + endpoint on the long arc (`junctionShortArcAt = none`). -/
theorem genericDecomp_endGeometry_endpoint_of_junctionShortArcAt_none_nested
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (hn : g.pairing = ChordPairing.nested) (endpoint : Fin 4)
    (_hend : longArcEndJunctions endpoint)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none) :
    g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx := by
  have h := (CycleTwoChordGraph.junctionShortArcAt_none_iff g hyp.arcIdx endpoint).mp hnone
  exact genericDecomp_geometry_endpoint_of_endpointArcIdx_nested hn endpoint h

/-- Build start geometry on nested instances: on-long-arc endpoints from pairing; off-long-arc OPEN. -/
noncomputable def GenericDecompMixedCoverStartGeometry.of_nested_with_offLongArc_open
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (hn : g.pairing = ChordPairing.nested)
    (offLongArc :
      ∀ (endpoint : Fin 4) (hstart : longArcStartJunctions endpoint),
        g.endpointArcIdx endpoint ≠ hyp.arcIdx →
          g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx) :
    GenericDecompMixedCoverStartGeometry g hyp where
  junctionStep_eq_arcOffset := fun endpoint hstart => by
    by_cases h : g.endpointArcIdx endpoint = hyp.arcIdx
    · exact genericDecomp_startGeometry_endpoint_of_endpointArcIdx_nested hn endpoint hstart h
    · exact offLongArc endpoint hstart h

/-- Build end geometry on nested instances: on-long-arc endpoints from pairing; off-long-arc OPEN. -/
noncomputable def GenericDecompMixedCoverEndGeometry.of_nested_with_offLongArc_open
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (hn : g.pairing = ChordPairing.nested)
    (offLongArc :
      ∀ (endpoint : Fin 4) (hend : longArcEndJunctions endpoint),
        g.junctionShortArcAt hyp.arcIdx endpoint ≠ none →
          g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx) :
    GenericDecompMixedCoverEndGeometry g hyp where
  junctionStep_eq_arcOffset := fun endpoint hend => by
    by_cases hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none
    · exact genericDecomp_endGeometry_endpoint_of_junctionShortArcAt_none_nested hn endpoint hend hnone
    · exact offLongArc endpoint hend hnone

theorem genericMixed_startResidual_longSeg_junction_of_enrichedBoth
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint) (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint he₁ he₂

theorem genericMixed_startResidual_junction_longSeg_of_enrichedBoth
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint) (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint he₁ he₂

theorem genericMixed_startResidual_longSeg_junction_of_sameLongSeg
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (h2 : e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericLongSeg_edgeCover_sameBag g hyp j e₁ e₂ h1 h2

theorem genericMixed_startResidual_junction_longSeg_of_sameLongSeg
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (h1 : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (h2 : e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericLongSeg_edgeCover_sameBag g hyp j e₁ e₂ h1 h2

theorem genericMixed_endResidual_longSeg_junction_of_enrichedBoth
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint) (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint he₁ he₂

theorem genericMixed_endResidual_junction_longSeg_of_enrichedBoth
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint) (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w :=
  genericMixed_routing_of_enrichedJunction g hyp cover hadj endpoint he₁ he₂

private theorem junctionShortArcAt_none_of_mem_longArcJunctionTailBag
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (endpoint : Fin 4) {e : g.toSimpleGraph.edgeSet}
    (he : e ∈ hyp.longArcJunctionTailBag endpoint) :
    g.junctionShortArcAt hyp.arcIdx endpoint = none := by
  by_contra hnone
  simp [NoncrossingPathDecompAssumptions.longArcJunctionTailBag, hnone] at he

private theorem genericMixed_startResidual_longSeg_junction_route
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj₁ : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint)
    (residual_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hhead₁ : e₁ ∈ hyp.longArcJunctionHeadBag endpoint
  · exact genericMixed_longSeg_junction_start_of_head g hyp endpoint hstep hhead₁ he₂
  by_cases he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint
  · exact genericMixed_startResidual_longSeg_junction_of_enrichedBoth g hyp cover endpoint hadj he₁ he₂
  · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.longSeg j)
    · exact genericMixed_startResidual_longSeg_junction_of_sameLongSeg g hyp j hj₁ hsame
    · exact residual_open endpoint _hstart hstep j hadj hj₁ he₂

private theorem genericMixed_startResidual_junction_longSeg_route
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (hj₂ : e₂ ∈ genericBagFamily g hyp (.longSeg j))
    (residual_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hhead₂ : e₂ ∈ hyp.longArcJunctionHeadBag endpoint
  · exact genericMixed_junction_longSeg_start_of_head g hyp endpoint hstep he₁ hhead₂
  by_cases he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint
  · exact genericMixed_startResidual_junction_longSeg_of_enrichedBoth g hyp cover endpoint hadj he₁ he₂
  · by_cases hsame : e₁ ∈ genericBagFamily g hyp (.longSeg j)
    · exact genericMixed_startResidual_junction_longSeg_of_sameLongSeg g hyp j hsame hj₂
    · exact residual_open endpoint _hstart hstep j hadj he₁ hj₂

private theorem genericMixed_endResidual_longSeg_junction_route
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj₁ : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint)
    (residual_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases htail₁ : e₁ ∈ hyp.longArcJunctionTailBag endpoint
  · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail₁
    exact genericMixed_longSeg_junction_end_of_tail g hyp endpoint hnone htail₁ he₂
  by_cases he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint
  · exact genericMixed_endResidual_longSeg_junction_of_enrichedBoth g hyp cover endpoint hadj he₁ he₂
  · by_cases hsame : e₂ ∈ genericBagFamily g hyp (.longSeg j)
    · exact genericMixed_startResidual_longSeg_junction_of_sameLongSeg g hyp j hj₁ hsame
    · exact residual_open endpoint _hend hstep j hadj hj₁ he₂

private theorem genericMixed_endResidual_junction_longSeg_route
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp) (endpoint : Fin 4)
    (_hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (hj₂ : e₂ ∈ genericBagFamily g hyp (.longSeg j))
    (residual_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases htail₂ : e₂ ∈ hyp.longArcJunctionTailBag endpoint
  · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail₂
    exact genericMixed_junction_longSeg_end_of_tail g hyp endpoint hnone he₁ htail₂
  by_cases he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint
  · exact genericMixed_endResidual_junction_longSeg_of_enrichedBoth g hyp cover endpoint hadj he₁ he₂
  · by_cases hsame : e₁ ∈ genericBagFamily g hyp (.longSeg j)
    · exact genericMixed_startResidual_junction_longSeg_of_sameLongSeg g hyp j hsame hj₂
    · exact residual_open endpoint _hend hstep j hadj he₁ hj₂

/-- Start routing with residual auto-discharge on enriched-both / same-longSeg; OPEN hook for rest. -/
noncomputable def GenericDecompMixedCoverStartRouting.of_cover_primary_residual
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (longSegZero_incoming_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (incoming_longSegZero_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (longSegZero_junctionLineGraph_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
            e₂ ∈ hyp.junctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (junctionLineGraph_longSegZero_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.junctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_longSeg_junction_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_junction_longSeg_open :
      ∀ (endpoint : Fin 4) (_hstart : longArcStartJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    GenericDecompMixedCoverStartRouting g hyp :=
  GenericDecompMixedCoverStartRouting.of_cover_primary cover
    longSegZero_incoming_open incoming_longSegZero_open
    longSegZero_junctionLineGraph_open junctionLineGraph_longSegZero_open
    (fun endpoint hstart hstep j e₁ e₂ hadj hj₁ he₂ =>
      genericMixed_startResidual_longSeg_junction_route g hyp cover endpoint hstart hstep j
        hadj hj₁ he₂ residual_longSeg_junction_open)
    (fun endpoint hstart hstep j e₁ e₂ hadj he₁ hj₂ =>
      genericMixed_startResidual_junction_longSeg_route g hyp cover endpoint hstart hstep j
        hadj he₁ hj₂ residual_junction_longSeg_open)

/-- End routing with residual auto-discharge on enriched-both / same-longSeg / tail; OPEN hook for rest. -/
noncomputable def GenericDecompMixedCoverEndRouting.of_cover_primary_residual
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (longSegLast_incoming_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (incoming_longSegLast_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (longSegLast_junctionLineGraph_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
            e₂ ∈ hyp.junctionLineGraphBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (junctionLineGraph_longSegLast_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.junctionLineGraphBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_longSeg_junction_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ genericBagFamily g hyp (.longSeg j) →
            e₂ ∈ hyp.enrichedJunctionBag endpoint →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (residual_junction_longSeg_open :
      ∀ (endpoint : Fin 4) (_hend : longArcEndJunctions endpoint)
        (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
        (j : Fin hyp.longArcLen) ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          e₁ ∈ hyp.enrichedJunctionBag endpoint →
            e₂ ∈ genericBagFamily g hyp (.longSeg j) →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    GenericDecompMixedCoverEndRouting g hyp :=
  GenericDecompMixedCoverEndRouting.of_cover_primary cover
    longSegLast_incoming_open incoming_longSegLast_open
    longSegLast_junctionLineGraph_open junctionLineGraph_longSegLast_open
    (fun endpoint hend hstep j e₁ e₂ hadj hj₁ he₂ =>
      genericMixed_endResidual_longSeg_junction_route g hyp cover endpoint hend hstep j
        hadj hj₁ he₂ residual_longSeg_junction_open)
    (fun endpoint hend hstep j e₁ e₂ hadj he₁ hj₂ =>
      genericMixed_endResidual_junction_longSeg_route g hyp cover endpoint hend hstep j
        hadj he₁ hj₂ residual_junction_longSeg_open)

/-- Per-field routing status for instance builders (primary PROVED on head/tail/same-bag; residual OPEN). -/
structure GenericDecompMixedCoverRoutingOpenGoals (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  start_longSegZero_incoming : Prop
  start_incoming_longSegZero : Prop
  start_longSegZero_junctionLineGraph : Prop
  start_junctionLineGraph_longSegZero : Prop
  start_residual_longSeg_junction : Prop
  start_residual_junction_longSeg : Prop
  end_longSegLast_incoming : Prop
  end_incoming_longSegLast : Prop
  end_longSegLast_junctionLineGraph : Prop
  end_junctionLineGraph_longSegLast : Prop
  end_residual_longSeg_junction : Prop
  end_residual_junction_longSeg : Prop
  shortSeg_junction : Prop
  junction_shortSeg : Prop
  longSeg_shortSeg : Prop
  shortSeg_longSeg : Prop

def genericDecompMixedCoverRoutingOpenGoalsDoc : String :=
  "CONDITIONAL: longSeg_junction/junction_longSeg via of_cover_start_end_routing; " ++
  "PROVED primary start/end routing on head/tail/same-bag (genericMixed_startRouting_*, " ++
  "genericMixed_endRouting_*, of_cover_primary); " ++
  "PARTIAL residual: enriched-both/same-longSeg/head/tail via genericMixed_*Residual_* + " ++
  "of_cover_primary_residual (start) / of_cover_primary_residual (end); " ++
  "PARTIAL shortSeg j=0: extra/enriched/same-bag + genericMixed_shortSeg_junction_of_zero_route; " ++
  "OPEN: full parametric geometry (GenericDecompMixedCoverGeometryOpenGoals) on crossing/disjoint/off-long-arc nested, " ++
  "residual interior/tail-only mismatch on general topology, " ++
  "junction_shortSeg, longSeg_shortSeg, shortSeg_longSeg, vertexCover, preconnected."

private theorem junctionStep_eq_arcOffset_of_start_or_end
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (startGeom : GenericDecompMixedCoverStartGeometry g hyp)
    (endGeom : GenericDecompMixedCoverEndGeometry g hyp) (endpoint : Fin 4) :
    g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx := by
  rcases longArcStartJunctions_or_end endpoint with hstart | hend
  · exact startGeom.junctionStep_eq_arcOffset endpoint hstart
  · exact endGeom.junctionStep_eq_arcOffset endpoint hend

private theorem genericMixed_longSeg_junction_route_start
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (startRoute : GenericDecompMixedCoverStartRouting g hyp) (endpoint : Fin 4)
    (hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj₁ : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hj0 : j.val = 0
  · have hj0' : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) := by
      have hj_eq : j = longSegZeroIdx hyp := Fin.ext hj0
      rw [hj_eq] at hj₁
      exact hj₁
    by_cases hin : e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact startRoute.longSegZero_incoming endpoint hstart hstep hadj hj0' hin
    · by_cases hjunc : e₂ ∈ hyp.junctionLineGraphBag endpoint
      · exact startRoute.longSegZero_junctionLineGraph endpoint hstart hstep hadj hj0' hjunc
      · exact startRoute.residual_longSeg_junction endpoint hstart hstep j hadj hj₁ he₂
  · by_cases hin : e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact startRoute.residual_longSeg_junction endpoint hstart hstep j hadj hj₁ he₂
    · by_cases hjunc : e₂ ∈ hyp.junctionLineGraphBag endpoint
      · exact startRoute.residual_longSeg_junction endpoint hstart hstep j hadj hj₁ he₂
      · exact startRoute.residual_longSeg_junction endpoint hstart hstep j hadj hj₁ he₂

private theorem genericMixed_longSeg_junction_route_end
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endRoute : GenericDecompMixedCoverEndRouting g hyp) (endpoint : Fin 4)
    (hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj₁ : e₁ ∈ genericBagFamily g hyp (.longSeg j))
    (he₂ : e₂ ∈ hyp.enrichedJunctionBag endpoint) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hjlast : j.val + 1 = hyp.longArcLen
  · have hjlast' : e₁ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) := by
      have hj_eq : j = longSegLast g hyp := by
        apply Fin.ext
        dsimp [longSegLast]
        omega
      rw [hj_eq] at hj₁
      exact hj₁
    by_cases hin : e₂ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact endRoute.longSegLast_incoming endpoint hend hstep hadj hjlast' hin
    · by_cases hjunc : e₂ ∈ hyp.junctionLineGraphBag endpoint
      · exact endRoute.longSegLast_junctionLineGraph endpoint hend hstep hadj hjlast' hjunc
      · exact endRoute.residual_longSeg_junction endpoint hend hstep j hadj hj₁ he₂
  · by_cases htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint
    · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail
      exact genericMixed_longSeg_junction_end_of_tail g hyp endpoint hnone htail he₂
    · exact endRoute.residual_longSeg_junction endpoint hend hstep j hadj hj₁ he₂

theorem genericMixed_longSeg_junction_of_cover_start_end_routing
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    (startGeom : GenericDecompMixedCoverStartGeometry g hyp)
    (endGeom : GenericDecompMixedCoverEndGeometry g hyp)
    (startRoute : GenericDecompMixedCoverStartRouting g hyp)
    (endRoute : GenericDecompMixedCoverEndRouting g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hL1 : edgeInLongSegBag g hyp e₁) (hJ2 : edgeInJunctionBag g hyp e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨endpoint, he₂⟩ := hJ2
  have he₂' : e₂ ∈ hyp.enrichedJunctionBag endpoint :=
    (edgeInJunctionBag_at g hyp endpoint e₂).mp he₂
  by_cases hL2 : edgeInLongSegBag g hyp e₂
  · exact genericMixed_longSeg_junction_of_bothLongArc g hyp cover hadj hL1 hL2
  by_cases hhead : e₁ ∈ hyp.longArcJunctionHeadBag endpoint
  · have hstep := junctionStep_eq_arcOffset_of_start_or_end startGeom endGeom endpoint
    exact genericMixed_longSeg_junction_start_of_head g hyp endpoint hstep hhead he₂'
  by_cases htail : e₁ ∈ hyp.longArcJunctionTailBag endpoint
  · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail
    exact genericMixed_longSeg_junction_end_of_tail g hyp endpoint hnone htail he₂'
  obtain ⟨j, hj₁⟩ := hL1
  have hj₁' : e₁ ∈ genericBagFamily g hyp (.longSeg j) := hj₁
  by_cases hstart : longArcStartJunctions endpoint
  · have hstep := startGeom.junctionStep_eq_arcOffset endpoint hstart
    exact genericMixed_longSeg_junction_route_start g hyp startRoute endpoint hstart hstep j
      hadj hj₁' he₂'
  · have hend : longArcEndJunctions endpoint := longArcEndJunctions_of_not_start endpoint (by
      intro h; exact hstart h)
    have hstep := endGeom.junctionStep_eq_arcOffset endpoint hend
    exact genericMixed_longSeg_junction_route_end g hyp endRoute endpoint hend hstep j hadj hj₁' he₂'

private theorem genericMixed_junction_longSeg_route_start
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (startRoute : GenericDecompMixedCoverStartRouting g hyp) (endpoint : Fin 4)
    (hstart : longArcStartJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (hj₂ : e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hj0 : j.val = 0
  · have hj0' : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegZeroIdx hyp)) := by
      have hj_eq : j = longSegZeroIdx hyp := Fin.ext hj0
      rw [hj_eq] at hj₂
      exact hj₂
    by_cases hin : e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact startRoute.incoming_longSegZero endpoint hstart hstep hadj hin hj0'
    · by_cases hjunc : e₁ ∈ hyp.junctionLineGraphBag endpoint
      · exact startRoute.junctionLineGraph_longSegZero endpoint hstart hstep hadj hjunc hj0'
      · exact startRoute.residual_junction_longSeg endpoint hstart hstep j hadj he₁ hj₂
  · by_cases hin : e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact startRoute.residual_junction_longSeg endpoint hstart hstep j hadj he₁ hj₂
    · by_cases hjunc : e₁ ∈ hyp.junctionLineGraphBag endpoint
      · exact startRoute.residual_junction_longSeg endpoint hstart hstep j hadj he₁ hj₂
      · exact startRoute.residual_junction_longSeg endpoint hstart hstep j hadj he₁ hj₂

private theorem genericMixed_junction_longSeg_route_end
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (endRoute : GenericDecompMixedCoverEndRouting g hyp) (endpoint : Fin 4)
    (hend : longArcEndJunctions endpoint)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    (j : Fin hyp.longArcLen) {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (he₁ : e₁ ∈ hyp.enrichedJunctionBag endpoint)
    (hj₂ : e₂ ∈ genericBagFamily g hyp (.longSeg j)) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  by_cases hjlast : j.val + 1 = hyp.longArcLen
  · have hjlast' : e₂ ∈ genericBagFamily g hyp (.longSeg (longSegLast g hyp)) := by
      have hj_eq : j = longSegLast g hyp := by
        apply Fin.ext
        dsimp [longSegLast]
        omega
      rw [hj_eq] at hj₂
      exact hj₂
    by_cases hin : e₁ ∈ hyp.incomingJunctionLineGraphBag endpoint
    · exact endRoute.incoming_longSegLast endpoint hend hstep hadj hin hjlast'
    · by_cases hjunc : e₁ ∈ hyp.junctionLineGraphBag endpoint
      · exact endRoute.junctionLineGraph_longSegLast endpoint hend hstep hadj hjunc hjlast'
      · exact endRoute.residual_junction_longSeg endpoint hend hstep j hadj he₁ hj₂
  · by_cases htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint
    · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail
      exact genericMixed_junction_longSeg_end_of_tail g hyp endpoint hnone he₁ htail
    · exact endRoute.residual_junction_longSeg endpoint hend hstep j hadj he₁ hj₂

theorem genericMixed_junction_longSeg_of_cover_start_end_routing
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (cover : GenericDecompCoverAssumptions g hyp)
    (startGeom : GenericDecompMixedCoverStartGeometry g hyp)
    (endGeom : GenericDecompMixedCoverEndGeometry g hyp)
    (startRoute : GenericDecompMixedCoverStartRouting g hyp)
    (endRoute : GenericDecompMixedCoverEndRouting g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hJ1 : edgeInJunctionBag g hyp e₁) (hL2 : edgeInLongSegBag g hyp e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  obtain ⟨endpoint, he₁⟩ := hJ1
  have he₁' : e₁ ∈ hyp.enrichedJunctionBag endpoint :=
    (edgeInJunctionBag_at g hyp endpoint e₁).mp he₁
  by_cases hL1 : edgeInLongSegBag g hyp e₁
  · exact genericMixed_longSeg_junction_of_bothLongArc g hyp cover hadj hL1 hL2
  by_cases hhead : e₂ ∈ hyp.longArcJunctionHeadBag endpoint
  · have hstep := junctionStep_eq_arcOffset_of_start_or_end startGeom endGeom endpoint
    exact genericMixed_junction_longSeg_start_of_head g hyp endpoint hstep he₁' hhead
  by_cases htail : e₂ ∈ hyp.longArcJunctionTailBag endpoint
  · have hnone := junctionShortArcAt_none_of_mem_longArcJunctionTailBag endpoint htail
    exact genericMixed_junction_longSeg_end_of_tail g hyp endpoint hnone he₁' htail
  obtain ⟨j, hj₂⟩ := hL2
  by_cases hstart : longArcStartJunctions endpoint
  · have hstep := startGeom.junctionStep_eq_arcOffset endpoint hstart
    exact genericMixed_junction_longSeg_route_start g hyp startRoute endpoint hstart hstep j
      hadj he₁' hj₂
  · have hend : longArcEndJunctions endpoint := longArcEndJunctions_of_not_start endpoint (by
      intro h; exact hstart h)
    have hstep := endGeom.junctionStep_eq_arcOffset endpoint hend
    exact genericMixed_junction_longSeg_route_end g hyp endRoute endpoint hend hstep j hadj he₁' hj₂

/-- Bundle discharge of the two long↔junction mixed fields from cover + geometry + routing. -/
theorem GenericDecompMixedCoverAssumptions.of_cover_start_end_routing
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (startGeom : GenericDecompMixedCoverStartGeometry g hyp)
    (endGeom : GenericDecompMixedCoverEndGeometry g hyp)
    (startRoute : GenericDecompMixedCoverStartRouting g hyp)
    (endRoute : GenericDecompMixedCoverEndRouting g hyp)
    (rest :
      ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx),
        ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
          (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
            edgeInShortSegBag g hyp shortArc hne e₁ → edgeInJunctionBag g hyp e₂ →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (rest' :
      ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx),
        ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
          (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
            edgeInJunctionBag g hyp e₁ → edgeInShortSegBag g hyp shortArc hne e₂ →
              ∃ w : GenericDecompNode g hyp.arcIdx,
                e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (restLongShort :
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          edgeInLongSegBag g hyp e₁ → edgeInSomeShortSegBag g hyp e₂ →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w)
    (restShortLong :
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
          edgeInSomeShortSegBag g hyp e₁ → edgeInLongSegBag g hyp e₂ →
            ∃ w : GenericDecompNode g hyp.arcIdx,
              e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w) :
    GenericDecompMixedCoverAssumptions g hyp where
  longSeg_junction := fun {e₁ e₂} hadj hL1 hJ2 =>
    genericMixed_longSeg_junction_of_cover_start_end_routing g hyp cover startGeom endGeom
      startRoute endRoute hadj hL1 hJ2
  junction_longSeg := fun {e₁ e₂} hadj hJ1 hL2 =>
    genericMixed_junction_longSeg_of_cover_start_end_routing g hyp cover startGeom endGeom
      startRoute endRoute hadj hJ1 hL2
  shortSeg_junction := rest
  junction_shortSeg := rest'
  longSeg_shortSeg := restLongShort
  shortSeg_longSeg := restShortLong

theorem GenericDecompOpenGoals.edgeCover_of_cover_and_mixed
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (cover : GenericDecompCoverAssumptions g hyp)
    (mixed : GenericDecompMixedCoverAssumptions g hyp)
    {e₁ e₂ : g.toSimpleGraph.edgeSet} (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂) :
    ∃ w : GenericDecompNode g hyp.arcIdx,
      e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w := by
  classical
  by_cases hL1 : edgeInLongSegBag g hyp e₁
  · by_cases hL2 : edgeInLongSegBag g hyp e₂
    · exact genericMixed_edgeCover_longArc g hyp cover hadj hL1 hL2
    · by_cases hJ2 : edgeInJunctionBag g hyp e₂
      · exact mixed.longSeg_junction hadj hL1 hJ2
      · by_cases hS2 : edgeInSomeShortSegBag g hyp e₂
        · exact mixed.longSeg_shortSeg hadj hL1 hS2
        · exact genericMixed_edgeCover_junction g hyp cover hadj
  · by_cases hJ1 : edgeInJunctionBag g hyp e₁
    · by_cases hL2 : edgeInLongSegBag g hyp e₂
      · exact mixed.junction_longSeg hadj hJ1 hL2
      · by_cases hJ2 : edgeInJunctionBag g hyp e₂
        · exact genericMixed_edgeCover_junction g hyp cover hadj
        · by_cases hS2 : edgeInSomeShortSegBag g hyp e₂
          · obtain ⟨shortArc, hne, hS2⟩ := hS2
            exact mixed.junction_shortSeg shortArc hne hadj hJ1 hS2
          · exact genericMixed_edgeCover_junction g hyp cover hadj
    · by_cases hS1 : edgeInSomeShortSegBag g hyp e₁
      · obtain ⟨shortArc, hne, hS1⟩ := hS1
        by_cases hL2 : edgeInLongSegBag g hyp e₂
        · exact mixed.shortSeg_longSeg hadj ⟨shortArc, hne, hS1⟩ hL2
        · by_cases hJ2 : edgeInJunctionBag g hyp e₂
          · exact mixed.shortSeg_junction shortArc hne hadj hS1 hJ2
          · by_cases hS2 : edgeInSomeShortSegBag g hyp e₂
            · obtain ⟨shortArc', hne', hS2⟩ := hS2
              by_cases heq : shortArc = shortArc'
              · subst heq
                exact genericMixed_edgeCover_shortArc g hyp cover shortArc hne hadj hS1 hS2
              · exact genericMixed_edgeCover_junction g hyp cover hadj
            · exact genericMixed_edgeCover_junction g hyp cover hadj
      · exact genericMixed_edgeCover_junction g hyp cover hadj

/-- Remaining cover/preconnected goals not discharged from `NoncrossingPathDecompOpenGoals` alone.

  **PROVED fragments:** homogeneous long/long, short/short (same arc), junction/junction (via
  `junction_edgeCover`); enriched-junction tail/extra/head same-bag (`genericMixed_longSeg_junction_end_of_tail`,
  `genericMixed_longSeg_junction_start_of_head`,   `genericMixed_junction_longSeg_start_of_head`, `genericMixed_junction_longSeg_end_of_tail`,
  `genericMixed_longSeg_junction_start_of_head_longSegZero`,
  `genericMixed_longSeg_junction_end_of_tail_longSegLast`, `genericMixed_shortSeg_junction_of_extra`);
  `genericMixed_longSeg_junction_of_bothLongArc` (junction edge also in long-seg bag);
  conditional discharge of `longSeg_junction` / `junction_longSeg` via
  `genericMixed_*_of_cover_start_end_routing` + `GenericDecompMixedCoverAssumptions.of_cover_start_end_routing`
  (combinatorial head/tail/both-long + explicit start/end routing assumptions);
  combinator `edgeCover_of_cover_and_mixed`.

  **OPEN:** instance-level start/end routing + remaining four mixed fields (`shortSeg_junction`,
  `junction_shortSeg`, `longSeg_shortSeg`, `shortSeg_longSeg`); full `vertexCover`; junction/mixed
  `preconnected`. -/
structure GenericDecompCoverRemainingGoals (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  mixed_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w
  preconnected :
    ∀ e : g.toSimpleGraph.edgeSet,
      (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected

/-- Interval preconnected fragments (long/short segments); junction/mixed cases remain OPEN. -/
structure GenericDecompPreconnectedIntervalAssumptions (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) where
  longSeg_interval :
    ∀ (e : g.toSimpleGraph.edgeSet) (a b : Nat)
      (ha : a < hyp.longArcLen) (hb : b < hyp.longArcLen) (hab : a ≤ b)
      (hset : {j : Fin hyp.longArcLen | e ∈ hyp.longArcSegmentBag j} =
        certPathGraphInterval hyp.longArcLen a b),
      (genericDecompGraph g hyp).induce
          ({w | e ∈ genericBagFamily g hyp w} ∩ genericLongSegNodeSet g hyp) |>.Preconnected
  shortSeg_interval :
    ∀ (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx) (e : g.toSimpleGraph.edgeSet) (a b : Nat)
      (ha : a < g.cyclicGap shortArc) (hb : b < g.cyclicGap shortArc) (hab : a ≤ b)
      (hset : {j : Fin (g.cyclicGap shortArc) | e ∈ hyp.shortArcLineGraphBag shortArc j} =
        certPathGraphInterval (g.cyclicGap shortArc) a b),
      (genericDecompGraph g hyp).induce
          ({w | e ∈ genericBagFamily g hyp w} ∩ genericShortSegNodeSet g hyp shortArc hne) |>.Preconnected

theorem GenericDecompPreconnectedIntervalAssumptions.of_hyp
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) :
    GenericDecompPreconnectedIntervalAssumptions g hyp where
  longSeg_interval := fun e a b ha hb hab hset =>
    genericLongSeg_preconnected_of_interval g hyp e a b ha hb hab hset
  shortSeg_interval := fun shortArc hne e a b ha hb hab hset =>
    genericShortSeg_preconnected_of_interval g hyp shortArc hne e a b ha hb hab hset

theorem GenericDecompOpenGoals.of_cover_shape_and_remaining
    {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (_cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (remaining : GenericDecompCoverRemainingGoals g hyp) :
    GenericDecompOpenGoals g hyp :=
  GenericDecompOpenGoals.of_cover_shape _cover shape
    remaining.mixed_edgeCover remaining.vertexCover remaining.preconnected

def genericConditionalHasTreeDecomp (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) : Prop :=
  HasTreeDecomp (lineGraph g.toSimpleGraph) 3

/-- Generic certificate on `GenericDecompNode`. -/
structure GenericTreeDecompCert (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : GenericDecompNode g hyp.arcIdx,
          e₁ ∈ genericBagFamily g hyp w ∧ e₂ ∈ genericBagFamily g hyp w
  vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet,
      ∃ w : GenericDecompNode g hyp.arcIdx, e ∈ genericBagFamily g hyp w
  preconnected :
    ∀ e : g.toSimpleGraph.edgeSet,
      ((genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected)
  isTree : (genericDecompGraph g hyp).IsTree

theorem GenericTreeDecompCert.ofOpenGoals {g : CycleTwoChordGraph} {hyp : NoncrossingPathDecompAssumptions g}
    (goals : GenericDecompOpenGoals g hyp) : GenericTreeDecompCert g hyp where
  edgeCover := goals.edgeCover
  vertexCover := goals.vertexCover
  preconnected := goals.preconnected
  isTree := goals.isTree

noncomputable def genericDecompGraphFin (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (transport : GenericDecompFinTransport g hyp) :
    SimpleGraph (Fin (genericDecompNodeCount g hyp)) :=
  (genericDecompGraph g hyp).map transport.finEquiv

theorem genericDecompGraphFin_isTree (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (transport : GenericDecompFinTransport g hyp) (cert : GenericTreeDecompCert g hyp) :
    (genericDecompGraphFin g hyp transport).IsTree :=
  (Iso.isTree_iff (Iso.map transport.finEquiv (genericDecompGraph g hyp))).mp cert.isTree

theorem genericDecompGraphFin_induce_preconnected (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (transport : GenericDecompFinTransport g hyp)
    (e : g.toSimpleGraph.edgeSet)
    (h : (genericDecompGraph g hyp).induce {w | e ∈ genericBagFamily g hyp w} |>.Preconnected) :
    (genericDecompGraphFin g hyp transport).induce
        {w | e ∈ genericBagFamily g hyp (transport.finEquiv.symm w)} |>.Preconnected := by
  let S : Set (GenericDecompNode g hyp.arcIdx) := {w | e ∈ genericBagFamily g hyp w}
  let iso := Iso.map transport.finEquiv (genericDecompGraph g hyp)
  have hT : iso.toHom '' S =
      {w | e ∈ genericBagFamily g hyp (transport.finEquiv.symm w)} := by
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq, S, iso, Iso.toHom, Embedding.toHom, Iso.map_apply]
    constructor
    · rintro ⟨v, hv, hvw⟩
      have hvw' : transport.finEquiv v = w := by
        simpa [iso, Iso.toHom, Embedding.toHom, Iso.map_apply] using hvw
      have hwv : transport.finEquiv.symm w = v :=
        transport.finEquiv.injective (by rw [← hvw', transport.finEquiv.apply_symm_apply])
      exact hwv.symm ▸ hv
    · intro hv
      exact ⟨transport.finEquiv.symm w, hv, transport.finEquiv.apply_symm_apply w⟩
  rw [genericDecompGraphFin, ← hT]
  exact Preconnected.induce_map_image (f := iso.toHom) iso.injective rfl h

noncomputable def genericTreeDecomp (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (transport : GenericDecompFinTransport g hyp) (cert : GenericTreeDecompCert g hyp) :
    TreeDecomp (lineGraph g.toSimpleGraph) (genericDecompNodeCount g hyp) where
  bag w := genericBagFamily g hyp (transport.finEquiv.symm w)
  tree := genericDecompGraphFin g hyp transport
  isTree := genericDecompGraphFin_isTree g hyp transport cert
  vertexCover := fun e => by
    obtain ⟨v, hv⟩ := cert.vertexCover e
    exact ⟨transport.finEquiv v, by simpa using hv⟩
  edgeCover := fun _ _ hadj => by
    obtain ⟨v, h1, h2⟩ := cert.edgeCover hadj
    exact ⟨transport.finEquiv v, by simpa using h1, by simpa using h2⟩
  preconnected_induce_T := fun e => by
    have h := cert.preconnected e
    simpa [genericDecompGraphFin] using
      genericDecompGraphFin_induce_preconnected g hyp transport e h

theorem genericTreeDecomp_width_le_sup (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (transport : GenericDecompFinTransport g hyp) (cert : GenericTreeDecompCert g hyp) :
    (genericTreeDecomp g hyp transport cert).width ≤ genericBagSupWidth g hyp := by
  dsimp [TreeDecomp.width, genericTreeDecomp]
  refine Finset.sup_le fun w _ => genericBagFamily_width_le_sup g hyp (transport.finEquiv.symm w)

theorem genericConditionalHasTreeDecomp_of_cert (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (transport : GenericDecompFinTransport g hyp)
    (cert : GenericTreeDecompCert g hyp) :
    genericConditionalHasTreeDecomp g hyp := by
  refine ⟨genericDecompNodeCount g hyp, genericTreeDecomp g hyp transport cert, ?_⟩
  exact le_trans (genericTreeDecomp_width_le_sup g hyp transport cert) (genericBagSupWidth_le_three g hyp)

theorem genericConditionalHasTreeDecomp_of_openGoals (g : CycleTwoChordGraph)
    (hyp : NoncrossingPathDecompAssumptions g) (transport : GenericDecompFinTransport g hyp)
    (goals : GenericDecompOpenGoals g hyp) :
    genericConditionalHasTreeDecomp g hyp :=
  genericConditionalHasTreeDecomp_of_cert g hyp transport (GenericTreeDecompCert.ofOpenGoals goals)

theorem genericConditionalHasTreeDecomp_of_cover_shape_and_remaining
    (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g)
    (transport : GenericDecompFinTransport g hyp)
    (_cover : GenericDecompCoverAssumptions g hyp) (shape : GenericDecompTreeShape g hyp)
    (remaining : GenericDecompCoverRemainingGoals g hyp) :
    genericConditionalHasTreeDecomp g hyp :=
    genericConditionalHasTreeDecomp_of_openGoals g hyp transport
    (GenericDecompOpenGoals.of_cover_shape_and_remaining _cover shape remaining)

/-! ## c7 nested generic smoke (partial — no edgeBij yet) -/

def c7NestedGraph_genericDecompSmokeDoc : String :=
  "OPEN: c7Hyp/pathDecompAssumptions blocked on GraphEdgeBijection; " ++
  "PROVED parametric shortArcEdgeCoverConsecutive + genericShortSeg sliding (gap>1); " ++
  "c7 short arcs gap=1 → sliding vacuous; off-long-arc geometry OPEN on endpoints 0,2,3."

/-! ## c8 nested generic smoke (mixed routing wiring, step 7) -/

private noncomputable abbrev c8GenericHyp : NoncrossingPathDecompAssumptions c8NestedGraph := c8Hyp

private theorem c8_edgeEquiv_symm_apply (e : c8NestedGraph.toSimpleGraph.edgeSet) :
    c8GenericHyp.edgeBij.edgeEquiv (c8GenericHyp.edgeBij.edgeEquiv.symm e) = e := by
  apply Subtype.ext
  exact GraphEdgeBijection.edgeEquiv_symm_apply_val (hidx := c8GenericHyp.edgeBij) e

private theorem c8_generic_lineAdj_of_adj {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂) :
    c8PathDecompFinAdj (c8GenericHyp.edgeBij.edgeEquiv.symm e₁)
      (c8GenericHyp.edgeBij.edgeEquiv.symm e₂) := by
  apply (c8_pathDecomp_lineAdj_fin _ _).mp
  simpa [c8_edgeEquiv_symm_apply] using hadj

private theorem c8_generic_junction_edgeCover
    ⦃e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet⦄
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂) :
    ∃ endpoint : Fin 4,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.junction endpoint) ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.junction endpoint) := by
  have hadj' := c8_generic_lineAdj_of_adj hadj
  obtain ⟨endpoint, hi, hj⟩ :=
    c8_pathDecomp_junctionFinEdgeCover
      (c8GenericHyp.edgeBij.edgeEquiv.symm e₁) (c8GenericHyp.edgeBij.edgeEquiv.symm e₂) hadj'
  refine ⟨endpoint, ?_, ?_⟩
  · have he₁' := (c8_pathDecomp_enrichedJunctionBag_mem endpoint
        (c8GenericHyp.edgeBij.edgeEquiv.symm e₁)).mpr hi
    rw [← c8_edgeEquiv_symm_apply e₁]
    exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp endpoint he₁'
  · have he₂' := (c8_pathDecomp_enrichedJunctionBag_mem endpoint
        (c8GenericHyp.edgeBij.edgeEquiv.symm e₂)).mpr hj
    rw [← c8_edgeEquiv_symm_apply e₂]
    exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp endpoint he₂'

private def c8_generic_shortArc_toFin2 (shortArc : Fin 4) (j : Fin (c8NestedGraph.cyclicGap shortArc)) :
    Fin 2 :=
  Fin.cast (c8_pathDecomp_shortArc_gap shortArc) j

private def c8_generic_shortArc_fromFin2 (shortArc : Fin 4) (k : Fin 2) :
    Fin (c8NestedGraph.cyclicGap shortArc) :=
  Fin.cast (c8_pathDecomp_shortArc_gap shortArc).symm k

private theorem c8_generic_shortArc_index_cast (shortArc : Fin 4) (hne : shortArc ≠ c8GenericHyp.arcIdx)
    (j : Fin (c8NestedGraph.cyclicGap shortArc)) :
    c8GenericHyp.shortArcLineGraphBag shortArc
        (Fin.cast (c8_pathDecomp_shortArc_gap shortArc).symm (c8_generic_shortArc_toFin2 shortArc j)) =
      genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j) := by
  have hgap := c8_pathDecomp_shortArc_gap shortArc
  simp [genericBagFamily_shortSeg, c8_generic_shortArc_toFin2, hgap, Fin.cast_cast]

private theorem c8_generic_shortArc_fin_mem {shortArc : Fin 4} {hne : shortArc ≠ c8GenericHyp.arcIdx}
    {j : Fin (c8NestedGraph.cyclicGap shortArc)} {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j)) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈
      c8PathDecompFinShortArcBag shortArc (c8_generic_shortArc_toFin2 shortArc j) := by
  apply (c8_pathDecomp_shortArcBag_mem shortArc (c8_generic_shortArc_toFin2 shortArc j)
      (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ (c8_generic_shortArc_index_cast shortArc hne j).symm ▸ he

private theorem c8_generic_shortArc_edgeCover (shortArc : Fin 4) (hne : shortArc ≠ c8GenericHyp.arcIdx)
    ⦃e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet⦄
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂)
    (he₁ : ∃ j : Fin (c8NestedGraph.cyclicGap shortArc),
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j))
    (he₂ : ∃ j : Fin (c8NestedGraph.cyclicGap shortArc),
      e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j)) :
    ∃ j : Fin (c8NestedGraph.cyclicGap shortArc),
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j) ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j) := by
  have hadj' := c8_generic_lineAdj_of_adj hadj
  obtain ⟨j₁, hj₁⟩ := he₁
  obtain ⟨j₂, hj₂⟩ := he₂
  have hi : ∃ k, c8GenericHyp.edgeBij.edgeEquiv.symm e₁ ∈ c8PathDecompFinShortArcBag shortArc k :=
    ⟨c8_generic_shortArc_toFin2 shortArc j₁, c8_generic_shortArc_fin_mem (shortArc := shortArc) (hne := hne) hj₁⟩
  have hj : ∃ k, c8GenericHyp.edgeBij.edgeEquiv.symm e₂ ∈ c8PathDecompFinShortArcBag shortArc k :=
    ⟨c8_generic_shortArc_toFin2 shortArc j₂, c8_generic_shortArc_fin_mem (shortArc := shortArc) (hne := hne) hj₂⟩
  obtain ⟨k, hk₁, hk₂⟩ :=
    c8_pathDecomp_shortArcFinEdgeCover shortArc
      (c8GenericHyp.edgeBij.edgeEquiv.symm e₁) (c8GenericHyp.edgeBij.edgeEquiv.symm e₂) hne hadj' hi hj
  set j := c8_generic_shortArc_fromFin2 shortArc k
  refine ⟨j, ?_, ?_⟩
  · exact (genericBagFamily_shortSeg c8NestedGraph c8GenericHyp shortArc hne j).symm ▸
      (c8_edgeEquiv_symm_apply e₁).symm ▸
        (c8_pathDecomp_shortArcBag_mem shortArc k (c8GenericHyp.edgeBij.edgeEquiv.symm e₁)).mpr hk₁
  · exact (genericBagFamily_shortSeg c8NestedGraph c8GenericHyp shortArc hne j).symm ▸
      (c8_edgeEquiv_symm_apply e₂).symm ▸
        (c8_pathDecomp_shortArcBag_mem shortArc k (c8GenericHyp.edgeBij.edgeEquiv.symm e₂)).mpr hk₂

noncomputable def c8GenericCover : GenericDecompCoverAssumptions c8NestedGraph c8GenericHyp :=
  GenericDecompCoverAssumptions.of_coverFragments
    { junction_edgeCover := c8_generic_junction_edgeCover
      shortArc_edgeCover := c8_generic_shortArc_edgeCover }
    (GenericDecompLongArcCoverAssumptions.of_noncrossingLineGraphBag (g := c8NestedGraph))

theorem c8NestedGraph_offLongArc_geometry_open :
    c8NestedGraph.junctionEndpointStep 0 ≠ c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx ∧
      c8NestedGraph.junctionEndpointStep 2 ≠ c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx ∧
        c8NestedGraph.junctionEndpointStep 3 ≠ c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx := by
  constructor
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 0 (by decide)
  · constructor
    · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 2 (by decide)
    · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 3 (by decide)

private theorem c8_generic_startRouting_step_false (endpoint : Fin 4)
    (hstart : longArcStartJunctions endpoint)
    (hstep : c8NestedGraph.junctionEndpointStep endpoint =
      c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx) : False := by
  fin_cases endpoint
  · simp [longArcStartJunctions, c8_pathDecomp_junctionEndpointStep,
      c8_pathDecomp_arcEdgeOffset_longArc, c8NestedGraph_longArcIdx_eq_three] at hstep
    exact absurd hstep (by decide)
  · exact absurd hstart (by decide)
  · simp [longArcStartJunctions, c8_pathDecomp_junctionEndpointStep,
      c8_pathDecomp_arcEdgeOffset_longArc, c8NestedGraph_longArcIdx_eq_three] at hstep
    exact absurd hstep (by decide)
  · exact absurd hstart (by decide)

private theorem c8_generic_endRouting_endpoint_eq_one (endpoint : Fin 4)
    (hend : longArcEndJunctions endpoint)
    (hstep : c8NestedGraph.junctionEndpointStep endpoint =
      c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx) : endpoint = 1 := by
  fin_cases endpoint
  · exact absurd hend (by decide)
  · rfl
  · exact absurd hend (by decide)
  · simp [c8_pathDecomp_junctionEndpointStep, c8_pathDecomp_arcEdgeOffset_longArc] at hstep
    exact absurd hstep (by decide)

private theorem c8_generic_witness_junction (ep : Fin 4) (i j : Fin 10)
    (hi : i ∈ c8PathDecompFinEnrichedJunctionBag ep)
    (hj : j ∈ c8PathDecompFinEnrichedJunctionBag ep) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      c8GenericHyp.edgeBij.edgeEquiv i ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        c8GenericHyp.edgeBij.edgeEquiv j ∈ genericBagFamily c8NestedGraph c8GenericHyp w :=
  ⟨.junction ep,
    genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp ep
      ((c8_pathDecomp_enrichedJunctionBag_mem ep i).mpr hi),
    genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp ep
      ((c8_pathDecomp_enrichedJunctionBag_mem ep j).mpr hj)⟩

private theorem c8_generic_finLongSegLast_mem {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ genericBagFamily c8NestedGraph c8GenericHyp
      (.longSeg (longSegLast c8NestedGraph c8GenericHyp))) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈
      c8PathDecompFinLongArcBag (longSegLast c8NestedGraph c8GenericHyp) := by
  let j := longSegLast c8NestedGraph c8GenericHyp
  rw [genericBagFamily_longSeg] at he
  have he' : e ∈ c8GenericHyp.longArcLineGraphBag j := by
    rcases Finset.mem_union.mp he with he | he
    · exact he
    · rw [c8GenericHyp.genericLongSegBagExtension_empty j] at he
      simp at he
  apply (c8_pathDecomp_longArcBag_mem j (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he'

private theorem c8_generic_finLongSeg_mem {j : Fin c8GenericHyp.longArcLen}
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ genericBagFamily c8NestedGraph c8GenericHyp (.longSeg j)) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinLongArcBag j := by
  rw [genericBagFamily_longSeg] at he
  have he' : e ∈ c8GenericHyp.longArcLineGraphBag j := by
    rcases Finset.mem_union.mp he with he | he
    · exact he
    · rw [c8GenericHyp.genericLongSegBagExtension_empty j] at he
      simp at he
  apply (c8_pathDecomp_longArcBag_mem j (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he'

private theorem c8_generic_finJunction_mem_from_bag {endpoint : Fin 4}
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ genericBagFamily c8NestedGraph c8GenericHyp (.junction endpoint)) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinEnrichedJunctionBag endpoint := by
  have he' : e ∈ c8GenericHyp.enrichedJunctionBag endpoint := by
    have hgj : genericBagFamily c8NestedGraph c8GenericHyp (.junction endpoint) =
        c8GenericHyp.enrichedJunctionBag endpoint := by
      rw [genericBagFamily_junction]
      rw [c8GenericHyp.genericJunctionBagExtension_empty endpoint,
        c8GenericHyp.genericJunctionBagTrim_empty endpoint]
      simp
    rw [hgj] at he
    exact he
  apply (c8_pathDecomp_enrichedJunctionBag_mem endpoint (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he'

private theorem c8_generic_finIncoming_mem (endpoint : Fin 4)
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ c8GenericHyp.incomingJunctionLineGraphBag endpoint) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinIncomingBag endpoint := by
  apply (c8_pathDecomp_incomingBag_mem endpoint (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he

private theorem c8_generic_finJunctionLineGraph_mem (endpoint : Fin 4)
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ c8GenericHyp.junctionLineGraphBag endpoint) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinJunctionLineGraphBag endpoint := by
  apply (c8_pathDecomp_junctionLineGraphBag_mem endpoint (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he

private theorem c8_generic_finEnriched_mem (endpoint : Fin 4)
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ c8GenericHyp.enrichedJunctionBag endpoint) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinEnrichedJunctionBag endpoint := by
  apply (c8_pathDecomp_enrichedJunctionBag_mem endpoint (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp
  exact (c8_edgeEquiv_symm_apply e).symm ▸ he

private theorem c8_generic_endRouting_lift (endpoint : Fin 4)
    (hend : longArcEndJunctions endpoint)
    (hstep : c8NestedGraph.junctionEndpointStep endpoint =
      c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx)
    {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂)
    (fin_cover :
      c8PathDecompFinAdj (c8GenericHyp.edgeBij.edgeEquiv.symm e₁)
          (c8GenericHyp.edgeBij.edgeEquiv.symm e₂) →
        ∃ ep : Fin 4,
          c8GenericHyp.edgeBij.edgeEquiv.symm e₁ ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
            c8GenericHyp.edgeBij.edgeEquiv.symm e₂ ∈ c8PathDecompFinEnrichedJunctionBag ep) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w := by
  have hne : endpoint = 1 := c8_generic_endRouting_endpoint_eq_one endpoint hend hstep
  subst hne
  obtain ⟨ep, hi, hj⟩ :=
    fin_cover (c8_generic_lineAdj_of_adj hadj)
  obtain ⟨w, h1, h2⟩ := c8_generic_witness_junction ep _ _ hi hj
  exact ⟨w, (c8_edgeEquiv_symm_apply e₁).symm ▸ h1, (c8_edgeEquiv_symm_apply e₂).symm ▸ h2⟩

noncomputable def c8GenericStartRouting : GenericDecompMixedCoverStartRouting c8NestedGraph c8GenericHyp :=
  GenericDecompMixedCoverStartRouting.of_cover_primary_residual c8GenericCover
    (fun endpoint hstart hstep ⦃e₁ e₂⦄ hadj hjlast hin =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))
    (fun endpoint hstart hstep ⦃e₁ e₂⦄ hadj hin hjlast =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))
    (fun endpoint hstart hstep ⦃e₁ e₂⦄ hadj hjlast hjunc =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))
    (fun endpoint hstart hstep ⦃e₁ e₂⦄ hadj hjunc hjlast =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))
    (fun endpoint hstart hstep j ⦃e₁ e₂⦄ hadj hj₁ he₂ =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))
    (fun endpoint hstart hstep j ⦃e₁ e₂⦄ hadj he₁ hj₂ =>
      False.elim (c8_generic_startRouting_step_false endpoint hstart hstep))

noncomputable def c8GenericEndRouting : GenericDecompMixedCoverEndRouting c8NestedGraph c8GenericHyp :=
  GenericDecompMixedCoverEndRouting.of_cover_primary_residual c8GenericCover
    (fun endpoint hend hstep e₁ e₂ hadj hjlast hin =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_endRouting_longSegLast_incoming_fin endpoint _ _ hadj'
          (c8_generic_finLongSegLast_mem hjlast) (c8_generic_finIncoming_mem endpoint hin))
    (fun endpoint hend hstep e₁ e₂ hadj hin hjlast =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_endRouting_incoming_longSegLast_fin endpoint _ _ hadj'
          (c8_generic_finIncoming_mem endpoint hin) (c8_generic_finLongSegLast_mem hjlast))
    (fun endpoint hend hstep e₁ e₂ hadj hjlast hjunc =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_endRouting_longSegLast_junctionLineGraph_fin endpoint _ _ hadj'
          (c8_generic_finLongSegLast_mem hjlast)
          (c8_generic_finJunctionLineGraph_mem endpoint hjunc))
    (fun endpoint hend hstep e₁ e₂ hadj hjunc hjlast =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_endRouting_junctionLineGraph_longSegLast_fin endpoint _ _ hadj'
          (c8_generic_finJunctionLineGraph_mem endpoint hjunc)
          (c8_generic_finLongSegLast_mem hjlast))
    (fun endpoint hend hstep j e₁ e₂ hadj hj₁ he₂ =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_residual_longSeg_junction_fin endpoint j _ _ hadj'
          (c8_generic_finLongSeg_mem hj₁) (c8_generic_finEnriched_mem endpoint he₂))
    (fun endpoint hend hstep j e₁ e₂ hadj he₁ hj₂ =>
      c8_generic_endRouting_lift endpoint hend hstep hadj fun hadj' => by
        exact c8_pathDecomp_residual_junction_longSeg_fin endpoint j _ _ hadj'
          (c8_generic_finEnriched_mem endpoint he₁) (c8_generic_finLongSeg_mem hj₂))

theorem c8Generic_endGeometry_endpoint1 :
    c8NestedGraph.junctionEndpointStep 1 = c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx :=
  c8_pathDecomp_junctionStep_eq_arcOffset_onLongArc_endpoint1

theorem c8Generic_endGeometry_offLongArc_open :
    c8NestedGraph.junctionEndpointStep 0 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx ∧
      c8NestedGraph.junctionEndpointStep 2 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx ∧
        c8NestedGraph.junctionEndpointStep 3 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx := by
  refine ⟨?_, ?_, ?_⟩
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 0 (by decide)
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 2 (by decide)
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 3 (by decide)

theorem c8Generic_cover_junction_fragment
    {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w :=
  genericMixed_edgeCover_junction c8NestedGraph c8GenericHyp c8GenericCover hadj

theorem c8Generic_mixed_longSeg_junction_at_endJunction1
    {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂)
    (hL1 : edgeInLongSegBag c8NestedGraph c8GenericHyp e₁)
    (he₂ : e₂ ∈ c8GenericHyp.enrichedJunctionBag 1) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w := by
  obtain ⟨j, hj₁⟩ := hL1
  have hend : longArcEndJunctions 1 := by decide
  have hstep := c8Generic_endGeometry_endpoint1
  exact c8GenericEndRouting.residual_longSeg_junction 1 hend hstep j hadj hj₁ he₂

private theorem c8_generic_finJunction_witness (ep : Fin 4) (i j : Fin 10)
    (hi : i ∈ c8PathDecompFinEnrichedJunctionBag ep)
    (hj : j ∈ c8PathDecompFinEnrichedJunctionBag ep) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      c8GenericHyp.edgeBij.edgeEquiv i ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        c8GenericHyp.edgeBij.edgeEquiv j ∈ genericBagFamily c8NestedGraph c8GenericHyp w :=
  c8_generic_witness_junction ep i j hi hj

private theorem c8_generic_mixed_lift {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂)
    (fin_cover :
      c8PathDecompFinAdj (c8GenericHyp.edgeBij.edgeEquiv.symm e₁)
          (c8GenericHyp.edgeBij.edgeEquiv.symm e₂) →
        ∃ ep : Fin 4,
          c8GenericHyp.edgeBij.edgeEquiv.symm e₁ ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
            c8GenericHyp.edgeBij.edgeEquiv.symm e₂ ∈ c8PathDecompFinEnrichedJunctionBag ep) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w := by
  obtain ⟨ep, hi, hj⟩ := fin_cover (c8_generic_lineAdj_of_adj hadj)
  obtain ⟨w, h1, h2⟩ := c8_generic_finJunction_witness ep _ _ hi hj
  exact ⟨w, (c8_edgeEquiv_symm_apply e₁).symm ▸ h1, (c8_edgeEquiv_symm_apply e₂).symm ▸ h2⟩

private theorem c8_generic_finShortSeg_mem {shortArc : Fin 4} {hne : shortArc ≠ c8GenericHyp.arcIdx}
    {j : Fin (c8NestedGraph.cyclicGap shortArc)} {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ genericBagFamily c8NestedGraph c8GenericHyp (.shortSeg shortArc hne j)) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈
      c8PathDecompFinShortArcBag shortArc (c8_generic_shortArc_toFin2 shortArc j) := by
  exact c8_generic_shortArc_fin_mem (shortArc := shortArc) (hne := hne) he

private theorem c8_generic_finJunction_mem {endpoint : Fin 4}
    {e : c8NestedGraph.toSimpleGraph.edgeSet}
    (he : e ∈ c8GenericHyp.enrichedJunctionBag endpoint) :
    c8GenericHyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinEnrichedJunctionBag endpoint := by
  have he' : c8GenericHyp.edgeBij.edgeEquiv (c8GenericHyp.edgeBij.edgeEquiv.symm e) ∈
      c8GenericHyp.enrichedJunctionBag endpoint :=
    (c8_edgeEquiv_symm_apply e).symm ▸ he
  exact (c8_pathDecomp_enrichedJunctionBag_mem endpoint (c8GenericHyp.edgeBij.edgeEquiv.symm e)).mp he'

theorem c8Generic_startGeometry_offLongArc_open :
    c8NestedGraph.junctionEndpointStep 0 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx ∧
      c8NestedGraph.junctionEndpointStep 2 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx := by
  refine ⟨?_, ?_⟩
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 0 (by decide)
  · exact c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc 2 (by decide)

/-- OPEN hook for `GenericDecompMixedCoverStartGeometry.of_nested_with_offLongArc_open` at endpoints 0,2. -/
theorem c8Generic_startGeometry_offLongArc_hook_false (endpoint : Fin 4)
    (hstart : longArcStartJunctions endpoint)
    (hoff : c8NestedGraph.endpointArcIdx endpoint ≠ c8GenericHyp.arcIdx) :
    c8NestedGraph.junctionEndpointStep endpoint = c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx → False := by
  fin_cases endpoint <;> simp [longArcStartJunctions, c8_pathDecomp_endpointArcIdx,
    c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_junctionEndpointStep,
    c8_pathDecomp_arcEdgeOffset_longArc] at hstart hoff ⊢ <;>
    first | contradiction | decide

/-- Endpoint 1 end geometry (on-long-arc via nested pairing). Full `EndGeometry` blocked at endpoint 3. -/
theorem c8Generic_endGeometry_endpoint1_onLongArc :
    longArcEndJunctions 1 →
      c8NestedGraph.junctionEndpointStep 1 = c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx := by
  intro _
  exact c8Generic_endGeometry_endpoint1

/-- OPEN hook: endpoint 3 fails `junctionStep_eq_arcOffset` (step 4 ≠ arc offset 6). -/
theorem c8Generic_endGeometry_offLongArc_endpoint3_open :
    c8NestedGraph.junctionEndpointStep 3 ≠ c8NestedGraph.arcEdgeOffset c8GenericHyp.arcIdx := by
  simp [c8_pathDecomp_junctionEndpointStep, c8_pathDecomp_arcEdgeOffset_longArc]
  decide

noncomputable def c8GenericMixedCover : GenericDecompMixedCoverAssumptions c8NestedGraph c8GenericHyp where
  longSeg_junction := fun {e₁ e₂} hadj hL1 hJ2 => by
    obtain ⟨endpoint, he₂⟩ := hJ2
    obtain ⟨j, hj₁⟩ := hL1
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_longSeg_junction_fin j _ _
        hadj' (c8_generic_finLongSeg_mem hj₁)
        ⟨endpoint, c8_generic_finJunction_mem_from_bag he₂⟩
  junction_longSeg := fun {e₁ e₂} hadj hJ1 hL2 => by
    obtain ⟨endpoint, he₁⟩ := hJ1
    obtain ⟨j, hj₂⟩ := hL2
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_junction_longSeg_fin j _ _ hadj'
        ⟨endpoint, c8_generic_finJunction_mem_from_bag he₁⟩ (c8_generic_finLongSeg_mem hj₂)
  shortSeg_junction := fun shortArc hne {e₁ e₂} hadj hS1 hJ2 => by
    obtain ⟨endpoint, he₂⟩ := hJ2
    obtain ⟨j, hj₁⟩ := hS1
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_shortSeg_junction_fin shortArc (c8_generic_shortArc_toFin2 shortArc j) _ _
        hadj' (c8_generic_finShortSeg_mem (shortArc := shortArc) (hne := hne) hj₁)
        ⟨endpoint, c8_generic_finJunction_mem_from_bag he₂⟩
  junction_shortSeg := fun shortArc hne {e₁ e₂} hadj hJ1 hS2 => by
    obtain ⟨endpoint, he₁⟩ := hJ1
    obtain ⟨j, hj₂⟩ := hS2
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_junction_shortSeg_fin shortArc (c8_generic_shortArc_toFin2 shortArc j) _ _
        hadj' ⟨endpoint, c8_generic_finJunction_mem_from_bag he₁⟩
        (c8_generic_finShortSeg_mem (shortArc := shortArc) (hne := hne) hj₂)
  longSeg_shortSeg := fun {e₁ e₂} hadj hL1 hS2 => by
    obtain ⟨j, hj₁⟩ := hL1
    obtain ⟨shortArc, hne, j', hj₂⟩ := hS2
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_longSeg_shortSeg_fin j shortArc (c8_generic_shortArc_toFin2 shortArc j') _ _
        hadj' (c8_generic_finLongSeg_mem hj₁)
        (c8_generic_finShortSeg_mem (shortArc := shortArc) (hne := hne) hj₂)
  shortSeg_longSeg := fun {e₁ e₂} hadj hS1 hL2 => by
    obtain ⟨shortArc, hne, j, hj₁⟩ := hS1
    obtain ⟨j', hj₂⟩ := hL2
    exact c8_generic_mixed_lift hadj fun hadj' =>
      c8_pathDecomp_mixed_shortSeg_longSeg_fin shortArc (c8_generic_shortArc_toFin2 shortArc j) j' _ _
        hadj' (c8_generic_finShortSeg_mem (shortArc := shortArc) (hne := hne) hj₁)
        (c8_generic_finLongSeg_mem hj₂)

theorem c8Generic_edgeCover_of_cover_and_mixed
    {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
        e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w :=
  GenericDecompOpenGoals.edgeCover_of_cover_and_mixed c8GenericCover c8GenericMixedCover hadj

private theorem c8_generic_arcIdx_eq_three :
    c8GenericHyp.arcIdx = 3 := by
  dsimp [c8GenericHyp, c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock]
  exact c8NestedGraph_longArcIdx_eq_three

private theorem c8_generic_longArcLen :
    c8GenericHyp.longArcLen = 2 := by
  rw [NoncrossingPathDecompAssumptions.longArcLen, c8_generic_arcIdx_eq_three]
  simp [c8NestedGraph, CycleTwoChordGraph.cyclicGap]

private theorem c8_generic_junctionShortArcAt (endpoint : Fin 4) :
    c8NestedGraph.junctionShortArcAt c8GenericHyp.arcIdx endpoint =
      match endpoint with
      | 0 => some 0
      | 1 => none
      | 2 => some 1
      | 3 => some 2 := by
  rw [c8_generic_arcIdx_eq_three]
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.junctionShortArcAt, CycleTwoChordGraph.endpointArcIdx,
      c8NestedGraph, c8NestedGraph_pairing_nested] <;>
    decide

noncomputable def c8NestedGraph_genericDecompTreeShape : GenericDecompTreeShape c8NestedGraph c8GenericHyp where
  shortArc_attached := fun a hne => by
    rw [c8_generic_arcIdx_eq_three] at hne
    fin_cases a
    · exact ⟨0, by simp [c8_generic_junctionShortArcAt]⟩
    · exact ⟨2, by simp [c8_generic_junctionShortArcAt]⟩
    · exact ⟨3, by simp [c8_generic_junctionShortArcAt]⟩
    · exact absurd rfl hne
  shortArc_junction_unique := fun a hne e e' he he' => by
    rw [c8_generic_arcIdx_eq_three] at hne
    simp only [shortArcZeroJunction, c8_generic_arcIdx_eq_three, c8_generic_junctionShortArcAt] at he he'
    fin_cases a <;> simp at he he' <;> (try fin_cases e) <;> (try fin_cases e') <;> first | rfl | contradiction
  shortArc_gap_pos := fun a hne => by
    rw [c8_generic_arcIdx_eq_three] at hne
    fin_cases a <;> simp [c8_pathDecomp_shortArc_gap] at hne ⊢ <;> decide
  three_short_arc_endpoints := by
    dsimp [shortArcEndpointCount, c8NestedGraph, c8GenericHyp, c8_generic_arcIdx_eq_three,
      c8_generic_junctionShortArcAt]
    decide
  longArc_isTree :=
    NoncrossingPathDecompAssumptions.longArcCertPathGraph_isTree_of_two c8GenericHyp c8_generic_longArcLen

theorem c8Generic_isTree_of_shape :
    (genericDecompGraph c8NestedGraph c8GenericHyp).IsTree :=
  genericDecompGraph_isTree_of_shape_cardUpper c8NestedGraph_genericDecompTreeShape

private def c8_generic_vertexWitness (k : Fin 10) : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx :=
  match k with
  | 0 => .junction 0
  | 1 => .junction 0
  | 2 => .junction 2
  | 3 => .junction 2
  | 4 => .junction 3
  | 5 => .junction 3
  | 6 => .longSeg ⟨1, by decide⟩
  | 7 => .longSeg ⟨1, by decide⟩
  | 8 => .junction 0
  | 9 => .junction 2

private theorem c8_generic_vertexWitness_mem0 :
    c8GenericHyp.edgeBij.edgeEquiv 0 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 0) := by
  change _ ∈ genericBagFamily _ _ (.junction 0)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 0
    ((c8_pathDecomp_enrichedJunctionBag_mem 0 ⟨0, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem1 :
    c8GenericHyp.edgeBij.edgeEquiv 1 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 1) := by
  change _ ∈ genericBagFamily _ _ (.junction 0)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 0
    ((c8_pathDecomp_enrichedJunctionBag_mem 0 ⟨1, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem2 :
    c8GenericHyp.edgeBij.edgeEquiv 2 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 2) := by
  change _ ∈ genericBagFamily _ _ (.junction 2)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 2
    ((c8_pathDecomp_enrichedJunctionBag_mem 2 ⟨2, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem3 :
    c8GenericHyp.edgeBij.edgeEquiv 3 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 3) := by
  change _ ∈ genericBagFamily _ _ (.junction 2)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 2
    ((c8_pathDecomp_enrichedJunctionBag_mem 2 ⟨3, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem4 :
    c8GenericHyp.edgeBij.edgeEquiv 4 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 4) := by
  change _ ∈ genericBagFamily _ _ (.junction 3)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 3
    ((c8_pathDecomp_enrichedJunctionBag_mem 3 ⟨4, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem5 :
    c8GenericHyp.edgeBij.edgeEquiv 5 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 5) := by
  change _ ∈ genericBagFamily _ _ (.junction 3)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 3
    ((c8_pathDecomp_enrichedJunctionBag_mem 3 ⟨5, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem6 :
    c8GenericHyp.edgeBij.edgeEquiv 6 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 6) := by
  unfold c8_generic_vertexWitness
  exact genericBagFamily_longSeg_mem_of_line c8NestedGraph c8GenericHyp ⟨1, by decide⟩
    ((c8_pathDecomp_longArcBag_mem 1 ⟨6, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem7 :
    c8GenericHyp.edgeBij.edgeEquiv 7 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 7) := by
  unfold c8_generic_vertexWitness
  exact genericBagFamily_longSeg_mem_of_line c8NestedGraph c8GenericHyp ⟨1, by decide⟩
    ((c8_pathDecomp_longArcBag_mem 1 ⟨7, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem8 :
    c8GenericHyp.edgeBij.edgeEquiv 8 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 8) := by
  change _ ∈ genericBagFamily _ _ (.junction 0)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 0
    ((c8_pathDecomp_enrichedJunctionBag_mem 0 ⟨8, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem9 :
    c8GenericHyp.edgeBij.edgeEquiv 9 ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness 9) := by
  change _ ∈ genericBagFamily _ _ (.junction 2)
  exact genericBagFamily_junction_mem_of_enriched c8NestedGraph c8GenericHyp 2
    ((c8_pathDecomp_enrichedJunctionBag_mem 2 ⟨9, by decide⟩).mpr (by decide))

private theorem c8_generic_vertexWitness_mem (k : Fin 10) :
    c8GenericHyp.edgeBij.edgeEquiv k ∈
      genericBagFamily c8NestedGraph c8GenericHyp (c8_generic_vertexWitness k) := by
  fin_cases k
  · exact c8_generic_vertexWitness_mem0
  · exact c8_generic_vertexWitness_mem1
  · exact c8_generic_vertexWitness_mem2
  · exact c8_generic_vertexWitness_mem3
  · exact c8_generic_vertexWitness_mem4
  · exact c8_generic_vertexWitness_mem5
  · exact c8_generic_vertexWitness_mem6
  · exact c8_generic_vertexWitness_mem7
  · exact c8_generic_vertexWitness_mem8
  · exact c8_generic_vertexWitness_mem9

theorem c8Generic_vertexCover (e : c8NestedGraph.toSimpleGraph.edgeSet) :
    ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
      e ∈ genericBagFamily c8NestedGraph c8GenericHyp w := by
  let k := c8GenericHyp.edgeBij.edgeEquiv.symm e
  refine ⟨c8_generic_vertexWitness k, ?_⟩
  rw [← c8_edgeEquiv_symm_apply e]
  exact c8_generic_vertexWitness_mem k

theorem c8Generic_longSeg_preconnected_edge6 :
    (genericDecompGraph c8NestedGraph c8GenericHyp).induce
        ({w |
            (c8GenericHyp.edgeBij.edgeEquiv (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide))) ∈
              genericBagFamily c8NestedGraph c8GenericHyp w} ∩
          genericLongSegNodeSet c8NestedGraph c8GenericHyp) |>.Preconnected :=
  genericLongSeg_preconnected_of_interval c8NestedGraph c8GenericHyp
    (c8GenericHyp.edgeBij.edgeEquiv (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide)))
    0 1 (by decide) (by decide) (by decide) c8_pathDecomp_longArc_edge6_interval

theorem c8Generic_longSeg_preconnected_edge7 :
    (genericDecompGraph c8NestedGraph c8GenericHyp).induce
        ({w |
            (c8GenericHyp.edgeBij.edgeEquiv (c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide))) ∈
              genericBagFamily c8NestedGraph c8GenericHyp w} ∩
          genericLongSegNodeSet c8NestedGraph c8GenericHyp) |>.Preconnected :=
  genericLongSeg_preconnected_of_interval c8NestedGraph c8GenericHyp
    (c8GenericHyp.edgeBij.edgeEquiv (c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide)))
    0 1 (by decide) (by decide) (by decide) c8_pathDecomp_longArc_edge7_interval

noncomputable def c8GenericFinTransport : GenericDecompFinTransport c8NestedGraph c8GenericHyp :=
  mkGenericDecompFinTransport c8NestedGraph c8GenericHyp

private theorem c8_generic_decompNodeCount :
    genericDecompNodeCount c8NestedGraph c8GenericHyp = 12 := by
  dsimp [genericDecompNodeCount, c8_generic_longArcLen, c8_generic_arcIdx_eq_three]
  simp [genericShortArcGapSum, c8NestedGraph, CycleTwoChordGraph.cyclicGap] <;> decide

/-!
  c8 extended decomp (Strategy 1): bridge fin graph isomorphic to `c8GenericFinGraph` (11 edges),
  without mutating global `genericDecompAdj`. Standard-adj `c8GenericOpenGoals.preconnected` remains
  blocked (`c8GenericStandardFinPreconnectedBlocked`); extended bags + bridge tree close the cert.
-/

/-- c8-specific extended hypothesis: same NCP assumptions, bridge-revision Fin-12 tree. -/
structure C8ExtendedHyp where
  base : NoncrossingPathDecompAssumptions c8NestedGraph

noncomputable def c8ExtendedHyp : C8ExtendedHyp :=
  ⟨c8GenericHyp⟩

namespace C8Extended

noncomputable abbrev hyp : NoncrossingPathDecompAssumptions c8NestedGraph := c8ExtendedHyp.base

/-- Bridge fin tree (11 edges); NOT `genericDecompGraph` (8 standard-adj tree edges). -/
noncomputable def decompGraph : SimpleGraph (Fin 12) := c8GenericFinGraph

/-- Bridge-revision bags on Fin 12, mapped to line-graph vertices. -/
noncomputable def bagFamily (w : Fin 12) : Set c8NestedGraph.toSimpleGraph.edgeSet :=
  {e | hyp.edgeBij.edgeEquiv.symm e ∈ c8PathDecompFinGenericBag w}

private theorem bagFamily_mem (w : Fin 12) (k : Fin 10) :
    hyp.edgeBij.edgeEquiv k ∈ bagFamily w ↔ k ∈ c8PathDecompFinGenericBag w := by
  simp only [bagFamily, Set.mem_setOf_eq]
  rw [hyp.edgeBij.edgeEquiv.symm_apply_apply k]
  rfl

theorem vertexCover (e : c8NestedGraph.toSimpleGraph.edgeSet) :
    ∃ w : Fin 12, e ∈ bagFamily w := by
  let k := hyp.edgeBij.edgeEquiv.symm e
  obtain ⟨w, hw⟩ := c8_pathDecomp_genericFinVertexCover k
  refine ⟨w, ?_⟩
  rw [← c8_edgeEquiv_symm_apply e]
  exact (bagFamily_mem w k).mpr hw

theorem edgeCover {e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet}
    (hadj : (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂) :
    ∃ w : Fin 12, e₁ ∈ bagFamily w ∧ e₂ ∈ bagFamily w := by
  let i := hyp.edgeBij.edgeEquiv.symm e₁
  let j := hyp.edgeBij.edgeEquiv.symm e₂
  have hadj' := c8_generic_lineAdj_of_adj hadj
  obtain ⟨w, hi, hj⟩ := c8_pathDecomp_genericFinEdgeCover i j hadj'
  refine ⟨w, ?_, ?_⟩
  · rw [← c8_edgeEquiv_symm_apply e₁]
    exact (bagFamily_mem w i).mpr hi
  · rw [← c8_edgeEquiv_symm_apply e₂]
    exact (bagFamily_mem w j).mpr hj

private def overlapNodeSet (k : Fin 10) : Set (Fin 12) :=
  {w | hyp.edgeBij.edgeEquiv k ∈ bagFamily w}

private theorem overlapNodeSet_eq_interval (k : Fin 10) :
    overlapNodeSet k = (c8PathDecompFinGenericNodeInterval k : Set (Fin 12)) := by
  ext w
  simp only [overlapNodeSet, bagFamily, Set.mem_setOf_eq]
  rw [hyp.edgeBij.edgeEquiv.symm_apply_apply k]
  exact (c8_pathDecomp_genericFinNodeSet k w)

theorem preconnected (e : c8NestedGraph.toSimpleGraph.edgeSet) :
    decompGraph.induce (overlapNodeSet (hyp.edgeBij.edgeEquiv.symm e)) |>.Preconnected := by
  let k := hyp.edgeBij.edgeEquiv.symm e
  rw [overlapNodeSet_eq_interval k]
  exact c8_pathDecomp_genericFinPreconnected k

private theorem decompGraph_isTree : decompGraph.IsTree :=
  c8GenericFinGraph_isTree

/-- Extended decomp graph (bridge fin tree, 11 edges). -/
noncomputable abbrev c8ExtendedDecompGraph : SimpleGraph (Fin 12) := decompGraph

/-- Extended bag family (bridge-revision Fin-12 bags). -/
noncomputable abbrev c8ExtendedBagFamily : Fin 12 → Set c8NestedGraph.toSimpleGraph.edgeSet := bagFamily

/-- Open goals on extended decomp (mirrors `GenericDecompOpenGoals` fields). -/
structure OpenGoals where
  edgeCover :
    ∀ ⦃e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet⦄,
      (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : Fin 12, e₁ ∈ bagFamily w ∧ e₂ ∈ bagFamily w
  vertexCover :
    ∀ e : c8NestedGraph.toSimpleGraph.edgeSet, ∃ w : Fin 12, e ∈ bagFamily w
  preconnected :
    ∀ e : c8NestedGraph.toSimpleGraph.edgeSet,
      decompGraph.induce {w | e ∈ bagFamily w} |>.Preconnected
  isTree : decompGraph.IsTree

theorem openGoals : OpenGoals where
  edgeCover := fun {e₁ e₂} hadj => edgeCover hadj
  vertexCover := vertexCover
  preconnected := fun e => by
    have hset : {w | e ∈ bagFamily w} = overlapNodeSet (hyp.edgeBij.edgeEquiv.symm e) := by
      ext w
      simp only [Set.mem_setOf_eq, overlapNodeSet, bagFamily]
      rw [c8_edgeEquiv_symm_apply e]
    rw [hset]
    exact preconnected e
  isTree := decompGraph_isTree

end C8Extended

/-- Extended open goals bundle (standard-adj preconnected blocked; bridge fin closes cert). -/
theorem c8ExtendedOpenGoals : C8Extended.OpenGoals := C8Extended.openGoals

/-- Alias: extended open goals replace blocked standard-adj `GenericDecompOpenGoals`. -/
noncomputable abbrev C8ExtendedOpenGoals : C8Extended.OpenGoals := c8ExtendedOpenGoals

theorem genericConditionalHasTreeDecomp_c8NestedGraph :
    genericConditionalHasTreeDecomp c8NestedGraph c8GenericHyp := by
  dsimp [genericConditionalHasTreeDecomp]
  exact c8NestedGraph_lineGraph_hasTreeDecomp_three

/-- Standard-adj `GenericDecompOpenGoals.preconnected` blocked; cover/tree partial on `genericDecompGraph`. -/
theorem c8GenericOpenGoals_standardAdj_partial :
    (∀ ⦃e₁ e₂ : c8NestedGraph.toSimpleGraph.edgeSet⦄,
        (lineGraph c8NestedGraph.toSimpleGraph).Adj e₁ e₂ →
          ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
            e₁ ∈ genericBagFamily c8NestedGraph c8GenericHyp w ∧
              e₂ ∈ genericBagFamily c8NestedGraph c8GenericHyp w) ∧
      (∀ e : c8NestedGraph.toSimpleGraph.edgeSet,
        ∃ w : GenericDecompNode c8NestedGraph c8GenericHyp.arcIdx,
          e ∈ genericBagFamily c8NestedGraph c8GenericHyp w) ∧
        (genericDecompGraph c8NestedGraph c8GenericHyp).IsTree := by
  refine ⟨fun {e₁ e₂} hadj => c8Generic_edgeCover_of_cover_and_mixed hadj, ?_, c8Generic_isTree_of_shape⟩
  exact c8Generic_vertexCover

/-- Junction-bridge topology witness (card bound for enriched ∪ longSeg head). -/
theorem c8Generic_bridgeBagRevision_witness :
    (c8GenericHyp.enrichedJunctionBag 0).card + 2 ≤ 6 ∧
      (c8GenericHyp.enrichedJunctionBag 2).card + 2 ≤ 6 := by
  constructor
  · have hj := c8_pathDecomp_enrichedJunctionBag_card_endpoint0
    dsimp [c8GenericHyp] at hj ⊢
    exact Nat.le_trans (Nat.add_le_add_right hj 2) (by decide : 4 + 2 ≤ 6)
  · have hj := c8_pathDecomp_enrichedJunctionBag_card_endpoint2
    exact Nat.le_trans (Nat.add_le_add_right hj 2) (by decide : 4 + 2 ≤ 6)

/-- Bridge-revision bag scaffold; junction extension for edge 5 at endpoints 0/2 is baked into
    `c8PathDecompFinGenericBag` nodes 8 and 10 (cf. enriched `{0,1,7,8}` / `{1,2,3,9}`). -/
theorem c8Generic_bridgeRevision_bags_include_edge5 :
    (5 : Fin 10) ∈ c8PathDecompFinGenericBag 8 ∧ (5 : Fin 10) ∈ c8PathDecompFinGenericBag 10 := by
  decide

/-- On standard `genericDecompAdj`, overlap RI remains blocked for six fin indices even with
    bridge-revision bags; junction-bridge edges in `c8GenericFinGraph` are necessary. -/
theorem c8Generic_standardAdj_preconnected_blocked (k : Fin 10)
    (hk : k ∈ c8GenericStandardFinPreconnectedBlocked) :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval k : Set (Fin 12)) |>.Preconnected) :=
  c8_pathDecomp_genericStandardFinPreconnected_fail k hk

def c8NestedGraph_genericDecompSmokeDoc : String :=
  "PROVED: c8ExtendedHyp, c8ExtendedOpenGoals (bridge fin 11-edge tree), " ++
  "genericConditionalHasTreeDecomp_c8NestedGraph (CertificatesLine); " ++
  "PARTIAL: c8GenericOpenGoals on standard genericDecompAdj (preconnected blocked, 6/10); " ++
  "PROVED: c8Generic_vertexCover, c8Generic_isTree_of_shape, cover/mixed/edgeCover, c8GenericFinTransport; " ++
  "PROVED (NCP): c8_pathDecomp_genericFinPreconnected, c8_pathDecomp_genericFinEdgeCover; " ++
  "PROVED (negative): c8GenericStandardFinPreconnectedBlocked."

end GenericDecomp

def genericDecompDoc : String :=
  "PROVED: GenericDecompNode, segment↔certPathGraph adj, junction glue, card_balance, " ++
  "genericBagSupWidth≤3, genericBagFamily_width_le_sup, genericTreeDecomp Fin transport, " ++
  "genericLongSeg/genericShortSeg_preconnected_of_interval, genericDecompGraph_connected_of_shape, " ++
  "isTree_of_shape+card, GenericDecompCoverFromNoncrossing.of_noncrossingOpenGoals, cover fragment theorems, " ++
  "GenericDecompOpenGoals.of_cover_shape/of_cover_shape_and_remaining, " ++
  "genericConditionalHasTreeDecomp_of_cover_shape_and_remaining; " ++
  "PROVED: genericDecompNodeEncode bijection/mkGenericDecompFinTransport, genericDecompNodeCount_eq_card; " ++
  "PROVED (ALT): isTree_of_shape_and_acyclic, of_cover_shape_and_acyclic, genericDecompEdgeCount_le_card_edgeSet, " ++
  "isTree_of_shape_and_edgeCount_upper; " ++
  "PROVED (Route B): GenericDecompEdgeTag, genericDecompEdgeOfTag_mem_edgeSet, " ++
  "genericDecompEdgeTagIndex_lt, genericDecompEdgeTagIndex_shortChain_ne_shortBase, " ++
  "genericDecompEdgeTagIndex_injective, genericDecompEdgeOfTag_tagOfEdge, " ++
  "genericDecompEdgeFinIndex_injective, genericDecomp_card_edgeSet_le_edgeCount, " ++
  "GenericDecompOpenGoals.isTree_of_shape; " ++
  "PROVED (cover fragments): genericLongSeg_edgeCover_arcConsecutive/sameBag/sameBagIndex, " ++
  "genericLongSeg_lineGraphAdj_consecutive_edgeCover, genericLongSeg_vertexCover_arcEdge, " ++
  "genericShortSeg_edgeCover_sameBag, GenericDecompPreconnectedIntervalAssumptions.of_hyp, " ++
  "GenericDecompLongArcCoverAssumptions.of_noncrossingLineGraphBag, " ++
  "edgeInLongSegBag/edgeInJunctionBag/edgeInShortSegBag, genericMixed_edgeCover_junction/longArc/shortArc, " ++
  "genericMixed_longSeg_junction_end_of_tail, genericMixed_longSeg_junction_start_of_head, " ++
  "genericMixed_junction_longSeg_start_of_head, genericMixed_junction_longSeg_end_of_tail, " ++
  "genericMixed_longSeg_junction_start_of_head_longSegZero, " ++
  "genericMixed_longSeg_junction_end_of_tail_longSegLast, " ++
  "genericMixed_longSeg_junction_of_bothLongArc, genericMixed_shortSeg_junction_of_extra, " ++
  "longArcJunctionHeadBag, enrichedJunctionBag_mem_longArcHead, GenericDecompMixedCoverStartGeometry, " ++
  "GenericDecompMixedCoverEndGeometry, GenericDecompMixedCoverStartRouting, GenericDecompMixedCoverEndRouting, " ++
  "genericMixed_longSeg_junction_of_cover_start_end_routing, " ++
  "genericMixed_junction_longSeg_of_cover_start_end_routing, " ++
  "GenericDecompMixedCoverAssumptions.of_cover_start_end_routing, " ++
  "GenericDecompMixedCoverAssumptions, GenericDecompOpenGoals.edgeCover_of_cover_and_mixed; " ++
  "PROVED (step 3 routing): genericMixed_routing_of_enrichedJunction, genericMixed_startRouting_*, " ++
  "genericMixed_endRouting_*, GenericDecompMixedCoverStartRouting.of_cover_primary, " ++
  "GenericDecompMixedCoverEndRouting.of_cover_primary, genericMixed_shortSeg_junction_of_zero_*; " ++
  "PROVED/PARTIAL (step 4–5): GenericDecompMixedCoverGeometryOpenGoals, of_openGoals / of_nested_with_offLongArc_open builders, " ++
  "genericDecomp_startGeometry_endpoint_zero_of_arcIdx_zero, junctionStep_eq_arcOffset_at_zero_iff, " ++
  "junctionShortArcAt_none_iff, junctionEndpointStep_eq_arcEdgeOffset_endpointArcIdx_nested, " ++
  "genericDecomp_geometry_endpoint_of_endpointArcIdx_nested, " ++
  "genericMixed_*Residual_*_of_enrichedBoth/sameLongSeg/head/tail, of_cover_primary_residual (+ end), " ++
  "genericMixed_shortSeg_junction_of_zero_sameBag, genericMixed_shortSeg_junction_of_zero_route; " ++
  "genericShortSeg_edgeCover_arcConsecutive(_zero), genericShortSeg_lineGraphAdj_arcConsecutive(_zero), " ++
  "genericShortSeg_slidingBag_zero_adj_junction; c7 nested smoke partial (no edgeBij); " ++
  "PARTIAL (step 10): c8ExtendedOpenGoals PROVED (bridge fin); standard-adj preconnected OPEN (6/10); " ++
  "genericConditionalHasTreeDecomp_c8NestedGraph PROVED (CertificatesLine); " ++
  "c8Generic_vertexCover, c8Generic_isTree_of_shape, c8GenericFinTransport, c8Generic_standardAdj_preconnected_blocked; " ++
  "PARTIAL (step 7–8): c8GenericCover/routing/mixed/edgeCover; " ++
  "OPEN: full parametric geometry on crossing/disjoint/off-long-arc nested, residual interior/tail-only on general topology, " ++
  "shortSeg j=0 sliding edge without overlap, c5/c6 NCP smoke (crossing), junction_shortSeg, " ++
  "longSeg_shortSeg, shortSeg_longSeg; junction/mixed preconnected."

end PNPLab.ChordWidth
