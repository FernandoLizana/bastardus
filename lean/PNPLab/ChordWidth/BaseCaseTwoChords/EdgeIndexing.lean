/-
  Stable cyclic edge indexing for C_n + two chords (Route F+A pilot).

  Canonical order: n cycle edges from p0 forward, then chord1, chord2.
  Matches path-decomposition bag order along cyclic arcs; smoke certificates use sorted
  `Sym2` order in `CertificatesLine.lean` (different bijection, same |E(G)| = n+2).
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.ModEq
import PNPLab.ChordWidth.BaseCaseTwoChords.ArcLengths
import PNPLab.ChordWidth.BaseCaseTwoChords.DegreeBounds
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.LineGraph
import PNPLab.ChordWidth.TreeDecomp.CertificatesLine

namespace PNPLab.ChordWidth

open SimpleGraph
open SmokeLineGraphCert

/-!
  ## Fin (n+2) ↔ edges of G (combinatorial indexing)
-/

def CycleTwoChordGraph.chord1Sym2 (g : CycleTwoChordGraph) : Sym2 (Fin g.n) :=
  s(⟨g.chord1.1, g.chord1_fst_lt⟩, ⟨g.chord1.2, g.chord1_snd_lt⟩)

def CycleTwoChordGraph.chord2Sym2 (g : CycleTwoChordGraph) : Sym2 (Fin g.n) :=
  s(⟨g.chord2.1, g.chord2_fst_lt⟩, ⟨g.chord2.2, g.chord2_snd_lt⟩)

def CycleTwoChordGraph.cyclicCycleEdgeSym2 (g : CycleTwoChordGraph) (k : Nat) (_hk : k < g.n) :
    Sym2 (Fin g.n) :=
  s(g.cyclicEndpointFin k, g.cyclicEndpointFin (k + 1))

def CycleTwoChordGraph.graphEdgeSym2 (g : CycleTwoChordGraph) (k : Fin (g.n + 2)) : Sym2 (Fin g.n) :=
  if h : k.val < g.n then g.cyclicCycleEdgeSym2 k.val h
  else if _h' : k.val = g.n then g.chord1Sym2
  else g.chord2Sym2

def CycleTwoChordGraph.chord1EdgeIndex (g : CycleTwoChordGraph) : Fin (g.n + 2) :=
  ⟨g.n, by omega⟩

def CycleTwoChordGraph.chord2EdgeIndex (g : CycleTwoChordGraph) : Fin (g.n + 2) :=
  ⟨g.n + 1, by omega⟩

def CycleTwoChordGraph.cycleEdgeGlobalIndexAt (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n) :
    Fin (g.n + 2) :=
  ⟨k, by omega⟩

theorem CycleTwoChordGraph.graphEdgeSym2_eq_chord1 (g : CycleTwoChordGraph) :
    g.graphEdgeSym2 g.chord1EdgeIndex = g.chord1Sym2 := by
  simp [graphEdgeSym2, chord1EdgeIndex]

theorem CycleTwoChordGraph.graphEdgeSym2_eq_chord2 (g : CycleTwoChordGraph) :
    g.graphEdgeSym2 g.chord2EdgeIndex = g.chord2Sym2 := by
  simp [graphEdgeSym2, chord2EdgeIndex]

theorem CycleTwoChordGraph.chord1EdgeIndex_val (g : CycleTwoChordGraph) :
    g.chord1EdgeIndex.val = g.n :=
  rfl

theorem CycleTwoChordGraph.chord2EdgeIndex_val (g : CycleTwoChordGraph) :
    g.chord2EdgeIndex.val = g.n + 1 :=
  rfl

theorem CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val (g : CycleTwoChordGraph) (k : Nat)
    (hk : k < g.n) : (g.cycleEdgeGlobalIndexAt k hk).val = k :=
  rfl

theorem CycleTwoChordGraph.graphEdgeSym2_cycleEdgeGlobalIndexAt (g : CycleTwoChordGraph) (k : Nat)
    (hk : k < g.n) :
    g.graphEdgeSym2 (g.cycleEdgeGlobalIndexAt k hk) = g.cyclicCycleEdgeSym2 k hk := by
  simp [graphEdgeSym2, cycleEdgeGlobalIndexAt, hk]

/-!
  ## Arc offsets (pairing-independent; from ArcLengths)
-/

def CycleTwoChordGraph.arcEdgeOffset (g : CycleTwoChordGraph) : Fin 4 → Nat
  | 0 => 0
  | 1 => g.cyclicGap 0
  | 2 => g.cyclicGap 0 + g.cyclicGap 1
  | 3 => g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 2

theorem CycleTwoChordGraph.arcEdgeOffset_add_lt (g : CycleTwoChordGraph) (a : Fin 4) (j : Nat)
    (hj : j < g.cyclicGap a) : g.arcEdgeOffset a + j < g.n := by
  have _ := g.cyclicGaps_sum
  fin_cases a <;> simp [arcEdgeOffset, cyclicGap] at * <;> omega

def CycleTwoChordGraph.arcEdgeGlobalIndex (g : CycleTwoChordGraph) (a : Fin 4) (j : Nat)
    (hj : j < g.cyclicGap a) : Fin (g.n + 2) :=
  ⟨g.arcEdgeOffset a + j, by
    have := g.arcEdgeOffset_add_lt a j hj
    omega⟩

theorem CycleTwoChordGraph.arcEdgeOffset_four (g : CycleTwoChordGraph) :
    g.arcEdgeOffset 3 + g.cyclicGap 3 = g.n := by
  have h := g.cyclicGaps_sum
  simp [arcEdgeOffset, cyclicGap] at h ⊢
  exact h

theorem CycleTwoChordGraph.arcEdgeGlobalIndex_is_graphEdgeIndex (g : CycleTwoChordGraph) (a : Fin 4)
    (j : Nat) (hj : j < g.cyclicGap a) :
    (g.arcEdgeGlobalIndex a j hj).val = g.arcEdgeOffset a + j :=
  rfl

/-!
  ## Membership in `G.edgeSet` (generic)

  Cycle/chord edges are structurally in `toSimpleGraphNoncrossing` (`sup_adj` + `edge_adj`).
  `cyclicEdgeInGraph_of` (DegreeBounds) removes the per-step hypothesis.
-/

theorem CycleTwoChordGraph.cyclicCycleEdge_mem (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n) :
    g.cyclicCycleEdgeSym2 k hk ∈ g.toSimpleGraph.edgeSet := by
  apply (mem_edgeSet _).mpr
  rw [g.toSimpleGraph_eq_noncrossing]
  simp [toSimpleGraphNoncrossing]
  exact Or.inl (Or.inl (g.cyclicEdgeInGraph_of k))

theorem CycleTwoChordGraph.cyclicCycleEdgeSym2_of_cycleGraph_adj (g : CycleTwoChordGraph)
    {u v : Fin g.n} (hadj : (cycleGraph g.n).Adj u v) :
    ∃ k hk, g.cyclicCycleEdgeSym2 k hk = s(u, v) := by
  have hmod := g.fin_cycleAdj_nat_mod hadj
  rcases hmod with huv | hvu
  · refine ⟨g.cyclicStepOfFin u, g.cyclicStepOfFin_lt u, ?_⟩
    simp only [cyclicCycleEdgeSym2, Sym2.eq_iff]
    refine Or.inl ⟨?_, ?_⟩
    · exact g.cyclicEndpointFin_cyclicStepOfFin u
    · calc g.cyclicEndpointFin (g.cyclicStepOfFin u + 1)
          _ = g.cyclicEndpointFinNext (g.cyclicEndpointFin (g.cyclicStepOfFin u)) :=
            g.cyclicEndpointFin_succ (g.cyclicStepOfFin u)
          _ = g.cyclicEndpointFinNext u := by rw [g.cyclicEndpointFin_cyclicStepOfFin u]
          _ = v := g.cyclicEndpointFinNext_of_mod huv
  · refine ⟨g.cyclicStepOfFin v, g.cyclicStepOfFin_lt v, ?_⟩
    simp only [cyclicCycleEdgeSym2, Sym2.eq_iff]
    refine Or.inr ⟨?_, ?_⟩
    · exact g.cyclicEndpointFin_cyclicStepOfFin v
    · calc g.cyclicEndpointFin (g.cyclicStepOfFin v + 1)
          _ = g.cyclicEndpointFinNext (g.cyclicEndpointFin (g.cyclicStepOfFin v)) :=
            g.cyclicEndpointFin_succ (g.cyclicStepOfFin v)
          _ = g.cyclicEndpointFinNext v := by rw [g.cyclicEndpointFin_cyclicStepOfFin v]
          _ = u := g.cyclicEndpointFinNext_of_mod hvu

theorem CycleTwoChordGraph.graphEdgeSym2_mem_cycle (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n) :
    g.graphEdgeSym2 (g.cycleEdgeGlobalIndexAt k hk) ∈ g.toSimpleGraph.edgeSet := by
  simpa [graphEdgeSym2_cycleEdgeGlobalIndexAt] using g.cyclicCycleEdge_mem k hk

theorem CycleTwoChordGraph.chord1Sym2_mem (g : CycleTwoChordGraph) :
    g.chord1Sym2 ∈ g.toSimpleGraph.edgeSet := by
  apply (mem_edgeSet _).mpr
  rw [g.toSimpleGraph_eq_noncrossing]
  simp only [toSimpleGraphNoncrossing, sup_adj]
  refine Or.inl (Or.inr ?_)
  exact (edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, Fin.ne_of_val_ne g.chord1_fst_ne_snd⟩

theorem CycleTwoChordGraph.chord2Sym2_mem (g : CycleTwoChordGraph) :
    g.chord2Sym2 ∈ g.toSimpleGraph.edgeSet := by
  apply (mem_edgeSet _).mpr
  rw [g.toSimpleGraph_eq_noncrossing]
  simp only [toSimpleGraphNoncrossing, sup_adj]
  refine Or.inr ?_
  exact (edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, Fin.ne_of_val_ne g.chord2_fst_ne_snd⟩

theorem CycleTwoChordGraph.graphEdgeSym2_mem (g : CycleTwoChordGraph) (k : Fin (g.n + 2)) :
    g.graphEdgeSym2 k ∈ g.toSimpleGraph.edgeSet := by
  by_cases h : k.val < g.n
  · simpa [graphEdgeSym2, cycleEdgeGlobalIndexAt, h] using
      g.graphEdgeSym2_mem_cycle k.val h
  · by_cases h' : k.val = g.n
    · simpa [graphEdgeSym2, cycleEdgeGlobalIndexAt, h, h', graphEdgeSym2_eq_chord1] using
        g.chord1Sym2_mem
    · have h2 : k.val = g.n + 1 := by omega
      simpa [graphEdgeSym2, cycleEdgeGlobalIndexAt, h, h', h2, graphEdgeSym2_eq_chord2] using
        g.chord2Sym2_mem

theorem CycleTwoChordGraph.graphEdgeSym2_mem_chord1 (g : CycleTwoChordGraph) :
    g.graphEdgeSym2 g.chord1EdgeIndex ∈ g.toSimpleGraph.edgeSet := by
  rw [graphEdgeSym2_eq_chord1]
  exact g.chord1Sym2_mem

theorem CycleTwoChordGraph.graphEdgeSym2_mem_chord2 (g : CycleTwoChordGraph) :
    g.graphEdgeSym2 g.chord2EdgeIndex ∈ g.toSimpleGraph.edgeSet := by
  rw [graphEdgeSym2_eq_chord2]
  exact g.chord2Sym2_mem

theorem CycleTwoChordGraph.cyclicEndpointFin_eq_mod (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (h : g.cyclicEndpointFin k₁ = g.cyclicEndpointFin k₂) :
    g.p0 + k₁ ≡ g.p0 + k₂ [MOD g.n] :=
  Fin.ext_iff.mp h

theorem CycleTwoChordGraph.cyclicEndpointFin_eq_mod_cancel (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (h : g.cyclicEndpointFin k₁ = g.cyclicEndpointFin k₂) :
    k₁ ≡ k₂ [MOD g.n] := by
  have := g.cyclicEndpointFin_eq_mod h
  exact Nat.ModEq.add_left_cancel' g.p0 this

theorem CycleTwoChordGraph.cyclicEndpointFin_injective (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (hk₁ : k₁ < g.n) (hk₂ : k₂ < g.n) (h : g.cyclicEndpointFin k₁ = g.cyclicEndpointFin k₂) :
    k₁ = k₂ := by
  have heq : (g.p0 + k₁) % g.n = (g.p0 + k₂) % g.n := Fin.ext_iff.mp h
  have hmod : g.p0 + k₁ ≡ g.p0 + k₂ [MOD g.n] := heq
  have hkm : k₁ ≡ k₂ [MOD g.n] := Nat.ModEq.add_left_cancel' g.p0 hmod
  rw [Nat.ModEq, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hkm
  exact hkm

theorem CycleTwoChordGraph.cyclicEndpointFin_succ_injective (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (hk₁ : k₁ + 1 < g.n) (hk₂ : k₂ + 1 < g.n)
    (h : g.cyclicEndpointFin (k₁ + 1) = g.cyclicEndpointFin (k₂ + 1)) : k₁ = k₂ := by
  exact Nat.succ.inj (g.cyclicEndpointFin_injective (by omega) (by omega) h)

theorem CycleTwoChordGraph.cyclicCycleEdgeSym2_injective (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (hk₁ : k₁ < g.n) (hk₂ : k₂ < g.n)
    (h : g.cyclicCycleEdgeSym2 k₁ hk₁ = g.cyclicCycleEdgeSym2 k₂ hk₂) : k₁ = k₂ := by
  simp only [cyclicCycleEdgeSym2, Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact g.cyclicEndpointFin_injective hk₁ hk₂ h1
  · exfalso
    have hn4 : 4 ≤ g.n := g.ordered_implies_n_ge_four
    have hmod1 : k₁ ≡ k₂ + 1 [MOD g.n] := g.cyclicEndpointFin_eq_mod_cancel h1
    have hmod2 : k₁ + 1 ≡ k₂ [MOD g.n] := g.cyclicEndpointFin_eq_mod_cancel h2
    have hstep : k₁ + 1 ≡ k₂ + 2 [MOD g.n] := Nat.ModEq.add_right 1 hmod1
    have hdiff : k₂ ≡ k₂ + 2 [MOD g.n] := hmod2.symm.trans hstep
    have hdiv : g.n ∣ 2 := by
      simpa using (Nat.modEq_iff_dvd' (Nat.le_add_right k₂ 2)).1 hdiff
    have hle : g.n ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    omega

theorem CycleTwoChordGraph.chord1Sym2_ne_chord2Sym2 (g : CycleTwoChordGraph) :
    g.chord1Sym2 ≠ g.chord2Sym2 := by
  intro h
  have hdisj := g.chord1_chord2_endpoints_disjoint
  simp only [chord1Sym2, chord2Sym2, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hdisj.1 (Fin.ext_iff.mp h1)
  · exact hdisj.2.2.1 (Fin.ext_iff.mp h2)

theorem CycleTwoChordGraph.chord1IsCycleEdge_of_eq_cyclicCycleEdgeSym2 (g : CycleTwoChordGraph)
    (k : Nat) (hk : k < g.n) (h : g.chord1Sym2 = g.cyclicCycleEdgeSym2 k hk) :
    g.chord1IsCycleEdge := by
  have hadj : (cycleGraph g.n).Adj (g.cyclicEndpointFin k) (g.cyclicEndpointFin (k + 1)) :=
    g.cyclicEdgeInGraph_of k
  simp only [chord1Sym2, cyclicCycleEdgeSym2, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2] at hadj
    exact g.chord1IsCycleEdge_of_cycle_adj hadj
  · rw [← h1, ← h2] at hadj
    exact g.chord1IsCycleEdge_of_cycle_adj hadj.symm

theorem CycleTwoChordGraph.chord2IsCycleEdge_of_eq_cyclicCycleEdgeSym2 (g : CycleTwoChordGraph)
    (k : Nat) (hk : k < g.n) (h : g.chord2Sym2 = g.cyclicCycleEdgeSym2 k hk) :
    g.chord2IsCycleEdge := by
  have hadj : (cycleGraph g.n).Adj (g.cyclicEndpointFin k) (g.cyclicEndpointFin (k + 1)) :=
    g.cyclicEdgeInGraph_of k
  simp only [chord2Sym2, cyclicCycleEdgeSym2, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2] at hadj
    exact g.chord2IsCycleEdge_of_cycle_adj hadj
  · rw [← h1, ← h2] at hadj
    exact g.chord2IsCycleEdge_of_cycle_adj hadj.symm

theorem CycleTwoChordGraph.chord1Sym2_ne_cyclicCycleEdgeSym2 (g : CycleTwoChordGraph)
    (hnd : g.isNondegenerate) (k : Nat) (hk : k < g.n) :
    g.chord1Sym2 ≠ g.cyclicCycleEdgeSym2 k hk :=
  fun h => hnd.1 (g.chord1IsCycleEdge_of_eq_cyclicCycleEdgeSym2 k hk h)

theorem CycleTwoChordGraph.chord2Sym2_ne_cyclicCycleEdgeSym2 (g : CycleTwoChordGraph)
    (hnd : g.isNondegenerate) (k : Nat) (hk : k < g.n) :
    g.chord2Sym2 ≠ g.cyclicCycleEdgeSym2 k hk :=
  fun h => hnd.2 (g.chord2IsCycleEdge_of_eq_cyclicCycleEdgeSym2 k hk h)

theorem CycleTwoChordGraph.mem_toSimpleGraph_edgeSet_elim (g : CycleTwoChordGraph)
    (e : Sym2 (Fin g.n)) (he : e ∈ g.toSimpleGraph.edgeSet) :
    e ∈ (cycleGraph g.n).edgeSet ∨ e = g.chord1Sym2 ∨ e = g.chord2Sym2 :=
  Sym2.inductionOn e (fun u v he => by
    rw [mem_edgeSet, g.toSimpleGraph_eq_noncrossing, g.toSimpleGraphNoncrossing_eq_sup,
      sup_adj] at he
    rcases he with he | he
    · rcases he with he | he
      · exact Or.inl ((mem_edgeSet _).2 he)
      · exact Or.inr (Or.inl (by
          obtain ⟨h, _⟩ := (edge_adj _ _ _ _).1 he
          rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · subst hu hv; rfl
          · subst hu hv; rw [chord1Sym2, Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (by
        obtain ⟨h, _⟩ := (edge_adj _ _ _ _).1 he
        rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst hu hv; rfl
        · subst hu hv; rw [chord2Sym2, Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩))) he

theorem CycleTwoChordGraph.graphEdgeSym2_injective (g : CycleTwoChordGraph)
    (hnd : g.isNondegenerate) {k₁ k₂ : Fin (g.n + 2)} (h : g.graphEdgeSym2 k₁ = g.graphEdgeSym2 k₂) :
    k₁ = k₂ := by
  apply Fin.ext
  by_cases hk₁ : k₁.val < g.n
  · by_cases hk₂ : k₂.val < g.n
    · have hcycle :
          g.cyclicCycleEdgeSym2 k₁.val hk₁ = g.cyclicCycleEdgeSym2 k₂.val hk₂ := by
        simpa [graphEdgeSym2, hk₁, hk₂] using h
      have heq : k₁.val = k₂.val :=
        g.cyclicCycleEdgeSym2_injective (hk₁ := hk₁) (hk₂ := hk₂) hcycle
      omega
    · by_cases hch : k₂.val = g.n
      · exfalso
        have heq := g.chord1Sym2_ne_cyclicCycleEdgeSym2 hnd k₁.val hk₁
        exact heq (by simpa [graphEdgeSym2, hk₁, hch, graphEdgeSym2_eq_chord1] using h.symm)
      · have h2 : k₂.val = g.n + 1 := by omega
        exfalso
        have heq := g.chord2Sym2_ne_cyclicCycleEdgeSym2 hnd k₁.val hk₁
        exact heq (by simpa [graphEdgeSym2, hk₁, h2, graphEdgeSym2_eq_chord2] using h.symm)
  · by_cases hch₁ : k₁.val = g.n
    · by_cases hk₂ : k₂.val < g.n
      · exfalso
        have heq := g.chord1Sym2_ne_cyclicCycleEdgeSym2 hnd k₂.val hk₂
        exact heq (by simpa [graphEdgeSym2, hch₁, hk₂, graphEdgeSym2_eq_chord1] using h)
      · by_cases hch₂ : k₂.val = g.n
        · omega
        · have h2 : k₂.val = g.n + 1 := by omega
          exfalso
          exact g.chord1Sym2_ne_chord2Sym2 <|
            by simpa [graphEdgeSym2, hch₁, h2, graphEdgeSym2_eq_chord1, graphEdgeSym2_eq_chord2] using h
    · have h1 : k₁.val = g.n + 1 := by omega
      by_cases hk₂ : k₂.val < g.n
      · exfalso
        have heq := g.chord2Sym2_ne_cyclicCycleEdgeSym2 hnd k₂.val hk₂
        exact heq (by simpa [graphEdgeSym2, h1, hk₂, graphEdgeSym2_eq_chord2] using h)
      · by_cases hch₂ : k₂.val = g.n
        · exfalso
          exact g.chord1Sym2_ne_chord2Sym2 <|
            by simpa [graphEdgeSym2, hch₂, h1, graphEdgeSym2_eq_chord1, graphEdgeSym2_eq_chord2] using h.symm
        · omega

theorem CycleTwoChordGraph.graphEdgeSym2_surj (g : CycleTwoChordGraph)
    (e : Sym2 (Fin g.n)) (he : e ∈ g.toSimpleGraph.edgeSet) :
    ∃ k : Fin (g.n + 2), g.graphEdgeSym2 k = e := by
  rcases g.mem_toSimpleGraph_edgeSet_elim e he with he | he | he
  · exact @Sym2.inductionOn (Fin g.n)
      (fun e' => e' ∈ (cycleGraph g.n).edgeSet → ∃ k : Fin (g.n + 2), g.graphEdgeSym2 k = e') e
      (fun u v hecy => by
        have hadj := (mem_edgeSet (G := cycleGraph g.n)).1 hecy
        obtain ⟨k, hk, hecycle⟩ := g.cyclicCycleEdgeSym2_of_cycleGraph_adj hadj
        exact ⟨g.cycleEdgeGlobalIndexAt k hk, by simpa [graphEdgeSym2_cycleEdgeGlobalIndexAt] using hecycle⟩)
      he
  · exact ⟨g.chord1EdgeIndex, by simpa [graphEdgeSym2_eq_chord1] using he.symm⟩
  · exact ⟨g.chord2EdgeIndex, by simpa [graphEdgeSym2_eq_chord2] using he.symm⟩

/-!
  ## Fin (n+2) index ↔ `G.edgeSet` vertex (L(G) vertex)
-/

def CycleTwoChordGraph.graphEdgeVertex (g : CycleTwoChordGraph) (k : Fin (g.n + 2))
    (h : g.graphEdgeSym2 k ∈ g.toSimpleGraph.edgeSet) : g.toSimpleGraph.edgeSet :=
  ⟨g.graphEdgeSym2 k, h⟩

theorem CycleTwoChordGraph.graphEdgeVertex_val (g : CycleTwoChordGraph) (k : Fin (g.n + 2))
    (h : g.graphEdgeSym2 k ∈ g.toSimpleGraph.edgeSet) :
    (g.graphEdgeVertex k h).val = g.graphEdgeSym2 k :=
  rfl

theorem CycleTwoChordGraph.graphEdgeVertex_lineGraph (g : CycleTwoChordGraph) (k : Fin (g.n + 2))
    (h : g.graphEdgeSym2 k ∈ g.toSimpleGraph.edgeSet) :
    (g.graphEdgeVertex k h : Sym2 (Fin g.n)) = g.graphEdgeSym2 k :=
  rfl

/-- Bijection certificate for `graphEdgeSym2` onto `G.edgeSet` (membership from `graphEdgeSym2_mem`). -/
structure GraphEdgeBijection (g : CycleTwoChordGraph) where
  edgeInj : ∀ {k₁ k₂ : Fin (g.n + 2)}, g.graphEdgeSym2 k₁ = g.graphEdgeSym2 k₂ → k₁ = k₂
  edgeSurj :
    ∀ e : Sym2 (Fin g.n), e ∈ g.toSimpleGraph.edgeSet →
      ∃ k : Fin (g.n + 2), g.graphEdgeSym2 k = e

theorem CycleTwoChordGraph.graphEdgeBijection (g : CycleTwoChordGraph) (hnd : g.isNondegenerate) :
    GraphEdgeBijection g where
  edgeInj := fun h => g.graphEdgeSym2_injective hnd h
  edgeSurj := g.graphEdgeSym2_surj

theorem CycleTwoChordGraph.arcConsecutive_graphEdgeSym2_share_vertex (g : CycleTwoChordGraph) (a : Fin 4)
    (j : Nat) (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    let base := g.arcEdgeOffset a + j
    g.cyclicEndpointFin (base + 1) ∈ g.cyclicCycleEdgeSym2 base (by
      have := g.arcEdgeOffset_add_lt a j hj; omega) ∧
      g.cyclicEndpointFin (base + 1) ∈ g.cyclicCycleEdgeSym2 (base + 1) (by
        have := g.arcEdgeOffset_add_lt a (j + 1) hj'; omega) := by
  dsimp [cyclicCycleEdgeSym2, Sym2.mem_iff]
  constructor <;> simp [cyclicEndpointFin, Nat.add_mod, Nat.add_assoc]

theorem CycleTwoChordGraph.arcEdgeOffset_succ_lt_n (g : CycleTwoChordGraph) (a : Fin 4)
    (p : Nat) (hp : p + 1 < g.cyclicGap a) :
    g.arcEdgeOffset a + p + 1 < g.n := by
  have := g.arcEdgeOffset_add_lt a (p + 1) hp
  simpa [Nat.add_assoc] using this

private theorem CycleTwoChordGraph.arcLocalPos_globalIndex_ne (g : CycleTwoChordGraph) (a : Fin 4)
    {p₁ p₂ : Nat} (hp₁ : p₁ < g.cyclicGap a) (hp₂ : p₂ < g.cyclicGap a) (hne : p₁ ≠ p₂) :
    g.arcEdgeOffset a + p₁ ≠ g.arcEdgeOffset a + p₂ := by
  intro h
  apply hne
  omega

private theorem CycleTwoChordGraph.cyclicEndpointFin_eq_of_eq_succ (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (hk₁ : k₁ < g.n) (hk₂succ : k₂ + 1 < g.n)
    (h : g.cyclicEndpointFin k₁ = g.cyclicEndpointFin (k₂ + 1)) : k₁ = k₂ + 1 :=
  g.cyclicEndpointFin_injective hk₁ hk₂succ h

private theorem CycleTwoChordGraph.cyclicEndpointFin_eq_of_succ_eq (g : CycleTwoChordGraph) {k₁ k₂ : Nat}
    (hk₁succ : k₁ + 1 < g.n) (hk₂ : k₂ < g.n)
    (h : g.cyclicEndpointFin (k₁ + 1) = g.cyclicEndpointFin k₂) : k₁ + 1 = k₂ :=
  g.cyclicEndpointFin_injective hk₁succ hk₂ h

private theorem CycleTwoChordGraph.cyclicEndpointFin_eq_zero (g : CycleTwoChordGraph) :
    g.cyclicEndpointFin g.n = g.cyclicEndpointFin 0 := by
  ext
  simp [cyclicEndpointFin, Nat.add_mod]

private theorem CycleTwoChordGraph.cyclicGap0_lt_n (g : CycleTwoChordGraph) : g.cyclicGap 0 < g.n := by
  have hsum := g.cyclicGaps_sum
  have h1 := g.cyclicGap_pos 1
  have h2 := g.cyclicGap_pos 2
  have h3 := g.cyclicGap_pos 3
  simp [cyclicGap] at hsum h1 h2 h3 ⊢
  omega

private theorem CycleTwoChordGraph.cyclicGap1_lt_n (g : CycleTwoChordGraph) : g.cyclicGap 1 < g.n := by
  have hsum := g.cyclicGaps_sum
  have h0 := g.cyclicGap_pos 0
  have h2 := g.cyclicGap_pos 2
  have h3 := g.cyclicGap_pos 3
  simp [cyclicGap] at hsum h0 h2 h3 ⊢
  omega

private theorem CycleTwoChordGraph.cyclicGap2_lt_n (g : CycleTwoChordGraph) : g.cyclicGap 2 < g.n := by
  have hsum := g.cyclicGaps_sum
  have h0 := g.cyclicGap_pos 0
  have h1 := g.cyclicGap_pos 1
  have h3 := g.cyclicGap_pos 3
  simp [cyclicGap] at hsum h0 h1 h3 ⊢
  omega

private theorem CycleTwoChordGraph.arcEdgeOffset_three_add_pos (g : CycleTwoChordGraph) (p : Nat) :
    0 < g.arcEdgeOffset 3 + p := by
  have h0 := g.cyclicGap_pos 0
  have h1 := g.cyclicGap_pos 1
  have h2 := g.cyclicGap_pos 2
  simp [arcEdgeOffset, cyclicGap] at h0 h1 h2 ⊢
  omega

private theorem CycleTwoChordGraph.arcEdgeOffset_add_succ_eq_n_arc (g : CycleTwoChordGraph) (a : Fin 4)
    (p : Nat) (hp : p < g.cyclicGap a) (h : g.arcEdgeOffset a + p + 1 = g.n) : a = 3 := by
  have hsum := g.cyclicGaps_sum
  have hgap0 := g.cyclicGap_pos 0
  have hgap1 := g.cyclicGap_pos 1
  have hgap2 := g.cyclicGap_pos 2
  have hgap3 := g.cyclicGap_pos 3
  fin_cases a
  · simp [arcEdgeOffset, cyclicGap] at h hp hsum hgap0 hgap1 hgap2 hgap3 ⊢
    have hnle : g.n ≤ g.p1 - g.p0 := by
      calc g.n = p + 1 := h.symm
          _ ≤ g.p1 - g.p0 := Nat.succ_le_of_lt hp
    exact absurd g.cyclicGap0_lt_n (Nat.not_lt_of_le hnle)
  · simp [arcEdgeOffset, cyclicGap] at h hp hsum hgap0 hgap1 hgap2 hgap3 ⊢
    exfalso
    omega
  · simp [arcEdgeOffset, cyclicGap] at h hp hsum hgap0 hgap1 hgap2 hgap3 ⊢
    exfalso
    omega
  · rfl

private theorem CycleTwoChordGraph.arcEdgeOffset_add_succ_eq_n_iff (g : CycleTwoChordGraph) (a : Fin 4)
    (p : Nat) (hp : p < g.cyclicGap a) (h : g.arcEdgeOffset a + p + 1 = g.n) :
    a = 3 ∧ p + 1 = g.cyclicGap a := by
  have ha3 := g.arcEdgeOffset_add_succ_eq_n_arc a p hp h
  have hsecond : p + 1 = g.cyclicGap a := by
    subst ha3
    simp [arcEdgeOffset, cyclicGap] at h hp ⊢
    have hoffset := g.arcEdgeOffset_four
    simp [arcEdgeOffset, cyclicGap] at hoffset
    omega
  exact ⟨ha3, hsecond⟩

/-- Shared endpoint on the same cyclic arc forces consecutive local positions.
    Handles arc-end wrap (`arcIdx = 3`, `p + 1 = cyclicGap`, global index `k + 1 = n`) by contradiction. -/
theorem CycleTwoChordGraph.arcLocalEdgePos_sharedVertex_consecutive (g : CycleTwoChordGraph) (a : Fin 4)
    {p₁ p₂ : Nat} (hp₁ : p₁ < g.cyclicGap a) (hp₂ : p₂ < g.cyclicGap a) (hne : p₁ ≠ p₂)
    {v : Fin g.n}
    (hv1 : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset a + p₁) (g.arcEdgeOffset_add_lt a p₁ hp₁))
    (hv2 : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset a + p₂) (g.arcEdgeOffset_add_lt a p₂ hp₂)) :
    p₁ + 1 = p₂ ∨ p₂ + 1 = p₁ := by
  set k₁ := g.arcEdgeOffset a + p₁
  set k₂ := g.arcEdgeOffset a + p₂
  have hk₁ : k₁ < g.n := g.arcEdgeOffset_add_lt a p₁ hp₁
  have hk₂ : k₂ < g.n := g.arcEdgeOffset_add_lt a p₂ hp₂
  have hkne : k₁ ≠ k₂ := g.arcLocalPos_globalIndex_ne a hp₁ hp₂ hne
  simp only [cyclicCycleEdgeSym2, Sym2.mem_iff] at hv1 hv2
  rcases hv1 with hv1 | hv1 <;> rcases hv2 with hv2 | hv2
  · exact absurd (g.cyclicEndpointFin_injective hk₁ hk₂ (hv1.symm.trans hv2)) hkne
  · right
    by_cases hk₂succ : k₂ + 1 < g.n
    · have h := g.cyclicEndpointFin_eq_of_eq_succ hk₁ hk₂succ (hv1.symm.trans hv2)
      omega
    · have hk₂succ' : k₂ + 1 = g.n := by omega
      have hkn : g.arcEdgeOffset a + p₂ + 1 = g.n := by simpa [k₂, Nat.add_assoc] using hk₂succ'
      obtain ⟨ha3, _⟩ := g.arcEdgeOffset_add_succ_eq_n_iff a p₂ hp₂ hkn
      subst ha3
      have hk₁pos : 0 < k₁ := by
        unfold k₁
        exact g.arcEdgeOffset_three_add_pos p₁
      have heq0 : g.cyclicEndpointFin k₁ = g.cyclicEndpointFin 0 := by
        calc g.cyclicEndpointFin k₁ = v := hv1.symm
            _ = g.cyclicEndpointFin (k₂ + 1) := hv2
            _ = g.cyclicEndpointFin g.n := by rw [hk₂succ']
            _ = g.cyclicEndpointFin 0 := g.cyclicEndpointFin_eq_zero
      exfalso
      exact hk₁pos.ne' (g.cyclicEndpointFin_injective hk₁ g.n_pos heq0)
  · left
    by_cases hk₁succ : k₁ + 1 < g.n
    · have h := g.cyclicEndpointFin_eq_of_succ_eq hk₁succ hk₂ (hv1.symm.trans hv2)
      omega
    · have hk₁succ' : k₁ + 1 = g.n := by omega
      have hkn : g.arcEdgeOffset a + p₁ + 1 = g.n := by simpa [k₁, Nat.add_assoc] using hk₁succ'
      obtain ⟨ha3, _⟩ := g.arcEdgeOffset_add_succ_eq_n_iff a p₁ hp₁ hkn
      subst ha3
      have hk₂pos : 0 < k₂ := by
        unfold k₂
        exact g.arcEdgeOffset_three_add_pos p₂
      have heq0 : g.cyclicEndpointFin k₂ = g.cyclicEndpointFin 0 := by
        calc g.cyclicEndpointFin k₂ = v := hv2.symm
            _ = g.cyclicEndpointFin (k₁ + 1) := hv1
            _ = g.cyclicEndpointFin g.n := by rw [hk₁succ']
            _ = g.cyclicEndpointFin 0 := g.cyclicEndpointFin_eq_zero
      exfalso
      exact hk₂pos.ne' (g.cyclicEndpointFin_injective hk₂ g.n_pos heq0)
  · by_cases hk₁s : k₁ + 1 < g.n <;> by_cases hk₂s : k₂ + 1 < g.n
    · · exact absurd (Nat.succ.inj (g.cyclicEndpointFin_injective hk₁s hk₂s (hv1.symm.trans hv2))) hkne
    · · have hk₂sn : k₂ + 1 = g.n := by omega
        exfalso
        have heqfin : g.cyclicEndpointFin (k₁ + 1) = g.cyclicEndpointFin 0 := by
          calc g.cyclicEndpointFin (k₁ + 1) = g.cyclicEndpointFin (k₂ + 1) := hv1.symm.trans hv2
              _ = g.cyclicEndpointFin g.n := by rw [hk₂sn]
              _ = g.cyclicEndpointFin 0 := g.cyclicEndpointFin_eq_zero
        have h0 : k₁ + 1 = 0 := g.cyclicEndpointFin_injective hk₁s g.n_pos heqfin
        exact Nat.succ_ne_zero k₁ h0
    · · have hk₁sn : k₁ + 1 = g.n := by omega
        exfalso
        have heqfin : g.cyclicEndpointFin (k₂ + 1) = g.cyclicEndpointFin 0 := by
          calc g.cyclicEndpointFin (k₂ + 1) = g.cyclicEndpointFin (k₁ + 1) := hv2.symm.trans hv1
              _ = g.cyclicEndpointFin g.n := by rw [hk₁sn]
              _ = g.cyclicEndpointFin 0 := g.cyclicEndpointFin_eq_zero
        have h0 : k₂ + 1 = 0 := g.cyclicEndpointFin_injective hk₂s g.n_pos heqfin
        exact Nat.succ_ne_zero k₂ h0
    · · exact absurd (Nat.succ.inj (by omega)) hkne

namespace GraphEdgeBijection

variable {g : CycleTwoChordGraph} (hidx : GraphEdgeBijection g)

noncomputable def edgeEquiv : Fin (g.n + 2) ≃ g.toSimpleGraph.edgeSet where
  toFun k := g.graphEdgeVertex k (g.graphEdgeSym2_mem k)
  invFun e :=
    Classical.choose (hidx.edgeSurj e.val e.property)
  left_inv k :=
    hidx.edgeInj (Classical.choose_spec (hidx.edgeSurj (g.graphEdgeSym2 k) (g.graphEdgeSym2_mem k)))
  right_inv e := by
    apply Subtype.ext
    exact Classical.choose_spec (hidx.edgeSurj e.val e.property)

theorem edgeEquiv_apply (k : Fin (g.n + 2)) :
    hidx.edgeEquiv k = g.graphEdgeVertex k (g.graphEdgeSym2_mem k) :=
  rfl

theorem edgeEquiv_symm_apply_val (e : g.toSimpleGraph.edgeSet) :
    g.graphEdgeSym2 (hidx.edgeEquiv.symm e) = e.val := by
  have := Classical.choose_spec (hidx.edgeSurj e.val e.property)
  exact this

theorem lineGraph_vertex_eq (k : Fin (g.n + 2)) :
    (hidx.edgeEquiv k : Sym2 (Fin g.n)) = g.graphEdgeSym2 k :=
  rfl

/-- Route F+A: edge index as a vertex of `lineGraph G` (Mathlib: vertices = `G.edgeSet`). -/
noncomputable def lineGraphVertex (k : Fin (g.n + 2)) : g.toSimpleGraph.edgeSet :=
  hidx.edgeEquiv k

theorem lineGraphVertex_eq_graphEdgeSym2 (k : Fin (g.n + 2)) :
    (hidx.lineGraphVertex k : Sym2 (Fin g.n)) = g.graphEdgeSym2 k :=
  hidx.lineGraph_vertex_eq k

theorem lineGraphVertex_mem_edgeSet (k : Fin (g.n + 2)) :
    (hidx.lineGraphVertex k : Sym2 (Fin g.n)) ∈ g.toSimpleGraph.edgeSet := by
  rw [lineGraphVertex_eq_graphEdgeSym2]
  exact g.graphEdgeSym2_mem k

theorem lineGraphAdj_of_shared_vertex {k₁ k₂ : Fin (g.n + 2)} (v : Fin g.n)
    (hv1 : v ∈ g.graphEdgeSym2 k₁) (hv2 : v ∈ g.graphEdgeSym2 k₂)
    (hne : k₁ ≠ k₂) :
    (lineGraph g.toSimpleGraph).Adj (hidx.lineGraphVertex k₁) (hidx.lineGraphVertex k₂) := by
  rw [lineGraph_adj_iff]
  refine ⟨fun heq => hne (hidx.edgeEquiv.injective heq), ⟨v, hv1, hv2⟩⟩

theorem arcConsecutive_lineGraphAdj (g : CycleTwoChordGraph) (hidx : GraphEdgeBijection g)
    (a : Fin 4) (j : Nat) (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    let base := g.arcEdgeOffset a + j
    (lineGraph g.toSimpleGraph).Adj
      (hidx.lineGraphVertex (g.cycleEdgeGlobalIndexAt base (by
        have := g.arcEdgeOffset_add_lt a j hj; omega)))
      (hidx.lineGraphVertex (g.cycleEdgeGlobalIndexAt (base + 1) (by
        have := g.arcEdgeOffset_add_lt a (j + 1) hj'; omega))) := by
  intro base
  have hk0 : base < g.n := by
    have := g.arcEdgeOffset_add_lt a j hj
    omega
  have hk1 : base + 1 < g.n := by
    have := g.arcEdgeOffset_add_lt a (j + 1) hj'
    omega
  have hshare := g.arcConsecutive_graphEdgeSym2_share_vertex a j hj hj'
  have hv1 :
      g.cyclicEndpointFin (base + 1) ∈
        g.graphEdgeSym2 (g.cycleEdgeGlobalIndexAt base hk0) := by
    rw [g.graphEdgeSym2_cycleEdgeGlobalIndexAt base hk0]
    exact hshare.1
  have hv2 :
      g.cyclicEndpointFin (base + 1) ∈
        g.graphEdgeSym2 (g.cycleEdgeGlobalIndexAt (base + 1) hk1) := by
    rw [g.graphEdgeSym2_cycleEdgeGlobalIndexAt (base + 1) hk1]
    exact hshare.2
  exact hidx.lineGraphAdj_of_shared_vertex (g.cyclicEndpointFin (base + 1)) hv1 hv2 <|
    Fin.ne_of_val_ne (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val])

end GraphEdgeBijection

/-!
  ## Combinatorial count ↔ Fintype.card (when equiv available)
-/

theorem CycleTwoChordGraph.graphEdgeCount_eq_card_of_equiv
    (g : CycleTwoChordGraph) (e : Fin (g.n + 2) ≃ g.toSimpleGraph.edgeSet) :
    g.graphEdgeCountNondegenerate = Fintype.card g.toSimpleGraph.edgeSet := by
  rw [CycleTwoChordGraph.graphEdgeCountNondegenerate_eq, ← Fintype.card_congr e, Fintype.card_fin]

/-!
  ## Smoke: |E(G)| = n+2 for c8 nested (via CertificatesLine equiv)
-/

theorem c8NestedGraph_graphEdgeCount_eq_card :
    c8NestedGraph.graphEdgeCountNondegenerate =
      Fintype.card c8NestedSmokeGraph.edgeSet := by
  have hcount : c8NestedGraph.graphEdgeCountNondegenerate = 10 := by
    rw [CycleTwoChordGraph.graphEdgeCountNondegenerate_eq]
    rfl
  have hcard : Fintype.card c8NestedSmokeGraph.edgeSet = 10 := by
    simpa [Fintype.card_fin] using Fintype.card_congr c8Nested_edgeEquiv.symm
  rw [hcount, hcard]

/-!
  ## Smoke: c8 nested `graphEdgeSym2` ↔ `L(G)` vertices
-/

theorem c8NestedGraph_graphEdgeSym2_mem_smoke (k : Fin 10) :
    c8NestedGraph.graphEdgeSym2 k ∈ c8NestedSmokeGraph.edgeSet := by
  fin_cases k <;> native_decide

theorem c8NestedGraph_graphEdgeSym2_mem (k : Fin 10) :
    c8NestedGraph.graphEdgeSym2 k ∈ c8NestedGraph.toSimpleGraph.edgeSet := by
  rw [c8NestedGraph_toSimpleGraph_eq_smoke]
  exact c8NestedGraph_graphEdgeSym2_mem_smoke k

theorem c8NestedGraph_graphEdgeSym2_injective :
    ∀ {k₁ k₂ : Fin 10}, c8NestedGraph.graphEdgeSym2 k₁ = c8NestedGraph.graphEdgeSym2 k₂ → k₁ = k₂ := by
  intro k₁ k₂ h
  fin_cases k₁ <;> fin_cases k₂ <;>
    simp [c8NestedGraph, CycleTwoChordGraph.graphEdgeSym2,
      CycleTwoChordGraph.cyclicCycleEdgeSym2, CycleTwoChordGraph.cyclicEndpointFin,
      CycleTwoChordGraph.chord1Sym2, CycleTwoChordGraph.chord2Sym2,
      CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2] at h ⊢ <;>
    first | rfl | contradiction

theorem c8NestedSmokeGraph_eq_c8SmokeGraph : c8NestedSmokeGraph = c8SmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c8NestedSmokeGraph, c8SmokeGraph]

theorem c8NestedGraph_graphEdgeSym2_surj (e : Sym2 (Fin c8NestedGraph.n))
    (he : e ∈ c8NestedGraph.toSimpleGraph.edgeSet) :
    ∃ k : Fin 10, c8NestedGraph.graphEdgeSym2 k = e := by
  rw [c8NestedGraph_toSimpleGraph_eq_smoke, c8NestedSmokeGraph_eq_c8SmokeGraph] at he
  obtain ⟨i, hi⟩ := (c8SmokeGraph_edgeInRange e).mp he
  fin_cases i <;> simp only [c8Nested_baseEdgeSym2] at hi <;> subst hi <;> native_decide

theorem c8NestedGraph_graphEdgeBijection : GraphEdgeBijection c8NestedGraph where
  edgeInj := c8NestedGraph_graphEdgeSym2_injective
  edgeSurj := c8NestedGraph_graphEdgeSym2_surj

theorem c8NestedGraph_graphEdgeCount_eq_card_via_graphEdgeBijection :
    c8NestedGraph.graphEdgeCountNondegenerate =
      Fintype.card c8NestedGraph.toSimpleGraph.edgeSet :=
  c8NestedGraph.graphEdgeCount_eq_card_of_equiv c8NestedGraph_graphEdgeBijection.edgeEquiv

/-!
  ## Smoke: c7 nested (degenerate — chord₂ = cycle edge (1,2); |edgeSet| = 8, combinatorial |E| = 9)

  `GraphEdgeBijection` needs `graphEdgeSym2` injective on `Fin (n+2)`; c7 fails at `k=1` vs `k=8`.
  Partial: mem + surj onto `edgeSet`; full bijection OPEN (needs nondegenerate spacing like c8's p₁+1≠p₂).
-/

theorem c7NestedGraph_graphEdgeCount_combinatorial :
    c7NestedGraph.graphEdgeCountNondegenerate = 9 := by
  rw [CycleTwoChordGraph.graphEdgeCountNondegenerate_eq]
  rfl

theorem c7NestedGraph_graphEdgeSym2_mem_smoke (k : Fin 9) :
    c7NestedGraph.graphEdgeSym2 k ∈ c7NestedSmokeGraph.edgeSet := by
  fin_cases k <;> native_decide

theorem c7NestedGraph_graphEdgeSym2_mem (k : Fin 9) :
    c7NestedGraph.graphEdgeSym2 k ∈ c7NestedGraph.toSimpleGraph.edgeSet := by
  rw [c7NestedGraph_toSimpleGraph_eq_smoke]
  exact c7NestedGraph_graphEdgeSym2_mem_smoke k

theorem c7NestedGraph_graphEdgeSym2_surj (e : Sym2 (Fin c7NestedGraph.n))
    (he : e ∈ c7NestedGraph.toSimpleGraph.edgeSet) :
    ∃ k : Fin 9, c7NestedGraph.graphEdgeSym2 k = e := by
  rw [c7NestedGraph_toSimpleGraph_eq_smoke] at he
  exact c7NestedGraph.graphEdgeSym2_surj e he

theorem c7NestedGraph_graphEdgeSym2_not_injective :
    ∃ k₁ k₂ : Fin 9, k₁ ≠ k₂ ∧ c7NestedGraph.graphEdgeSym2 k₁ = c7NestedGraph.graphEdgeSym2 k₂ :=
  ⟨1, 8, by decide, by native_decide⟩

def c7NestedGraph_graphEdgeBijectionOpenDoc : String :=
  "OPEN: c7NestedGraph_graphEdgeBijection — degenerate nested (p₁+1=p₂) gives graphEdgeSym2 1 = graphEdgeSym2 8; " ++
  "PROVED partial: mem, surj, non_injective witness; mirror c8 nondegenerate spacing to close."

def edgeIndexingDoc : String :=
  "PROVED: graphEdgeSym2_mem/inj/surj (nondegenerate→graphEdgeBijection), mem_toSimpleGraph_edgeSet_elim, " ++
  "GraphEdgeBijection→edgeEquiv/lineGraphVertex, arcConsecutive_lineGraphAdj; c8 smoke inj/surj; " ++
  "c7 partial mem/surj (bijection OPEN: chord₂=cycle edge)."

end PNPLab.ChordWidth
