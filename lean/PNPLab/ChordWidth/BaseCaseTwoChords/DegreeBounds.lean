/-
  Δ = 3 admissibility (Python `is_valid_delta3`) and nondegeneracy for C_n + two chords.

  Python skips configs where `max(degree) ≠ 3`; degenerate nested/disjoint pairings can yield
  maxDegree = 2 when a chord coincides with a cycle edge.
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.SimpleGraph.DegreeSup

namespace PNPLab.ChordWidth

open SimpleGraph

/-!
  ## Python-aligned Δ = 3 filter
-/

/-- Matches Python `is_valid_delta3`: exactly max degree 3 on the Mathlib graph. -/
def CycleTwoChordGraph.isDelta3Admissible (g : CycleTwoChordGraph) : Prop :=
  g.realMaxDegreeThree

theorem CycleTwoChordGraph.isDelta3Admissible_iff_realMaxDegreeThree (g : CycleTwoChordGraph) :
    g.isDelta3Admissible ↔ g.realMaxDegreeThree :=
  Iff.rfl

theorem CycleTwoChordGraph.isDelta3Admissible_iff_maxDegree_eq_three (g : CycleTwoChordGraph) :
    g.isDelta3Admissible ↔ g.toSimpleGraph.maxDegree = 3 := by
  unfold isDelta3Admissible realMaxDegreeThree
  rfl

theorem CycleTwoChordGraph.realMaxDegreeThree_implies_delta3Admissible
    (g : CycleTwoChordGraph) (h : g.realMaxDegreeThree) : g.isDelta3Admissible :=
  h

/-!
  ## Nondegeneracy: chord not already a cycle edge
-/

/-- Nat endpoints `(u,v)` already form a cycle edge in `C_n` (mod `n` adjacency). -/
def CycleTwoChordGraph.chordIsCycleEdge (g : CycleTwoChordGraph) (u v : Nat) : Prop :=
  u ≠ v ∧ u < g.n ∧ v < g.n ∧ ((u + 1) % g.n = v ∨ (v + 1) % g.n = u)

def CycleTwoChordGraph.chord1IsCycleEdge (g : CycleTwoChordGraph) : Prop :=
  g.chordIsCycleEdge g.chord1.1 g.chord1.2

def CycleTwoChordGraph.chord2IsCycleEdge (g : CycleTwoChordGraph) : Prop :=
  g.chordIsCycleEdge g.chord2.1 g.chord2.2

/-- Both chords are new edges (Python keeps these; excludes all-degenerate Δ = 2 shapes). -/
def CycleTwoChordGraph.isNondegenerate (g : CycleTwoChordGraph) : Prop :=
  ¬ g.chord1IsCycleEdge ∧ ¬ g.chord2IsCycleEdge

/-- Fully degenerate: both chords subsumed by the cycle (maxDegree = 2). -/
def CycleTwoChordGraph.isFullyDegenerate (g : CycleTwoChordGraph) : Prop :=
  g.chord1IsCycleEdge ∧ g.chord2IsCycleEdge

/-!
  ## Crossing: ordered endpoints ⇒ both chords are new cycle edges
-/

theorem CycleTwoChordGraph.crossing_chord1_not_cycleEdge (g : CycleTwoChordGraph)
    (hc : g.chordsCross) : ¬ g.chord1IsCycleEdge := by
  intro h
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, _⟩
  cases pairing
  · simp [chord1IsCycleEdge, chordIsCycleEdge, chord1] at h
    rcases h with ⟨_, hp0, hp2, huv⟩
    rcases huv with huv | huv
    · by_cases hlt : p0 + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at huv; omega
      · have : p0 + 1 = n := by omega
        rw [this, Nat.mod_self] at huv
        omega
    · by_cases hlt : p2 + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at huv; omega
      · have : p2 + 1 = n := by omega
        rw [this, Nat.mod_self] at huv
        omega
  · simp [chordsCross] at hc
  · simp [chordsCross] at hc

theorem CycleTwoChordGraph.crossing_chord2_not_cycleEdge (g : CycleTwoChordGraph)
    (hc : g.chordsCross) : ¬ g.chord2IsCycleEdge := by
  intro h
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, _⟩
  cases pairing
  · simp [chord2IsCycleEdge, chordIsCycleEdge, chord2] at h
    rcases h with ⟨_, hp1, hp3, huv⟩
    rcases huv with huv | huv
    · by_cases hlt : p1 + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at huv; omega
      · have : p1 + 1 = n := by omega
        rw [this, Nat.mod_self] at huv
        omega
    · by_cases hlt : p3 + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at huv; omega
      · have : p3 + 1 = n := by omega
        rw [this, Nat.mod_self] at huv
        omega
  · simp [chordsCross] at hc
  · simp [chordsCross] at hc

theorem CycleTwoChordGraph.crossing_isNondegenerate (g : CycleTwoChordGraph) (hc : g.chordsCross) :
    g.isNondegenerate :=
  ⟨g.crossing_chord1_not_cycleEdge hc, g.crossing_chord2_not_cycleEdge hc⟩

/-!
  ## Nested / disjoint: sufficient degeneracy conditions
-/

theorem CycleTwoChordGraph.nested_chord2_isCycleEdge_of_succ (g : CycleTwoChordGraph)
    (hn : g.pairing = ChordPairing.nested) (h12' : g.p2 = g.p1 + 1) :
    g.chord2IsCycleEdge := by
  obtain ⟨_, _, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  subst hn
  have h12 : p2 = p1 + 1 := by simpa using h12'
  simp only [chord2IsCycleEdge, chordIsCycleEdge, chord2]
  have hp1 : p1 < n := by omega
  refine ⟨by omega, hp1, by omega, Or.inl ?_⟩
  calc
    (p1 + 1) % n = p2 % n := by rw [h12]
    _ = p2 := Nat.mod_eq_of_lt (by omega)

theorem CycleTwoChordGraph.disjoint_chord1_isCycleEdge_of_succ (g : CycleTwoChordGraph)
    (hd : g.pairing = ChordPairing.disjoint) (h01' : g.p1 = g.p0 + 1) :
    g.chord1IsCycleEdge := by
  obtain ⟨_, h12, _, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  subst hd
  have h01 : p1 = p0 + 1 := by simpa using h01'
  simp only [chord1IsCycleEdge, chordIsCycleEdge, chord1]
  have hp0 : p0 < n := by omega
  refine ⟨by omega, hp0, by omega, Or.inl ?_⟩
  calc
    (p0 + 1) % n = p1 % n := by rw [h01]
    _ = p1 := Nat.mod_eq_of_lt (by omega)

theorem CycleTwoChordGraph.nested_not_nondegenerate_of_inner_cycle
    (g : CycleTwoChordGraph) (hn : g.pairing = ChordPairing.nested) (h12 : g.p2 = g.p1 + 1) :
    ¬ g.isNondegenerate := by
  intro hnd
  exact hnd.2 (g.nested_chord2_isCycleEdge_of_succ hn h12)

theorem CycleTwoChordGraph.disjoint_not_nondegenerate_of_first_cycle
    (g : CycleTwoChordGraph) (hd : g.pairing = ChordPairing.disjoint) (h01 : g.p1 = g.p0 + 1) :
    ¬ g.isNondegenerate := by
  intro hnd
  exact hnd.1 (g.disjoint_chord1_isCycleEdge_of_succ hd h01)

/-!
  ## Chord endpoint bookkeeping (Fin / Nat)
-/

theorem CycleTwoChordGraph.chord1_fst_ne_snd (g : CycleTwoChordGraph) :
    g.chord1.1 ≠ g.chord1.2 := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord1] <;> omega

theorem CycleTwoChordGraph.chord2_fst_ne_snd (g : CycleTwoChordGraph) :
    g.chord2.1 ≠ g.chord2.2 := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord2] <;> omega

theorem CycleTwoChordGraph.n_pos (g : CycleTwoChordGraph) : 0 < g.n := by
  obtain ⟨_, _, _, h3n⟩ := g.ordered
  omega

def CycleTwoChordGraph.cyclicEndpointFin (g : CycleTwoChordGraph) (step : Nat) : Fin g.n :=
  ⟨(g.p0 + step) % g.n, Nat.mod_lt _ g.n_pos⟩

def CycleTwoChordGraph.cyclicEndpointFinNext (g : CycleTwoChordGraph) (v : Fin g.n) : Fin g.n :=
  ⟨(v.val + 1) % g.n, Nat.mod_lt _ g.n_pos⟩

theorem CycleTwoChordGraph.cyclicEndpointFinNext_val (g : CycleTwoChordGraph) (v : Fin g.n) :
    (g.cyclicEndpointFinNext v).val = (v.val + 1) % g.n := by
  simp [cyclicEndpointFinNext]

theorem CycleTwoChordGraph.cyclicEndpointFin_succ (g : CycleTwoChordGraph) (k : Nat) :
    g.cyclicEndpointFin (k + 1) = g.cyclicEndpointFinNext (g.cyclicEndpointFin k) := by
  ext
  simp only [cyclicEndpointFin, cyclicEndpointFinNext, Fin.val_mk]
  calc (g.p0 + (k + 1)) % g.n
      _ = (g.p0 + k + 1) % g.n := by rw [Nat.add_assoc]
      _ = ((g.p0 + k) % g.n + 1) % g.n := by
        rw [Nat.add_mod]
        simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ g.n_pos)]

theorem CycleTwoChordGraph.cyclicEndpointFinNext_sub_self (g : CycleTwoChordGraph) (v : Fin g.n) :
    (g.cyclicEndpointFinNext v - v).val = 1 := by
  by_cases hlt : v.val + 1 < g.n
  · have hle : v ≤ g.cyclicEndpointFinNext v := by
      simp [Fin.le_def, cyclicEndpointFinNext, Nat.mod_eq_of_lt hlt]
    rw [Fin.sub_val_of_le hle, cyclicEndpointFinNext_val, Nat.mod_eq_of_lt hlt]
    omega
  · have hvlast : v.val = g.n - 1 := by omega
    have hnpos : 0 < g.n := g.n_pos
    have hvnext : (g.cyclicEndpointFinNext v).val = 0 := by
      simp [cyclicEndpointFinNext, hvlast, Nat.sub_add_cancel (Nat.one_le_of_lt hnpos), Nat.mod_self]
    have hn1 : 1 < g.n := by
      have h4 : 4 ≤ g.n := g.ordered_implies_n_ge_four
      omega
    rw [show g.cyclicEndpointFinNext v = ⟨(0 : Nat), hnpos⟩ from Fin.ext hvnext,
      show v = ⟨g.n - 1, by omega⟩ from Fin.ext hvlast]
    have hlt' : (⟨0, hnpos⟩ : Fin g.n) < ⟨g.n - 1, by omega⟩ := by
      simp [Fin.lt_def, hn1]
    rw [Fin.coe_sub_iff_lt.mpr hlt']
    simp
    omega

/-- Cycle step `(p0+k) → (p0+k+1)` is a cycle-graph edge (used in edge indexing). -/
def CycleTwoChordGraph.cyclicEdgeInGraph (g : CycleTwoChordGraph) (k : Nat) : Prop :=
  (cycleGraph g.n).Adj (g.cyclicEndpointFin k) (g.cyclicEndpointFin (k + 1))

theorem CycleTwoChordGraph.cyclicEdgeInGraph_of (g : CycleTwoChordGraph) (k : Nat) :
    g.cyclicEdgeInGraph k := by
  dsimp [cyclicEdgeInGraph]
  rw [cycleGraph_adj', g.cyclicEndpointFin_succ k]
  exact Or.inr (g.cyclicEndpointFinNext_sub_self (g.cyclicEndpointFin k))

/-- Cyclic step index recovering `v` from `cyclicEndpointFin step = v` (inverse on `Fin n`). -/
def CycleTwoChordGraph.cyclicStepOfFin (g : CycleTwoChordGraph) (v : Fin g.n) : Nat :=
  (v.val + g.n - g.p0) % g.n

theorem CycleTwoChordGraph.cyclicStepOfFin_lt (g : CycleTwoChordGraph) (v : Fin g.n) :
    g.cyclicStepOfFin v < g.n :=
  Nat.mod_lt _ g.n_pos

theorem CycleTwoChordGraph.cyclicEndpointFin_cyclicStepOfFin (g : CycleTwoChordGraph) (v : Fin g.n) :
    g.cyclicEndpointFin (g.cyclicStepOfFin v) = v := by
  ext
  simp only [cyclicEndpointFin, cyclicStepOfFin, Fin.val_mk]
  obtain ⟨_, _, _, _⟩ := g.ordered
  have hp0 : g.p0 < g.n := by omega
  have hvn : v.val < g.n := v.isLt
  by_cases hvp : v.val < g.p0
  · have hlt : v.val + g.n - g.p0 < g.n := by omega
    have hmod : (v.val + g.n - g.p0) % g.n = v.val + g.n - g.p0 := Nat.mod_eq_of_lt hlt
    have hsum : g.p0 + (v.val + g.n - g.p0) = v.val + g.n := by omega
    calc (g.p0 + (v.val + g.n - g.p0) % g.n) % g.n
        _ = (g.p0 + (v.val + g.n - g.p0)) % g.n := by rw [hmod]
        _ = (v.val + g.n) % g.n := by rw [hsum]
        _ = v.val := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt hvn, Nat.mod_self]
          exact Nat.mod_eq_of_lt hvn
  · have hge : g.p0 ≤ v.val := le_of_not_gt hvp
    have hlt : v.val - g.p0 < g.n := by omega
    have hmod : (v.val + g.n - g.p0) % g.n = v.val - g.p0 := by
      have hsum : v.val + g.n - g.p0 = v.val - g.p0 + g.n := by omega
      calc (v.val + g.n - g.p0) % g.n
          _ = (v.val - g.p0 + g.n) % g.n := by rw [hsum]
          _ = v.val - g.p0 := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt hlt, Nat.mod_self]
            exact Nat.mod_eq_of_lt hlt
    have hadd : g.p0 + (v.val - g.p0) = v.val := Nat.add_sub_of_le hge
    calc (g.p0 + (v.val + g.n - g.p0) % g.n) % g.n
        _ = (g.p0 + (v.val - g.p0)) % g.n := by rw [hmod]
        _ = v.val % g.n := by rw [hadd]
        _ = v.val := Nat.mod_eq_of_lt hvn

theorem CycleTwoChordGraph.cyclicEndpointFinNext_of_mod (g : CycleTwoChordGraph) {u v : Fin g.n}
    (huv : (u.val + 1) % g.n = v.val) :
    g.cyclicEndpointFinNext u = v := by
  ext
  simp [cyclicEndpointFinNext, huv]

theorem CycleTwoChordGraph.chord1_chord2_endpoints_disjoint (g : CycleTwoChordGraph) :
    g.chord1.1 ≠ g.chord2.1 ∧ g.chord1.1 ≠ g.chord2.2 ∧
      g.chord1.2 ≠ g.chord2.1 ∧ g.chord1.2 ≠ g.chord2.2 := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord1, chord2] <;> omega

private theorem nat_mod_one_eq_add_one {a n : ℕ} (hge : n ≤ a) (hlt : a < 2 * n) (h : a % n = 1) (hn : 1 ≤ n) :
    a = n + 1 := by
  have hdiv : a / n = 1 := by
    have hlo : 1 ≤ a / n := by rw [Nat.le_div_iff_mul_le hn]; omega
    have hhi : a / n < 2 := Nat.div_lt_of_lt_mul (by omega : a < n * 2)
    omega
  have hdecomp := Nat.div_add_mod a n
  rw [hdiv, h] at hdecomp
  exact show a = n + 1 by omega

private theorem fin_cycleAdj_nat_mod_aux (n u v : ℕ) (hu : u < n) (hv : v < n)
    (hadj : (cycleGraph n).Adj ⟨u, hu⟩ ⟨v, hv⟩) :
    (u + 1) % n = v ∨ (v + 1) % n = u := by
  rw [cycleGraph_adj'] at hadj
  simp only [Fin.val_sub] at hadj
  rcases hadj with h | h
  · right
    by_cases hbound : n - v + u < n
    · have hsum : n - v + u = 1 := by rw [Nat.mod_eq_of_lt hbound] at h; exact h
      have hvlast : v + 1 = n := by omega
      have hp0 : u = 0 := by omega
      rw [hvlast, Nat.mod_self, hp0]
    · have hge : n ≤ n - v + u := le_of_not_gt hbound
      have hsum : n - v + u = n + 1 :=
        nat_mod_one_eq_add_one hge (by omega) h (by omega)
      have hv1 : v + 1 = u := by omega
      have hlt : v + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hlt, hv1]
  · left
    by_cases hbound : n - u + v < n
    · have hsum : n - u + v = 1 := by rw [Nat.mod_eq_of_lt hbound] at h; exact h
      have hvlast : u + 1 = n := by omega
      have hp0 : v = 0 := by omega
      rw [hvlast, Nat.mod_self, hp0]
    · have hge : n ≤ n - u + v := le_of_not_gt hbound
      have hsum : n - u + v = n + 1 :=
        nat_mod_one_eq_add_one hge (by omega) h (by omega)
      have hv : v = u + 1 := by omega
      have hlt : u + 1 < n := by omega
      rw [hv, Nat.mod_eq_of_lt hlt]

theorem CycleTwoChordGraph.fin_cycleAdj_nat_mod (g : CycleTwoChordGraph) {u v : Fin g.n}
    (hadj : (cycleGraph g.n).Adj u v) :
    (u.val + 1) % g.n = v.val ∨ (v.val + 1) % g.n = u.val :=
  fin_cycleAdj_nat_mod_aux g.n u.val v.val u.isLt v.isLt hadj

theorem CycleTwoChordGraph.chord1IsCycleEdge_of_cycle_adj (g : CycleTwoChordGraph)
    (hadj : (cycleGraph g.n).Adj (⟨g.chord1.1, g.chord1_fst_lt⟩) (⟨g.chord1.2, g.chord1_snd_lt⟩)) :
    g.chord1IsCycleEdge := by
  unfold chord1IsCycleEdge chordIsCycleEdge
  refine ⟨g.chord1_fst_ne_snd, g.chord1_fst_lt, g.chord1_snd_lt, ?_⟩
  exact fin_cycleAdj_nat_mod_aux g.n g.chord1.1 g.chord1.2 g.chord1_fst_lt g.chord1_snd_lt hadj

theorem CycleTwoChordGraph.chord2IsCycleEdge_of_cycle_adj (g : CycleTwoChordGraph)
    (hadj : (cycleGraph g.n).Adj (⟨g.chord2.1, g.chord2_fst_lt⟩) (⟨g.chord2.2, g.chord2_snd_lt⟩)) :
    g.chord2IsCycleEdge := by
  unfold chord2IsCycleEdge chordIsCycleEdge
  refine ⟨g.chord2_fst_ne_snd, g.chord2_fst_lt, g.chord2_snd_lt, ?_⟩
  exact fin_cycleAdj_nat_mod_aux g.n g.chord2.1 g.chord2.2 g.chord2_fst_lt g.chord2_snd_lt hadj

theorem CycleTwoChordGraph.not_cycle_adj_of_chord2_not_cycleEdge (g : CycleTwoChordGraph)
    (h : ¬ g.chord2IsCycleEdge) :
    ¬ (cycleGraph g.n).Adj (⟨g.chord2.1, g.chord2_fst_lt⟩) (⟨g.chord2.2, g.chord2_snd_lt⟩) :=
  fun hadj => h (g.chord2IsCycleEdge_of_cycle_adj hadj)

theorem CycleTwoChordGraph.not_cycle_adj_of_chord1_not_cycleEdge (g : CycleTwoChordGraph)
    (h : ¬ g.chord1IsCycleEdge) :
    ¬ (cycleGraph g.n).Adj (⟨g.chord1.1, g.chord1_fst_lt⟩) (⟨g.chord1.2, g.chord1_snd_lt⟩) :=
  fun hadj => h (g.chord1IsCycleEdge_of_cycle_adj hadj)

/-!
  ## Generic Δ ≤ 3 / nondegenerate ⇒ Δ = 3
-/

private def CycleTwoChordGraph.chord1Edge (g : CycleTwoChordGraph) :
    SimpleGraph (Fin g.n) :=
  edge (⟨g.chord1.1, g.chord1_fst_lt⟩) ⟨g.chord1.2, g.chord1_snd_lt⟩

private def CycleTwoChordGraph.chord2Edge (g : CycleTwoChordGraph) :
    SimpleGraph (Fin g.n) :=
  edge (⟨g.chord2.1, g.chord2_fst_lt⟩) ⟨g.chord2.2, g.chord2_snd_lt⟩

theorem CycleTwoChordGraph.toSimpleGraphNoncrossing_eq_sup (g : CycleTwoChordGraph) :
    g.toSimpleGraphNoncrossing = cycleGraph g.n ⊔ g.chord1Edge ⊔ g.chord2Edge := by
  simp [CycleTwoChordGraph.toSimpleGraphNoncrossing, chord1Edge, chord2Edge]

theorem CycleTwoChordGraph.toSimpleGraphNoncrossing_degree_le_three
    (g : CycleTwoChordGraph) (v : Fin g.n) :
    g.toSimpleGraphNoncrossing.degree v ≤ 3 := by
  classical
  suffices (cycleGraph g.n ⊔
      edge (⟨g.chord1.1, g.chord1_fst_lt⟩) ⟨g.chord1.2, g.chord1_snd_lt⟩ ⊔
      edge (⟨g.chord2.1, g.chord2_fst_lt⟩) ⟨g.chord2.2, g.chord2_snd_lt⟩).degree v ≤ 3 by
    unfold toSimpleGraphNoncrossing
    exact this
  have hne1 : (⟨g.chord1.1, g.chord1_fst_lt⟩ : Fin g.n) ≠ ⟨g.chord1.2, g.chord1_snd_lt⟩ :=
    fun h => g.chord1_fst_ne_snd (Fin.ext_iff.mp h)
  have hne2 : (⟨g.chord2.1, g.chord2_fst_lt⟩ : Fin g.n) ≠ ⟨g.chord2.2, g.chord2_snd_lt⟩ :=
    fun h => g.chord2_fst_ne_snd (Fin.ext_iff.mp h)
  have hdisj := g.chord1_chord2_endpoints_disjoint
  have hdisjFin :
      (⟨g.chord1.1, g.chord1_fst_lt⟩ : Fin g.n) ≠ ⟨g.chord2.1, g.chord2_fst_lt⟩ ∧
        (⟨g.chord1.1, g.chord1_fst_lt⟩ : Fin g.n) ≠ ⟨g.chord2.2, g.chord2_snd_lt⟩ ∧
          (⟨g.chord1.2, g.chord1_snd_lt⟩ : Fin g.n) ≠ ⟨g.chord2.1, g.chord2_fst_lt⟩ ∧
            (⟨g.chord1.2, g.chord1_snd_lt⟩ : Fin g.n) ≠ ⟨g.chord2.2, g.chord2_snd_lt⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact hdisj.1 (Fin.ext_iff.mp h)
    · exact hdisj.2.1 (Fin.ext_iff.mp h)
    · exact hdisj.2.2.1 (Fin.ext_iff.mp h)
    · exact hdisj.2.2.2 (Fin.ext_iff.mp h)
  have hcycle : (cycleGraph g.n).degree v = 2 :=
    cycleGraph_degree_eq_two_of_four_le g.ordered_implies_n_ge_four v
  have hedges :
      (edge (⟨g.chord1.1, g.chord1_fst_lt⟩) ⟨g.chord1.2, g.chord1_snd_lt⟩).degree v +
        (edge (⟨g.chord2.1, g.chord2_fst_lt⟩) ⟨g.chord2.2, g.chord2_snd_lt⟩).degree v ≤ 1 :=
    degree_edge_add_degree_edge_le_one_of_endpoint_disjoint hne1 hne2
      ⟨hdisjFin.1, hdisjFin.2.1, hdisjFin.2.2.1, hdisjFin.2.2.2⟩
  have hbound := degree_sup_sup_le_add (cycleGraph g.n)
    (edge (⟨g.chord1.1, g.chord1_fst_lt⟩) ⟨g.chord1.2, g.chord1_snd_lt⟩)
    (edge (⟨g.chord2.1, g.chord2_fst_lt⟩) ⟨g.chord2.2, g.chord2_snd_lt⟩) v
  omega

theorem CycleTwoChordGraph.toSimpleGraphNoncrossing_maxDegree_le_three (g : CycleTwoChordGraph) :
    g.toSimpleGraphNoncrossing.maxDegree ≤ 3 := by
  classical
  apply maxDegree_le_of_forall_degree_le
  exact g.toSimpleGraphNoncrossing_degree_le_three

theorem CycleTwoChordGraph.chord1_fst_degree_eq_three_of_nondegenerate
    (g : CycleTwoChordGraph) (hnd : g.isNondegenerate) :
    g.toSimpleGraphNoncrossing.degree (⟨g.chord1.1, g.chord1_fst_lt⟩) = 3 := by
  classical
  set s1 := (⟨g.chord1.1, g.chord1_fst_lt⟩ : Fin g.n)
  set t1 := (⟨g.chord1.2, g.chord1_snd_lt⟩ : Fin g.n)
  set G := cycleGraph g.n ⊔ edge s1 t1 ⊔ edge (⟨g.chord2.1, g.chord2_fst_lt⟩) ⟨g.chord2.2, g.chord2_snd_lt⟩
  have hne1 : s1 ≠ t1 := fun h => g.chord1_fst_ne_snd (Fin.ext_iff.mp h)
  have hnadj : ¬ (cycleGraph g.n).Adj s1 t1 :=
    g.not_cycle_adj_of_chord1_not_cycleEdge hnd.1
  have hstep := degree_sup_edge_endpoint_of_not_adj (cycleGraph g.n) hne1 hnadj
  have hcycle := cycleGraph_degree_eq_two_of_four_le g.ordered_implies_n_ge_four s1
  have hbase : (cycleGraph g.n ⊔ edge s1 t1).degree s1 = 3 := by rw [hstep, hcycle]
  have hle : (cycleGraph g.n ⊔ edge s1 t1).degree s1 ≤ G.degree s1 :=
    degree_le_degree_sup (cycleGraph g.n ⊔ edge s1 t1) _ s1
  have hle3 : G.degree s1 ≤ 3 := g.toSimpleGraphNoncrossing_degree_le_three s1
  have hge3 : 3 ≤ G.degree s1 := by omega
  have heq : G.degree s1 = 3 := le_antisymm hle3 hge3
  unfold toSimpleGraphNoncrossing
  exact heq

theorem CycleTwoChordGraph.toSimpleGraph_maxDegree_le (g : CycleTwoChordGraph) :
    g.toSimpleGraph.maxDegree ≤ 3 := by
  simpa [g.toSimpleGraph_eq_noncrossing] using g.toSimpleGraphNoncrossing_maxDegree_le_three

theorem CycleTwoChordGraph.toSimpleGraph_maxDegree_le_three_holds (g : CycleTwoChordGraph) :
    g.toSimpleGraph_maxDegree_le_three :=
  g.toSimpleGraph_maxDegree_le

theorem CycleTwoChordGraph.isNondegenerate_implies_realMaxDegreeThree
    (g : CycleTwoChordGraph) (hnd : g.isNondegenerate) : g.realMaxDegreeThree := by
  have hdeg3 := g.chord1_fst_degree_eq_three_of_nondegenerate hnd
  have hmax : g.toSimpleGraphNoncrossing.maxDegree = 3 :=
    le_antisymm g.toSimpleGraphNoncrossing_maxDegree_le_three (by
      calc
        3 = g.toSimpleGraphNoncrossing.degree _ := hdeg3.symm
        _ ≤ g.toSimpleGraphNoncrossing.maxDegree := degree_le_maxDegree _ _)
  exact g.realMaxDegreeThree_of_graph_eq g.toSimpleGraph_eq_noncrossing hmax

theorem CycleTwoChordGraph.isNondegenerate_implies_delta3Admissible
    (g : CycleTwoChordGraph) (hnd : g.isNondegenerate) : g.isDelta3Admissible :=
  g.isNondegenerate_implies_realMaxDegreeThree hnd

theorem CycleTwoChordGraph.crossing_isDelta3Admissible (g : CycleTwoChordGraph) (hc : g.chordsCross) :
    g.isDelta3Admissible :=
  g.isNondegenerate_implies_delta3Admissible (g.crossing_isNondegenerate hc)

/-!
  ## Δ = 3 transport (smoke / computable graph equality)
-/

theorem CycleTwoChordGraph.isDelta3Admissible_of_graph_eq
    {g : CycleTwoChordGraph} {sg : SimpleGraph (Fin g.n)} [DecidableRel sg.Adj]
    (hgraph : g.toSimpleGraph = sg) (hdeg : sg.maxDegree = 3) : g.isDelta3Admissible :=
  g.realMaxDegreeThree_of_graph_eq hgraph hdeg

theorem CycleTwoChordGraph.crossing_isDelta3Admissible_of_smoke
    {g : CycleTwoChordGraph} (_hc : g.chordsCross)
    {sg : SimpleGraph (Fin g.n)} [DecidableRel sg.Adj]
    (hgraph : g.toSimpleGraph = sg) (hdeg : sg.maxDegree = 3) : g.isDelta3Admissible :=
  g.isDelta3Admissible_of_graph_eq hgraph hdeg

def delta3BoundsDoc : String :=
  "isDelta3Admissible = Python is_valid_delta3; crossing_isNondegenerate + generic Δ≤3/Δ=3 proved; " ++
  "cyclicEdgeInGraph_of generic; DegreeSup: neighborFinset_sup + degree_sup_le_add + edge/cycle bounds"

end PNPLab.ChordWidth
