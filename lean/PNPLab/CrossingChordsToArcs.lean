/-
  G1 discharge: C_n + two chords with four distinct endpoints → `CrossingArcs`.

  Matches Python `crossing_branch_sets` (`k4_minor_lower_bound.py`):
  sort the four endpoints on the cycle; each open arc is the internal vertices
  between consecutive endpoints (wrapping on the last).

  This is the combinatorial graph→arcs map; no Lean `axiom`.
  E2: multihop frontier mass 461/461 uses the same construction.
-/

import PNPLab.WhitneyEarAxiom

namespace PNPLab.Bicyclic

open WhitneyEar

/-- Four distinct cycle endpoints in increasing order `0 ≤ p0 < p1 < p2 < p3 < n`. -/
structure CrossingEndpoints where
  n : Nat
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  ordered :
    p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < n

/-- Open-arc internal counts between consecutive sorted endpoints (wrap on last). -/
def CrossingEndpoints.toArcs (e : CrossingEndpoints) : CrossingArcs where
  a0 := e.p1 - e.p0 - 1
  a1 := e.p2 - e.p1 - 1
  a2 := e.p3 - e.p2 - 1
  a3 := e.n - e.p3 + e.p0 - 1

/-- Total internals = `n - 4` (four endpoints removed from the cycle). -/
theorem CrossingEndpoints.toArcs_total (e : CrossingEndpoints) :
    e.toArcs.total = e.n - 4 := by
  obtain ⟨hp01, hp12, hp23, hp3n⟩ := e.ordered
  simp [CrossingEndpoints.toArcs, CrossingArcs.total]
  omega

/-- Params package: cycle length + computed arcs. -/
def CrossingEndpoints.toParams (e : CrossingEndpoints) : CrossingGraphParams :=
  CrossingGraphParams.ofArcs e.n e.toArcs

theorem CrossingEndpoints.toParams_arcs (e : CrossingEndpoints) :
    (CrossingEndpoints.toParams e).arcs = e.toArcs :=
  rfl

/-- Embed witness from endpoints (G1 combinatorial path). -/
def CrossingEndpoints.embedWitness (e : CrossingEndpoints) : CrossingEmbedWitness :=
  crossing_graph_embed_witness (CrossingEndpoints.toParams e)

/-- Positive hop budget when `n > 4`. -/
theorem CrossingEndpoints.total_pos_of_gt4 (e : CrossingEndpoints) (hn : 4 < e.n) :
    0 < e.toArcs.total := by
  rw [CrossingEndpoints.toArcs_total]
  omega

/-- Frontier tip exists whenever `n > 4`. -/
theorem CrossingEndpoints.frontier_tip (e : CrossingEndpoints) (hn : 4 < e.n) :
    ∃ i : Fin 4, frontierTipKind (e.toArcs.get i) = some .shortcutOnShorterArc :=
  crossing_frontier_tip_exists e.toArcs (e.total_pos_of_gt4 hn)

/-- Canonical C₆ sample: endpoints `0,1,2,3` ⇒ arcs `(0,0,0,2)`. -/
def c6Endpoints0123 : CrossingEndpoints where
  n := 6
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  ordered := by decide

theorem c6Endpoints0123_arcs_a0 : c6Endpoints0123.toArcs.a0 = 0 := rfl
theorem c6Endpoints0123_arcs_a1 : c6Endpoints0123.toArcs.a1 = 0 := rfl
theorem c6Endpoints0123_arcs_a2 : c6Endpoints0123.toArcs.a2 = 0 := rfl
theorem c6Endpoints0123_arcs_a3 : c6Endpoints0123.toArcs.a3 = 2 := rfl

theorem c6Endpoints0123_total :
    c6Endpoints0123.toArcs.total = 2 := by
  rw [CrossingEndpoints.toArcs_total]; rfl

/--
  Alternating sample on C₈: endpoints `0,2,4,6` ⇒ four unit arcs
  (matches the abstract `c6CrossingArcs` hop shape on a larger cycle).
-/
def c8EndpointsEven : CrossingEndpoints where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  ordered := by decide

theorem c8EndpointsEven_arcs_a0 : c8EndpointsEven.toArcs.a0 = 1 := rfl
theorem c8EndpointsEven_arcs_a1 : c8EndpointsEven.toArcs.a1 = 1 := rfl
theorem c8EndpointsEven_arcs_a2 : c8EndpointsEven.toArcs.a2 = 1 := rfl
theorem c8EndpointsEven_arcs_a3 : c8EndpointsEven.toArcs.a3 = 1 := rfl

theorem c8EndpointsEven_total_eq_c6Demo :
    c8EndpointsEven.toArcs.total = c6CrossingArcs.total := by
  native_decide

/-- Bundle: sorted endpoints → arcs → embed → frontier tip (`n > 4`). -/
theorem crossing_chords_to_arcs_bundle (e : CrossingEndpoints) (hn : 4 < e.n) :
    e.toArcs.total = e.n - 4 ∧
      (CrossingEndpoints.toParams e).arcs = e.toArcs ∧
      ∃ i : Fin 4,
        frontierTipKind (e.toArcs.get i) = some .shortcutOnShorterArc :=
  ⟨e.toArcs_total, e.toParams_arcs, e.frontier_tip hn⟩

/--
  Hop budget for a crossing on `C_n` is `n - 4`.
  Every crossing with `5 ≤ n ≤ 14` therefore lies in the pack-routing window
  `total ≤ maxCrossingHopBudget` (= 10).
-/
theorem crossing_hop_budget_le_pack_window
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    e.toArcs.total ≤ 10 := by
  rw [CrossingEndpoints.toArcs_total]
  omega

def crossingChordsToArcsDoc : String :=
  "backend/proof_complexity/k4_minor_lower_bound.py :: crossing_branch_sets"

end PNPLab.Bicyclic
