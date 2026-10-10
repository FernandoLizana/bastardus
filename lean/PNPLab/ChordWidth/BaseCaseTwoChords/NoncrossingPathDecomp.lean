/-
  Route F+A pilot: parametric path decomposition toward `HasTreeDecomp (lineGraph G) 3`
  for noncrossing `CycleTwoChordGraph` instances.

  **PROVED:** arc-local + short-arc sliding bags (card ≤ 4, width ≤ 3), chord-junction bags,
    enriched junction bags, `LongArcSegmentFragment`, c8 smoke GraphEdgeBijection hook,
    global assembly scaffold (`globalBagFamily`, `globalDecompGraph`, 7-node path relay), open-goals bundle,
    `conditionalHasTreeDecomp_of_openGoals` (conditional on `NoncrossingPathDecompOpenGoals`).
  **CONDITIONAL:** `NoncrossingLongArcBlock` + `GraphEdgeBijection` + discharged open goals.
  **OPEN:** generic instance discharge of all `NoncrossingPathDecompOpenGoals` fields;
    c8 7-node fork tree at width≤4 infeasible (junc₁ hub needs 6 edges).
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import PNPLab.ChordWidth.BaseCaseTwoChords.ArcLengths
import PNPLab.ChordWidth.BaseCaseTwoChords.DegreeBounds
import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.BaseCaseTwoChords.EdgeIndexing
import PNPLab.ChordWidth.LineGraph
import PNPLab.ChordWidth.TreeDecomp.Basic
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.Certificates
import PNPLab.ChordWidth.TreeDecomp.CertificatesLine

namespace PNPLab.ChordWidth

open SimpleGraph
open SmokeLineGraphCert
open TreeDecomp

/-! ## Cycle endpoint indexing (p0-forward steps) -/

def CycleTwoChordGraph.cycleStepOfNatEndpoint (g : CycleTwoChordGraph) (p : Nat) (_hp : p < g.n) :
    Nat :=
  (p + g.n - g.p0) % g.n

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_lt (g : CycleTwoChordGraph) (p : Nat)
    (hp : p < g.n) : g.cycleStepOfNatEndpoint p hp < g.n := by
  unfold cycleStepOfNatEndpoint
  exact Nat.mod_lt _ g.n_pos

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_chord1_fst (g : CycleTwoChordGraph) :
    g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt = 0 := by
  unfold cycleStepOfNatEndpoint
  obtain ⟨h01, _, _, _⟩ := g.ordered
  rcases g with ⟨_, _, _, _, _, pairing, _⟩
  cases pairing <;> simp [CycleTwoChordGraph.chord1, Nat.add_mod, Nat.mod_eq_of_lt] <;> omega

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_chord1_snd (g : CycleTwoChordGraph) :
    g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt =
      (g.chord1.2 + g.n - g.p0) % g.n := by
  unfold cycleStepOfNatEndpoint
  rfl

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_chord2_fst (g : CycleTwoChordGraph) :
    g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt =
      (g.chord2.1 + g.n - g.p0) % g.n := by
  unfold cycleStepOfNatEndpoint
  rfl

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_chord2_snd (g : CycleTwoChordGraph) :
    g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt =
      (g.chord2.2 + g.n - g.p0) % g.n := by
  unfold cycleStepOfNatEndpoint
  rfl

theorem CycleTwoChordGraph.chord_endpoint_ge_p0 (g : CycleTwoChordGraph) :
    g.p0 ≤ g.chord1.1 ∧ g.p0 ≤ g.chord1.2 ∧ g.p0 ≤ g.chord2.1 ∧ g.p0 ≤ g.chord2.2 := by
  obtain ⟨h01, h12, h23, _⟩ := g.ordered
  rcases g with ⟨_, _, _, _, _, pairing, _⟩
  cases pairing <;> simp [CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2] <;> omega

/-! ## Long arc selection (max cyclic gap; tie-break toward higher index) -/

def CycleTwoChordGraph.longArcIdx (g : CycleTwoChordGraph) : Fin 4 :=
  if g.cyclicGap 3 ≥ g.cyclicGap 0 ∧ g.cyclicGap 3 ≥ g.cyclicGap 1 ∧ g.cyclicGap 3 ≥ g.cyclicGap 2 then
    ⟨3, by decide⟩
  else if g.cyclicGap 2 ≥ g.cyclicGap 0 ∧ g.cyclicGap 2 ≥ g.cyclicGap 1 then
    ⟨2, by decide⟩
  else if g.cyclicGap 1 ≥ g.cyclicGap 0 then
    ⟨1, by decide⟩
  else
    ⟨0, by decide⟩

/-! ## Sliding bags along cyclic arcs (edge-index Fin (n+2)) -/

def CycleTwoChordGraph.longArcSlidingBag (g : CycleTwoChordGraph) (a : Fin 4) (j : Nat)
    (hj : j < g.cyclicGap a) : Finset (Fin (g.n + 2)) :=
  let base := g.arcEdgeOffset a + j
  let e0 := g.cycleEdgeGlobalIndexAt base (by
    have := g.arcEdgeOffset_add_lt a j hj
    omega)
  let ePrev : Option (Fin (g.n + 2)) :=
    if 0 < j then
      some (g.cycleEdgeGlobalIndexAt (base - 1) (by
        have := g.arcEdgeOffset_add_lt a j hj
        omega))
    else none
  let eNext : Option (Fin (g.n + 2)) :=
    if hj' : j + 1 < g.cyclicGap a then
      some (g.cycleEdgeGlobalIndexAt (base + 1) (by
        have := g.arcEdgeOffset_add_lt a (j + 1) hj'
        omega))
    else none
  ePrev.toFinset ∪ {e0} ∪ eNext.toFinset

def CycleTwoChordGraph.longArcBagFamily (g : CycleTwoChordGraph) (a : Fin 4) (i : Fin (g.cyclicGap a)) :
    Finset (Fin (g.n + 2)) :=
  g.longArcSlidingBag a i.val i.isLt

private theorem Option.toFinset_card_le {α} (o : Option α) : o.toFinset.card ≤ 1 := by
  cases o <;> simp [Option.toFinset]

theorem CycleTwoChordGraph.longArcSlidingBag_card_le_four (g : CycleTwoChordGraph) (a : Fin 4)
    (j : Nat) (hj : j < g.cyclicGap a) :
    (g.longArcSlidingBag a j hj).card ≤ 4 := by
  simp only [longArcSlidingBag, Option.toFinset, Finset.card_union, Finset.card_singleton]
  split_ifs <;> simp [Finset.card_insert_of_notMem, Finset.mem_singleton] <;> omega

theorem CycleTwoChordGraph.longArcBag_width_le_three (g : CycleTwoChordGraph) (a : Fin 4)
    (i : Fin (g.cyclicGap a)) :
    (g.longArcBagFamily a i).card - 1 ≤ 3 := by
  have h := g.longArcSlidingBag_card_le_four a i.val i.isLt
  simp only [longArcBagFamily]
  omega

theorem CycleTwoChordGraph.longArcSlidingBag_covers_arc_consecutive (g : CycleTwoChordGraph)
    (a : Fin 4) (j : Nat) (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    let base := g.arcEdgeOffset a + j
    g.cycleEdgeGlobalIndexAt base (by
      have := g.arcEdgeOffset_add_lt a j hj
      omega) ∈ g.longArcSlidingBag a j hj ∧
      g.cycleEdgeGlobalIndexAt (base + 1) (by
        have := g.arcEdgeOffset_add_lt a (j + 1) hj'
        omega) ∈ g.longArcSlidingBag a j hj := by
  dsimp [longArcSlidingBag, cycleEdgeGlobalIndexAt]
  constructor <;> simp [hj', Option.mem_toFinset, Option.some, Finset.mem_union, Finset.mem_insert]

/-! ## Chord-junction bags (four endpoints) -/

def CycleTwoChordGraph.chord1StartJunctionBag (g : CycleTwoChordGraph) : Finset (Fin (g.n + 2)) :=
  {g.cycleEdgeGlobalIndexAt (g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt)
      (g.cycleStepOfNatEndpoint_lt _ _),
    g.chord1EdgeIndex}

def CycleTwoChordGraph.chord1EndJunctionBag (g : CycleTwoChordGraph) : Finset (Fin (g.n + 2)) :=
  {g.cycleEdgeGlobalIndexAt (g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt)
      (g.cycleStepOfNatEndpoint_lt _ _),
    g.chord1EdgeIndex}

def CycleTwoChordGraph.chord2StartJunctionBag (g : CycleTwoChordGraph) : Finset (Fin (g.n + 2)) :=
  {g.cycleEdgeGlobalIndexAt (g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt)
      (g.cycleStepOfNatEndpoint_lt _ _),
    g.chord2EdgeIndex}

def CycleTwoChordGraph.chord2EndJunctionBag (g : CycleTwoChordGraph) : Finset (Fin (g.n + 2)) :=
  {g.cycleEdgeGlobalIndexAt (g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt)
      (g.cycleStepOfNatEndpoint_lt _ _),
    g.chord2EdgeIndex}

def CycleTwoChordGraph.chordJunctionBagFamily (g : CycleTwoChordGraph) : Fin 4 → Finset (Fin (g.n + 2))
  | 0 => g.chord1StartJunctionBag
  | 1 => g.chord1EndJunctionBag
  | 2 => g.chord2StartJunctionBag
  | 3 => g.chord2EndJunctionBag

def CycleTwoChordGraph.chordJunctionBagSupWidth (g : CycleTwoChordGraph) : Nat :=
  (Finset.univ : Finset (Fin 4)).sup fun i => (g.chordJunctionBagFamily i).card - 1

theorem CycleTwoChordGraph.cycleEdgeGlobalIndexAt_ne_chord1EdgeIndex (g : CycleTwoChordGraph)
    (k : Nat) (hk : k < g.n) :
    g.cycleEdgeGlobalIndexAt k hk ≠ g.chord1EdgeIndex := by
  intro h
  have := congrArg Fin.val h
  simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, CycleTwoChordGraph.chord1EdgeIndex_val] at this
  omega

theorem CycleTwoChordGraph.cycleEdgeGlobalIndexAt_ne_chord2EdgeIndex (g : CycleTwoChordGraph)
    (k : Nat) (hk : k < g.n) :
    g.cycleEdgeGlobalIndexAt k hk ≠ g.chord2EdgeIndex := by
  intro h
  have := congrArg Fin.val h
  simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, CycleTwoChordGraph.chord2EdgeIndex_val] at this
  omega

theorem CycleTwoChordGraph.chordJunctionBagSupWidth_le_three (g : CycleTwoChordGraph) :
    g.chordJunctionBagSupWidth ≤ 3 := by
  dsimp [chordJunctionBagSupWidth, chordJunctionBagFamily]
  refine Finset.sup_le fun i _ => ?_
  fin_cases i <;>
    simp [chord1StartJunctionBag, chord1EndJunctionBag, chord2StartJunctionBag,
      chord2EndJunctionBag, cycleStepOfNatEndpoint_lt, cycleEdgeGlobalIndexAt_ne_chord1EdgeIndex,
      cycleEdgeGlobalIndexAt_ne_chord2EdgeIndex, Finset.card_insert_of_notMem, Finset.card_singleton]

theorem CycleTwoChordGraph.chord1StartJunctionBag_mem (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt) :
    g.cycleEdgeGlobalIndexAt k hk ∈ g.chord1StartJunctionBag ∧
      g.chord1EdgeIndex ∈ g.chord1StartJunctionBag := by
  subst hk_eq
  dsimp [chord1StartJunctionBag, cycleEdgeGlobalIndexAt, chord1EdgeIndex]
  constructor <;> simp [chord1EdgeIndex_val, cycleEdgeGlobalIndexAt_val, Finset.mem_insert]

theorem CycleTwoChordGraph.chord1EndJunctionBag_mem (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt) :
    g.cycleEdgeGlobalIndexAt k hk ∈ g.chord1EndJunctionBag ∧
      g.chord1EdgeIndex ∈ g.chord1EndJunctionBag := by
  subst hk_eq
  dsimp [chord1EndJunctionBag, cycleEdgeGlobalIndexAt, chord1EdgeIndex]
  constructor <;> simp [chord1EdgeIndex_val, cycleEdgeGlobalIndexAt_val, Finset.mem_insert]

theorem CycleTwoChordGraph.chord2StartJunctionBag_mem (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt) :
    g.cycleEdgeGlobalIndexAt k hk ∈ g.chord2StartJunctionBag ∧
      g.chord2EdgeIndex ∈ g.chord2StartJunctionBag := by
  subst hk_eq
  dsimp [chord2StartJunctionBag, cycleEdgeGlobalIndexAt, chord2EdgeIndex]
  constructor <;> simp [chord2EdgeIndex_val, cycleEdgeGlobalIndexAt_val, Finset.mem_insert]

theorem CycleTwoChordGraph.chord2EndJunctionBag_mem (g : CycleTwoChordGraph) (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt) :
    g.cycleEdgeGlobalIndexAt k hk ∈ g.chord2EndJunctionBag ∧
      g.chord2EdgeIndex ∈ g.chord2EndJunctionBag := by
  subst hk_eq
  dsimp [chord2EndJunctionBag, cycleEdgeGlobalIndexAt, chord2EdgeIndex]
  constructor <;> simp [chord2EdgeIndex_val, cycleEdgeGlobalIndexAt_val, Finset.mem_insert]

/-! ## Block 5: short-arc indexing (three non-long arcs) -/

def nonLongArcIdx (longIdx : Fin 4) : Fin 3 → Fin 4
  | 0 =>
    match longIdx with
    | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0
  | 1 =>
    match longIdx with
    | 0 => 2 | 1 => 2 | 2 => 1 | 3 => 1
  | 2 =>
    match longIdx with
    | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 2

theorem nonLongArcIdx_ne (longIdx : Fin 4) (k : Fin 3) : nonLongArcIdx longIdx k ≠ longIdx := by
  fin_cases longIdx <;> fin_cases k <;> decide

def CycleTwoChordGraph.junctionEndpointIdx (g : CycleTwoChordGraph) (endpoint : Fin 4) : Nat :=
  match endpoint with
  | 0 => g.chord1.1
  | 1 => g.chord1.2
  | 2 => g.chord2.1
  | 3 => g.chord2.2

theorem CycleTwoChordGraph.junctionEndpointIdx_lt (g : CycleTwoChordGraph) (endpoint : Fin 4) :
    g.junctionEndpointIdx endpoint < g.n := by
  fin_cases endpoint <;> simp [junctionEndpointIdx] <;> first
    | exact g.chord1_fst_lt
    | exact g.chord1_snd_lt
    | exact g.chord2_fst_lt
    | exact g.chord2_snd_lt

def CycleTwoChordGraph.junctionEndpointStep (g : CycleTwoChordGraph) (endpoint : Fin 4) : Nat :=
  g.cycleStepOfNatEndpoint (g.junctionEndpointIdx endpoint)
    (g.junctionEndpointIdx_lt endpoint)

theorem CycleTwoChordGraph.junctionEndpointStep_zero (g : CycleTwoChordGraph) :
    g.junctionEndpointStep 0 = 0 := by
  unfold junctionEndpointStep junctionEndpointIdx
  exact g.cycleStepOfNatEndpoint_chord1_fst

/-- Start geometry at endpoint `0` holds iff the long arc is arc `0` (`arcEdgeOffset 0 = 0`). -/
theorem CycleTwoChordGraph.junctionStep_eq_arcOffset_at_zero_iff
    (g : CycleTwoChordGraph) (arcIdx : Fin 4) :
    g.junctionEndpointStep 0 = g.arcEdgeOffset arcIdx ↔ arcIdx = 0 := by
  rw [g.junctionEndpointStep_zero]
  constructor
  · intro h
    fin_cases arcIdx
    · rfl
    · simp [arcEdgeOffset] at h
      have := g.cyclicGap_pos 0
      omega
    · simp [arcEdgeOffset] at h
      have := g.cyclicGap_pos 0
      have := g.cyclicGap_pos 1
      omega
    · simp [arcEdgeOffset] at h
      have := g.cyclicGap_pos 0
      have := g.cyclicGap_pos 1
      have := g.cyclicGap_pos 2
      omega
  · intro h
    subst h
    rfl

theorem CycleTwoChordGraph.cycleStepOfNatEndpoint_of_ge_p0 (g : CycleTwoChordGraph) (p : Nat)
    (hp : p < g.n) (hge : g.p0 ≤ p) :
    g.cycleStepOfNatEndpoint p hp = p - g.p0 := by
  unfold cycleStepOfNatEndpoint
  obtain ⟨_, _, _, h3n⟩ := g.ordered
  have hlt : p - g.p0 < g.n := by omega
  have hmod : (p + g.n - g.p0) % g.n = (p - g.p0) % g.n := by
    have hsum : p + g.n - g.p0 = (p - g.p0) + g.n := by omega
    calc (p + g.n - g.p0) % g.n
        = ((p - g.p0) + g.n) % g.n := by rw [hsum]
      _ = (p - g.p0) % g.n := by simpa using Nat.add_mod_left (p - g.p0) g.n
  rw [hmod, Nat.mod_eq_of_lt hlt]

def CycleTwoChordGraph.incomingCycleStepAtEndpoint (g : CycleTwoChordGraph) (endpoint : Fin 4) : Nat :=
  (g.junctionEndpointStep endpoint + g.n - 1) % g.n

theorem CycleTwoChordGraph.incomingCycleStepAtEndpoint_lt (g : CycleTwoChordGraph)
    (endpoint : Fin 4) : g.incomingCycleStepAtEndpoint endpoint < g.n := by
  unfold incomingCycleStepAtEndpoint
  exact Nat.mod_lt _ g.n_pos

def CycleTwoChordGraph.incomingCycleEdgeGlobalIndex (g : CycleTwoChordGraph) (endpoint : Fin 4) :
    Fin (g.n + 2) :=
  g.cycleEdgeGlobalIndexAt (g.incomingCycleStepAtEndpoint endpoint)
    (g.incomingCycleStepAtEndpoint_lt endpoint)

theorem CycleTwoChordGraph.incomingCycleEdgeGlobalIndex_ne_chord1 (g : CycleTwoChordGraph)
    (endpoint : Fin 4) :
    g.incomingCycleEdgeGlobalIndex endpoint ≠ g.chord1EdgeIndex := by
  intro h
  have hval := congrArg Fin.val h
  simp [incomingCycleEdgeGlobalIndex, cycleEdgeGlobalIndexAt_val, chord1EdgeIndex_val] at hval
  have hlt := g.incomingCycleStepAtEndpoint_lt endpoint
  omega

theorem CycleTwoChordGraph.incomingCycleEdgeGlobalIndex_ne_chord2 (g : CycleTwoChordGraph)
    (endpoint : Fin 4) :
    g.incomingCycleEdgeGlobalIndex endpoint ≠ g.chord2EdgeIndex := by
  intro h
  have hval := congrArg Fin.val h
  simp [incomingCycleEdgeGlobalIndex, cycleEdgeGlobalIndexAt_val, chord2EdgeIndex_val] at hval
  have hlt := g.incomingCycleStepAtEndpoint_lt endpoint
  omega

def CycleTwoChordGraph.endpointArcIdx (g : CycleTwoChordGraph) (endpoint : Fin 4) : Fin 4 :=
  match g.pairing with
  | .crossing =>
    match endpoint with
    | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2
  | .nested =>
    match endpoint with
    | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2
  | .disjoint =>
    match endpoint with
    | 0 => 0 | 1 => 0 | 2 => 2 | 3 => 2

def CycleTwoChordGraph.junctionShortArcAt (g : CycleTwoChordGraph) (longIdx : Fin 4)
    (endpoint : Fin 4) : Option (Fin 4) :=
  let a := g.endpointArcIdx endpoint
  if a = longIdx then none else some a

/-- Endpoint lies on the long arc iff `junctionShortArcAt` is `none`. -/
theorem CycleTwoChordGraph.junctionShortArcAt_none_iff (g : CycleTwoChordGraph)
    (longIdx endpoint : Fin 4) :
    g.junctionShortArcAt longIdx endpoint = none ↔ g.endpointArcIdx endpoint = longIdx := by
  unfold junctionShortArcAt
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro h
    subst h
    simp [junctionShortArcAt]

/-- Nested pairing: junction cycle step matches `arcEdgeOffset` of the endpoint's arc index. -/
theorem CycleTwoChordGraph.junctionEndpointStep_eq_arcEdgeOffset_endpointArcIdx_nested
    (g : CycleTwoChordGraph) (hn : g.pairing = ChordPairing.nested) (endpoint : Fin 4) :
    g.junctionEndpointStep endpoint = g.arcEdgeOffset (g.endpointArcIdx endpoint) := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  fin_cases endpoint
  · simp [junctionEndpointStep, junctionEndpointIdx, endpointArcIdx, arcEdgeOffset, cyclicGap, chord1, hn,
      cycleStepOfNatEndpoint, g.cycleStepOfNatEndpoint_chord1_fst]
  · simp only [junctionEndpointStep, junctionEndpointIdx, hn]
    rw [g.cycleStepOfNatEndpoint_of_ge_p0 g.chord1.2 g.chord1_snd_lt (by simp [hn, chord1]; omega)]
    simp [endpointArcIdx, arcEdgeOffset, cyclicGap, hn, chord1]
    omega
  · simp only [junctionEndpointStep, junctionEndpointIdx, hn]
    rw [g.cycleStepOfNatEndpoint_of_ge_p0 g.chord2.1 g.chord2_fst_lt (by simp [hn, chord2]; omega)]
    simp [endpointArcIdx, arcEdgeOffset, cyclicGap, hn, chord2]
  · simp only [junctionEndpointStep, junctionEndpointIdx, hn]
    rw [g.cycleStepOfNatEndpoint_of_ge_p0 g.chord2.2 g.chord2_snd_lt (by simp [hn, chord2]; omega)]
    simp [endpointArcIdx, arcEdgeOffset, cyclicGap, hn, chord2]
    omega

def CycleTwoChordGraph.arcSlidingBag (g : CycleTwoChordGraph) (a : Fin 4) (j : Nat)
    (hj : j < g.cyclicGap a) : Finset (Fin (g.n + 2)) :=
  g.longArcSlidingBag a j hj

def CycleTwoChordGraph.shortArcSlidingBag (g : CycleTwoChordGraph) (a : Fin 4) (j : Nat)
    (hj : j < g.cyclicGap a) : Finset (Fin (g.n + 2)) :=
  g.arcSlidingBag a j hj

def CycleTwoChordGraph.shortArcBagFamily (g : CycleTwoChordGraph) (a : Fin 4)
    (i : Fin (g.cyclicGap a)) : Finset (Fin (g.n + 2)) :=
  g.shortArcSlidingBag a i.val i.isLt

theorem CycleTwoChordGraph.shortArcSlidingBag_card_le_four (g : CycleTwoChordGraph) (a : Fin 4)
    (j : Nat) (hj : j < g.cyclicGap a) :
    (g.shortArcSlidingBag a j hj).card ≤ 4 :=
  g.longArcSlidingBag_card_le_four a j hj

theorem CycleTwoChordGraph.shortArcBag_width_le_three (g : CycleTwoChordGraph) (a : Fin 4)
    (i : Fin (g.cyclicGap a)) :
    (g.shortArcBagFamily a i).card - 1 ≤ 3 := by
  have h := g.shortArcSlidingBag_card_le_four a i.val i.isLt
  simp only [shortArcBagFamily]
  omega

private theorem card_pair_union_le_two {α} [DecidableEq α] (x y : α) :
    ({x} ∪ {y} : Finset α).card ≤ 2 := by
  rw [Finset.card_union]
  simp only [Finset.card_singleton, Finset.inter_singleton, Finset.card_singleton]
  split_ifs <;> omega

theorem CycleTwoChordGraph.shortArcSlidingBag_zero_card_le_two (g : CycleTwoChordGraph) (a : Fin 4)
    (hgap : 0 < g.cyclicGap a) :
    (g.shortArcSlidingBag a 0 (Nat.zero_lt_of_lt hgap)).card ≤ 2 := by
  have hj := Nat.zero_lt_of_lt hgap
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hgap) with hgap1 | hgap2
  · have hgap1' : g.cyclicGap a = 1 := hgap1.symm
    simp [shortArcSlidingBag, arcSlidingBag, longArcSlidingBag, hgap1', Option.toFinset,
      Finset.card_singleton]
  · have hnext : 0 + 1 < g.cyclicGap a := hgap2
    have hcard : (g.longArcSlidingBag a 0 hj).card ≤ 2 := by
      unfold longArcSlidingBag
      have hnot : ¬ (0 : Nat) < 0 := by decide
      simp only [hnot, hnext, Option.toFinset, Finset.empty_union]
      exact card_pair_union_le_two _ _
    simpa [shortArcSlidingBag, arcSlidingBag] using hcard

theorem CycleTwoChordGraph.shortArcSlidingBag_covers_consecutive (g : CycleTwoChordGraph) (a : Fin 4)
    (j : Nat) (hj : j < g.cyclicGap a) (hj' : j + 1 < g.cyclicGap a) :
    let base := g.arcEdgeOffset a + j
    g.cycleEdgeGlobalIndexAt base (by
      have := g.arcEdgeOffset_add_lt a j hj
      omega) ∈ g.shortArcSlidingBag a j hj ∧
      g.cycleEdgeGlobalIndexAt (base + 1) (by
        have := g.arcEdgeOffset_add_lt a (j + 1) hj'
        omega) ∈ g.shortArcSlidingBag a j hj :=
  g.longArcSlidingBag_covers_arc_consecutive a j hj hj'

theorem CycleTwoChordGraph.shortArcSlidingBag_zero_adj_arcConsecutive (g : CycleTwoChordGraph)
    (a : Fin 4) (hgap : 1 < g.cyclicGap a) :
    g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a) (g.arcEdgeOffset_add_lt a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap))) ∈
        g.shortArcSlidingBag a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)) ∧
      g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset a + 1) (g.arcEdgeOffset_add_lt a 1 hgap) ∈
        g.shortArcSlidingBag a 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)) := by
  have hj := Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)
  have hj' : 0 + 1 < g.cyclicGap a := hgap
  simpa using g.shortArcSlidingBag_covers_consecutive a 0 hj hj'

/-! ## Conditional long-arc block -/

structure NoncrossingLongArcBlock (g : CycleTwoChordGraph) where
  arcIdx : Fin 4
  hlen : 0 < g.cyclicGap arcIdx
  hnc : ¬ g.chordsCross
  hΔ : g.isDelta3Admissible
  hnd : g.isNondegenerate

namespace NoncrossingLongArcBlock

variable {g : CycleTwoChordGraph} (blk : NoncrossingLongArcBlock g)

def bagSupWidth : Nat :=
  (Finset.univ : Finset (Fin (g.cyclicGap blk.arcIdx))).sup
    fun i => (g.longArcBagFamily blk.arcIdx i).card - 1

theorem bag_width_le_three : blk.bagSupWidth ≤ 3 :=
  Finset.sup_le fun i _ => g.longArcBag_width_le_three blk.arcIdx i

end NoncrossingLongArcBlock

/-! ## Assumptions bundle (Route F+A) -/

structure NoncrossingPathDecompAssumptions (g : CycleTwoChordGraph) extends
    NoncrossingLongArcBlock g where
  edgeBij : GraphEdgeBijection g
  /-- Optional junction–junction tree edges (running-intersection bridges; default none). -/
  genericJunctionBridge : Fin 4 → Fin 4 → Prop := fun _ _ => False
  /-- Junction-bridge relation is symmetric (needed for `genericDecompAdj_symm`). -/
  genericJunctionBridge_symm :
      ∀ e e', genericJunctionBridge e e' → genericJunctionBridge e' e := by
    intro e e' h
    cases h
  /-- Junction-bridge relation is irreflexive (needed for `genericDecompAdj` loopless). -/
  genericJunctionBridge_irrefl :
      ∀ e, ¬ genericJunctionBridge e e := by
    intro e h
    cases h
  /-- Suppress longSeg-zero ↔ junction glue replaced by `genericJunctionBridge`. -/
  genericLongSegStartBridgeSuppress : Fin 4 → Prop := fun _ => False
  /-- Suppress longSeg-last ↔ junction glue replaced by `genericJunctionBridge`. -/
  genericLongSegEndBridgeSuppress : Fin 4 → Prop := fun _ => False
  /-- Bridge partner at suppressed start junction (none when not suppressed). -/
  genericLongSegStartBridgePartner : Fin 4 → Option (Fin 4) := fun _ => none
  /-- Bridge partner at suppressed end junction (none when not suppressed). -/
  genericLongSegEndBridgePartner : Fin 4 → Option (Fin 4) := fun _ => none
  /-- Optional extra edges on longSeg bags (running-intersection bridges; default none). -/
  genericLongSegBagExtension (j : Fin (g.cyclicGap arcIdx)) : Finset g.toSimpleGraph.edgeSet := ∅
  /-- Optional extra edges on enriched junction bags (running-intersection bridges). -/
  genericJunctionBagExtension (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet := ∅
  /-- Optional trim from enriched junction bags when extension replaces coverage. -/
  genericJunctionBagTrim (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet := ∅
  /-- Partner exists and bridges when start glue is suppressed. -/
  genericLongSegStartBridgePartner_spec :
    ∀ e, genericLongSegStartBridgeSuppress e →
      ∃ e', genericLongSegStartBridgePartner e = some e' ∧ genericJunctionBridge e' e := by
    intro e h
    exact False.elim h
  /-- Partner exists and bridges when end glue is suppressed. -/
  genericLongSegEndBridgePartner_spec :
    ∀ e, genericLongSegEndBridgeSuppress e →
      ∃ e', genericLongSegEndBridgePartner e = some e' ∧ genericJunctionBridge e' e := by
    intro e h
    exact False.elim h
  /-- Start suppress at endpoint 2 uses partner junction 0 (c8 pilot). -/
  genericLongSegStartBridgePartner_two :
      genericLongSegStartBridgeSuppress 2 →
        genericLongSegStartBridgePartner 2 = some 0 := by
    intro h
    exact False.elim h
  /-- End suppress at endpoint 3 uses partner junction 2 (c8 pilot). -/
  genericLongSegEndBridgePartner_three :
      genericLongSegEndBridgeSuppress 3 →
        genericLongSegEndBridgePartner 3 = some 2 := by
    intro h
    exact False.elim h
  /-- Endpoint 0 is never start-bridge-suppressed (only `longStartEndpoint 1` may be). -/
  genericLongSegStartBridgeSuppress_not_at_zero :
      ¬ genericLongSegStartBridgeSuppress 0 := by
    intro h
    exact False.elim h
  /-- Endpoint 1 is never end-bridge-suppressed (only `longEndEndpoint 1` may be). -/
  genericLongSegEndBridgeSuppress_not_at_one :
      ¬ genericLongSegEndBridgeSuppress 1 := by
    intro h
    exact False.elim h
  /-- Optional long-seg bag extension is empty by default. -/
  genericLongSegBagExtension_empty :
      ∀ j, genericLongSegBagExtension j = ∅ := by
    intro j
    rfl
  genericJunctionBagExtension_empty :
      ∀ endpoint, genericJunctionBagExtension endpoint = ∅ := by
    intro endpoint
    rfl
  genericJunctionBagTrim_empty :
      ∀ endpoint, genericJunctionBagTrim endpoint = ∅ := by
    intro endpoint
    rfl

namespace NoncrossingPathDecompAssumptions

variable {g : CycleTwoChordGraph} (hyp : NoncrossingPathDecompAssumptions g)

noncomputable def longArcLineGraphBag (i : Fin (g.cyclicGap hyp.arcIdx)) :
    Finset g.toSimpleGraph.edgeSet :=
  (g.longArcBagFamily hyp.arcIdx i).image hyp.edgeBij.edgeEquiv

theorem arcEdgeCoverConsecutive (j : Nat) (hj : j < g.cyclicGap hyp.arcIdx)
    (hj' : j + 1 < g.cyclicGap hyp.arcIdx) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
      have := g.arcEdgeOffset_add_lt hyp.arcIdx j hj
      omega)) ∈ hyp.longArcLineGraphBag ⟨j, hj⟩ ∧
      hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j + 1) (by
        have := g.arcEdgeOffset_add_lt hyp.arcIdx (j + 1) hj'
        omega)) ∈ hyp.longArcLineGraphBag ⟨j, hj⟩ := by
  dsimp [longArcLineGraphBag, CycleTwoChordGraph.longArcBagFamily, CycleTwoChordGraph.longArcSlidingBag]
  have hcover := g.longArcSlidingBag_covers_arc_consecutive hyp.arcIdx j hj hj'
  constructor
  · exact Finset.mem_image.mpr ⟨_, hcover.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hcover.2, rfl⟩

private theorem longArc_cycleIndex_succ_lt_n (p : Nat) (hp : p + 1 < g.cyclicGap hyp.arcIdx) :
    g.arcEdgeOffset hyp.arcIdx + p + 1 < g.n := by
  have := g.arcEdgeOffset_add_lt hyp.arcIdx (p + 1) hp
  simpa [Nat.add_assoc] using this

private theorem longArcSlidingBag_mem_arcLocalPos (j : Nat) (hj : j < g.cyclicGap hyp.arcIdx)
    (k : Fin (g.n + 2)) (hk : k ∈ g.longArcSlidingBag hyp.arcIdx j hj) :
    ∃ (p : Nat) (hp : p < g.cyclicGap hyp.arcIdx),
      k = g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + p)
        (g.arcEdgeOffset_add_lt hyp.arcIdx p hp) := by
  dsimp [CycleTwoChordGraph.longArcSlidingBag] at hk
  set base := g.arcEdgeOffset hyp.arcIdx + j
  by_cases hjpos : 0 < j
  · by_cases hjnext : j + 1 < g.cyclicGap hyp.arcIdx
    · simp [hjpos, hjnext, base, Option.toFinset, Finset.mem_union, Finset.mem_insert] at hk
      rcases hk with hk | hk | hk
      · subst hk
        refine ⟨j - 1, by omega, Fin.eq_of_val_eq (by
          simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base]; omega)⟩
      · subst hk
        refine ⟨j, hj, Fin.eq_of_val_eq (by
          simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base])⟩
      · subst hk
        refine ⟨j + 1, hjnext, Fin.eq_of_val_eq (by
          simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base]; omega)⟩
    · simp [hjpos, hjnext, base, Option.toFinset, Finset.mem_union, Finset.mem_insert] at hk
      rcases hk with hk | hk
      · subst hk
        refine ⟨j - 1, by omega, Fin.eq_of_val_eq (by
          simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base]; omega)⟩
      · subst hk
        refine ⟨j, hj, Fin.eq_of_val_eq (by
          simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base])⟩
  · have hj0 : j = 0 := by omega
    subst hj0
    by_cases hjnext : 1 < g.cyclicGap hyp.arcIdx
    · simp [hjpos, hjnext, base, Option.toFinset, Finset.mem_union, Finset.mem_insert] at hk
      rcases hk with hk | hk
      · subst hk
        exact ⟨0, hj, Fin.eq_of_val_eq (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base])⟩
      · subst hk
        exact ⟨1, hjnext, Fin.eq_of_val_eq (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base])⟩
    · simp [hjpos, hjnext, base, Option.toFinset, Finset.mem_union, Finset.mem_insert] at hk
      subst hk
      exact ⟨0, hj, Fin.eq_of_val_eq (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val, base])⟩

private theorem longArcLocalPos_sharedVertex_consecutive {p₁ p₂ : Nat}
    (hp₁ : p₁ < g.cyclicGap hyp.arcIdx) (hp₂ : p₂ < g.cyclicGap hyp.arcIdx) (hne : p₁ ≠ p₂)
    {v : Fin g.n}
    (hv1 : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset hyp.arcIdx + p₁)
      (g.arcEdgeOffset_add_lt hyp.arcIdx p₁ hp₁))
    (hv2 : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset hyp.arcIdx + p₂)
      (g.arcEdgeOffset_add_lt hyp.arcIdx p₂ hp₂)) :
    p₁ + 1 = p₂ ∨ p₂ + 1 = p₁ :=
  g.arcLocalEdgePos_sharedVertex_consecutive hyp.arcIdx hp₁ hp₂ hne hv1 hv2

/-!
  Long-arc global `lineGraph` edge cover chain (see `longArcLineGraphBag_edgeCover` below).
-/

noncomputable def junctionLineGraphBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  (g.chordJunctionBagFamily endpoint).image hyp.edgeBij.edgeEquiv

def combinedBagSupWidth : Nat :=
  max ((Finset.univ : Finset (Fin (g.cyclicGap hyp.arcIdx))).sup
      fun i => (g.longArcBagFamily hyp.arcIdx i).card - 1)
    g.chordJunctionBagSupWidth

theorem combinedBagSupWidth_le_three : combinedBagSupWidth hyp ≤ 3 := by
  dsimp [combinedBagSupWidth]
  exact max_le (Finset.sup_le fun i _ => g.longArcBag_width_le_three hyp.arcIdx i)
    g.chordJunctionBagSupWidth_le_three

/-! ### Block 3: arc path segment on `certPathGraph` -/

def longArcLen : Nat := g.cyclicGap hyp.arcIdx

def longArcCertPathGraph : SimpleGraph (Fin hyp.longArcLen) :=
  certPathGraph hyp.longArcLen

theorem longArcCertPathGraph_isTree_of_two (h : hyp.longArcLen = 2) :
    hyp.longArcCertPathGraph.IsTree := by
  rw [longArcCertPathGraph, h]
  exact certPathGraph_two_isTree

theorem longArcCertPathGraph_isTree_of_one (h : hyp.longArcLen = 1) :
    hyp.longArcCertPathGraph.IsTree := by
  rw [longArcCertPathGraph, h]
  exact certPathGraph_one_isTree

noncomputable def longArcSegmentBag (i : Fin hyp.longArcLen) : Finset g.toSimpleGraph.edgeSet :=
  hyp.longArcLineGraphBag i

theorem longArcLineGraphBag_mem_iff_arcIndex (j : Nat) (hj : j < hyp.longArcLen)
    (e : g.toSimpleGraph.edgeSet) :
    e ∈ hyp.longArcLineGraphBag ⟨j, hj⟩ ↔
      ∃ k ∈ g.longArcBagFamily hyp.arcIdx ⟨j, by
          have hlen : hyp.longArcLen = g.cyclicGap hyp.arcIdx := rfl
          exact hlen ▸ hj⟩,
        hyp.edgeBij.edgeEquiv k = e := by
  constructor
  · intro he
    dsimp [longArcLineGraphBag, CycleTwoChordGraph.longArcBagFamily] at he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    exact ⟨k, hk, rfl⟩
  · intro ⟨k, hk, hk_eq⟩
    subst hk_eq
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

theorem longArcLineGraphBag_edgeCover
    {e₁ e₂ : g.toSimpleGraph.edgeSet}
    (hadj : (lineGraph g.toSimpleGraph).Adj e₁ e₂)
    (hj₁ : ∃ j : Fin hyp.longArcLen, e₁ ∈ hyp.longArcLineGraphBag j)
    (hj₂ : ∃ j : Fin hyp.longArcLen, e₂ ∈ hyp.longArcLineGraphBag j) :
    ∃ j : Fin hyp.longArcLen, e₁ ∈ hyp.longArcLineGraphBag j ∧ e₂ ∈ hyp.longArcLineGraphBag j := by
  obtain ⟨j₁, hj₁'⟩ := hj₁
  obtain ⟨j₂, hj₂'⟩ := hj₂
  obtain ⟨k₁, hk₁, hk₁_eq⟩ := (hyp.longArcLineGraphBag_mem_iff_arcIndex j₁.val j₁.isLt e₁).mp hj₁'
  obtain ⟨k₂, hk₂, hk₂_eq⟩ := (hyp.longArcLineGraphBag_mem_iff_arcIndex j₂.val j₂.isLt e₂).mp hj₂'
  rw [← hk₁_eq, ← hk₂_eq] at hadj
  rw [lineGraph_adj_iff] at hadj
  obtain ⟨hne, v, hv1, hv2⟩ := hadj
  have hv1_graph : v ∈ g.graphEdgeSym2 k₁ := by
    rw [← hyp.edgeBij.lineGraph_vertex_eq k₁]
    exact hv1
  have hv2_graph : v ∈ g.graphEdgeSym2 k₂ := by
    rw [← hyp.edgeBij.lineGraph_vertex_eq k₂]
    exact hv2
  obtain ⟨p₁, hp₁, hp₁_eq⟩ := longArcSlidingBag_mem_arcLocalPos hyp j₁.val j₁.isLt k₁ hk₁
  obtain ⟨p₂, hp₂, hp₂_eq⟩ := longArcSlidingBag_mem_arcLocalPos hyp j₂.val j₂.isLt k₂ hk₂
  have hv1' : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset hyp.arcIdx + p₁)
      (g.arcEdgeOffset_add_lt hyp.arcIdx p₁ hp₁) := by
    rw [← g.graphEdgeSym2_cycleEdgeGlobalIndexAt, ← hp₁_eq]
    exact hv1_graph
  have hv2' : v ∈ g.cyclicCycleEdgeSym2 (g.arcEdgeOffset hyp.arcIdx + p₂)
      (g.arcEdgeOffset_add_lt hyp.arcIdx p₂ hp₂) := by
    rw [← g.graphEdgeSym2_cycleEdgeGlobalIndexAt, ← hp₂_eq]
    exact hv2_graph
  by_cases hpeq : p₁ = p₂
  · subst hpeq
    have hk_eq : k₁ = k₂ := by
      rw [hp₁_eq, hp₂_eq]
    have he₁₂ : hyp.edgeBij.edgeEquiv k₁ = hyp.edgeBij.edgeEquiv k₂ := by
      rw [hk_eq]
    exact (hne he₁₂).elim
  · have hconsec := longArcLocalPos_sharedVertex_consecutive hyp hp₁ hp₂ hpeq hv1' hv2'
    rcases hconsec with hconsec | hconsec
    · have hp₁' : p₁ + 1 < g.cyclicGap hyp.arcIdx := by omega
      have hk₂_succ : k₂ = g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + p₁ + 1)
          (g.arcEdgeOffset_add_lt hyp.arcIdx (p₁ + 1) hp₁') := by
        rw [hp₂_eq]
        exact Fin.eq_of_val_eq (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val]; omega)
      refine ⟨⟨p₁, hp₁⟩, ?_, ?_⟩
      · rw [← hk₁_eq, hp₁_eq]
        exact (arcEdgeCoverConsecutive hyp p₁ hp₁ hp₁').1
      · rw [← hk₂_eq, hk₂_succ]
        exact (arcEdgeCoverConsecutive hyp p₁ hp₁ hp₁').2
    · have hp₂' : p₂ + 1 < g.cyclicGap hyp.arcIdx := by omega
      have hk₁_succ : k₁ = g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + p₂ + 1)
          (g.arcEdgeOffset_add_lt hyp.arcIdx (p₂ + 1) hp₂') := by
        rw [hp₁_eq]
        exact Fin.eq_of_val_eq (by simp [CycleTwoChordGraph.cycleEdgeGlobalIndexAt_val]; omega)
      refine ⟨⟨p₂, hp₂⟩, ?_, ?_⟩
      · rw [← hk₁_eq, hk₁_succ]
        exact (arcEdgeCoverConsecutive hyp p₂ hp₂ hp₂').2
      · rw [← hk₂_eq, hp₂_eq]
        exact (arcEdgeCoverConsecutive hyp p₂ hp₂ hp₂').1

theorem longArcSegment_preconnected_of_interval (x : g.toSimpleGraph.edgeSet) (a b : Nat)
    (ha : a < hyp.longArcLen) (hb : b < hyp.longArcLen) (hab : a ≤ b)
    (hset : {w : Fin hyp.longArcLen | x ∈ hyp.longArcSegmentBag w} =
      certPathGraphInterval hyp.longArcLen a b) :
    hyp.longArcCertPathGraph.induce {w : Fin hyp.longArcLen | x ∈ hyp.longArcSegmentBag w} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected hyp.longArcLen a b ha hb hab

theorem longArcSegment_preconnected_bag (x : g.toSimpleGraph.edgeSet) (a b : Nat)
    (ha : a < hyp.longArcLen) (hb : b < hyp.longArcLen) (hab : a ≤ b)
    (hset : {w : Fin hyp.longArcLen | x ∈ hyp.longArcSegmentBag w} =
      certPathGraphInterval hyp.longArcLen a b) :
    hyp.longArcCertPathGraph.induce {w : Fin hyp.longArcLen | x ∈ hyp.longArcSegmentBag w} |>.Preconnected :=
  hyp.longArcSegment_preconnected_of_interval x a b ha hb hab hset

structure LongArcSegmentFragment (g : CycleTwoChordGraph) (hyp : NoncrossingPathDecompAssumptions g) where
  isTree : hyp.longArcCertPathGraph.IsTree
  edgeCover_consecutive :
    ∀ (j : Nat) (hj : j < hyp.longArcLen) (hj' : j + 1 < hyp.longArcLen),
      hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j) (by
        have := g.arcEdgeOffset_add_lt hyp.arcIdx j hj; omega)) ∈ hyp.longArcLineGraphBag ⟨j, hj⟩ ∧
      hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + j + 1) (by
        have := g.arcEdgeOffset_add_lt hyp.arcIdx (j + 1) hj'; omega)) ∈ hyp.longArcLineGraphBag ⟨j, hj⟩

/-! ### Block 3: junction glue at chord endpoints -/

private theorem cyclicCycleEdgeSym2_mem_endpoint (k : Nat) (hk : k < g.n) (endpoint : Fin g.n)
    (h : endpoint = g.cyclicEndpointFin k ∨ endpoint = g.cyclicEndpointFin (k + 1)) :
    endpoint ∈ g.cyclicCycleEdgeSym2 k hk := by
  simp [CycleTwoChordGraph.cyclicCycleEdgeSym2, Sym2.mem_iff]
  cases h <;> simp [*]

theorem junctionLineGraphBag_mem_chord1Start_cycle (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt k hk) ∈ hyp.junctionLineGraphBag 0 ∧
      hyp.edgeBij.edgeEquiv g.chord1EdgeIndex ∈ hyp.junctionLineGraphBag 0 := by
  have hmem := g.chord1StartJunctionBag_mem k hk hk_eq
  constructor
  · exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hmem.2, rfl⟩

theorem junctionLineGraphBag_chord1Start_edgeCover (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt) :
    ∃ w : Fin 4,
      hyp.edgeBij.lineGraphVertex (g.cycleEdgeGlobalIndexAt k hk) ∈ hyp.junctionLineGraphBag w ∧
        hyp.edgeBij.lineGraphVertex g.chord1EdgeIndex ∈ hyp.junctionLineGraphBag w :=
  ⟨0, junctionLineGraphBag_mem_chord1Start_cycle hyp k hk hk_eq⟩

theorem junctionLineGraphBag_mem_chord1End_cycle (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt k hk) ∈ hyp.junctionLineGraphBag 1 ∧
      hyp.edgeBij.edgeEquiv g.chord1EdgeIndex ∈ hyp.junctionLineGraphBag 1 := by
  have hmem := g.chord1EndJunctionBag_mem k hk hk_eq
  constructor
  · exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hmem.2, rfl⟩

theorem junctionLineGraphBag_mem_chord2Start_cycle (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt k hk) ∈ hyp.junctionLineGraphBag 2 ∧
      hyp.edgeBij.edgeEquiv g.chord2EdgeIndex ∈ hyp.junctionLineGraphBag 2 := by
  have hmem := g.chord2StartJunctionBag_mem k hk hk_eq
  constructor
  · exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hmem.2, rfl⟩

theorem junctionLineGraphBag_mem_chord2End_cycle (k : Nat) (hk : k < g.n)
    (hk_eq : k = g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt k hk) ∈ hyp.junctionLineGraphBag 3 ∧
      hyp.edgeBij.edgeEquiv g.chord2EdgeIndex ∈ hyp.junctionLineGraphBag 3 := by
  have hmem := g.chord2EndJunctionBag_mem k hk hk_eq
  constructor
  · exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hmem.2, rfl⟩

/-! ### Block 5: enriched junction bags (junction ∪ incoming ∪ short arc at j = 0) -/

noncomputable def shortArcLineGraphBag (shortArc : Fin 4) (i : Fin (g.cyclicGap shortArc)) :
    Finset g.toSimpleGraph.edgeSet :=
  (g.shortArcBagFamily shortArc i).image hyp.edgeBij.edgeEquiv

theorem shortArcEdgeCoverConsecutive (shortArc : Fin 4) (_hne : shortArc ≠ hyp.arcIdx) (j : Nat)
    (hj : j < g.cyclicGap shortArc) (hj' : j + 1 < g.cyclicGap shortArc) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + j) (by
      have := g.arcEdgeOffset_add_lt shortArc j hj
      omega)) ∈ hyp.shortArcLineGraphBag shortArc ⟨j, hj⟩ ∧
      hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + j + 1) (by
        have := g.arcEdgeOffset_add_lt shortArc (j + 1) hj'
        omega)) ∈ hyp.shortArcLineGraphBag shortArc ⟨j, hj⟩ := by
  dsimp [shortArcLineGraphBag, CycleTwoChordGraph.shortArcBagFamily,
    CycleTwoChordGraph.shortArcSlidingBag, CycleTwoChordGraph.arcSlidingBag,
    CycleTwoChordGraph.longArcSlidingBag]
  have hcover := g.shortArcSlidingBag_covers_consecutive shortArc j hj hj'
  constructor
  · exact Finset.mem_image.mpr ⟨_, hcover.1, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, hcover.2, rfl⟩

theorem shortArcEdgeCoverConsecutive_zero (shortArc : Fin 4) (hne : shortArc ≠ hyp.arcIdx)
    (hgap : 1 < g.cyclicGap shortArc) :
    hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc) (by
      have := g.arcEdgeOffset_add_lt shortArc 0 (Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap))
      omega)) ∈ hyp.shortArcLineGraphBag shortArc ⟨0, Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)⟩ ∧
      hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + 1) (by
        exact g.arcEdgeOffset_add_lt shortArc 1 hgap)) ∈
        hyp.shortArcLineGraphBag shortArc ⟨0, Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)⟩ := by
  have hj := Nat.zero_lt_of_lt (Nat.lt_trans (by decide : (0 : Nat) < 1) hgap)
  exact hyp.shortArcEdgeCoverConsecutive shortArc hne 0 hj hgap

noncomputable def incomingJunctionLineGraphBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  {hyp.edgeBij.edgeEquiv (g.incomingCycleEdgeGlobalIndex endpoint)}

/-- When `junctionShortArcAt = some a`, add the short-arc successor edge (not the full sliding bag). -/
noncomputable def shortArcJunctionExtraBag (endpoint : Fin 4) (shortArc : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  if h : 1 < g.cyclicGap shortArc then
    {hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + 1) (by
      exact g.arcEdgeOffset_add_lt shortArc 1 h))}
  else ∅

def junctionLongArcAnchor (endpoint : Fin 4) : Option (Fin hyp.longArcLen) :=
  match endpoint with
  | 0 => some ⟨0, hyp.hlen⟩
  | 1 => some ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen (by omega)⟩
  | 2 => some ⟨0, hyp.hlen⟩
  | 3 => some ⟨hyp.longArcLen - 1, Nat.sub_lt hyp.hlen (by omega)⟩

/-- When the long arc meets this endpoint at its last segment, include that segment edge. -/
noncomputable def longArcJunctionTailBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  if g.junctionShortArcAt hyp.arcIdx endpoint ≠ none then
    ∅
  else
    match hyp.junctionLongArcAnchor endpoint with
    | none => ∅
    | some anchor =>
      if anchor.val + 1 = hyp.longArcLen then
        {hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + anchor.val) (by
          exact g.arcEdgeOffset_add_lt hyp.arcIdx anchor.val anchor.isLt))}
      else ∅

/-- When the long arc meets this endpoint at its first segment (`anchor = 0`), include that edge. -/
noncomputable def longArcJunctionHeadBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  if g.junctionShortArcAt hyp.arcIdx endpoint ≠ none then
    ∅
  else
    match hyp.junctionLongArcAnchor endpoint with
    | none => ∅
    | some anchor =>
      if anchor.val = 0 then
        {hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + 0) (by
          exact g.arcEdgeOffset_add_lt hyp.arcIdx 0 hyp.hlen))}
      else ∅

noncomputable def enrichedJunctionBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  let base := hyp.junctionLineGraphBag endpoint
  let incoming := hyp.incomingJunctionLineGraphBag endpoint
  match g.junctionShortArcAt hyp.arcIdx endpoint with
  | none => base ∪ incoming ∪ hyp.longArcJunctionTailBag endpoint
  | some a => base ∪ incoming ∪ hyp.shortArcJunctionExtraBag endpoint a

noncomputable def enrichedJunctionLineGraphBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  hyp.enrichedJunctionBag endpoint

theorem enrichedJunctionBag_mem_junction (endpoint : Fin 4) (e : g.toSimpleGraph.edgeSet)
    (he : e ∈ hyp.junctionLineGraphBag endpoint) :
    e ∈ hyp.enrichedJunctionBag endpoint := by
  unfold enrichedJunctionBag
  match g.junctionShortArcAt hyp.arcIdx endpoint with
  | none => exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  | some _ => exact Finset.mem_union_left _ (Finset.mem_union_left _ he)

theorem enrichedJunctionBag_mem_incoming (endpoint : Fin 4) :
    hyp.edgeBij.edgeEquiv (g.incomingCycleEdgeGlobalIndex endpoint) ∈
      hyp.enrichedJunctionBag endpoint := by
  have hin : hyp.edgeBij.edgeEquiv (g.incomingCycleEdgeGlobalIndex endpoint) ∈
      hyp.incomingJunctionLineGraphBag endpoint := by
    simp [incomingJunctionLineGraphBag]
  have hbi : hyp.edgeBij.edgeEquiv (g.incomingCycleEdgeGlobalIndex endpoint) ∈
      hyp.junctionLineGraphBag endpoint ∪ hyp.incomingJunctionLineGraphBag endpoint :=
    Finset.mem_union_right _ hin
  unfold enrichedJunctionBag
  match g.junctionShortArcAt hyp.arcIdx endpoint with
  | none => exact Finset.mem_union_left _ hbi
  | some _ => exact Finset.mem_union_left _ hbi

theorem enrichedJunctionBag_mem_longArcTail (endpoint : Fin 4)
    (hnone : g.junctionShortArcAt hyp.arcIdx endpoint = none)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionTailBag endpoint) :
    e ∈ hyp.enrichedJunctionBag endpoint := by
  unfold enrichedJunctionBag
  rw [hnone]
  exact Finset.mem_union_right _ he

theorem enrichedJunctionBag_mem_shortArcExtra (endpoint : Fin 4) (shortArc : Fin 4)
    (hshort : g.junctionShortArcAt hyp.arcIdx endpoint = some shortArc)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.shortArcJunctionExtraBag endpoint shortArc) :
    e ∈ hyp.enrichedJunctionBag endpoint := by
  unfold enrichedJunctionBag
  rw [hshort]
  exact Finset.mem_union_right _ he

theorem longArcJunctionTailBag_mem_longArcLineGraphBag (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionTailBag endpoint) :
    ∃ j : Fin hyp.longArcLen, e ∈ hyp.longArcLineGraphBag j := by
  unfold longArcJunctionTailBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx endpoint ≠ none
  · simp [hshort] at he
  · simp [hshort] at he
    cases hanchor : hyp.junctionLongArcAnchor endpoint with
    | none => exact absurd he (by simp [hanchor] at he)
    | some anchor =>
      by_cases htail : anchor.val + 1 = hyp.longArcLen
      · simp [hanchor, htail] at he
        obtain rfl := he
        refine ⟨⟨anchor.val, anchor.isLt⟩, ?_⟩
        dsimp [longArcLineGraphBag, CycleTwoChordGraph.longArcBagFamily]
        refine Finset.mem_image.mpr ⟨g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + anchor.val)
          (g.arcEdgeOffset_add_lt hyp.arcIdx anchor.val anchor.isLt), ?_, rfl⟩
        dsimp [CycleTwoChordGraph.longArcSlidingBag]
        simp [Option.toFinset, Finset.mem_union, Finset.mem_insert]
      · exact absurd he (by simp [hanchor, htail] at he)

theorem longArcJunctionHeadBag_mem_longArcLineGraphBag (endpoint : Fin 4)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionHeadBag endpoint) :
    e ∈ hyp.longArcLineGraphBag ⟨0, hyp.hlen⟩ := by
  unfold longArcJunctionHeadBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx endpoint ≠ none
  · simp [hshort] at he
  · simp [hshort] at he
    cases hanchor : hyp.junctionLongArcAnchor endpoint with
    | none => exact absurd he (by simp [hanchor] at he)
    | some anchor =>
      by_cases hhead : anchor.val = 0
      · simp [hanchor, hhead] at he
        obtain rfl := he
        dsimp [longArcLineGraphBag, CycleTwoChordGraph.longArcBagFamily]
        refine Finset.mem_image.mpr ⟨g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset hyp.arcIdx + 0)
          (g.arcEdgeOffset_add_lt hyp.arcIdx 0 hyp.hlen), ?_, rfl⟩
        dsimp [CycleTwoChordGraph.longArcSlidingBag]
        simp [Option.toFinset, Finset.mem_union, Finset.mem_insert]
      · exact absurd he (by simp [hanchor, hhead] at he)

private theorem longArcJunctionHeadBag_mem_junctionLineGraphBag_zero
    (hstep : g.junctionEndpointStep 0 = g.arcEdgeOffset hyp.arcIdx)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionHeadBag 0) :
    e ∈ hyp.junctionLineGraphBag 0 := by
  unfold longArcJunctionHeadBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx 0 ≠ none
  · simp [hshort] at he
  · simp [hshort, junctionLongArcAnchor] at he
    obtain rfl := he
    have hk : g.arcEdgeOffset hyp.arcIdx =
        g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt := by
      calc g.arcEdgeOffset hyp.arcIdx
          = g.junctionEndpointStep 0 := hstep.symm
        _ = g.cycleStepOfNatEndpoint g.chord1.1 g.chord1_fst_lt := rfl
    exact (junctionLineGraphBag_mem_chord1Start_cycle hyp _ _ hk).1

private theorem longArcJunctionHeadBag_mem_junctionLineGraphBag_two
    (hstep : g.junctionEndpointStep 2 = g.arcEdgeOffset hyp.arcIdx)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionHeadBag 2) :
    e ∈ hyp.junctionLineGraphBag 2 := by
  unfold longArcJunctionHeadBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx 2 ≠ none
  · simp [hshort] at he
  · simp [hshort, junctionLongArcAnchor] at he
    obtain rfl := he
    have hk : g.arcEdgeOffset hyp.arcIdx =
        g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt := by
      calc g.arcEdgeOffset hyp.arcIdx
          = g.junctionEndpointStep 2 := hstep.symm
        _ = g.cycleStepOfNatEndpoint g.chord2.1 g.chord2_fst_lt := rfl
    exact (junctionLineGraphBag_mem_chord2Start_cycle hyp _ _ hk).1

private theorem longArcJunctionHeadBag_mem_junctionLineGraphBag_one
    (hstep : g.junctionEndpointStep 1 = g.arcEdgeOffset hyp.arcIdx)
    (hlen : hyp.longArcLen = 1) {e : g.toSimpleGraph.edgeSet}
    (he : e ∈ hyp.longArcJunctionHeadBag 1) :
    e ∈ hyp.junctionLineGraphBag 1 := by
  unfold longArcJunctionHeadBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx 1 ≠ none
  · simp [hshort] at he
  · simp [hshort, junctionLongArcAnchor, hlen] at he
    obtain rfl := he
    have hk : g.arcEdgeOffset hyp.arcIdx =
        g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt := by
      calc g.arcEdgeOffset hyp.arcIdx
          = g.junctionEndpointStep 1 := hstep.symm
        _ = g.cycleStepOfNatEndpoint g.chord1.2 g.chord1_snd_lt := rfl
    exact (junctionLineGraphBag_mem_chord1End_cycle hyp _ _ hk).1

private theorem longArcJunctionHeadBag_mem_junctionLineGraphBag_three
    (hstep : g.junctionEndpointStep 3 = g.arcEdgeOffset hyp.arcIdx)
    (hlen : hyp.longArcLen = 1) {e : g.toSimpleGraph.edgeSet}
    (he : e ∈ hyp.longArcJunctionHeadBag 3) :
    e ∈ hyp.junctionLineGraphBag 3 := by
  unfold longArcJunctionHeadBag at he
  by_cases hshort : g.junctionShortArcAt hyp.arcIdx 3 ≠ none
  · simp [hshort] at he
  · simp [hshort, junctionLongArcAnchor, hlen] at he
    obtain rfl := he
    have hk : g.arcEdgeOffset hyp.arcIdx =
        g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt := by
      calc g.arcEdgeOffset hyp.arcIdx
          = g.junctionEndpointStep 3 := hstep.symm
        _ = g.cycleStepOfNatEndpoint g.chord2.2 g.chord2_snd_lt := rfl
    exact (junctionLineGraphBag_mem_chord2End_cycle hyp _ _ hk).1

theorem longArcJunctionHeadBag_mem_junctionLineGraphBag (endpoint : Fin 4)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionHeadBag endpoint) :
    e ∈ hyp.junctionLineGraphBag endpoint := by
  fin_cases endpoint
  · exact longArcJunctionHeadBag_mem_junctionLineGraphBag_zero hyp hstep he
  · by_cases hlen : hyp.longArcLen = 1
    · exact longArcJunctionHeadBag_mem_junctionLineGraphBag_one hyp hstep hlen he
    · unfold longArcJunctionHeadBag at he
      have hne0 : hyp.longArcLen - 1 ≠ 0 := by
        have hle : 1 ≤ hyp.longArcLen := Nat.succ_le_of_lt hyp.hlen
        omega
      by_cases hshort : g.junctionShortArcAt hyp.arcIdx 1 ≠ none
      · exact absurd he (by simp [hshort, junctionLongArcAnchor, hne0] at he)
      · exact absurd he (by simp [hshort, junctionLongArcAnchor, hne0] at he)
  · exact longArcJunctionHeadBag_mem_junctionLineGraphBag_two hyp hstep he
  · by_cases hlen : hyp.longArcLen = 1
    · exact longArcJunctionHeadBag_mem_junctionLineGraphBag_three hyp hstep hlen he
    · unfold longArcJunctionHeadBag at he
      have hne0 : hyp.longArcLen - 1 ≠ 0 := by
        have hle : 1 ≤ hyp.longArcLen := Nat.succ_le_of_lt hyp.hlen
        omega
      by_cases hshort : g.junctionShortArcAt hyp.arcIdx 3 ≠ none
      · exact absurd he (by simp [hshort, junctionLongArcAnchor, hne0] at he)
      · exact absurd he (by simp [hshort, junctionLongArcAnchor, hne0] at he)

theorem enrichedJunctionBag_mem_longArcHead (endpoint : Fin 4)
    (hstep : g.junctionEndpointStep endpoint = g.arcEdgeOffset hyp.arcIdx)
    {e : g.toSimpleGraph.edgeSet} (he : e ∈ hyp.longArcJunctionHeadBag endpoint) :
    e ∈ hyp.enrichedJunctionBag endpoint := by
  have hjunc := longArcJunctionHeadBag_mem_junctionLineGraphBag hyp endpoint hstep he
  exact enrichedJunctionBag_mem_junction (g := g) hyp endpoint e hjunc

theorem shortArcJunctionExtraBag_mem_shortArcLineGraphBag (endpoint : Fin 4) (shortArc : Fin 4)
    (h : 1 < g.cyclicGap shortArc) {e : g.toSimpleGraph.edgeSet}
    (he : e ∈ hyp.shortArcJunctionExtraBag endpoint shortArc) :
    ∃ j : Fin (g.cyclicGap shortArc), e ∈ hyp.shortArcLineGraphBag shortArc j := by
  have he' : e = hyp.edgeBij.edgeEquiv (g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + 1)
      (g.arcEdgeOffset_add_lt shortArc 1 h)) := by
    simpa [shortArcJunctionExtraBag, h, Set.mem_singleton_iff] using he
  rw [he']
  refine ⟨⟨1, h⟩, ?_⟩
  dsimp [shortArcLineGraphBag, CycleTwoChordGraph.shortArcBagFamily]
  refine Finset.mem_image.mpr ⟨g.cycleEdgeGlobalIndexAt (g.arcEdgeOffset shortArc + 1)
    (g.arcEdgeOffset_add_lt shortArc 1 h), ?_, rfl⟩
  dsimp [CycleTwoChordGraph.shortArcSlidingBag, CycleTwoChordGraph.arcSlidingBag,
    CycleTwoChordGraph.longArcSlidingBag]
  simp [Option.toFinset, Finset.mem_union, Finset.mem_insert]

theorem junctionEnrichedCardLeFour (endpoint : Fin 4) :
    (hyp.enrichedJunctionBag endpoint).card ≤ 4 := by
  have hjunc : (g.chordJunctionBagFamily endpoint).card ≤ 2 := by
    fin_cases endpoint <;>
      simp [CycleTwoChordGraph.chordJunctionBagFamily,
        CycleTwoChordGraph.chord1StartJunctionBag, CycleTwoChordGraph.chord1EndJunctionBag,
        CycleTwoChordGraph.chord2StartJunctionBag, CycleTwoChordGraph.chord2EndJunctionBag,
        CycleTwoChordGraph.cycleEdgeGlobalIndexAt_ne_chord1EdgeIndex,
        CycleTwoChordGraph.cycleEdgeGlobalIndexAt_ne_chord2EdgeIndex,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals omega
  have hjunc_img : (hyp.junctionLineGraphBag endpoint).card ≤ 2 := by
    dsimp [junctionLineGraphBag]
    have hcard := Finset.card_image_of_injective (g.chordJunctionBagFamily endpoint)
      hyp.edgeBij.edgeEquiv.injective
    rw [hcard]
    exact hjunc
  have hincoming : (hyp.incomingJunctionLineGraphBag endpoint).card ≤ 1 := by
    simp [incomingJunctionLineGraphBag]
  have htail : (hyp.longArcJunctionTailBag endpoint).card ≤ 1 := by
    unfold longArcJunctionTailBag
    split_ifs with hshort
    · exact Nat.zero_le _
    · cases hanchor : hyp.junctionLongArcAnchor endpoint with
      | none => simp [hanchor]
      | some anchor =>
        simp only [hanchor]
        split_ifs <;> simp [Finset.card_empty, Finset.card_singleton]
  match hshortArc : g.junctionShortArcAt hyp.arcIdx endpoint with
  | none =>
    have heq : hyp.enrichedJunctionBag endpoint =
        hyp.junctionLineGraphBag endpoint ∪ hyp.incomingJunctionLineGraphBag endpoint ∪
          hyp.longArcJunctionTailBag endpoint := by
      simp [enrichedJunctionBag, hshortArc, Finset.union_assoc]
    rw [heq]
    have hmid := Finset.card_union_le (hyp.junctionLineGraphBag endpoint)
      (hyp.incomingJunctionLineGraphBag endpoint)
    have hfinal := Finset.card_union_le
      (hyp.junctionLineGraphBag endpoint ∪ hyp.incomingJunctionLineGraphBag endpoint)
      (hyp.longArcJunctionTailBag endpoint)
    omega
  | some shortArc =>
    have hextra : (hyp.shortArcJunctionExtraBag endpoint shortArc).card ≤ 1 := by
      simp [shortArcJunctionExtraBag]
      split_ifs <;> simp [Finset.card_singleton, Finset.card_empty]
    have heq : hyp.enrichedJunctionBag endpoint =
        hyp.junctionLineGraphBag endpoint ∪ hyp.incomingJunctionLineGraphBag endpoint ∪
          hyp.shortArcJunctionExtraBag endpoint shortArc := by
      simp [enrichedJunctionBag, hshortArc, Finset.union_assoc]
    rw [heq]
    have hmid := Finset.card_union_le (hyp.junctionLineGraphBag endpoint)
      (hyp.incomingJunctionLineGraphBag endpoint)
    have hfinal := Finset.card_union_le
      (hyp.junctionLineGraphBag endpoint ∪ hyp.incomingJunctionLineGraphBag endpoint)
      (hyp.shortArcJunctionExtraBag endpoint shortArc)
    omega

theorem widthThreeEnrichedBag (endpoint : Fin 4) :
    (hyp.enrichedJunctionBag endpoint).card - 1 ≤ 3 := by
  have h := @junctionEnrichedCardLeFour g hyp endpoint
  omega

def globalDecompNodeCount : Nat := hyp.longArcLen + 5

def globalDecompAdj (i j : Fin hyp.globalDecompNodeCount) : Prop :=
  certPathGraphAdj hyp.globalDecompNodeCount i j

instance globalDecompAdj_symmInst : Std.Symm hyp.globalDecompAdj where
  symm := fun i j h => (certPathGraphAdj_symmInst hyp.globalDecompNodeCount).symm i j h

instance globalDecompAdj_irreflInst : Std.Irrefl hyp.globalDecompAdj where
  irrefl := fun i h => (certPathGraphAdj_irreflInst hyp.globalDecompNodeCount).irrefl i h

def globalDecompGraph : SimpleGraph (Fin hyp.globalDecompNodeCount) where
  Adj := hyp.globalDecompAdj
  symm := inferInstance
  loopless := inferInstance

theorem globalDecompGraph_eq_certPathGraph :
    hyp.globalDecompGraph = certPathGraph hyp.globalDecompNodeCount := by
  ext i j
  simp [globalDecompGraph, globalDecompAdj, certPathGraph, certPathGraphAdj]

theorem globalDecompGraph_isTree_of_seven (h : hyp.globalDecompNodeCount = 7) :
    hyp.globalDecompGraph.IsTree := by
  rw [globalDecompGraph_eq_certPathGraph, h]
  exact certPathGraph7_isTree

/-- Dedicated relay bag on the global path at index `longArcLen` (between arc segments and junctions). -/
noncomputable def globalPathRelayBag : Finset g.toSimpleGraph.edgeSet := ∅

/-- On the global path tree, place cross-junction shared edges at intervening junction nodes. -/
noncomputable def globalJunctionPathBridgeBag (_endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet := ∅

/-- Drop junction edges superseded by the relay bag or segment bags on the path pilot. -/
noncomputable def globalJunctionPathTrimBag (_endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet := ∅

noncomputable def globalJunctionBag (endpoint : Fin 4) : Finset g.toSimpleGraph.edgeSet :=
  (hyp.enrichedJunctionBag endpoint ∪ globalJunctionPathBridgeBag endpoint) \
    globalJunctionPathTrimBag endpoint

noncomputable def globalBagFamily (i : Fin hyp.globalDecompNodeCount) :
    Finset g.toSimpleGraph.edgeSet :=
  if hi : i.val < hyp.longArcLen then
    hyp.longArcSegmentBag ⟨i.val, hi⟩
  else if hi' : i.val = hyp.longArcLen then
    globalPathRelayBag
  else
    hyp.globalJunctionBag ⟨i.val - hyp.longArcLen - 1, by
      have hnode : hyp.globalDecompNodeCount = hyp.longArcLen + 5 := rfl
      have hi'' : i.val < hyp.longArcLen + 5 := by simpa [hnode] using i.isLt
      have hle : hyp.longArcLen + 1 ≤ i.val := by
        have hle' : hyp.longArcLen ≤ i.val := le_of_not_gt hi
        rcases eq_or_lt_of_le hle' with heq | hlt
        · exact absurd heq.symm hi'
        · omega
      omega⟩

theorem cardSegmentBagEq (j : Fin hyp.longArcLen) :
    (hyp.longArcSegmentBag j).card = (g.longArcBagFamily hyp.arcIdx j).card := by
  dsimp [longArcSegmentBag, longArcLineGraphBag]
  exact Finset.card_image_of_injective (g.longArcBagFamily hyp.arcIdx j)
    hyp.edgeBij.edgeEquiv.injective

theorem globalBagFamily_junction (endpoint : Fin 4) :
    hyp.globalBagFamily ⟨hyp.longArcLen + 1 + endpoint.val, by
      dsimp [globalDecompNodeCount]; omega⟩ =
      hyp.globalJunctionBag endpoint := by
  ext e
  simp only [globalBagFamily, globalJunctionBag, globalJunctionPathBridgeBag,
    globalJunctionPathTrimBag]
  have hlt : ¬ (hyp.longArcLen + 1 + endpoint.val < hyp.longArcLen) := by omega
  have hne : ¬ (hyp.longArcLen + 1 + endpoint.val = hyp.longArcLen) := by omega
  simp only [hlt, hne, ↓reduceIte]
  have hsub : hyp.longArcLen + 1 + endpoint.val - hyp.longArcLen - 1 = endpoint.val := by omega
  simp [hsub, Fin.val_mk]

theorem globalBagFamily_relay :
    hyp.globalBagFamily ⟨hyp.longArcLen, by
      dsimp [globalDecompNodeCount]; omega⟩ = globalPathRelayBag := by
  ext e
  simp [globalBagFamily, globalPathRelayBag]

theorem globalBagFamily_longArc (j : Fin hyp.longArcLen) :
    hyp.globalBagFamily (Fin.castAdd 5 j) = hyp.longArcSegmentBag j := by
  ext e
  simp [globalBagFamily, longArcSegmentBag]

noncomputable def globalBagSupWidth : Nat :=
  (Finset.univ : Finset (Fin hyp.globalDecompNodeCount)).sup
    fun i => (hyp.globalBagFamily i).card - 1

theorem globalPathRelayBag_card_le_four :
    (globalPathRelayBag : Finset g.toSimpleGraph.edgeSet).card ≤ 4 := by
  simp [globalPathRelayBag]

theorem globalJunctionBag_card_le_four (endpoint : Fin 4) :
    (hyp.globalJunctionBag endpoint).card ≤ 4 := by
  simp [globalJunctionBag, globalJunctionPathBridgeBag, globalJunctionPathTrimBag]
  exact junctionEnrichedCardLeFour hyp endpoint

theorem globalBagFamily_junction_width (endpoint : Fin 4) :
    (hyp.globalBagFamily ⟨hyp.longArcLen + 1 + endpoint.val, by
      dsimp [globalDecompNodeCount]; omega⟩).card - 1 ≤ 3 := by
  rw [globalBagFamily_junction hyp endpoint]
  simp only [globalJunctionBag, globalJunctionPathBridgeBag, globalJunctionPathTrimBag,
    Finset.union_empty, Finset.sdiff_empty]
  have := junctionEnrichedCardLeFour hyp endpoint
  omega

theorem globalBagFamily_relay_width :
    (hyp.globalBagFamily ⟨hyp.longArcLen, by
      dsimp [globalDecompNodeCount]; omega⟩).card - 1 ≤ 3 := by
  rw [globalBagFamily_relay hyp]
  have h := globalPathRelayBag_card_le_four (g := g)
  omega

theorem globalBagSupWidth_le_three : hyp.globalBagSupWidth ≤ 3 := by
  dsimp [globalBagSupWidth, globalBagFamily]
  refine Finset.sup_le fun i _ => ?_
  by_cases hi : i.val < hyp.longArcLen
  · have h := g.longArcBag_width_le_three hyp.arcIdx ⟨i.val, hi⟩
    have h' : (hyp.longArcSegmentBag ⟨i.val, hi⟩).card - 1 ≤ 3 := by
      rw [@cardSegmentBagEq g hyp ⟨i.val, hi⟩]
      exact h
    simp only [globalBagFamily, dif_pos hi]
    exact h'
  · by_cases hrelay : i.val = hyp.longArcLen
    · have hi_eq : i = ⟨hyp.longArcLen, by
          dsimp [globalDecompNodeCount]; omega⟩ := Fin.ext hrelay
      rw [hi_eq]
      exact globalBagFamily_relay_width hyp
    · have hend_lt : i.val - hyp.longArcLen - 1 < 4 := by
        have hnode : hyp.globalDecompNodeCount = hyp.longArcLen + 5 := rfl
        have hi' : i.val < hyp.longArcLen + 5 := by simpa [hnode] using i.isLt
        have hle : hyp.longArcLen + 1 ≤ i.val := by
          rcases eq_or_lt_of_le (le_of_not_gt hi) with heq | hlt
          · exact absurd heq.symm hrelay
          · omega
        omega
      have hi_eq : i = ⟨hyp.longArcLen + 1 + (i.val - hyp.longArcLen - 1), by
          have hnode : hyp.globalDecompNodeCount = hyp.longArcLen + 5 := rfl
          omega⟩ := Fin.ext (by
            have hsub : hyp.longArcLen + 1 + (i.val - hyp.longArcLen - 1) = i.val := by omega
            exact hsub.symm)
      rw [hi_eq]
      exact globalBagFamily_junction_width hyp ⟨i.val - hyp.longArcLen - 1, hend_lt⟩

/-! ### Open goals bundle + conditional certificate -/

structure NoncrossingPathDecompOpenGoals (hyp : NoncrossingPathDecompAssumptions g) where
  enrichedJunctionCardBound :
    ∀ endpoint : Fin 4,
      (hyp.enrichedJunctionBag endpoint).card ≤ 4
  junction_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ endpoint : Fin 4,
          e₁ ∈ hyp.enrichedJunctionBag endpoint ∧ e₂ ∈ hyp.enrichedJunctionBag endpoint
  shortArc_edgeCover :
    ∀ (shortArc : Fin 4), shortArc ≠ hyp.arcIdx →
      ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
        (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        (∃ j : Fin (g.cyclicGap shortArc), e₁ ∈ hyp.shortArcLineGraphBag shortArc j) →
        (∃ j : Fin (g.cyclicGap shortArc), e₂ ∈ hyp.shortArcLineGraphBag shortArc j) →
          ∃ j : Fin (g.cyclicGap shortArc),
            e₁ ∈ hyp.shortArcLineGraphBag shortArc j ∧ e₂ ∈ hyp.shortArcLineGraphBag shortArc j
  global_edgeCover :
    ∀ ⦃e₁ e₂ : g.toSimpleGraph.edgeSet⦄,
      (lineGraph g.toSimpleGraph).Adj e₁ e₂ →
        ∃ w : Fin hyp.globalDecompNodeCount, e₁ ∈ hyp.globalBagFamily w ∧ e₂ ∈ hyp.globalBagFamily w
  global_vertexCover :
    ∀ e : g.toSimpleGraph.edgeSet, ∃ w : Fin hyp.globalDecompNodeCount, e ∈ hyp.globalBagFamily w
  global_preconnected :
    ∀ e : g.toSimpleGraph.edgeSet,
      (hyp.globalDecompGraph.induce {w | e ∈ hyp.globalBagFamily w} |>.Preconnected)
  global_tree : hyp.globalDecompGraph.IsTree

def conditionalHasTreeDecomp : Prop :=
  HasTreeDecomp (lineGraph g.toSimpleGraph) 3

noncomputable def globalTreeDecomp (goals : NoncrossingPathDecompOpenGoals hyp) :
    TreeDecomp (lineGraph g.toSimpleGraph) hyp.globalDecompNodeCount where
  bag w := hyp.globalBagFamily w
  tree := hyp.globalDecompGraph
  isTree := goals.global_tree
  vertexCover := goals.global_vertexCover
  edgeCover := goals.global_edgeCover
  preconnected_induce_T := goals.global_preconnected

theorem conditionalHasTreeDecomp_of_openGoals (goals : NoncrossingPathDecompOpenGoals hyp) :
    conditionalHasTreeDecomp (g := g) := by
  refine ⟨hyp.globalDecompNodeCount, hyp.globalTreeDecomp goals, ?_⟩
  show (hyp.globalTreeDecomp goals).width ≤ 3
  dsimp [TreeDecomp.width, globalTreeDecomp]
  exact globalBagSupWidth_le_three hyp

end NoncrossingPathDecompAssumptions

/-! ## c7 nested smoke (Route F+A instance; degenerate — no GraphEdgeBijection) -/

def c7NestedGraph_pathDecompAssumptionsOpenDoc : String :=
  "OPEN: c7NestedGraph_pathDecompAssumptions — blocked on c7NestedGraph_graphEdgeBijection " ++
  "(degenerate nested p₁+1=p₂); PROVED gap/junction/sliding smoke below."

theorem c7NestedGraph_longArcIdx_eq_three :
    c7NestedGraph.longArcIdx = 3 := by
  dsimp [CycleTwoChordGraph.longArcIdx, c7NestedGraph, CycleTwoChordGraph.cyclicGap]

theorem c7_pathDecomp_shortArc_gap (a : Fin 4) :
    c7NestedGraph.cyclicGap a = match a with | 0 | 1 | 2 => 1 | 3 => 4 := by
  fin_cases a <;> simp [c7NestedGraph, CycleTwoChordGraph.cyclicGap]

theorem c7_pathDecomp_longArcLen :
    c7NestedGraph.cyclicGap c7NestedGraph.longArcIdx = 4 := by
  rw [c7NestedGraph_longArcIdx_eq_three]
  simp [c7NestedGraph, CycleTwoChordGraph.cyclicGap]

theorem c7_pathDecomp_junctionShortArcAt (endpoint : Fin 4) :
    c7NestedGraph.junctionShortArcAt c7NestedGraph.longArcIdx endpoint =
      match endpoint with
      | 0 => some 0
      | 1 => none
      | 2 => some 1
      | 3 => some 2 := by
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.junctionShortArcAt, CycleTwoChordGraph.endpointArcIdx,
      c7NestedGraph, c7NestedGraph_longArcIdx_eq_three] <;>
    decide

theorem c7_pathDecomp_shortArc0_card :
    (c7NestedGraph.shortArcSlidingBag 0 0 (by decide)).card ≤ 2 := by
  exact c7NestedGraph.shortArcSlidingBag_zero_card_le_two 0 (by decide)

theorem c7_pathDecomp_shortArcSliding_zero_vacuous (a : Fin 4) (hne : a ≠ c7NestedGraph.longArcIdx)
    (h : 1 < c7NestedGraph.cyclicGap a) : False := by
  rw [c7NestedGraph_longArcIdx_eq_three] at hne
  rw [c7_pathDecomp_shortArc_gap a] at h
  fin_cases a <;> simp at hne h

def c7NestedGraph_pathDecompSmokeDoc : String :=
  "PROVED: longArcIdx=3, gap vector, junctionShortArcAt, shortArc0 card, sliding vacuous (gap=1); " ++
  "OPEN: pathDecompAssumptions (GraphEdgeBijection + nondegenerate longArcBlock), globalBag smoke."

/-! ## c8 nested smoke (Route F+A pilot instance) -/

theorem c8NestedGraph_isNondegenerate : c8NestedGraph.isNondegenerate := by
  constructor <;> intro h <;>
    simp [c8NestedGraph, CycleTwoChordGraph.chord1IsCycleEdge, CycleTwoChordGraph.chord2IsCycleEdge,
      CycleTwoChordGraph.chordIsCycleEdge, CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2] at h

def c8NestedGraph_longArcBlock : NoncrossingLongArcBlock c8NestedGraph where
  arcIdx := c8NestedGraph.longArcIdx
  hlen := by
    dsimp [CycleTwoChordGraph.longArcIdx, c8NestedGraph, CycleTwoChordGraph.cyclicGap]
    decide
  hnc := c8NestedGraph_not_crossing
  hΔ := c8NestedGraph.isNondegenerate_implies_delta3Admissible c8NestedGraph_isNondegenerate
  hnd := c8NestedGraph_isNondegenerate

def c8GenericJunctionBridge (e e' : Fin 4) : Prop :=
  (e = 0 ∧ e' = 1) ∨ (e = 1 ∧ e' = 0) ∨
    (e = 0 ∧ e' = 2) ∨ (e = 2 ∧ e' = 0) ∨
      (e = 2 ∧ e' = 3) ∨ (e = 3 ∧ e' = 2)

instance (e e' : Fin 4) : Decidable (c8GenericJunctionBridge e e') := by
  unfold c8GenericJunctionBridge
  infer_instance

def c8GenericLongSegStartBridgeSuppress (e : Fin 4) : Prop := e = 2

instance (e : Fin 4) : Decidable (c8GenericLongSegStartBridgeSuppress e) := by
  unfold c8GenericLongSegStartBridgeSuppress
  infer_instance

def c8GenericLongSegEndBridgeSuppress (e : Fin 4) : Prop := e = 3

instance (e : Fin 4) : Decidable (c8GenericLongSegEndBridgeSuppress e) := by
  unfold c8GenericLongSegEndBridgeSuppress
  infer_instance

noncomputable def c8NestedGraph_pathDecompAssumptions :
    NoncrossingPathDecompAssumptions c8NestedGraph where
  toNoncrossingLongArcBlock := c8NestedGraph_longArcBlock
  edgeBij := c8NestedGraph_graphEdgeBijection
  genericJunctionBridge := c8GenericJunctionBridge
  genericJunctionBridge_symm := fun e e' h => by
    rcases h with h | h | h | h | h | h
    all_goals simp [c8GenericJunctionBridge] at h ⊢ <;> tauto
  genericJunctionBridge_irrefl := fun e h => by
    fin_cases e
    all_goals rcases h with h | h | h | h | h | h <;> simp [c8GenericJunctionBridge] at h
  genericLongSegStartBridgeSuppress := c8GenericLongSegStartBridgeSuppress
  genericLongSegEndBridgeSuppress := c8GenericLongSegEndBridgeSuppress
  genericLongSegStartBridgePartner := fun e => if e = 2 then some 0 else none
  genericLongSegEndBridgePartner := fun e =>
    if e = 3 then some 2 else none
  genericLongSegStartBridgePartner_spec := by
    intro e h
    fin_cases e <;> simp [c8GenericLongSegStartBridgeSuppress, c8GenericJunctionBridge] at h ⊢ <;>
      first | exact ⟨0, by decide, by decide⟩
  genericLongSegEndBridgePartner_spec := by
    intro e h
    fin_cases e <;> simp [c8GenericLongSegEndBridgeSuppress, c8GenericJunctionBridge] at h ⊢ <;>
      exact ⟨2, by decide, by decide⟩
  genericLongSegStartBridgePartner_two := by
    intro h; simp [c8GenericLongSegStartBridgeSuppress] at h; decide
  genericLongSegEndBridgePartner_three := by
    intro h; simp [c8GenericLongSegEndBridgeSuppress] at h; decide
  genericLongSegStartBridgeSuppress_not_at_zero := by decide
  genericLongSegEndBridgeSuppress_not_at_one := by decide
  genericLongSegBagExtension_empty := by
    intro j; fin_cases j <;> rfl
  genericJunctionBagExtension_empty := by
    intro endpoint; fin_cases endpoint <;> rfl
  genericJunctionBagTrim_empty := by
    intro endpoint; fin_cases endpoint <;> rfl
  genericLongSegBagExtension := fun _ => ∅
  genericJunctionBagExtension := fun _ => ∅
  genericJunctionBagTrim := fun _ => ∅

theorem c8NestedGraph_longArcBlock_width :
    c8NestedGraph_longArcBlock.bagSupWidth ≤ 3 :=
  c8NestedGraph_longArcBlock.bag_width_le_three

theorem c8NestedGraph_pathDecompAssumptions_combined_width :
    NoncrossingPathDecompAssumptions.combinedBagSupWidth c8NestedGraph_pathDecompAssumptions ≤ 3 :=
  NoncrossingPathDecompAssumptions.combinedBagSupWidth_le_three c8NestedGraph_pathDecompAssumptions

theorem c8NestedGraph_longArcIdx_eq_three :
    c8NestedGraph.longArcIdx = 3 := by
  dsimp [CycleTwoChordGraph.longArcIdx, c8NestedGraph, CycleTwoChordGraph.cyclicGap]

theorem c8_pathDecomp_nonLongArcIdx_arc3 :
    nonLongArcIdx c8NestedGraph.longArcIdx 0 = 0 ∧
      nonLongArcIdx c8NestedGraph.longArcIdx 1 = 1 ∧
        nonLongArcIdx c8NestedGraph.longArcIdx 2 = 2 := by
  dsimp [nonLongArcIdx, c8NestedGraph_longArcIdx_eq_three]
  decide

theorem c8_pathDecomp_shortArc0_card :
    (c8NestedGraph.shortArcSlidingBag 0 0 (by decide)).card ≤ 4 := by
  exact c8NestedGraph.shortArcSlidingBag_card_le_four 0 0 (by decide)

theorem c8_pathDecomp_shortArc0_covers :
    c8NestedGraph.cycleEdgeGlobalIndexAt 0 (by decide) ∈
      c8NestedGraph.shortArcSlidingBag 0 0 (by decide) := by
  have := c8NestedGraph.shortArcSlidingBag_covers_consecutive 0 0 (by decide) (by decide)
  exact this.1

private theorem c8_pathDecomp_longArc_edge6_interval_fin :
    {w : Fin 2 |
        c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide) ∈ c8NestedGraph.longArcBagFamily 3 w} =
      certPathGraphInterval 2 0 1 := by
  ext w
  fin_cases w <;>
    simp [certPathGraphInterval, Set.mem_setOf_eq, CycleTwoChordGraph.longArcBagFamily,
      CycleTwoChordGraph.longArcSlidingBag, c8NestedGraph, CycleTwoChordGraph.cyclicGap,
      CycleTwoChordGraph.longArcIdx, CycleTwoChordGraph.arcEdgeOffset,
      CycleTwoChordGraph.cycleEdgeGlobalIndexAt] <;> decide

private theorem c8_pathDecomp_longArc_edge7_interval_fin :
    {w : Fin 2 |
        c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide) ∈ c8NestedGraph.longArcBagFamily 3 w} =
      certPathGraphInterval 2 0 1 := by
  ext w
  fin_cases w <;>
    simp [certPathGraphInterval, Set.mem_setOf_eq, CycleTwoChordGraph.longArcBagFamily,
      CycleTwoChordGraph.longArcSlidingBag, c8NestedGraph, CycleTwoChordGraph.cyclicGap,
      CycleTwoChordGraph.longArcIdx, CycleTwoChordGraph.arcEdgeOffset,
      CycleTwoChordGraph.cycleEdgeGlobalIndexAt] <;> decide

theorem c8_pathDecomp_longArc_edge6_interval :
    {w : Fin 2 |
        c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
          (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide)) ∈
            c8NestedGraph_pathDecompAssumptions.longArcLineGraphBag w} =
      certPathGraphInterval 2 0 1 := by
  rw [← c8_pathDecomp_longArc_edge6_interval_fin]
  ext w
  simp [NoncrossingPathDecompAssumptions.longArcLineGraphBag,
    NoncrossingPathDecompAssumptions.longArcSegmentBag, c8NestedGraph_pathDecompAssumptions,
    c8NestedGraph_longArcBlock, c8NestedGraph_longArcIdx_eq_three,
    CycleTwoChordGraph.longArcBagFamily, Finset.mem_image]

theorem c8_pathDecomp_longArc_edge7_interval :
    {w : Fin 2 |
        c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
          (c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide)) ∈
            c8NestedGraph_pathDecompAssumptions.longArcLineGraphBag w} =
      certPathGraphInterval 2 0 1 := by
  rw [← c8_pathDecomp_longArc_edge7_interval_fin]
  ext w
  simp [NoncrossingPathDecompAssumptions.longArcLineGraphBag,
    NoncrossingPathDecompAssumptions.longArcSegmentBag, c8NestedGraph_pathDecompAssumptions,
    c8NestedGraph_longArcBlock, c8NestedGraph_longArcIdx_eq_three,
    CycleTwoChordGraph.longArcBagFamily, Finset.mem_image]

theorem c8_pathDecomp_globalDecompNodeCount :
    NoncrossingPathDecompAssumptions.globalDecompNodeCount c8NestedGraph_pathDecompAssumptions = 7 := by
  dsimp [NoncrossingPathDecompAssumptions.globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.longArcLen, c8NestedGraph_pathDecompAssumptions,
    c8NestedGraph_longArcBlock, CycleTwoChordGraph.cyclicGap, CycleTwoChordGraph.longArcIdx, c8NestedGraph]

theorem c8_pathDecomp_globalBagFamily_width :
    NoncrossingPathDecompAssumptions.globalBagSupWidth c8NestedGraph_pathDecompAssumptions ≤ 3 :=
  NoncrossingPathDecompAssumptions.globalBagSupWidth_le_three c8NestedGraph_pathDecompAssumptions

theorem c8_pathDecomp_enrichedJunctionBag_card_endpoint0 :
    (NoncrossingPathDecompAssumptions.enrichedJunctionBag c8NestedGraph_pathDecompAssumptions 0).card ≤ 4 := by
  have := NoncrossingPathDecompAssumptions.widthThreeEnrichedBag c8NestedGraph_pathDecompAssumptions 0
  omega

theorem c8_pathDecomp_longArc_edge6_preconnected :
    (certPathGraph 2).induce
        {w : Fin 2 |
          c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
            (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide)) ∈
              c8NestedGraph_pathDecompAssumptions.longArcSegmentBag w} |>.Preconnected :=
  NoncrossingPathDecompAssumptions.longArcSegment_preconnected_bag
    c8NestedGraph_pathDecompAssumptions
    (c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
      (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide)))
    0 1 (by decide) (by decide) (by decide) c8_pathDecomp_longArc_edge6_interval

theorem c8_pathDecomp_longArc_edge7_preconnected :
    (certPathGraph 2).induce
        {w : Fin 2 |
          c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
            (c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide)) ∈
              c8NestedGraph_pathDecompAssumptions.longArcSegmentBag w} |>.Preconnected :=
  NoncrossingPathDecompAssumptions.longArcSegment_preconnected_bag
    c8NestedGraph_pathDecompAssumptions
    (c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
      (c8NestedGraph.cycleEdgeGlobalIndexAt 7 (by decide)))
    0 1 (by decide) (by decide) (by decide) c8_pathDecomp_longArc_edge7_interval

theorem c8_pathDecomp_junction_chord1Start_mem :
    c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv
        (c8NestedGraph.cycleEdgeGlobalIndexAt 0 (by decide)) ∈
      c8NestedGraph_pathDecompAssumptions.junctionLineGraphBag 0 ∧
    c8NestedGraph_pathDecompAssumptions.edgeBij.edgeEquiv c8NestedGraph.chord1EdgeIndex ∈
      c8NestedGraph_pathDecompAssumptions.junctionLineGraphBag 0 :=
  NoncrossingPathDecompAssumptions.junctionLineGraphBag_mem_chord1Start_cycle
    c8NestedGraph_pathDecompAssumptions 0 (by decide)
    (by simp [CycleTwoChordGraph.cycleStepOfNatEndpoint_chord1_fst, c8NestedGraph])

theorem c8_pathDecomp_junction_chord1Start_adj :
    (lineGraph c8NestedGraph.toSimpleGraph).Adj
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex
        (c8NestedGraph.cycleEdgeGlobalIndexAt 0 (by decide)))
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex c8NestedGraph.chord1EdgeIndex) := by
  exact c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphAdj_of_shared_vertex
    (k₁ := c8NestedGraph.cycleEdgeGlobalIndexAt 0 (by decide))
    (k₂ := c8NestedGraph.chord1EdgeIndex)
    (c8NestedGraph.cyclicEndpointFin 0)
    (by native_decide)
    (by native_decide)
    (by decide)

theorem c8_pathDecomp_junction_chord1End_adj :
    (lineGraph c8NestedGraph.toSimpleGraph).Adj
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex
        (c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide)))
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex c8NestedGraph.chord1EdgeIndex) := by
  exact c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphAdj_of_shared_vertex
    (k₁ := c8NestedGraph.cycleEdgeGlobalIndexAt 6 (by decide))
    (k₂ := c8NestedGraph.chord1EdgeIndex)
    (⟨6, by decide⟩ : Fin c8NestedGraph.n)
    (by native_decide)
    (by native_decide)
    (by decide)

theorem c8_pathDecomp_junction_chord2Start_adj :
    (lineGraph c8NestedGraph.toSimpleGraph).Adj
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex
        (c8NestedGraph.cycleEdgeGlobalIndexAt 2 (by decide)))
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex c8NestedGraph.chord2EdgeIndex) := by
  exact c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphAdj_of_shared_vertex
    (k₁ := c8NestedGraph.cycleEdgeGlobalIndexAt 2 (by decide))
    (k₂ := c8NestedGraph.chord2EdgeIndex)
    (⟨2, by decide⟩ : Fin c8NestedGraph.n)
    (by native_decide)
    (by native_decide)
    (by decide)

theorem c8_pathDecomp_junction_chord2End_adj :
    (lineGraph c8NestedGraph.toSimpleGraph).Adj
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex
        (c8NestedGraph.cycleEdgeGlobalIndexAt 4 (by decide)))
      (c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphVertex c8NestedGraph.chord2EdgeIndex) := by
  exact c8NestedGraph_pathDecompAssumptions.edgeBij.lineGraphAdj_of_shared_vertex
    (k₁ := c8NestedGraph.cycleEdgeGlobalIndexAt 4 (by decide))
    (k₂ := c8NestedGraph.chord2EdgeIndex)
    (⟨4, by decide⟩ : Fin c8NestedGraph.n)
    (by native_decide)
    (by native_decide)
    (by decide)

/-! ### c8 open-goals discharge (Fin 10 edge-index characterizations) -/

noncomputable abbrev c8Hyp : NoncrossingPathDecompAssumptions c8NestedGraph :=
  c8NestedGraph_pathDecompAssumptions

private theorem c8_pathDecomp_edgeEquiv_eq (k : Fin 10) :
    (c8Hyp.edgeBij.edgeEquiv k : Sym2 (Fin c8NestedGraph.n)) = c8NestedGraph.graphEdgeSym2 k := by
  rw [GraphEdgeBijection.edgeEquiv_apply]
  exact GraphEdgeBijection.lineGraph_vertex_eq c8Hyp.edgeBij k

def c8PathDecompFinEnrichedJunctionBag : Fin 4 → Finset (Fin 10)
  | 0 => {0, 1, 7, 8}
  | 1 => {5, 6, 7, 8}
  | 2 => {1, 2, 3, 9}
  | 3 => {3, 4, 5, 9}

def c8PathDecompFinShortArcBag (a : Fin 4) (_j : Fin 2) : Finset (Fin 10) :=
  match a with
  | 0 => {0, 1}
  | 1 => {2, 3}
  | 2 => {4, 5}
  | 3 => {6, 7}

private def c8PathDecompFinGlobalBag : Fin 7 → Finset (Fin 10)
  | 0 => {6, 7}
  | 1 => {6, 7}
  | 2 => ∅
  | 3 => {0, 1, 7, 8}
  | 4 => {5, 6, 7, 8}
  | 5 => {1, 2, 3, 9}
  | 6 => {3, 4, 5, 9}

private def c8PathDecompLineEdges : List (Nat × Nat) :=
  [(0, 1), (0, 7), (0, 8), (1, 2), (1, 9), (2, 3), (2, 9), (3, 4), (3, 9), (4, 5), (4, 9),
    (5, 6), (5, 8), (6, 7), (6, 8), (7, 8)]

def c8PathDecompFinAdj (i j : Fin 10) : Prop :=
  i ≠ j ∧
    ((i.val, j.val) ∈ c8PathDecompLineEdges ∨ (j.val, i.val) ∈ c8PathDecompLineEdges)

private theorem c8_pathDecomp_edgeSet_eq (k : Fin 10) :
    (c8Hyp.edgeBij.edgeEquiv k : c8NestedGraph.toSimpleGraph.edgeSet) =
      ⟨c8NestedGraph.graphEdgeSym2 k, c8NestedGraph_graphEdgeSym2_mem k⟩ := by
  apply Subtype.ext
  exact c8_pathDecomp_edgeEquiv_eq k

private def c8PathDecompToCert : Fin 10 → Fin 10
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 9
  | 7 => 2
  | 8 => 1
  | 9 => 5

private theorem c8_pathDecomp_graphEdge_eq_cert (k : Fin 10) :
    c8NestedGraph.graphEdgeSym2 k = c8Nested_baseEdgeSym2 (c8PathDecompToCert k) := by
  fin_cases k <;> native_decide

private theorem c8_pathDecomp_certAdj_iff (i j : Fin 10) :
    graphOfEdgeList10Adj c8Nested_lineEdges (c8PathDecompToCert i) (c8PathDecompToCert j) ↔
      c8PathDecompFinAdj i j := by
  fin_cases i <;> fin_cases j <;>
    simp [graphOfEdgeList10Adj, c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompToCert,
      c8Nested_lineEdges] <;>
    first | contradiction | decide

theorem c8_pathDecomp_lineAdj_fin (i j : Fin 10) :
    (lineGraph c8NestedGraph.toSimpleGraph).Adj (c8Hyp.edgeBij.edgeEquiv i)
        (c8Hyp.edgeBij.edgeEquiv j) ↔
      c8PathDecompFinAdj i j := by
  rw [lineGraph_adj_iff]
  have hne :
      c8Hyp.edgeBij.edgeEquiv i ≠ c8Hyp.edgeBij.edgeEquiv j ↔ i ≠ j := by
    constructor
    · intro h hEq; exact h (congrArg _ hEq)
    · intro h hEq; exact h (c8Hyp.edgeBij.edgeEquiv.injective hEq)
  rw [hne]
  rw [GraphEdgeBijection.lineGraph_vertex_eq (hidx := c8Hyp.edgeBij) i,
    GraphEdgeBijection.lineGraph_vertex_eq (hidx := c8Hyp.edgeBij) j,
    c8_pathDecomp_graphEdge_eq_cert i, c8_pathDecomp_graphEdge_eq_cert j]
  fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompToCert, c8Nested_baseEdgeSym2, Sym2.mem_iff, c8PathDecompFinAdj,
      c8PathDecompLineEdges, List.mem_cons, List.mem_nil_iff, and_imp, exists_imp] <;>
    decide

private theorem c8_pathDecomp_globalFinEdgeCover (i j : Fin 10) (hadj : c8PathDecompFinAdj i j) :
    ∃ w : Fin 7, i ∈ c8PathDecompFinGlobalBag w ∧ j ∈ c8PathDecompFinGlobalBag w := by
  fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinGlobalBag] at hadj ⊢ <;>
    first | contradiction | decide

theorem c8_pathDecomp_shortArcFinBag_eq (a : Fin 4) (k l : Fin 2) :
    c8PathDecompFinShortArcBag a k = c8PathDecompFinShortArcBag a l := by
  fin_cases a <;> fin_cases k <;> fin_cases l <;> rfl

theorem c8_pathDecomp_shortArcFinEdgeCover (a : Fin 4) (i j : Fin 10)
    (hne : a ≠ c8NestedGraph.longArcIdx) (hadj : c8PathDecompFinAdj i j)
    (hi : ∃ k, i ∈ c8PathDecompFinShortArcBag a k)
    (hj : ∃ k, j ∈ c8PathDecompFinShortArcBag a k) :
    ∃ k : Fin 2, i ∈ c8PathDecompFinShortArcBag a k ∧ j ∈ c8PathDecompFinShortArcBag a k := by
  rw [c8NestedGraph_longArcIdx_eq_three] at hne
  rcases hi with ⟨ki, hki⟩
  rcases hj with ⟨kj, hkj⟩
  fin_cases a
  · exact ⟨ki, hki, (c8_pathDecomp_shortArcFinBag_eq 0 kj ki).symm ▸ hkj⟩
  · exact ⟨ki, hki, (c8_pathDecomp_shortArcFinBag_eq 1 kj ki).symm ▸ hkj⟩
  · exact ⟨ki, hki, (c8_pathDecomp_shortArcFinBag_eq 2 kj ki).symm ▸ hkj⟩
  · exact absurd rfl hne

theorem c8_pathDecomp_junctionFinEdgeCover (i j : Fin 10) (hadj : c8PathDecompFinAdj i j) :
    ∃ endpoint : Fin 4,
      i ∈ c8PathDecompFinEnrichedJunctionBag endpoint ∧
        j ∈ c8PathDecompFinEnrichedJunctionBag endpoint := by
  fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinEnrichedJunctionBag] at hadj ⊢ <;>
    first | contradiction | decide

private theorem c8_pathDecomp_junctionShortArcAt (endpoint : Fin 4) :
    c8NestedGraph.junctionShortArcAt c8NestedGraph.longArcIdx endpoint =
      match endpoint with
      | 0 => some 0
      | 1 => none
      | 2 => some 1
      | 3 => some 2 := by
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.junctionShortArcAt, CycleTwoChordGraph.endpointArcIdx,
      c8NestedGraph, c8NestedGraph_longArcIdx_eq_three] <;>
    decide

private theorem c8_pathDecomp_incomingCycleStep (endpoint : Fin 4) :
    c8NestedGraph.incomingCycleStepAtEndpoint endpoint =
      match endpoint with
      | 0 => 7
      | 1 => 5
      | 2 => 1
      | 3 => 3 := by
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.incomingCycleStepAtEndpoint,
      CycleTwoChordGraph.junctionEndpointStep, CycleTwoChordGraph.junctionEndpointIdx,
      CycleTwoChordGraph.cycleStepOfNatEndpoint, c8NestedGraph,
      CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2]

theorem c8_pathDecomp_shortArc_gap (a : Fin 4) : c8NestedGraph.cyclicGap a = 2 := by
  fin_cases a <;> simp [c8NestedGraph, CycleTwoChordGraph.cyclicGap]

private theorem c8_pathDecomp_longArcLen :
    c8Hyp.longArcLen = 2 := by
  dsimp [NoncrossingPathDecompAssumptions.longArcLen, c8Hyp,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    CycleTwoChordGraph.cyclicGap, CycleTwoChordGraph.longArcIdx, c8NestedGraph]

private theorem c8_pathDecomp_junctionLongArcAnchor (endpoint : Fin 4) :
    c8Hyp.junctionLongArcAnchor endpoint =
      match endpoint with
      | 0 => some ⟨0, by decide⟩
      | 1 => some ⟨1, by decide⟩
      | 2 => some ⟨0, by decide⟩
      | 3 => some ⟨1, by decide⟩ := by
  fin_cases endpoint <;>
    simp [NoncrossingPathDecompAssumptions.junctionLongArcAnchor, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
      c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_longArcLen,
      CycleTwoChordGraph.cyclicGap, c8NestedGraph] <;>
    decide

theorem c8_pathDecomp_enrichedJunctionBag_mem (endpoint : Fin 4) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.enrichedJunctionBag endpoint ↔
      k ∈ c8PathDecompFinEnrichedJunctionBag endpoint := by
  fin_cases endpoint <;> fin_cases k <;>
    simp [NoncrossingPathDecompAssumptions.enrichedJunctionBag,
      NoncrossingPathDecompAssumptions.incomingJunctionLineGraphBag,
      NoncrossingPathDecompAssumptions.shortArcJunctionExtraBag,
      NoncrossingPathDecompAssumptions.longArcJunctionTailBag,
      NoncrossingPathDecompAssumptions.junctionLineGraphBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
      c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_junctionShortArcAt,
      c8_pathDecomp_incomingCycleStep, c8_pathDecomp_junctionLongArcAnchor,
      NoncrossingPathDecompAssumptions.junctionLongArcAnchor,
      NoncrossingPathDecompAssumptions.longArcLen,
      CycleTwoChordGraph.chordJunctionBagFamily,
      CycleTwoChordGraph.chord1StartJunctionBag, CycleTwoChordGraph.chord1EndJunctionBag,
      CycleTwoChordGraph.chord2StartJunctionBag, CycleTwoChordGraph.chord2EndJunctionBag,
      CycleTwoChordGraph.incomingCycleEdgeGlobalIndex, CycleTwoChordGraph.shortArcBagFamily,
      CycleTwoChordGraph.shortArcSlidingBag, CycleTwoChordGraph.arcSlidingBag,
      CycleTwoChordGraph.longArcSlidingBag, CycleTwoChordGraph.cyclicGap,
      CycleTwoChordGraph.arcEdgeOffset, CycleTwoChordGraph.cycleEdgeGlobalIndexAt,
      CycleTwoChordGraph.cycleStepOfNatEndpoint, c8NestedGraph, CycleTwoChordGraph.chord1,
      CycleTwoChordGraph.chord2, CycleTwoChordGraph.chord1EdgeIndex,
      CycleTwoChordGraph.chord2EdgeIndex, Finset.mem_image, Finset.mem_union] <;>
    first | rfl | decide

theorem c8_pathDecomp_shortArcBag_mem (a : Fin 4) (j : Fin 2) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈
        c8Hyp.shortArcLineGraphBag a (Fin.cast (c8_pathDecomp_shortArc_gap a).symm j) ↔
      k ∈ c8PathDecompFinShortArcBag a j := by
  fin_cases a <;> fin_cases j <;> fin_cases k <;>
    simp [c8_pathDecomp_shortArc_gap, NoncrossingPathDecompAssumptions.shortArcLineGraphBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, CycleTwoChordGraph.shortArcBagFamily,
      CycleTwoChordGraph.shortArcSlidingBag, CycleTwoChordGraph.arcSlidingBag,
      CycleTwoChordGraph.longArcSlidingBag, CycleTwoChordGraph.cyclicGap,
      CycleTwoChordGraph.arcEdgeOffset, CycleTwoChordGraph.cycleEdgeGlobalIndexAt,
      c8NestedGraph, Finset.mem_image] <;>
    first | rfl | decide

def c8PathDecompFinLongArcBag : Fin 2 → Finset (Fin 10)
  | 0 | 1 => {6, 7}

def c8PathDecompFinIncomingBag : Fin 4 → Finset (Fin 10)
  | 0 => {7}
  | 1 => {5}
  | 2 => {1}
  | 3 => {3}

def c8PathDecompFinJunctionLineGraphBag : Fin 4 → Finset (Fin 10)
  | 0 => {0, 8}
  | 1 => {6, 8}
  | 2 => {2, 9}
  | 3 => {4, 9}

private def c8PathDecompFinLongArcHeadBag : Fin 4 → Finset (Fin 10) :=
  fun _ => ∅

private def c8PathDecompFinLongArcTailBag : Fin 4 → Finset (Fin 10)
  | 0 | 2 | 3 => ∅
  | 1 => {7}

theorem c8_pathDecomp_longArcBag_mem (j : Fin 2) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.longArcLineGraphBag j ↔ k ∈ c8PathDecompFinLongArcBag j := by
  fin_cases j <;> fin_cases k <;>
    simp [NoncrossingPathDecompAssumptions.longArcLineGraphBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
      c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_longArcLen,
      CycleTwoChordGraph.longArcBagFamily, CycleTwoChordGraph.longArcSlidingBag,
      CycleTwoChordGraph.cyclicGap, CycleTwoChordGraph.arcEdgeOffset,
      CycleTwoChordGraph.cycleEdgeGlobalIndexAt, c8NestedGraph, Finset.mem_image] <;>
    first | rfl | decide

theorem c8_pathDecomp_incomingBag_mem (endpoint : Fin 4) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.incomingJunctionLineGraphBag endpoint ↔
      k ∈ c8PathDecompFinIncomingBag endpoint := by
  fin_cases endpoint <;> fin_cases k <;>
    simp [NoncrossingPathDecompAssumptions.incomingJunctionLineGraphBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8_pathDecomp_incomingCycleStep,
      CycleTwoChordGraph.incomingCycleEdgeGlobalIndex, CycleTwoChordGraph.incomingCycleStepAtEndpoint,
      CycleTwoChordGraph.cycleEdgeGlobalIndexAt, c8NestedGraph, Finset.mem_singleton] <;>
    first | rfl | decide

theorem c8_pathDecomp_junctionLineGraphBag_mem (endpoint : Fin 4) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.junctionLineGraphBag endpoint ↔
      k ∈ c8PathDecompFinJunctionLineGraphBag endpoint := by
  fin_cases endpoint <;> fin_cases k <;>
    simp [NoncrossingPathDecompAssumptions.junctionLineGraphBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
      c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_junctionShortArcAt,
      c8_pathDecomp_incomingCycleStep, c8_pathDecomp_junctionLongArcAnchor,
      CycleTwoChordGraph.chordJunctionBagFamily, CycleTwoChordGraph.chord1StartJunctionBag,
      CycleTwoChordGraph.chord1EndJunctionBag, CycleTwoChordGraph.chord2StartJunctionBag,
      CycleTwoChordGraph.chord2EndJunctionBag, CycleTwoChordGraph.chord1EdgeIndex,
      CycleTwoChordGraph.chord2EdgeIndex, CycleTwoChordGraph.cycleEdgeGlobalIndexAt,
      CycleTwoChordGraph.cycleStepOfNatEndpoint, c8NestedGraph, CycleTwoChordGraph.chord1,
      CycleTwoChordGraph.chord2, Finset.mem_insert, Finset.mem_singleton] <;>
    first | rfl | decide

private theorem c8_pathDecomp_longArcTailBag_mem (endpoint : Fin 4) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.longArcJunctionTailBag endpoint ↔
      k ∈ c8PathDecompFinLongArcTailBag endpoint := by
  fin_cases endpoint <;> fin_cases k <;>
    simp [NoncrossingPathDecompAssumptions.longArcJunctionTailBag, c8Hyp,
      c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
      c8NestedGraph_longArcIdx_eq_three, c8_pathDecomp_junctionShortArcAt,
      c8_pathDecomp_junctionLongArcAnchor, c8_pathDecomp_longArcLen,
      CycleTwoChordGraph.cyclicGap, CycleTwoChordGraph.arcEdgeOffset,
      CycleTwoChordGraph.cycleEdgeGlobalIndexAt, c8NestedGraph, Finset.mem_singleton] <;>
    first | rfl | decide

theorem c8NestedGraph_pairing_nested : c8NestedGraph.pairing = ChordPairing.nested := rfl

theorem c8_pathDecomp_endpointArcIdx (endpoint : Fin 4) :
    c8NestedGraph.endpointArcIdx endpoint =
      match endpoint with
      | 0 => 0
      | 1 => 3
      | 2 => 1
      | 3 => 2 := by
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.endpointArcIdx, c8NestedGraph_pairing_nested]

theorem c8_pathDecomp_junctionEndpointStep (endpoint : Fin 4) :
    c8NestedGraph.junctionEndpointStep endpoint =
      match endpoint with
      | 0 => 0
      | 1 => 6
      | 2 => 2
      | 3 => 4 := by
  fin_cases endpoint <;>
    simp [CycleTwoChordGraph.junctionEndpointStep, CycleTwoChordGraph.junctionEndpointIdx,
      CycleTwoChordGraph.cycleStepOfNatEndpoint, c8NestedGraph, CycleTwoChordGraph.chord1,
      CycleTwoChordGraph.chord2, CycleTwoChordGraph.cycleStepOfNatEndpoint_chord1_fst]

theorem c8_pathDecomp_arcEdgeOffset_longArc :
    c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx = 6 := by
  rw [c8NestedGraph_longArcIdx_eq_three]
  decide

theorem c8_pathDecomp_junctionStep_eq_arcOffset_onLongArc_endpoint1 :
    c8NestedGraph.junctionEndpointStep 1 = c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx := by
  rw [c8_pathDecomp_junctionEndpointStep, c8_pathDecomp_arcEdgeOffset_longArc]

theorem c8_pathDecomp_junctionStep_ne_arcOffset_offLongArc (endpoint : Fin 4)
    (hoff : c8NestedGraph.endpointArcIdx endpoint ≠ c8NestedGraph.longArcIdx) :
    c8NestedGraph.junctionEndpointStep endpoint ≠
      c8NestedGraph.arcEdgeOffset c8NestedGraph.longArcIdx := by
  fin_cases endpoint <;> simp [c8_pathDecomp_endpointArcIdx, c8NestedGraph_longArcIdx_eq_three,
    c8_pathDecomp_junctionEndpointStep, c8_pathDecomp_arcEdgeOffset_longArc] at hoff ⊢ <;>
    first | contradiction | decide

theorem c8_pathDecomp_longArcLen_eq_two : c8Hyp.longArcLen = 2 := c8_pathDecomp_longArcLen

/-- Interior long-seg index: none when `longArcLen = 2` (only head/tail segments). -/
theorem c8_pathDecomp_no_interior_longSeg :
    ∀ j : Fin c8Hyp.longArcLen, j.val = 0 ∨ j.val + 1 = c8Hyp.longArcLen := by
  intro j
  fin_cases j <;> simp [c8_pathDecomp_longArcLen_eq_two]

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_endRouting_longSegLast_incoming_fin (endpoint : Fin 4) (i j : Fin 10)
    (hadj : c8PathDecompFinAdj i j) (hi : i ∈ c8PathDecompFinLongArcBag 1)
    (hj : j ∈ c8PathDecompFinIncomingBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      j ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinIncomingBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi hj ⊢ <;>
    first | contradiction | exact ⟨1, by decide, by decide⟩

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_endRouting_incoming_longSegLast_fin (endpoint : Fin 4) (i j : Fin 10)
    (hadj : c8PathDecompFinAdj i j) (hi : i ∈ c8PathDecompFinIncomingBag endpoint)
    (hj : j ∈ c8PathDecompFinLongArcBag 1) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      j ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinIncomingBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi hj ⊢ <;>
    first | contradiction | exact ⟨1, by decide, by decide⟩

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_endRouting_longSegLast_junctionLineGraph_fin (endpoint : Fin 4)
    (i j : Fin 10) (hadj : c8PathDecompFinAdj i j) (hi : i ∈ c8PathDecompFinLongArcBag 1)
    (hj : j ∈ c8PathDecompFinJunctionLineGraphBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      j ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinJunctionLineGraphBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi hj ⊢ <;>
    first | contradiction | decide

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_endRouting_junctionLineGraph_longSegLast_fin (endpoint : Fin 4)
    (i j : Fin 10) (hadj : c8PathDecompFinAdj i j) (hi : i ∈ c8PathDecompFinJunctionLineGraphBag endpoint)
    (hj : j ∈ c8PathDecompFinLongArcBag 1) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      j ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinJunctionLineGraphBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi hj ⊢ <;>
    first | contradiction | decide

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_residual_longSeg_junction_fin (endpoint : Fin 4) (j : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinLongArcBag j)
    (hk : k ∈ c8PathDecompFinEnrichedJunctionBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinEnrichedJunctionBag] at hadj hi hk ⊢ <;>
    first | contradiction | decide

set_option maxHeartbeats 800000 in
theorem c8_pathDecomp_residual_junction_longSeg_fin (endpoint : Fin 4) (j : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinEnrichedJunctionBag endpoint)
    (hk : k ∈ c8PathDecompFinLongArcBag j) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  fin_cases endpoint <;> fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinEnrichedJunctionBag] at hadj hi hk ⊢ <;>
    first | contradiction | decide

private noncomputable def c8GlobalNode (w : Fin 7) : Fin c8Hyp.globalDecompNodeCount :=
  Fin.cast c8_pathDecomp_globalDecompNodeCount.symm w

private theorem c8_pathDecomp_globalBag_mem_seg0 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 0) ↔ k ∈ c8PathDecompFinGlobalBag 0 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    NoncrossingPathDecompAssumptions.globalPathRelayBag,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    NoncrossingPathDecompAssumptions.longArcSegmentBag] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_seg1 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 1) ↔ k ∈ c8PathDecompFinGlobalBag 1 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    NoncrossingPathDecompAssumptions.globalPathRelayBag,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    NoncrossingPathDecompAssumptions.longArcSegmentBag] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_relay (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 2) ↔ k ∈ c8PathDecompFinGlobalBag 2 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    NoncrossingPathDecompAssumptions.globalPathRelayBag,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_junc0 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 3) ↔ k ∈ c8PathDecompFinGlobalBag 3 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    NoncrossingPathDecompAssumptions.globalJunctionBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathBridgeBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathTrimBag,
    NoncrossingPathDecompAssumptions.enrichedJunctionBag] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_junc1 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 4) ↔ k ∈ c8PathDecompFinGlobalBag 4 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    c8_pathDecomp_junctionShortArcAt, c8NestedGraph_longArcIdx_eq_three,
    NoncrossingPathDecompAssumptions.globalJunctionBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathBridgeBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathTrimBag,
    NoncrossingPathDecompAssumptions.enrichedJunctionBag,
    NoncrossingPathDecompAssumptions.longArcJunctionTailBag,
    NoncrossingPathDecompAssumptions.incomingJunctionLineGraphBag,
    NoncrossingPathDecompAssumptions.junctionLineGraphBag,
    NoncrossingPathDecompAssumptions.shortArcJunctionExtraBag,
    CycleTwoChordGraph.chordJunctionBagFamily, CycleTwoChordGraph.incomingCycleEdgeGlobalIndex,
    c8NestedGraph, CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_image] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_junc2 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 5) ↔ k ∈ c8PathDecompFinGlobalBag 5 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    NoncrossingPathDecompAssumptions.globalJunctionBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathBridgeBag,
    NoncrossingPathDecompAssumptions.globalJunctionPathTrimBag,
    NoncrossingPathDecompAssumptions.enrichedJunctionBag] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem_junc3 (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode 6) ↔ k ∈ c8PathDecompFinGlobalBag 6 := by
  fin_cases k <;> simp [c8GlobalNode, c8_pathDecomp_globalDecompNodeCount,
    NoncrossingPathDecompAssumptions.globalBagFamily, c8Hyp,
    c8NestedGraph_pathDecompAssumptions, c8NestedGraph_longArcBlock,
    c8_pathDecomp_junctionShortArcAt, c8NestedGraph_longArcIdx_eq_three,
    NoncrossingPathDecompAssumptions.globalJunctionBag,
    NoncrossingPathDecompAssumptions.enrichedJunctionBag,
    NoncrossingPathDecompAssumptions.shortArcJunctionExtraBag,
    CycleTwoChordGraph.shortArcBagFamily, CycleTwoChordGraph.arcEdgeOffset,
    c8NestedGraph, Finset.mem_union, Finset.mem_image] <;> first | rfl | decide

private theorem c8_pathDecomp_globalBag_mem (w : Fin 7) (k : Fin 10) :
    c8Hyp.edgeBij.edgeEquiv k ∈ c8Hyp.globalBagFamily (c8GlobalNode w) ↔ k ∈ c8PathDecompFinGlobalBag w := by
  match w with
  | 0 => exact c8_pathDecomp_globalBag_mem_seg0 k
  | 1 => exact c8_pathDecomp_globalBag_mem_seg1 k
  | 2 => exact c8_pathDecomp_globalBag_mem_relay k
  | 3 => exact c8_pathDecomp_globalBag_mem_junc0 k
  | 4 => exact c8_pathDecomp_globalBag_mem_junc1 k
  | 5 => exact c8_pathDecomp_globalBag_mem_junc2 k
  | 6 => exact c8_pathDecomp_globalBag_mem_junc3 k

theorem c8_pathDecomp_enrichedJunctionBag_card_endpoint1 :
    (c8Hyp.enrichedJunctionBag 1).card ≤ 4 :=
  NoncrossingPathDecompAssumptions.junctionEnrichedCardLeFour c8Hyp 1

theorem c8_pathDecomp_enrichedJunctionBag_card_endpoint2 :
    (c8Hyp.enrichedJunctionBag 2).card ≤ 4 :=
  NoncrossingPathDecompAssumptions.junctionEnrichedCardLeFour c8Hyp 2

theorem c8_pathDecomp_enrichedJunctionBag_card_endpoint3 :
    (c8Hyp.enrichedJunctionBag 3).card ≤ 4 :=
  NoncrossingPathDecompAssumptions.junctionEnrichedCardLeFour c8Hyp 3

private theorem c8_pathDecomp_globalFinVertexCover (k : Fin 10) :
    ∃ w : Fin 7, k ∈ c8PathDecompFinGlobalBag w := by
  fin_cases k <;> decide

/-! c8 generic-decomp fin scaffold (12 nodes = 2 long + 6 short + 4 junction; vertexCover PROVED). -/

def c8PathDecompFinGenericBag : Fin 12 → Finset (Fin 10)
  | 0 | 1 => {6, 7}
  | 2 | 3 => {0, 1}
  | 4 | 5 => {2, 3}
  | 6 | 7 => {4, 5}
  | 8 => {0, 1, 5, 7, 8}
  | 9 => {5, 6, 7, 8}
  | 10 => {1, 2, 3, 5, 9}
  | 11 => {3, 4, 5, 9}

theorem c8_pathDecomp_genericFinVertexCover (k : Fin 10) :
    ∃ w : Fin 12, k ∈ c8PathDecompFinGenericBag w := by
  fin_cases k <;> decide

def c8PathDecompFinGenericNodeInterval (k : Fin 10) : Finset (Fin 12) :=
  match k with
  | 0 => {2, 3, 8}
  | 1 => {2, 3, 8, 10}
  | 2 => {4, 5, 10}
  | 3 => {4, 5, 10, 11}
  | 4 => {6, 7, 11}
  | 5 => {6, 7, 8, 9, 10, 11}
  | 6 => {0, 1, 9}
  | 7 => {0, 1, 8, 9}
  | 8 => {8, 9}
  | 9 => {10, 11}

theorem c8_pathDecomp_genericFinNodeSet (k : Fin 10) (w : Fin 12) :
    k ∈ c8PathDecompFinGenericBag w ↔ w ∈ c8PathDecompFinGenericNodeInterval k := by
  fin_cases k <;> fin_cases w <;>
    simp [c8PathDecompFinGenericBag, c8PathDecompFinGenericNodeInterval] <;> decide

theorem c8_pathDecomp_genericFinEdgeCover (i j : Fin 10) (hadj : c8PathDecompFinAdj i j) :
    ∃ w : Fin 12, i ∈ c8PathDecompFinGenericBag w ∧ j ∈ c8PathDecompFinGenericBag w := by
  fin_cases i <;> fin_cases j <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinGenericBag] at hadj ⊢ <;>
    first | contradiction | decide

/-! c8 generic-decomp fin graph (12 nodes): mirrors `genericDecompAdj` on the Fin-12 encoding.
    Junction-bridge edges (8–10, 8–9, 10–11) replace suppressed longSeg–junction glue for overlap RI. -/

def c8GenericFinGraphLineEdges : List (Nat × Nat) :=
  [(0, 1), (1, 9), (2, 3), (2, 8), (4, 5), (4, 10), (6, 7), (6, 11), (8, 9), (8, 10), (10, 11)]

def c8GenericFinGraphAdj (i j : Fin 12) : Prop :=
  i ≠ j ∧
    ((i.val, j.val) ∈ c8GenericFinGraphLineEdges ∨ (j.val, i.val) ∈ c8GenericFinGraphLineEdges)

instance c8GenericFinGraphAdj_symmInst : Std.Symm c8GenericFinGraphAdj where
  symm := fun i j h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance c8GenericFinGraphAdj_irreflInst : Std.Irrefl c8GenericFinGraphAdj where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

instance (i j : Fin 12) : Decidable (c8GenericFinGraphAdj i j) := by
  unfold c8GenericFinGraphAdj
  infer_instance

def c8GenericFinGraph : SimpleGraph (Fin 12) where
  Adj := c8GenericFinGraphAdj
  symm := inferInstance
  loopless := inferInstance

instance : DecidableRel c8GenericFinGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (c8GenericFinGraphAdj i j))

theorem c8GenericFinGraph_isTree : c8GenericFinGraph.IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨by native_decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

theorem c8_pathDecomp_genericFinPreconnected (k : Fin 10) :
    c8GenericFinGraph.induce (c8PathDecompFinGenericNodeInterval k : Set (Fin 12)) |>.Preconnected := by
  fin_cases k <;> native_decide

/-! Standard `genericDecompAdj` on Fin-12 (no junction-bridge edges 8–9, 8–10, 10–11).
    With bridge-revision bags (`c8PathDecompFinGenericBag`, edge 5 at junc₀/junc₂), overlap RI still
    fails — junction-bridge edges are necessary for the fin scaffold. -/

def c8GenericStandardFinGraphLineEdges : List (Nat × Nat) :=
  [(0, 1), (1, 9), (2, 3), (2, 8), (4, 5), (4, 10), (6, 7), (6, 11)]

def c8GenericStandardFinGraphAdj (i j : Fin 12) : Prop :=
  i ≠ j ∧
    ((i.val, j.val) ∈ c8GenericStandardFinGraphLineEdges ∨
      (j.val, i.val) ∈ c8GenericStandardFinGraphLineEdges)

instance c8GenericStandardFinGraphAdj_symmInst : Std.Symm c8GenericStandardFinGraphAdj where
  symm := fun i j h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance c8GenericStandardFinGraphAdj_irreflInst : Std.Irrefl c8GenericStandardFinGraphAdj where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

instance (i j : Fin 12) : Decidable (c8GenericStandardFinGraphAdj i j) := by
  unfold c8GenericStandardFinGraphAdj
  infer_instance

def c8GenericStandardFinGraph : SimpleGraph (Fin 12) where
  Adj := c8GenericStandardFinGraphAdj
  symm := inferInstance
  loopless := inferInstance

instance : DecidableRel c8GenericStandardFinGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (c8GenericStandardFinGraphAdj i j))

/-- Overlap edges whose node supersets fail RI on standard adj even with bridge-revision bags. -/
def c8GenericStandardFinPreconnectedBlocked : Finset (Fin 10) := {1, 3, 5, 7, 8, 9}

theorem c8GenericStandardFinPreconnectedBlocked_card :
    c8GenericStandardFinPreconnectedBlocked.card = 6 := by native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_one :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 1 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_three :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 3 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_five :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 5 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_seven :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 7 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_eight :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 8 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_genericStandardFinPreconnected_fail_nine :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval 9 : Set (Fin 12)) |>.Preconnected) := by
  native_decide

theorem c8_pathDecomp_genericStandardFinPreconnected_fail (k : Fin 10)
    (hk : k ∈ c8GenericStandardFinPreconnectedBlocked) :
    ¬ (c8GenericStandardFinGraph.induce (c8PathDecompFinGenericNodeInterval k : Set (Fin 12)) |>.Preconnected) := by
  fin_cases k <;> simp [c8GenericStandardFinPreconnectedBlocked] at hk ⊢ <;>
    first
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_one
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_three
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_five
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_seven
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_eight
    | exact c8_pathDecomp_genericStandardFinPreconnected_fail_nine
    | contradiction

/-! 7-node path scaffold (seg×longArcLen + relay + junc×4); running intersection fails at width ≤ 4. -/

private def c8PathDecompGlobalGraphAdj (i j : Fin 7) : Prop :=
  certPathGraphAdj 7 i j

instance c8PathDecompGlobalGraphAdj_symmInst : Std.Symm c8PathDecompGlobalGraphAdj where
  symm := fun i j h => (certPathGraphAdj_symmInst 7).symm i j h

instance c8PathDecompGlobalGraphAdj_irreflInst : Std.Irrefl c8PathDecompGlobalGraphAdj where
  irrefl := fun i h => (certPathGraphAdj_irreflInst 7).irrefl i h

private def c8PathDecompGlobalGraph : SimpleGraph (Fin 7) where
  Adj := c8PathDecompGlobalGraphAdj
  symm := inferInstance
  loopless := inferInstance

private theorem c8_pathDecomp_globalDecompGraph_adj (i j : Fin 7) :
    c8Hyp.globalDecompGraph.Adj i j ↔ c8PathDecompGlobalGraphAdj i j := by
  simp [NoncrossingPathDecompAssumptions.globalDecompGraph,
    NoncrossingPathDecompAssumptions.globalDecompAdj, c8Hyp,
    c8PathDecompGlobalGraphAdj, certPathGraphAdj]

instance (i j : Fin 7) : Decidable (c8PathDecompGlobalGraphAdj i j) := by
  unfold c8PathDecompGlobalGraphAdj
  infer_instance

instance : DecidableRel c8PathDecompGlobalGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (c8PathDecompGlobalGraphAdj i j))

private theorem c8PathDecompGlobalGraph_isTree : c8PathDecompGlobalGraph.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨by native_decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  decide

theorem c8_pathDecomp_globalDecompGraph_isTree :
    c8Hyp.globalDecompGraph.IsTree :=
  NoncrossingPathDecompAssumptions.globalDecompGraph_isTree_of_seven c8Hyp
    c8_pathDecomp_globalDecompNodeCount

/-! c8 mixed-cover fin discharge (gap=2 short arcs: sliding bags coincide). -/

theorem c8_pathDecomp_mixed_longSeg_junction_fin (j : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinLongArcBag j)
    (hk : ∃ endpoint : Fin 4, k ∈ c8PathDecompFinEnrichedJunctionBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  obtain ⟨endpoint, hk⟩ := hk
  exact c8_pathDecomp_residual_longSeg_junction_fin endpoint j i k hadj hi hk

theorem c8_pathDecomp_mixed_junction_longSeg_fin (j : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : ∃ endpoint : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag endpoint)
    (hk : k ∈ c8PathDecompFinLongArcBag j) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  obtain ⟨endpoint, hi⟩ := hi
  exact c8_pathDecomp_residual_junction_longSeg_fin endpoint j i k hadj hi hk

set_option maxHeartbeats 1600000 in
private theorem c8_pathDecomp_mixed_shortSeg_junction_fin_aux (a : Fin 4) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinShortArcBag a 0)
    (hk : ∃ endpoint : Fin 4, k ∈ c8PathDecompFinEnrichedJunctionBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  obtain ⟨endpoint, hk⟩ := hk
  fin_cases a <;> fin_cases endpoint <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinShortArcBag,
      c8PathDecompFinEnrichedJunctionBag] at hadj hi hk ⊢ <;>
    first | contradiction | decide

theorem c8_pathDecomp_mixed_shortSeg_junction_fin (a : Fin 4) (sj : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinShortArcBag a sj)
    (hk : ∃ endpoint : Fin 4, k ∈ c8PathDecompFinEnrichedJunctionBag endpoint) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  have hi' : i ∈ c8PathDecompFinShortArcBag a 0 :=
    (c8_pathDecomp_shortArcFinBag_eq a sj 0).symm ▸ hi
  exact c8_pathDecomp_mixed_shortSeg_junction_fin_aux a i k hadj hi' hk

set_option maxHeartbeats 1600000 in
private theorem c8_pathDecomp_mixed_junction_shortSeg_fin_aux (a : Fin 4) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : ∃ endpoint : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag endpoint)
    (hk : k ∈ c8PathDecompFinShortArcBag a 0) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  obtain ⟨endpoint, hi⟩ := hi
  fin_cases a <;> fin_cases endpoint <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinShortArcBag,
      c8PathDecompFinEnrichedJunctionBag] at hadj hi hk ⊢ <;>
    first | contradiction | decide

theorem c8_pathDecomp_mixed_junction_shortSeg_fin (a : Fin 4) (sj : Fin 2) (i k : Fin 10)
    (hadj : c8PathDecompFinAdj i k) (hi : ∃ endpoint : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag endpoint)
    (hk : k ∈ c8PathDecompFinShortArcBag a sj) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  have hk' : k ∈ c8PathDecompFinShortArcBag a 0 :=
    (c8_pathDecomp_shortArcFinBag_eq a sj 0).symm ▸ hk
  exact c8_pathDecomp_mixed_junction_shortSeg_fin_aux a i k hadj hi hk'

theorem c8_pathDecomp_longArcFinBag_eq (j j' : Fin 2) :
    c8PathDecompFinLongArcBag j = c8PathDecompFinLongArcBag j' := by
  fin_cases j <;> fin_cases j' <;> rfl

/-! Only cross-region long↔short line edge on c8 is (5,6); discharge via enriched junc₁. -/

set_option maxHeartbeats 1600000 in
theorem c8_pathDecomp_mixed_longSeg_shortSeg_fin (lj : Fin 2) (a : Fin 4) (sj : Fin 2)
    (i k : Fin 10) (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinLongArcBag lj)
    (hk : k ∈ c8PathDecompFinShortArcBag a sj) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  have hk' : k ∈ c8PathDecompFinShortArcBag a 0 :=
    (c8_pathDecomp_shortArcFinBag_eq a sj 0).symm ▸ hk
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinShortArcBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi hk' ⊢ <;>
    first
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩
      | exact ⟨3, by decide, by decide⟩
      | contradiction

set_option maxHeartbeats 1600000 in
theorem c8_pathDecomp_mixed_shortSeg_longSeg_fin (a : Fin 4) (sj : Fin 2) (lj : Fin 2)
    (i k : Fin 10) (hadj : c8PathDecompFinAdj i k) (hi : i ∈ c8PathDecompFinShortArcBag a sj)
    (hk : k ∈ c8PathDecompFinLongArcBag lj) :
    ∃ ep : Fin 4, i ∈ c8PathDecompFinEnrichedJunctionBag ep ∧
      k ∈ c8PathDecompFinEnrichedJunctionBag ep := by
  have hi' : i ∈ c8PathDecompFinShortArcBag a 0 :=
    (c8_pathDecomp_shortArcFinBag_eq a sj 0).symm ▸ hi
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    simp [c8PathDecompFinAdj, c8PathDecompLineEdges, c8PathDecompFinLongArcBag,
      c8PathDecompFinShortArcBag, c8PathDecompFinEnrichedJunctionBag] at hadj hi' hk ⊢ <;>
    first
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩
      | exact ⟨3, by decide, by decide⟩
      | contradiction

/-! c8 fork tree: seg₀–seg₁–relay–junc₀–junc₁ with junc₂/junc₃ leaves at junc₁ (index 4). -/

private def c8PathDecompForkLineEdges : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (4, 6)]

private def c8PathDecompForkGraphAdj (i j : Fin 7) : Prop :=
  i ≠ j ∧
    ((i.val, j.val) ∈ c8PathDecompForkLineEdges ∨ (j.val, i.val) ∈ c8PathDecompForkLineEdges)

instance c8PathDecompForkGraphAdj_symmInst : Std.Symm c8PathDecompForkGraphAdj where
  symm := fun i j h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance c8PathDecompForkGraphAdj_irreflInst : Std.Irrefl c8PathDecompForkGraphAdj where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

instance (i j : Fin 7) : Decidable (c8PathDecompForkGraphAdj i j) := by
  unfold c8PathDecompForkGraphAdj
  infer_instance

private def c8PathDecompForkGraph : SimpleGraph (Fin 7) where
  Adj := c8PathDecompForkGraphAdj
  symm := inferInstance
  loopless := inferInstance

instance : DecidableRel c8PathDecompForkGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (c8PathDecompForkGraphAdj i j))

private theorem c8PathDecompForkGraph_isTree : c8PathDecompForkGraph.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨by native_decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  decide

/-- On the fork tree, closing to connected node supersets forces junc₁ (index 4) for these six edges. -/
private def c8PathDecompForkJunc1Required : Finset (Fin 10) := {1, 3, 5, 6, 8, 9}

private theorem c8_pathDecomp_forkJunc1_required_card :
    c8PathDecompForkJunc1Required.card = 6 := by native_decide

private theorem c8_pathDecomp_forkJunc1_currentBag_card :
    c8PathDecompFinGlobalBag 4 = {5, 6, 7, 8} := by decide

/-!
Running intersection on the fork tree requires connected node supersets. Current bare membership
(e.g. k=1 at `{3,5}` omitting hub 4) fails preconnected — see `c8_pathDecomp_forkFinPreconnected_one`.
Closing to connected supersets forces six edges through junc₁ (`c8PathDecompForkJunc1Required`), exceeding
width ≤4 (card ≤5). Discharge parked; c8 tw=3 via `c8NestedGraph_lineGraph_hasTreeDecomp_three`.
-/

private def c8PathDecompFinNodeInterval (k : Fin 10) : Finset (Fin 7) :=
  match k with
  | 0 => {3}
  | 1 => {3, 5}
  | 2 => {5}
  | 3 => {5, 6}
  | 4 => {6}
  | 5 => {4, 6}
  | 6 => {0, 1, 4}
  | 7 => {0, 1, 3, 4}
  | 8 => {3, 4}
  | 9 => {5, 6}

private theorem c8_pathDecomp_globalFinNodeSet (k : Fin 10) (w : Fin 7) :
    k ∈ c8PathDecompFinGlobalBag w ↔ w ∈ c8PathDecompFinNodeInterval k := by
  fin_cases k <;> fin_cases w <;>
    simp [c8PathDecompFinGlobalBag, c8PathDecompFinNodeInterval] <;> decide

private theorem c8_pathDecomp_forkFinPreconnected_one :
    ¬ (c8PathDecompForkGraph.induce (c8PathDecompFinNodeInterval 1 : Set (Fin 7)) |>.Preconnected) := by
  native_decide

private theorem c8_pathDecomp_forkFinPreconnected_five :
    (c8PathDecompForkGraph.induce (c8PathDecompFinNodeInterval 5 : Set (Fin 7)) |>.Preconnected) := by
  native_decide

/- block-parked: c8NestedGraph_pathDecompOpenGoals / discharge via fork tree at width≤4 infeasible
noncomputable def c8NestedGraph_pathDecompOpenGoals := ...
theorem c8NestedGraph_pathDecomp_hasTreeDecomp_three := ...
Use `c8NestedGraph_lineGraph_hasTreeDecomp_three` (CertificatesLine iso transport) for c8 tw=3.
-/

def noncrossingPathDecompDoc : String :=
  "PROVED: longArc/shortArc/enrichedJunction bags (card≤4, width≤3), LongArcSegmentFragment, " ++
  "arcEdgeCoverConsecutive, shortArcEdgeCoverConsecutive, longArcLineGraphBag_edgeCover, " ++
  "globalBagFamily/globalDecompGraph (7-node path scaffold), certPathGraph7_isTree, " ++
  "c7/c8 smoke GraphEdgeBijection + pathDecompAssumptions; " ++
  "c8 fork tree IsTree (c8PathDecompForkGraph), globalFinNodeSet, fork hub lower bound; " ++
  "c8 generic fin scaffold (12 nodes), bridge fin preconnected 10/10, standard-adj RI blocked (6 edges); " ++
  "OPEN: 7-node fork discharge at width≤4 — junc₁ needs 6 edges; path tree also blocked."

end PNPLab.ChordWidth
