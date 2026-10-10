/-
  Universal cyclic arc lengths and edge counts between four ordered endpoints on C_n.

  Structural lemmas for parametric path/tree decompositions of L(G).
-/

import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords

namespace PNPLab.ChordWidth

/-- Length of arc i along the cycle, for endpoints p0 < p1 < p2 < p3 < n. -/
def CycleTwoChordGraph.cyclicGap (g : CycleTwoChordGraph) : Fin 4 → Nat
  | 0 => g.p1 - g.p0
  | 1 => g.p2 - g.p1
  | 2 => g.p3 - g.p2
  | 3 => g.n - g.p3 + g.p0

theorem CycleTwoChordGraph.cyclicGap_pos (g : CycleTwoChordGraph) (i : Fin 4) :
    0 < g.cyclicGap i := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  fin_cases i <;> simp [cyclicGap] <;> omega

theorem CycleTwoChordGraph.cyclicGaps_sum (g : CycleTwoChordGraph) :
    g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 2 + g.cyclicGap 3 = g.n := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  simp [cyclicGap]
  omega

/-!
  ## Cycle edge counts per arc

  Each cyclic gap equals the number of cycle edges on that arc (not chord edges).
  Pairing affects chord placement only; the arc partition is pairing-independent.
-/

def CycleTwoChordGraph.cycleArcEdgeCount (g : CycleTwoChordGraph) (i : Fin 4) : Nat :=
  g.cyclicGap i

theorem CycleTwoChordGraph.cycleArcEdgeCount_eq_cyclicGap (g : CycleTwoChordGraph) (i : Fin 4) :
    g.cycleArcEdgeCount i = g.cyclicGap i :=
  rfl

theorem CycleTwoChordGraph.cycleArcEdgeCount_pos (g : CycleTwoChordGraph) (i : Fin 4) :
    0 < g.cycleArcEdgeCount i :=
  g.cyclicGap_pos i

def CycleTwoChordGraph.cycleEdgeCount (g : CycleTwoChordGraph) : Nat :=
  g.cyclicGap 0 + g.cyclicGap 1 + g.cyclicGap 2 + g.cyclicGap 3

theorem CycleTwoChordGraph.cycleEdgeCount_eq_n (g : CycleTwoChordGraph) :
    g.cycleEdgeCount = g.n := by
  dsimp [cycleEdgeCount]
  exact g.cyclicGaps_sum

def CycleTwoChordGraph.chordEdgeCount (_g : CycleTwoChordGraph) : Nat := 2

def CycleTwoChordGraph.graphEdgeCountNondegenerate (g : CycleTwoChordGraph) : Nat :=
  g.cycleEdgeCount + g.chordEdgeCount

theorem CycleTwoChordGraph.graphEdgeCountNondegenerate_eq (g : CycleTwoChordGraph) :
    g.graphEdgeCountNondegenerate = g.n + 2 := by
  simp [graphEdgeCountNondegenerate, cycleEdgeCount_eq_n, chordEdgeCount]

/-!
  ## Chord endpoint indices (pairing-dependent)
-/

def CycleTwoChordGraph.chord1EndpointIdx (g : CycleTwoChordGraph) : Nat × Nat :=
  match g.pairing with
  | .crossing => (0, 2)
  | .nested => (0, 3)
  | .disjoint => (0, 1)

def CycleTwoChordGraph.chord2EndpointIdx (g : CycleTwoChordGraph) : Nat × Nat :=
  match g.pairing with
  | .crossing => (1, 3)
  | .nested => (1, 2)
  | .disjoint => (2, 3)

theorem CycleTwoChordGraph.chord1EndpointIdx_fst_lt_snd (g : CycleTwoChordGraph) :
    g.chord1EndpointIdx.1 < g.chord1EndpointIdx.2 := by
  rcases g with ⟨_, _, _, _, _, pairing, ⟨_, h12, _, _⟩⟩
  cases pairing <;> simp [chord1EndpointIdx] <;> omega

theorem CycleTwoChordGraph.chord2EndpointIdx_fst_lt_snd (g : CycleTwoChordGraph) :
    g.chord2EndpointIdx.1 < g.chord2EndpointIdx.2 := by
  rcases g with ⟨_, _, _, _, _, pairing, ⟨_, h12, h23, _⟩⟩
  cases pairing <;> simp [chord2EndpointIdx] <;> omega

theorem CycleTwoChordGraph.chord1_eq_of_pairing (g : CycleTwoChordGraph) :
    match g.pairing with
    | .crossing => g.chord1 = (g.p0, g.p2)
    | .nested => g.chord1 = (g.p0, g.p3)
    | .disjoint => g.chord1 = (g.p0, g.p1) := by
  rcases g with ⟨_, _, _, _, _, pairing, _⟩
  cases pairing <;> rfl

theorem CycleTwoChordGraph.chord2_eq_of_pairing (g : CycleTwoChordGraph) :
    match g.pairing with
    | .crossing => g.chord2 = (g.p1, g.p3)
    | .nested => g.chord2 = (g.p1, g.p2)
    | .disjoint => g.chord2 = (g.p2, g.p3) := by
  rcases g with ⟨_, _, _, _, _, pairing, _⟩
  cases pairing <;> rfl

/-- Forward cycle edges from p0 to p2 (crossing chord1). -/
theorem CycleTwoChordGraph.chord1_forwardCycleEdges_crossing (g : CycleTwoChordGraph)
    (hc : g.pairing = ChordPairing.crossing) :
    g.cycleArcEdgeCount 0 + g.cycleArcEdgeCount 1 = g.p2 - g.p0 := by
  obtain ⟨h01, h12, _, _⟩ := g.ordered
  simp [hc, cycleArcEdgeCount, cyclicGap]
  omega

/-- Forward cycle edges from p0 to p3 (nested chord1). -/
theorem CycleTwoChordGraph.chord1_forwardCycleEdges_nested (g : CycleTwoChordGraph)
    (hn : g.pairing = ChordPairing.nested) :
    g.cycleArcEdgeCount 0 + g.cycleArcEdgeCount 1 + g.cycleArcEdgeCount 2 = g.p3 - g.p0 := by
  obtain ⟨h01, h12, h23, _⟩ := g.ordered
  simp [hn, cycleArcEdgeCount, cyclicGap]
  omega

def arcLengthsDoc : String :=
  "cyclicGap = cycleArcEdgeCount; sum = n; |E(G)| = n+2 combinatorial; chord indices by pairing."

end PNPLab.ChordWidth
