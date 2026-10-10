/-
  Bridge `CycleTwoChordGraph` → `CrossingEndpoints` → `tseitinAxioms`.

  Crossing branch uses existing `CrossingEndpointsTseitin` directly; noncrossing
  branch uses a chord1/chord2 generalized encoder. Smoke helpers wire fixed
  axioms into `TseitinWidthTreewidthCharacterization` for Phase 5 incremental work.
-/

import PNPLab.ChordWidth.BaseCaseTwoChords.CycleTwoChords
import PNPLab.ChordWidth.LiteratureHypothesis
import PNPLab.CrossingEndpointsTseitin

namespace PNPLab.ChordWidth

open PNPLab.Bicyclic
open PNPLab.Resolution
open SimpleGraph

/-- Default odd marking: charge 1 on `⟨p0, _⟩`, 0 elsewhere (matches `oddCharge`). -/
def CycleTwoChordGraph.defaultOddMarking (g : CycleTwoChordGraph) : OddMarkingOdd (Fin g.n) :=
  have hp0 : g.p0 < g.n := by obtain ⟨_, _, _, h3n⟩ := g.ordered; omega
  let φ : OddMarking (Fin g.n) := ⟨fun w => if w.val = g.p0 then 1 else 0⟩
  have hodd : OddMarking.isOdd φ := by
    simp only [OddMarking.isOdd, OddMarking.totalCharge, φ]
    have hsum : (∑ x : Fin g.n, if x.val = g.p0 then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single ⟨g.p0, hp0⟩]
      · simp
      · intro b _ hbne
        simp [Fin.ext_iff] at hbne
        simp [hbne]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    rw [hsum]
  ⟨φ, hodd⟩

/-! ### Noncrossing Tseitin encoder (crossing reuses `CrossingEndpoints`) -/

def CycleTwoChordGraph.sortedChord1 (g : CycleTwoChordGraph) : Nat × Nat :=
  let c := g.chord1
  if c.1 ≤ c.2 then c else (c.2, c.1)

def CycleTwoChordGraph.sortedChord2 (g : CycleTwoChordGraph) : Nat × Nat :=
  let c := g.chord2
  if c.1 ≤ c.2 then c else (c.2, c.1)

def CycleTwoChordGraph.cycleEdges (g : CycleTwoChordGraph) : List (Nat × Nat) :=
  (List.range g.n).map fun i => sortedEdge i ((i + 1) % g.n)

def CycleTwoChordGraph.edgeList (g : CycleTwoChordGraph) : List (Nat × Nat) :=
  sortEdgePairs (g.cycleEdges ++ [g.sortedChord1, g.sortedChord2])

def CycleTwoChordGraph.edgeVar (g : CycleTwoChordGraph) (u v : Nat) : Option Nat :=
  let p := sortedEdge u v
  let rec go (i : Nat) : List (Nat × Nat) → Option Nat
    | [] => none
    | y :: ys => if y = p then some (i + 1) else go (i + 1) ys
  go 0 g.edgeList

def CycleTwoChordGraph.neighbors (g : CycleTwoChordGraph) (v : Nat) : List Nat :=
  if v < g.n then
    let left := (v + g.n - 1) % g.n
    let right := (v + 1) % g.n
    let c1 := g.chord1
    let c2 := g.chord2
    let chordNbrs :=
      if v = c1.1 then [c1.2]
      else if v = c1.2 then [c1.1]
      else if v = c2.1 then [c2.2]
      else if v = c2.2 then [c2.1]
      else []
    sortUniqueNat (left :: right :: chordNbrs)
  else
    []

def CycleTwoChordGraph.incidentVars (g : CycleTwoChordGraph) (v : Nat) : List Lit :=
  (g.neighbors v).filterMap fun u => g.edgeVar v u

def CycleTwoChordGraph.oddCharge (g : CycleTwoChordGraph) (v : Nat) : Nat :=
  if v = g.p0 then 1 else 0

/-- Odd marking charge at vertex `v` (Nat-level, for encoder plumbing). -/
def CycleTwoChordGraph.oddChargeFromMarking (g : CycleTwoChordGraph) (φ : OddMarkingOdd (Fin g.n))
    (v : Nat) : Nat :=
  if h : v < g.n then φ.val.charge ⟨v, h⟩ else 0

theorem CycleTwoChordGraph.oddChargeFromMarking_default (g : CycleTwoChordGraph) (v : Nat) :
    g.oddChargeFromMarking g.defaultOddMarking v = g.oddCharge v := by
  unfold oddChargeFromMarking oddCharge defaultOddMarking
  by_cases hv : v < g.n
  · simp [hv]
  · have hp0lt : g.p0 < g.n := by obtain ⟨_, _, _, h3n⟩ := g.ordered; omega
    have hne : v ≠ g.p0 := by
      intro heq
      have : v < g.n := heq ▸ hp0lt
      omega
    simp [hv, hne]

def CycleTwoChordGraph.xorClausesForVertex (g : CycleTwoChordGraph) (v : Nat) : List Clause :=
  xorCnfNorm (g.incidentVars v) (g.oddCharge v)

def CycleTwoChordGraph.xorClausesForVertexFromMarking (g : CycleTwoChordGraph)
    (φ : OddMarkingOdd (Fin g.n)) (v : Nat) : List Clause :=
  xorCnfNorm (g.incidentVars v) (g.oddChargeFromMarking φ v)

def CycleTwoChordGraph.tseitinAxiomsNoncrossingFromMarking (g : CycleTwoChordGraph)
    (φ : OddMarkingOdd (Fin g.n)) : List Clause :=
  let raw := (List.range g.n).flatMap (g.xorClausesForVertexFromMarking φ ·)
  dedupSortedClauses (sortClauses raw)

def CycleTwoChordGraph.tseitinAxiomsFromMarking (g : CycleTwoChordGraph)
    (φ : OddMarkingOdd (Fin g.n)) : List Clause :=
  match g.pairing with
  | .crossing =>
    (⟨g.n, g.p0, g.p1, g.p2, g.p3, g.ordered⟩ : CrossingEndpoints).tseitinAxioms
  | .nested | .disjoint =>
    g.tseitinAxiomsNoncrossingFromMarking φ

def CycleTwoChordGraph.tseitinAxiomsNoncrossing (g : CycleTwoChordGraph) : List Clause :=
  let raw := (List.range g.n).flatMap (g.xorClausesForVertex ·)
  dedupSortedClauses (sortClauses raw)

/--
  Tseitin axioms for C_n + two chords.

  Crossing: reuse `CrossingEndpoints.tseitinAxioms` (Python `_all_axioms` track).
  Noncrossing: generalized chord1/chord2 encoder above.
-/
def CycleTwoChordGraph.tseitinAxioms (g : CycleTwoChordGraph) : List Clause :=
  match g.pairing with
  | .crossing =>
    (⟨g.n, g.p0, g.p1, g.p2, g.p3, g.ordered⟩ : CrossingEndpoints).tseitinAxioms
  | .nested | .disjoint =>
    g.tseitinAxiomsNoncrossing

theorem CycleTwoChordGraph.tseitinAxiomsFromMarking_eq_default (g : CycleTwoChordGraph)
    (φ : OddMarkingOdd (Fin g.n)) (hφ : φ = g.defaultOddMarking) :
    g.tseitinAxiomsFromMarking φ = g.tseitinAxioms := by
  subst hφ
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing
  · rfl
  · simp [tseitinAxiomsFromMarking, tseitinAxioms, tseitinAxiomsNoncrossingFromMarking,
      tseitinAxiomsNoncrossing]
    congr 1; congr 1
    apply List.flatMap_congr
    intro v hv
    simp [xorClausesForVertexFromMarking, xorClausesForVertex, oddChargeFromMarking_default]
  · simp [tseitinAxiomsFromMarking, tseitinAxioms, tseitinAxiomsNoncrossingFromMarking,
      tseitinAxiomsNoncrossing]
    congr 1; congr 1
    apply List.flatMap_congr
    intro v hv
    simp [xorClausesForVertexFromMarking, xorClausesForVertex, oddChargeFromMarking_default]

def tseitinFromMarking (g : CycleTwoChordGraph) :
    OddMarkingOdd (Fin g.n) → List Clause :=
  g.tseitinAxiomsFromMarking

theorem tseitinFromMarking_default (g : CycleTwoChordGraph) :
    tseitinFromMarking g g.defaultOddMarking = g.tseitinAxioms :=
  g.tseitinAxiomsFromMarking_eq_default _ rfl

theorem c5OfoldGraph_tseitinFromMarking_default :
    tseitinFromMarking c5OfoldGraph c5OfoldGraph.defaultOddMarking = c5OfoldGraph.tseitinAxioms :=
  tseitinFromMarking_default c5OfoldGraph

theorem c8NestedGraph_tseitinFromMarking_default :
    tseitinFromMarking c8NestedGraph c8NestedGraph.defaultOddMarking = c8NestedGraph.tseitinAxioms :=
  tseitinFromMarking_default c8NestedGraph

/-- Crossing branch: graph axioms via `toCrossingEndpoints`. -/
def CycleTwoChordGraph.tseitinAxioms_crossing (g : CycleTwoChordGraph)
    (hc : g.chordsCross) : List Clause :=
  (g.toCrossingEndpoints hc).tseitinAxioms

/-- Noncrossing branch: unified noncrossing encoder. -/
def CycleTwoChordGraph.tseitinAxioms_noncrossing (g : CycleTwoChordGraph)
    (_hnc : ¬ g.chordsCross) : List Clause :=
  g.tseitinAxioms

theorem CycleTwoChordGraph.tseitinAxioms_noncrossing_eq (g : CycleTwoChordGraph)
    (hnc : ¬ g.chordsCross) :
    g.tseitinAxioms_noncrossing hnc = g.tseitinAxioms := rfl

theorem CycleTwoChordGraph.tseitinAxioms_eq_crossing (g : CycleTwoChordGraph)
    (hc : g.chordsCross) :
    g.tseitinAxioms = (g.toCrossingEndpoints hc).tseitinAxioms := by
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing
  · rfl
  · simp [chordsCross] at hc
  · simp [chordsCross] at hc

theorem CycleTwoChordGraph.tseitinAxioms_crossing_eq (g : CycleTwoChordGraph)
    (hc : g.chordsCross) :
    g.tseitinAxioms_crossing hc = (g.toCrossingEndpoints hc).tseitinAxioms := rfl

theorem CycleTwoChordGraph.tseitinAxioms_crossing_eq_axioms (g : CycleTwoChordGraph)
    (hc : g.chordsCross) :
    g.tseitinAxioms_crossing hc = g.tseitinAxioms :=
  (tseitinAxioms_eq_crossing g hc).symm

/-! ### Smoke: c5Ofold graph ↔ endpoints axioms -/

theorem c5OfoldGraph_tseitinAxioms_eq :
    c5OfoldGraph.tseitinAxioms = c5OfoldEndpoints.tseitinAxioms := by
  rw [CycleTwoChordGraph.tseitinAxioms_eq_crossing c5OfoldGraph c5OfoldGraph_chordsCross,
    c5OfoldGraph_toCrossingEndpoints]

theorem c5OfoldGraph_tseitinAxioms_eq_ofold :
    c5OfoldGraph.tseitinAxioms = ofoldGAxioms := by
  rw [c5OfoldGraph_tseitinAxioms_eq, c5Ofold_tseitinAxioms_eq_ofold]

theorem c5OfoldGraph_tseitinAxioms_crossing_eq :
    c5OfoldGraph.tseitinAxioms_crossing c5OfoldGraph_chordsCross =
      c5OfoldEndpoints.tseitinAxioms := by
  rw [CycleTwoChordGraph.tseitinAxioms_crossing_eq_axioms, c5OfoldGraph_tseitinAxioms_eq]

theorem c5OfoldGraph_tseitinAxioms_length :
    c5OfoldGraph.tseitinAxioms.length = 18 := by
  rw [c5OfoldGraph_tseitinAxioms_eq, c5Ofold_tseitinAxioms_length]

/-! ### Smoke: c6Crossing graph ↔ endpoints axioms -/

theorem c6CrossingGraph_tseitinAxioms_eq :
    c6CrossingGraph.tseitinAxioms = c6Endpoints0123.tseitinAxioms := by
  rw [CycleTwoChordGraph.tseitinAxioms_eq_crossing c6CrossingGraph c6CrossingGraph_chordsCross,
    c6CrossingGraph_toCrossingEndpoints]

theorem c6CrossingGraph_tseitinAxioms_crossing_eq :
    c6CrossingGraph.tseitinAxioms_crossing c6CrossingGraph_chordsCross =
      c6Endpoints0123.tseitinAxioms := by
  rw [CycleTwoChordGraph.tseitinAxioms_crossing_eq_axioms, c6CrossingGraph_tseitinAxioms_eq]

/-! ### Literature hypothesis helpers (smoke axioms → `tseitin` field) -/

/--
  Constant Tseitin encoder from fixed axioms.

  Smoke regime: charge on `p0` only; axioms independent of odd marking φ.
  Full odd-marking φ-dependent encoding is Phase 5 remaining work.
-/
def tseitinFromAxioms {V : Type*} [Fintype V] (axioms : List Clause) :
    OddMarkingOdd V → List Clause :=
  fun _ => axioms

/--
  Build a `TseitinWidthTreewidthCharacterization` from fixed axioms and an
  explicit width hypothesis (literature layer — not a PNPLab proof).
-/
def TseitinWidthTreewidthCharacterization.ofAxioms
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ k : Nat)
    (axioms : List Clause)
    (width : ∀ φ : OddMarkingOdd V, ResolutionWidth (tseitinFromAxioms axioms φ) (max Δ k)) :
    TseitinWidthTreewidthCharacterization V G Δ k where
  tseitin := tseitinFromAxioms axioms
  width_eq := width

/--
  Partial unified smoke wiring: one axiom list on `g`, crossing branch matches
  `toCrossingEndpoints` encoder; both branches use `tseitinFromAxioms`.
-/
structure TwoChordSmokeTseitinUnification (g : CycleTwoChordGraph) where
  axioms : List Clause
  graph_axioms : axioms = g.tseitinAxioms
  crossing_bridge :
    ∀ (hc : g.chordsCross), axioms = (g.toCrossingEndpoints hc).tseitinAxioms
  noncrossing_axioms :
    ∀ (hnc : ¬ g.chordsCross), axioms = g.tseitinAxioms_noncrossing hnc

def TwoChordSmokeTseitinUnification.tseitin (u : TwoChordSmokeTseitinUnification g) :
    OddMarkingOdd (Fin g.n) → List Clause :=
  tseitinFromAxioms u.axioms

theorem TwoChordSmokeTseitinUnification.crossing_tseitin_eq
    (u : TwoChordSmokeTseitinUnification g) (hc : g.chordsCross)
    (_φ : OddMarkingOdd (Fin g.n)) :
    u.tseitin _φ = (g.toCrossingEndpoints hc).tseitinAxioms := by
  simp [TwoChordSmokeTseitinUnification.tseitin, tseitinFromAxioms]
  exact u.crossing_bridge hc

theorem TwoChordSmokeTseitinUnification.noncrossing_tseitin_eq
    (u : TwoChordSmokeTseitinUnification g) (_hnc : ¬ g.chordsCross)
    (_φ : OddMarkingOdd (Fin g.n)) :
    u.tseitin _φ = g.tseitinAxioms := by
  simp [TwoChordSmokeTseitinUnification.tseitin, tseitinFromAxioms]
  exact u.graph_axioms

def c5Ofold_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c5OfoldGraph where
  axioms := c5OfoldGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c5OfoldGraph hc
  noncrossing_axioms := fun hnc => absurd c5OfoldGraph_chordsCross hnc

def c6Crossing_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c6CrossingGraph where
  axioms := c6CrossingGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c6CrossingGraph hc
  noncrossing_axioms := fun hnc => absurd c6CrossingGraph_chordsCross hnc

def c8Nested_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c8NestedGraph where
  axioms := c8NestedGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc => absurd hc c8NestedGraph_not_crossing
  noncrossing_axioms := fun _ => rfl

def c7Crossing_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c7CrossingGraph where
  axioms := c7CrossingGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c7CrossingGraph hc
  noncrossing_axioms := fun hnc => absurd c7CrossingGraph_chordsCross hnc

def c8Crossing_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c8CrossingGraph where
  axioms := c8CrossingGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c8CrossingGraph hc
  noncrossing_axioms := fun hnc => absurd c8CrossingGraph_chordsCross hnc

def c9Crossing_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c9CrossingGraph where
  axioms := c9CrossingGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c9CrossingGraph hc
  noncrossing_axioms := fun hnc => absurd c9CrossingGraph_chordsCross hnc

def c10Crossing_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c10CrossingGraph where
  axioms := c10CrossingGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc =>
    CycleTwoChordGraph.tseitinAxioms_eq_crossing c10CrossingGraph hc
  noncrossing_axioms := fun hnc => absurd c10CrossingGraph_chordsCross hnc

def c7Nested_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c7NestedGraph where
  axioms := c7NestedGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc => absurd hc c7NestedGraph_not_crossing
  noncrossing_axioms := fun _ => rfl

def c9Nested_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c9NestedGraph where
  axioms := c9NestedGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc => absurd hc c9NestedGraph_not_crossing
  noncrossing_axioms := fun _ => rfl

def c10Nested_smoke_tseitin_unification : TwoChordSmokeTseitinUnification c10NestedGraph where
  axioms := c10NestedGraph.tseitinAxioms
  graph_axioms := rfl
  crossing_bridge := fun hc => absurd hc c10NestedGraph_not_crossing
  noncrossing_axioms := fun _ => rfl

def tseitinEncodingDoc : String :=
  "CycleTwoChordGraph.tseitinAxioms; crossing ↔ CrossingEndpoints; " ++
  "oddChargeFromMarking + tseitinFromMarking (default φ = p0 charge); " ++
  "c5Ofold/c8Nested smoke φ-default = tseitinAxioms; " ++
  "tseitinFromAxioms + TwoChordSmokeTseitinUnification"

def tseitinEncodingGapDoc : String :=
  "Remaining Fase 5: crossing branch φ-dependent encoder; prove width_eq from axioms; " ++
  "universal TwoChordSmokeTseitinUnification ∀ valid n"

end PNPLab.ChordWidth
