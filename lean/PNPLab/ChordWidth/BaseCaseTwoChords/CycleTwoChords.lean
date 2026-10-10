/-
  C_n + two chords (Fase 1): crossing vs noncrossing, Δ = 3 scaffolding.

  Wraps / extends `CrossingEndpoints` / `toSimpleGraph` from
  `CrossingEndpointsGraph.lean`; adds noncrossing pairings from the ear law
  track (`NoncrossingTwoChordsEar`).
-/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import PNPLab.CrossingEndpointsGraph
import PNPLab.NoncrossingTwoChordsEar

namespace PNPLab.ChordWidth

open Bicyclic
open SimpleGraph
open Outerplanar

/-- Legal chord pairings on four sorted cycle endpoints. -/
inductive ChordPairing where
  | crossing
  | nested
  | disjoint
  deriving DecidableEq

/--
  Cycle C_n with two chords on four distinct endpoints
  `p0 < p1 < p2 < p3 < n`.
-/
structure CycleTwoChordGraph where
  n : Nat
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  pairing : ChordPairing
  ordered : p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < n

/-- Four endpoints are distinct (follows from strict order). -/
theorem CycleTwoChordGraph.endpointsDistinct (g : CycleTwoChordGraph) :
    g.p0 ≠ g.p1 ∧ g.p0 ≠ g.p2 ∧ g.p0 ≠ g.p3 ∧
      g.p1 ≠ g.p2 ∧ g.p1 ≠ g.p3 ∧ g.p2 ≠ g.p3 := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Chords cross iff pairing is the crossing type `(p0,p2)` + `(p1,p3)`. -/
def CycleTwoChordGraph.chordsCross (g : CycleTwoChordGraph) : Prop :=
  g.pairing = ChordPairing.crossing

def CycleTwoChordGraph.chordsCross_dec (g : CycleTwoChordGraph) : Bool :=
  decide (g.pairing = ChordPairing.crossing)

theorem CycleTwoChordGraph.chordsCross_iff (g : CycleTwoChordGraph) :
    g.chordsCross ↔ g.chordsCross_dec = true := by
  simp [chordsCross, chordsCross_dec]

def CycleTwoChordGraph.chord1 (g : CycleTwoChordGraph) : Nat × Nat :=
  match g.pairing with
  | .crossing => (g.p0, g.p2)
  | .nested => (g.p0, g.p3)
  | .disjoint => (g.p0, g.p1)

def CycleTwoChordGraph.chord2 (g : CycleTwoChordGraph) : Nat × Nat :=
  match g.pairing with
  | .crossing => (g.p1, g.p3)
  | .nested => (g.p1, g.p2)
  | .disjoint => (g.p2, g.p3)

theorem CycleTwoChordGraph.chord1_fst_lt (g : CycleTwoChordGraph) : g.chord1.1 < g.n := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord1] <;> omega

theorem CycleTwoChordGraph.chord1_snd_lt (g : CycleTwoChordGraph) : g.chord1.2 < g.n := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord1] <;> omega

theorem CycleTwoChordGraph.chord2_fst_lt (g : CycleTwoChordGraph) : g.chord2.1 < g.n := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord2] <;> omega

theorem CycleTwoChordGraph.chord2_snd_lt (g : CycleTwoChordGraph) : g.chord2.2 < g.n := by
  obtain ⟨h01, h12, h23, h3n⟩ := g.ordered
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing <;> simp [chord2] <;> omega

/-- Bridge to `CrossingEndpoints` when chords cross. -/
def CycleTwoChordGraph.toCrossingEndpoints (g : CycleTwoChordGraph)
    (_hc : g.chordsCross) : CrossingEndpoints :=
  ⟨g.n, g.p0, g.p1, g.p2, g.p3, g.ordered⟩

/-- Noncrossing `SimpleGraph` via explicit chord endpoints. -/
def CycleTwoChordGraph.toSimpleGraphNoncrossing (g : CycleTwoChordGraph) :
    SimpleGraph (Fin g.n) :=
  cycleGraph g.n ⊔
    edge (⟨g.chord1.1, g.chord1_fst_lt⟩ : Fin g.n) ⟨g.chord1.2, g.chord1_snd_lt⟩ ⊔
    edge (⟨g.chord2.1, g.chord2_fst_lt⟩ : Fin g.n) ⟨g.chord2.2, g.chord2_snd_lt⟩

/-- Mathlib `SimpleGraph` for C_n + two chords (all pairings). -/
def CycleTwoChordGraph.toSimpleGraph (g : CycleTwoChordGraph) : SimpleGraph (Fin g.n) :=
  match g.pairing with
  | .crossing =>
    let e : CrossingEndpoints := ⟨g.n, g.p0, g.p1, g.p2, g.p3, g.ordered⟩
    e.toSimpleGraph
  | .nested | .disjoint =>
    g.toSimpleGraphNoncrossing

/-- Computable adjacency on the explicit noncrossing `cycleGraph ⊔ edge ⊔ edge` form. -/
instance CycleTwoChordGraph.decidableAdjNoncrossing (g : CycleTwoChordGraph) :
    DecidableRel g.toSimpleGraphNoncrossing.Adj := by
  unfold toSimpleGraphNoncrossing
  infer_instance

/-- Classical decidability for suppressed-core on generic instances. -/
noncomputable instance CycleTwoChordGraph.decidableAdj (g : CycleTwoChordGraph) :
    DecidableRel g.toSimpleGraph.Adj :=
  fun _ _ => Classical.propDecidable _

theorem CycleTwoChordGraph.crossing_toSimpleGraph_eq (g : CycleTwoChordGraph)
    (hc : g.chordsCross) :
    g.toSimpleGraph = (g.toCrossingEndpoints hc).toSimpleGraph := by
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing
  · apply SimpleGraph.ext
    funext u v
    rfl
  · simp [CycleTwoChordGraph.chordsCross] at hc
  · simp [CycleTwoChordGraph.chordsCross] at hc

/-- All pairings share the explicit `cycleGraph ⊔ edge ⊔ edge` form. -/
theorem CycleTwoChordGraph.toSimpleGraph_eq_noncrossing (g : CycleTwoChordGraph) :
    g.toSimpleGraph = g.toSimpleGraphNoncrossing := by
  rcases g with ⟨n, p0, p1, p2, p3, pairing, ordered⟩
  cases pairing
  · apply SimpleGraph.ext
    funext u v
    simp [CycleTwoChordGraph.toSimpleGraph, CycleTwoChordGraph.toSimpleGraphNoncrossing,
      CycleTwoChordGraph.chord1, CycleTwoChordGraph.chord2, Bicyclic.CrossingEndpoints.toSimpleGraph]
  · rfl
  · rfl

/-- Real maximum degree on the Mathlib `SimpleGraph` (Δ = 3 target). -/
def CycleTwoChordGraph.toSimpleGraph_maxDegree_le_three (g : CycleTwoChordGraph) : Prop :=
  g.toSimpleGraph.maxDegree ≤ 3

def CycleTwoChordGraph.realMaxDegreeThree (g : CycleTwoChordGraph) : Prop :=
  g.toSimpleGraph.maxDegree = 3

/--
  Phase 1 proxy: `4 ≤ n` (four distinct ordered endpoints ⇒ `n ≥ 4`).

  **Phase 5 gap:** see `DegreeBounds.lean` — `isDelta3Admissible` (= Python `is_valid_delta3`);
  crossing ⇒ `isNondegenerate` proved; generic nondegenerate ⇒ Δ=3 combinatorics still open.
-/
def CycleTwoChordGraph.maxDegree_eq_three (g : CycleTwoChordGraph) : Prop :=
  4 ≤ g.n

theorem CycleTwoChordGraph.ordered_implies_n_ge_four (g : CycleTwoChordGraph) :
    4 ≤ g.n := by
  obtain ⟨_, _, _, h3n⟩ := g.ordered
  omega

theorem CycleTwoChordGraph.maxDegree_eq_three_of_ordered (g : CycleTwoChordGraph) :
    g.maxDegree_eq_three :=
  g.ordered_implies_n_ge_four

theorem CycleTwoChordGraph.realMaxDegreeThree_implies_le
    (g : CycleTwoChordGraph) (h : g.realMaxDegreeThree) :
    g.toSimpleGraph_maxDegree_le_three := by
  unfold realMaxDegreeThree toSimpleGraph_maxDegree_le_three at *
  omega

theorem CycleTwoChordGraph.realMaxDegreeThree_implies_proxy
    (g : CycleTwoChordGraph) (_h : g.realMaxDegreeThree) :
    g.maxDegree_eq_three :=
  g.maxDegree_eq_three_of_ordered

/-- Transport `maxDegree = 3` along a smoke graph equality (no `native_decide` on `g` itself). -/
theorem CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq
    {g : CycleTwoChordGraph} {sg : SimpleGraph (Fin g.n)}
    [DecidableRel sg.Adj] (hgraph : g.toSimpleGraph = sg) (hdeg : sg.maxDegree = 3) :
    g.realMaxDegreeThree := by
  dsimp [CycleTwoChordGraph.realMaxDegreeThree]
  simpa [hgraph] using hdeg

theorem CycleTwoChordGraph.toSimpleGraph_maxDegree_le_three_of_graph_eq
    {g : CycleTwoChordGraph} {sg : SimpleGraph (Fin g.n)}
    [DecidableRel sg.Adj] (hgraph : g.toSimpleGraph = sg) (hdeg : sg.maxDegree ≤ 3) :
    g.toSimpleGraph_maxDegree_le_three := by
  dsimp [CycleTwoChordGraph.toSimpleGraph_maxDegree_le_three]
  simpa [hgraph] using hdeg

/-!
  **B1 (partial):** Generic `realMaxDegreeThree` remains smoke/transport for instances;
  **`toSimpleGraph_maxDegree_le` / `isNondegenerate → realMaxDegreeThree`** proved in
  `DegreeBounds.lean` via explicit `cycleGraph ⊔ edge ⊔ edge` degree bounds.
  **Proved generically:** `ordered_implies_n_ge_four`, endpoint distinctness, smoke transport,
  `toSimpleGraph_eq_noncrossing`, Δ ≤ 3 on all valid `g`, Δ = 3 when nondegenerate.
  **Open:** unconditional tw ∀n, iso, full main theorem (B1–B4 out of scope).
-/

/-- Smoke: C₇ crossing `(0,1,2,3)` (representative track). -/
def c7CrossingGraph : CycleTwoChordGraph where
  n := 7
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c7CrossingGraph_chordsCross : c7CrossingGraph.chordsCross := rfl

abbrev c7CrossingSmokeGraph : SimpleGraph (Fin c7CrossingGraph.n) :=
  cycleGraph c7CrossingGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c7CrossingGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c7CrossingGraph.n) ⟨3, by decide⟩

theorem c7CrossingSmokeGraph_maxDegree : c7CrossingSmokeGraph.maxDegree = 3 := by native_decide

theorem c7CrossingGraph_toSimpleGraph_eq_smoke :
    c7CrossingGraph.toSimpleGraph = c7CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c7CrossingSmokeGraph, c7CrossingGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c7CrossingGraph_realMaxDegreeThree : c7CrossingGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c7CrossingGraph_toSimpleGraph_eq_smoke
    c7CrossingSmokeGraph_maxDegree

/-- Smoke: C₇ nested `(0,1,2,3)`. -/
def c7NestedGraph : CycleTwoChordGraph where
  n := 7
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .nested
  ordered := by decide

theorem c7NestedGraph_not_crossing : ¬ c7NestedGraph.chordsCross := by
  simp [CycleTwoChordGraph.chordsCross, c7NestedGraph]

abbrev c7NestedSmokeGraph : SimpleGraph (Fin c7NestedGraph.n) :=
  cycleGraph c7NestedGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c7NestedGraph.n) ⟨3, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c7NestedGraph.n) ⟨2, by decide⟩

theorem c7NestedSmokeGraph_maxDegree : c7NestedSmokeGraph.maxDegree = 3 := by native_decide

theorem c7NestedGraph_toSimpleGraph_eq_smoke :
    c7NestedGraph.toSimpleGraph = c7NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c7NestedSmokeGraph, c7NestedGraph, CycleTwoChordGraph.toSimpleGraph,
    CycleTwoChordGraph.toSimpleGraphNoncrossing, CycleTwoChordGraph.chord1,
    CycleTwoChordGraph.chord2, Fin.isValue]

theorem c7NestedGraph_realMaxDegreeThree : c7NestedGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c7NestedGraph_toSimpleGraph_eq_smoke
    c7NestedSmokeGraph_maxDegree

/-- Smoke: C₈ crossing `(0,1,2,3)`. -/
def c8CrossingGraph : CycleTwoChordGraph where
  n := 8
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c8CrossingGraph_chordsCross : c8CrossingGraph.chordsCross := rfl

abbrev c8CrossingSmokeGraph : SimpleGraph (Fin c8CrossingGraph.n) :=
  cycleGraph c8CrossingGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c8CrossingGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c8CrossingGraph.n) ⟨3, by decide⟩

theorem c8CrossingSmokeGraph_maxDegree : c8CrossingSmokeGraph.maxDegree = 3 := by native_decide

theorem c8CrossingGraph_toSimpleGraph_eq_smoke :
    c8CrossingGraph.toSimpleGraph = c8CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c8CrossingSmokeGraph, c8CrossingGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c8CrossingGraph_realMaxDegreeThree : c8CrossingGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c8CrossingGraph_toSimpleGraph_eq_smoke
    c8CrossingSmokeGraph_maxDegree

/-- Smoke: C₉ crossing `(0,1,2,3)`. -/
def c9CrossingGraph : CycleTwoChordGraph where
  n := 9
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c9CrossingGraph_chordsCross : c9CrossingGraph.chordsCross := rfl

abbrev c9CrossingSmokeGraph : SimpleGraph (Fin c9CrossingGraph.n) :=
  cycleGraph c9CrossingGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c9CrossingGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c9CrossingGraph.n) ⟨3, by decide⟩

theorem c9CrossingSmokeGraph_maxDegree : c9CrossingSmokeGraph.maxDegree = 3 := by native_decide

theorem c9CrossingGraph_toSimpleGraph_eq_smoke :
    c9CrossingGraph.toSimpleGraph = c9CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c9CrossingSmokeGraph, c9CrossingGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c9CrossingGraph_realMaxDegreeThree : c9CrossingGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c9CrossingGraph_toSimpleGraph_eq_smoke
    c9CrossingSmokeGraph_maxDegree

/-- Smoke: C₉ nested `(0,2,3,5)` (representative gap shape). -/
def c9NestedGraph : CycleTwoChordGraph where
  n := 9
  p0 := 0
  p1 := 2
  p2 := 3
  p3 := 5
  pairing := .nested
  ordered := by decide

theorem c9NestedGraph_not_crossing : ¬ c9NestedGraph.chordsCross := by
  simp [CycleTwoChordGraph.chordsCross, c9NestedGraph]

abbrev c9NestedSmokeGraph : SimpleGraph (Fin c9NestedGraph.n) :=
  cycleGraph c9NestedGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c9NestedGraph.n) ⟨5, by decide⟩ ⊔
    edge (⟨2, by decide⟩ : Fin c9NestedGraph.n) ⟨3, by decide⟩

theorem c9NestedSmokeGraph_maxDegree : c9NestedSmokeGraph.maxDegree = 3 := by native_decide

theorem c9NestedGraph_toSimpleGraph_eq_smoke :
    c9NestedGraph.toSimpleGraph = c9NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c9NestedSmokeGraph, c9NestedGraph, CycleTwoChordGraph.toSimpleGraph,
    CycleTwoChordGraph.toSimpleGraphNoncrossing, CycleTwoChordGraph.chord1,
    CycleTwoChordGraph.chord2, Fin.isValue]

theorem c9NestedGraph_realMaxDegreeThree : c9NestedGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c9NestedGraph_toSimpleGraph_eq_smoke
    c9NestedSmokeGraph_maxDegree

/-- Smoke: C₁₀ crossing `(0,1,2,3)`. -/
def c10CrossingGraph : CycleTwoChordGraph where
  n := 10
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c10CrossingGraph_chordsCross : c10CrossingGraph.chordsCross := rfl

abbrev c10CrossingSmokeGraph : SimpleGraph (Fin c10CrossingGraph.n) :=
  cycleGraph c10CrossingGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c10CrossingGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c10CrossingGraph.n) ⟨3, by decide⟩

theorem c10CrossingSmokeGraph_maxDegree : c10CrossingSmokeGraph.maxDegree = 3 := by native_decide

theorem c10CrossingGraph_toSimpleGraph_eq_smoke :
    c10CrossingGraph.toSimpleGraph = c10CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c10CrossingSmokeGraph, c10CrossingGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c10CrossingGraph_realMaxDegreeThree : c10CrossingGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c10CrossingGraph_toSimpleGraph_eq_smoke
    c10CrossingSmokeGraph_maxDegree

/-- Smoke: C₁₀ nested `(0,1,2,3)`. -/
def c10NestedGraph : CycleTwoChordGraph where
  n := 10
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .nested
  ordered := by decide

theorem c10NestedGraph_not_crossing : ¬ c10NestedGraph.chordsCross := by
  simp [CycleTwoChordGraph.chordsCross, c10NestedGraph]

abbrev c10NestedSmokeGraph : SimpleGraph (Fin c10NestedGraph.n) :=
  cycleGraph c10NestedGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c10NestedGraph.n) ⟨3, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c10NestedGraph.n) ⟨2, by decide⟩

theorem c10NestedSmokeGraph_maxDegree : c10NestedSmokeGraph.maxDegree = 3 := by native_decide

theorem c10NestedGraph_toSimpleGraph_eq_smoke :
    c10NestedGraph.toSimpleGraph = c10NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c10NestedSmokeGraph, c10NestedGraph, CycleTwoChordGraph.toSimpleGraph,
    CycleTwoChordGraph.toSimpleGraphNoncrossing, CycleTwoChordGraph.chord1,
    CycleTwoChordGraph.chord2, Fin.isValue]

theorem c10NestedGraph_realMaxDegreeThree : c10NestedGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c10NestedGraph_toSimpleGraph_eq_smoke
    c10NestedSmokeGraph_maxDegree

/-- Smoke: C₅ crossing instance matching `c5OfoldEndpoints`. -/
def c5OfoldGraph : CycleTwoChordGraph where
  n := 5
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c5OfoldGraph_chordsCross : c5OfoldGraph.chordsCross := rfl

theorem c5OfoldGraph_toCrossingEndpoints :
    c5OfoldGraph.toCrossingEndpoints c5OfoldGraph_chordsCross = c5OfoldEndpoints := by
  rfl

theorem c5OfoldGraph_crossing_graph_eq :
    c5OfoldGraph.toSimpleGraph =
      (c5OfoldGraph.toCrossingEndpoints c5OfoldGraph_chordsCross).toSimpleGraph :=
  c5OfoldGraph.crossing_toSimpleGraph_eq c5OfoldGraph_chordsCross

abbrev c5OfoldSmokeGraph : SimpleGraph (Fin c5OfoldGraph.n) :=
  cycleGraph c5OfoldGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c5OfoldGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c5OfoldGraph.n) ⟨3, by decide⟩

theorem c5OfoldSmokeGraph_maxDegree : c5OfoldSmokeGraph.maxDegree = 3 := by native_decide

/-- Smoke: C₆ crossing instance. -/
def c6CrossingGraph : CycleTwoChordGraph where
  n := 6
  p0 := 0
  p1 := 1
  p2 := 2
  p3 := 3
  pairing := .crossing
  ordered := by decide

theorem c6CrossingGraph_chordsCross : c6CrossingGraph.chordsCross := rfl

theorem c6CrossingGraph_toCrossingEndpoints :
    c6CrossingGraph.toCrossingEndpoints c6CrossingGraph_chordsCross = c6Endpoints0123 := by
  rfl

theorem c6CrossingGraph_crossing_toSimpleGraph :
    c6CrossingGraph.toSimpleGraph =
      (c6CrossingGraph.toCrossingEndpoints c6CrossingGraph_chordsCross).toSimpleGraph :=
  c6CrossingGraph.crossing_toSimpleGraph_eq c6CrossingGraph_chordsCross

abbrev c6CrossingSmokeGraph : SimpleGraph (Fin c6CrossingGraph.n) :=
  cycleGraph c6CrossingGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c6CrossingGraph.n) ⟨2, by decide⟩ ⊔
    edge (⟨1, by decide⟩ : Fin c6CrossingGraph.n) ⟨3, by decide⟩

theorem c6CrossingSmokeGraph_maxDegree : c6CrossingSmokeGraph.maxDegree = 3 := by native_decide

/-- Smoke: C₈ nested noncrossing (matches `c8Nested` ear law). -/
def c8NestedGraph : CycleTwoChordGraph where
  n := 8
  p0 := 0
  p1 := 2
  p2 := 4
  p3 := 6
  pairing := .nested
  ordered := by decide

theorem c8NestedGraph_not_crossing : ¬ c8NestedGraph.chordsCross := by
  simp [CycleTwoChordGraph.chordsCross, c8NestedGraph]

abbrev c8NestedSmokeGraph : SimpleGraph (Fin c8NestedGraph.n) :=
  cycleGraph c8NestedGraph.n ⊔
    edge (⟨0, by decide⟩ : Fin c8NestedGraph.n) ⟨6, by decide⟩ ⊔
    edge (⟨2, by decide⟩ : Fin c8NestedGraph.n) ⟨4, by decide⟩

theorem c8NestedSmokeGraph_maxDegree : c8NestedSmokeGraph.maxDegree = 3 := by native_decide

theorem c5OfoldGraph_toSimpleGraph_eq_smoke :
    c5OfoldGraph.toSimpleGraph = c5OfoldSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c5OfoldSmokeGraph, c5OfoldGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c6CrossingGraph_toSimpleGraph_eq_smoke :
    c6CrossingGraph.toSimpleGraph = c6CrossingSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c6CrossingSmokeGraph, c6CrossingGraph, CycleTwoChordGraph.toSimpleGraph,
    Bicyclic.CrossingEndpoints.toSimpleGraph, Fin.isValue]

theorem c8NestedGraph_toSimpleGraph_eq_smoke :
    c8NestedGraph.toSimpleGraph = c8NestedSmokeGraph := by
  apply SimpleGraph.ext
  funext u v
  simp [c8NestedSmokeGraph, c8NestedGraph, CycleTwoChordGraph.toSimpleGraph,
    CycleTwoChordGraph.toSimpleGraphNoncrossing, CycleTwoChordGraph.chord1,
    CycleTwoChordGraph.chord2, Fin.isValue]

theorem c5OfoldGraph_maxDegree_three : c5OfoldGraph.maxDegree_eq_three :=
  c5OfoldGraph.maxDegree_eq_three_of_ordered

theorem c5OfoldGraph_realMaxDegreeThree : c5OfoldGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c5OfoldGraph_toSimpleGraph_eq_smoke
    c5OfoldSmokeGraph_maxDegree

theorem c5OfoldGraph_toSimpleGraph_maxDegree_le_three :
    c5OfoldGraph.toSimpleGraph_maxDegree_le_three :=
  c5OfoldGraph.realMaxDegreeThree_implies_le c5OfoldGraph_realMaxDegreeThree

theorem c6CrossingGraph_maxDegree_three : c6CrossingGraph.maxDegree_eq_three :=
  c6CrossingGraph.maxDegree_eq_three_of_ordered

theorem c6CrossingGraph_realMaxDegreeThree : c6CrossingGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c6CrossingGraph_toSimpleGraph_eq_smoke
    c6CrossingSmokeGraph_maxDegree

theorem c6CrossingGraph_toSimpleGraph_maxDegree_le_three :
    c6CrossingGraph.toSimpleGraph_maxDegree_le_three :=
  c6CrossingGraph.realMaxDegreeThree_implies_le c6CrossingGraph_realMaxDegreeThree

theorem c8NestedGraph_maxDegree_three : c8NestedGraph.maxDegree_eq_three :=
  c8NestedGraph.maxDegree_eq_three_of_ordered

theorem c8NestedGraph_realMaxDegreeThree : c8NestedGraph.realMaxDegreeThree :=
  CycleTwoChordGraph.realMaxDegreeThree_of_graph_eq c8NestedGraph_toSimpleGraph_eq_smoke
    c8NestedSmokeGraph_maxDegree

theorem c8NestedGraph_toSimpleGraph_maxDegree_le_three :
    c8NestedGraph.toSimpleGraph_maxDegree_le_three :=
  c8NestedGraph.realMaxDegreeThree_implies_le c8NestedGraph_realMaxDegreeThree

/-- Link nested graph to existing `NoncrossingTwoChords` smoke. -/
def c8NestedGraph_toNoncrossingTwoChords : NoncrossingTwoChords :=
  c8Nested

theorem c8NestedGraph_noncrossing_ear :
    c8NestedGraph_toNoncrossingTwoChords.whitney_ear = c8Nested.whitney_ear := by
  rfl

def cycleTwoChordsDoc : String :=
  "C_n + 2 chords; crossing ↔ CrossingEndpoints; noncrossing ↔ NoncrossingTwoChordsEar"

end PNPLab.ChordWidth
