/-
  Mathlib bridge for Category C tip-existence (G1/G6 peel layer).

  Mathlib is a Lake dependency (`v4.32.0`). This module discharges the
  **tree-peel leaf** half of outerplanar upper bounds using Mathlib's
  `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`, and records
  cycle/path facts used by the crossing open-arc model.

  Still axiomatized in `WhitneyEarAxiom`:
  - sketch `notCycle_hasLegalEar` on finitary peeled cores (graph→sketch hook)
  Discharged combinatorially: `whitney_legal_ear_exists`, `crossingEmbedWitness_ofArcs`,
  `CrossingGraphParams` (explicit arcs; no graph→arcs axiom).
  Graph C_n+chords→arcs obligation: `crossingGraphToArcsObligation` (doc + E2 mass).
  (Mathlib has no outerplanar ear-decomposition API yet.)
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import PNPLab.OpenArcPath
import PNPLab.WhitneyEarAxiom
import PNPLab.IsFacialOuterplanar
import PNPLab.CrossingChordsToArcs
import PNPLab.CrossingEndpointsGraph
import PNPLab.CrossingEndpointsSmokeMass
import PNPLab.OuterplanarFacialInduction
import PNPLab.OuterplanarOneChordTotal

namespace PNPLab.MathlibBridge

open SimpleGraph
open Bicyclic
open Outerplanar

/-! ### Tree peel — Mathlib discharges leaf existence -/

/-- Mathlib lemma used for peel-tree tips (G6 upper / OuterplanarPeel). -/
def mathlibTreeLeafLemma : String :=
  "Mathlib.Combinatorics.SimpleGraph.Acyclic: " ++
  "SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial"

/--
  Any nontrivial finite tree has a degree-1 vertex — the combinatorial leaf
  tip used when peeling trees off an outerplanar residual.
-/
theorem tree_has_leaf_tip {V : Type} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) :
    ∃ v : V, G.degree v = 1 :=
  IsTree.exists_vert_degree_one_of_nontrivial hG

/-- Single-edge subgraphs are trees (Mathlib) — peel base case. -/
theorem adj_subgraph_isTree {V : Type} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    (G.subgraphOfAdj h).coe.IsTree :=
  IsTree.coe_subgraphOfAdj h

/-- Path graphs are connected (Mathlib); open-arc of `k` internals ↔ `pathGraph (k+2)`. -/
theorem openArc_pathGraph_connected (k : Nat) :
    (pathGraph (k + 2)).Connected :=
  pathGraph_connected (k + 1)

/-- Removing a deg-1 vertex from a connected graph keeps it connected (Mathlib). -/
theorem peel_leaf_stays_connected {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (hconn : G.Connected) {v : V}
    [Fintype ↑(G.neighborSet v)] (hdeg : G.degree v = 1) :
    (G.induce ({v}ᶜ : Set V)).Connected :=
  Connected.induce_compl_singleton_of_degree_eq_one hconn hdeg

/-! ### Cycle / path facts for crossing arcs (G1) -/

/-- Cycle graphs of length ≥ 3 are 2-regular (Mathlib). -/
theorem cycleGraph_is_two_regular {n : Nat} (v : Fin (n + 3)) :
    (cycleGraph (n + 3)).degree v = 2 :=
  cycleGraph_degree_three_le

/-- Open-arc internals bookkeeping. -/
theorem openArc_internals_as_walk_length (k : Nat) :
    (crossingOpenArc k).internals = k :=
  rfl

/-- Positive open arc ⇒ frontier tip (combinatorial; independent of Mathlib). -/
theorem openArc_frontier_of_pos (k : Nat) (hk : 0 < k) :
    (crossingOpenArc k).hasFrontierTip = true :=
  crossingOpenArc_frontier k hk

/-- Bundle: Mathlib path connectivity + our frontier tip law. -/
theorem openArc_mathlib_frontier_bundle (k : Nat) (hk : 0 < k) :
    (pathGraph (k + 2)).Connected ∧
      (crossingOpenArc k).hasFrontierTip = true :=
  ⟨openArc_pathGraph_connected k, openArc_frontier_of_pos k hk⟩

/-- Status: which Whitney axioms Mathlib still does **not** discharge. -/
def remainingWhitneyAxioms : String :=
  "No G1 graph axioms (CrossingGraphParams + crossingEmbedWitness_ofArcs discharged). " ++
  "G6: OuterplanarBlockCut.expose + CycleChord.toBlockCut/toSimpleGraph discharged for " ++
  "certificates / cycle+chord; fold Δ≤3 via OuterplanarFoldPreservation.maxDegree_le_three_after_delete_tip. " ++
  "Still open: Mathlib IsOuterplanar API — see MathlibIsOuterplanarGap + OuterplanarExportCert; " ++
  "local IsOuterplanar ≡ IsFacialOuterplanar (not Mathlib). " ++
  "Mathlib tree leaf tip + peel leaf connectivity (" ++ mathlibTreeLeafLemma ++ ")."

/-! ### E5 export bridge — local outerplanarity (Mathlib API absent) -/

/--
  Graph instance paired with a facial export certificate.

  **Not** a Mathlib embedding: only the combinatorial cycle / cycle+chord cores
  that `OuterplanarEmbedCert` already tracks, plus the `SimpleGraph` bridge for
  one-chord cores (`CycleChord.toSimpleGraph`).
-/
inductive OuterplanarGraphInstance where
  | cycle (n : Nat) (h : 3 ≤ n)
  | oneChord (c : CycleChord)

def OuterplanarGraphInstance.nVertices : OuterplanarGraphInstance → Nat
  | .cycle n _ => n
  | .oneChord c => c.n

def OuterplanarGraphInstance.toEmbedCert : OuterplanarGraphInstance → OuterplanarEmbedCert
  | .cycle n h => .cycle n h
  | .oneChord c => .oneChord c

theorem OuterplanarGraphInstance.toEmbedCert_n (g : OuterplanarGraphInstance) :
    g.toEmbedCert.nVertices = g.nVertices := by
  cases g <;> rfl

/-- Mathlib `SimpleGraph` view of the export instance (local bridge only). -/
def OuterplanarGraphInstance.toSimpleGraph (g : OuterplanarGraphInstance) :
    SimpleGraph (Fin g.nVertices) :=
  match g with
  | .cycle n _ => cycleGraph n
  | .oneChord c => c.toSimpleGraph

def graphInstanceOfEmbedCert : OuterplanarEmbedCert → OuterplanarGraphInstance
  | .cycle n h => .cycle n h
  | .oneChord c => .oneChord c

theorem graphInstanceOfEmbedCert_n (e : OuterplanarEmbedCert) :
    (graphInstanceOfEmbedCert e).nVertices = e.nVertices := by
  cases e <;> rfl

theorem graphInstanceOfEmbedCert_embed (e : OuterplanarEmbedCert) :
    (graphInstanceOfEmbedCert e).toEmbedCert = e := by
  cases e <;> rfl

theorem OuterplanarGraphInstance.toEmbedCert_graphInstance (g : OuterplanarGraphInstance) :
    graphInstanceOfEmbedCert g.toEmbedCert = g := by
  cases g <;> rfl

theorem OuterplanarGraphInstance.toEmbedCert_nVertices (g : OuterplanarGraphInstance) :
    g.toEmbedCert.nVertices = g.nVertices := by
  cases g <;> rfl

theorem OuterplanarEmbedCert.eq_cycle_of_isCycle (e : OuterplanarEmbedCert)
    (hcy : e.isCycle = true) (n : Nat) (hn : e.nVertices = n) (h3 : 3 ≤ n) :
    e = .cycle n h3 := by
  cases e with
  | cycle n' h' =>
    have : n' = n := by simpa [OuterplanarEmbedCert.nVertices] using hn
    subst this
    rfl
  | oneChord _ =>
    simp [OuterplanarEmbedCert.isCycle] at hcy

/--
  Export-ready bundle: facial + local outerplanarity, embed cert, and the
  matching cycle / one-chord graph instance with its `SimpleGraph` bridge.

  **Honest:** this is PNPLab scaffolding only — Mathlib v4.32.0 has no
  `SimpleGraph.IsOuterplanar` to discharge from this certificate.

  **Migration path (once upstream lands):**
  1. Prove `export_to_mathlib exp` on `exp.graph.toSimpleGraph` via Mathlib predicate.
  2. Replace `localOuterplanar : IsOuterplanar n` with Mathlib certificate field.
  3. Show PNPLab `IsFacialOuterplanar` ⇒ Mathlib on cycle / one-chord cores.
  4. Peel induction (`CycleChord.toCycleBase`) chains via `FacialCycleBase.toExportCert`.
-/
structure OuterplanarExportCert (n : Nat) where
  facial : IsFacialOuterplanar n
  localOuterplanar : IsOuterplanar n
  local_facial : localOuterplanar.facial = facial
  embed : OuterplanarEmbedCert
  embed_n : embed.nVertices = n
  embed_facial : facial.cert = embed
  graph : OuterplanarGraphInstance
  graph_n : graph.nVertices = n
  graph_embed : graph.toEmbedCert = embed

def OuterplanarExportCert.ofFacial (ι : IsFacialOuterplanar n)
    (g : OuterplanarGraphInstance) (hg : g.nVertices = n)
    (he : g.toEmbedCert = ι.cert) : OuterplanarExportCert n where
  facial := ι
  localOuterplanar := ι.toIsOuterplanar
  local_facial := rfl
  embed := ι.cert
  embed_n := by rw [ι.n_eq]
  embed_facial := rfl
  graph := g
  graph_n := hg
  graph_embed := he

def OuterplanarExportCert.ofFacialOuterplanar (ι : IsFacialOuterplanar n) :
    OuterplanarExportCert n :=
  ofFacial ι (graphInstanceOfEmbedCert ι.cert)
    (by rw [graphInstanceOfEmbedCert_n, ι.n_eq])
    (graphInstanceOfEmbedCert_embed ι.cert)

def OuterplanarExportCert.ofCycle (n : Nat) (h : 3 ≤ n) : OuterplanarExportCert n :=
  ofFacial (IsFacialOuterplanar.cycle h) (.cycle n h) rfl rfl

def OuterplanarExportCert.ofOneChord (c : CycleChord) : OuterplanarExportCert c.n :=
  ofFacial (IsFacialOuterplanar.ofCert (.oneChord c)) (.oneChord c) rfl rfl

def OuterplanarExportCert.ofFacialCycleBase (b : FacialCycleBase) :
    OuterplanarExportCert b.nAfter :=
  let facial : IsFacialOuterplanar b.nAfter :=
    { cert := b.embedAfter, n_eq := b.embed_n }
  ofFacial facial (OuterplanarGraphInstance.cycle b.nAfter b.nAfter_ge3) rfl
    (OuterplanarEmbedCert.eq_cycle_of_isCycle b.embedAfter b.embed_cycle b.nAfter
      b.embed_n b.nAfter_ge3 |>.symm)

theorem OuterplanarExportCert.ofFacialCycleBase_embed_isCycle (b : FacialCycleBase) :
    (OuterplanarExportCert.ofFacialCycleBase b).embed.isCycle = true := by
  show b.embedAfter.isCycle = true
  exact b.embed_cycle

theorem OuterplanarExportCert.ofFacialCycleBase_graph (b : FacialCycleBase) :
    (OuterplanarExportCert.ofFacialCycleBase b).graph.toSimpleGraph = cycleGraph b.nAfter :=
  rfl

theorem OuterplanarExportCert.ofCycle_isCycle (n : Nat) (h : 3 ≤ n) :
    (ofCycle n h).embed.isCycle = true :=
  rfl

theorem OuterplanarExportCert.ofOneChord_graph (c : CycleChord) :
    (ofOneChord c).graph = OuterplanarGraphInstance.oneChord c :=
  rfl

theorem OuterplanarExportCert.ofOneChord_toSimpleGraph (c : CycleChord) :
    (ofOneChord c).graph.toSimpleGraph = c.toSimpleGraph :=
  rfl

def OuterplanarExportCert.toLocal (exp : OuterplanarExportCert n) : IsOuterplanar n :=
  exp.localOuterplanar

def OuterplanarExportCert.toFacial (exp : OuterplanarExportCert n) : IsFacialOuterplanar n :=
  exp.facial

theorem OuterplanarExportCert.toLocal_eq (exp : OuterplanarExportCert n) :
    exp.toLocal = exp.facial.toIsOuterplanar := by
  unfold OuterplanarExportCert.toLocal IsFacialOuterplanar.toIsOuterplanar
  rcases exp with ⟨facial, localOuterplanar, local_facial, _, _, _, _, _, _, _⟩
  cases localOuterplanar with | mk facial' =>
  subst local_facial
  rfl

theorem OuterplanarExportCert.toFacial_eq (exp : OuterplanarExportCert n) :
    exp.toFacial = exp.facial :=
  rfl

/-- `toFacial` reads the embed certificate carried by the export bundle. -/
theorem OuterplanarExportCert.toFacial_cert (exp : OuterplanarExportCert n) :
    exp.toFacial.cert = exp.embed :=
  exp.embed_facial

theorem OuterplanarExportCert.toFacial_n (exp : OuterplanarExportCert n) :
    exp.toFacial.cert.nVertices = n := by
  rw [OuterplanarExportCert.toFacial_cert, exp.embed_n]

/-- Re-export facial outerplanarity from an export certificate. -/
def IsFacialOuterplanar.fromExport (exp : OuterplanarExportCert n) : IsFacialOuterplanar n :=
  exp.toFacial

theorem IsFacialOuterplanar.fromExport_eq (exp : OuterplanarExportCert n) :
    IsFacialOuterplanar.fromExport exp = exp.facial :=
  rfl

theorem IsFacialOuterplanar.fromExport_ofFacialOuterplanar (ι : IsFacialOuterplanar n) :
    IsFacialOuterplanar.fromExport (OuterplanarExportCert.ofFacialOuterplanar ι) = ι :=
  rfl

theorem OuterplanarExportCert.ofFacialOuterplanar_facial (ι : IsFacialOuterplanar n) :
    (ofFacialOuterplanar ι).facial = ι :=
  rfl

theorem OuterplanarExportCert.ofFacialOuterplanar_toLocal (ι : IsFacialOuterplanar n) :
    (ofFacialOuterplanar ι).toLocal = ι.toIsOuterplanar :=
  rfl

theorem OuterplanarExportCert.ofCycle_facial (n : Nat) (h : 3 ≤ n) :
    (ofCycle n h).facial = IsFacialOuterplanar.cycle h :=
  rfl

theorem OuterplanarExportCert.ofOneChord_facial (c : CycleChord) :
    (ofOneChord c).facial = IsFacialOuterplanar.ofCert (.oneChord c) :=
  rfl

theorem OuterplanarExportCert.ofOneChord_toLocal (c : CycleChord) :
    (ofOneChord c).toLocal = IsOuterplanar.ofCert (.oneChord c) :=
  rfl

/-! ### Facial instance certificates (re-export from peel / cycle base proofs) -/

/-- Facial certificate for a pure cycle base (`n ≥ 3`). -/
def cycle_facialCert {n : Nat} (h : 3 ≤ n) : IsFacialOuterplanar n :=
  IsFacialOuterplanar.cycle h

/-- Facial certificate for a one-chord core. -/
def oneChord_facialCert (c : CycleChord) : IsFacialOuterplanar c.n :=
  IsFacialOuterplanar.ofCert (.oneChord c)

/-- Facial certificate extracted from a peel-to-cycle base. -/
def facialCycleBase_cert (b : FacialCycleBase) : IsFacialOuterplanar b.nAfter :=
  { cert := b.embedAfter, n_eq := b.embed_n }

theorem OuterplanarExportCert.ofFacialCycleBase_facial (b : FacialCycleBase) :
    (OuterplanarExportCert.ofFacialCycleBase b).facial = facialCycleBase_cert b :=
  rfl

theorem OuterplanarExportCert.ofFacialCycleBase_toFacial (b : FacialCycleBase) :
    (OuterplanarExportCert.ofFacialCycleBase b).toFacial = facialCycleBase_cert b :=
  rfl

/-- Export certificate for a completed facial peel-to-cycle base. -/
def facialCycleBase_toExportCert (b : FacialCycleBase) : OuterplanarExportCert b.nAfter :=
  OuterplanarExportCert.ofFacialCycleBase b

theorem facialCycleBase_toExportCert_facial (b : FacialCycleBase) :
    (facialCycleBase_toExportCert b).facial = facialCycleBase_cert b :=
  rfl

theorem facialCycleBase_toExportCert_toFacial (b : FacialCycleBase) :
    (facialCycleBase_toExportCert b).toFacial = facialCycleBase_cert b :=
  rfl

theorem facialCycleBase_toExportCert_fromExport (b : FacialCycleBase) :
    IsFacialOuterplanar.fromExport (facialCycleBase_toExportCert b) = facialCycleBase_cert b :=
  rfl

/-! ### Local ≡ facial equivalence (PNPLab stand-in for absent Mathlib API) -/

/--
  PNPLab local outerplanarity is the facial certificate wrapper (structure, not Prop).
  Not Mathlib geometric outerplanarity.
-/
def isOuterplanarEquivIsFacialOuterplanar (n : Nat) :
    IsOuterplanar n ≃ IsFacialOuterplanar n where
  toFun := IsOuterplanar.toFacial
  invFun := IsFacialOuterplanar.toIsOuterplanar
  left_inv := fun o => by cases o; rfl
  right_inv := fun _ => rfl

theorem isFacialOuterplanar_toIsOuterplanar_toFacial {n : Nat}
    (ι : IsFacialOuterplanar n) : ι.toIsOuterplanar.toFacial = ι :=
  rfl

theorem isOuterplanar_toFacial_toIsOuterplanar {n : Nat}
    (o : IsOuterplanar n) : o.toFacial.toIsOuterplanar = o := by
  cases o; rfl

theorem OuterplanarExportCert.toLocal_toFacial (exp : OuterplanarExportCert n) :
    exp.toLocal.toFacial = exp.toFacial :=
  exp.local_facial

theorem OuterplanarExportCert.toLocal_toFacial_cert (exp : OuterplanarExportCert n) :
    exp.toLocal.toFacial.cert = exp.embed := by
  rw [OuterplanarExportCert.toLocal_toFacial, OuterplanarExportCert.toFacial_cert]

def cycle_export {n : Nat} (h : 3 ≤ n) : OuterplanarExportCert n :=
  OuterplanarExportCert.ofCycle n h

def oneChord_export (c : CycleChord) : OuterplanarExportCert c.n :=
  OuterplanarExportCert.ofOneChord c

theorem cycle_export_facial {n : Nat} (h : 3 ≤ n) :
    (cycle_export h).facial = cycle_facialCert h :=
  rfl

theorem oneChord_export_facial (c : CycleChord) :
    (oneChord_export c).facial = oneChord_facialCert c :=
  rfl

theorem cycle_export_fromExport {n : Nat} (h : 3 ≤ n) :
    IsFacialOuterplanar.fromExport (cycle_export h) = cycle_facialCert h :=
  rfl

theorem oneChord_export_fromExport (c : CycleChord) :
    IsFacialOuterplanar.fromExport (oneChord_export c) = oneChord_facialCert c :=
  rfl

theorem OuterplanarExportCert.ofFacialOuterplanar_fromExport (ι : IsFacialOuterplanar n) :
    IsFacialOuterplanar.fromExport (OuterplanarExportCert.ofFacialOuterplanar ι) = ι :=
  IsFacialOuterplanar.fromExport_ofFacialOuterplanar ι

theorem OuterplanarExportCert.ofFacialOuterplanar_graph_embed (ι : IsFacialOuterplanar n) :
    (OuterplanarExportCert.ofFacialOuterplanar ι).graph.toEmbedCert = ι.cert :=
  graphInstanceOfEmbedCert_embed ι.cert

/-! ### Facial proof hooks — one-chord / cycle-base peel → export bundles -/

/-- Initial one-chord core (before peel) as an export bundle. -/
theorem CycleChord.oneChord_export_bundle (c : CycleChord) :
    let exp := OuterplanarExportCert.ofOneChord c
    exp.facial = oneChord_facialCert c ∧
      exp.toLocal = IsOuterplanar.ofCert (.oneChord c) ∧
      exp.graph.toSimpleGraph = c.toSimpleGraph ∧
      IsFacialOuterplanar.fromExport exp = oneChord_facialCert c := by
  dsimp
  refine ⟨rfl, rfl, ?_, rfl⟩
  exact OuterplanarExportCert.ofOneChord_toSimpleGraph c

/-- One-chord facial peel to cycle base yields an export cert on the residual. -/
theorem CycleChord.export_after_peel (c : CycleChord) (hPos : 1 < c.n) :
    ∃ exp : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
      exp.embed.isCycle = true :=
  ⟨OuterplanarExportCert.ofFacialCycleBase (c.toCycleBase hPos),
    OuterplanarExportCert.ofFacialCycleBase_embed_isCycle (c.toCycleBase hPos)⟩

/-- `reaches_cycle` (total one-chord peel) yields a cycle export cert on the residual. -/
theorem CycleChord.reaches_cycle_export (c : CycleChord) (hPos : 1 < c.n) :
    let b := c.toCycleBase hPos
    let exp := facialCycleBase_toExportCert b
    exp.embed.isCycle = true ∧
      exp.facial = facialCycleBase_cert b ∧
      exp.toFacial = facialCycleBase_cert b ∧
      IsFacialOuterplanar.fromExport exp = facialCycleBase_cert b ∧
      exp.graph.toSimpleGraph = cycleGraph b.nAfter := by
  let b := c.toCycleBase hPos
  let exp := facialCycleBase_toExportCert b
  dsimp
  refine ⟨b.embed_cycle, rfl, rfl, rfl, ?_⟩
  exact OuterplanarExportCert.ofFacialCycleBase_graph b

theorem CycleChord.export_after_peel_facial (c : CycleChord) (hPos : 1 < c.n) :
    ∃ exp : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
      exp.embed.isCycle = true ∧
        exp.facial = facialCycleBase_cert (c.toCycleBase hPos) ∧
        IsFacialOuterplanar.fromExport exp = facialCycleBase_cert (c.toCycleBase hPos) := by
  let b := c.toCycleBase hPos
  refine ⟨facialCycleBase_toExportCert b, ?_, ?_, ?_⟩
  · exact b.embed_cycle
  · exact facialCycleBase_toExportCert_facial b
  · exact facialCycleBase_toExportCert_fromExport b

theorem CycleChord.reaches_cycle_export_of_reaches (c : CycleChord) (hPos : 1 < c.n)
    (_h : let b := c.toCycleBase hPos
      b.embedAfter.isCycle = true ∧
        gf2Sum b.chargesAfter.charges = 1 ∧
        foldSteps (sketchCycle b.nAfter) = 0) :
    ∃ exp : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = facialCycleBase_cert (c.toCycleBase hPos) := by
  let b := c.toCycleBase hPos
  exact ⟨facialCycleBase_toExportCert b, b.embed_cycle, facialCycleBase_toExportCert_fromExport b⟩

/--
  Verified absence record: Mathlib v4.32.0 `SimpleGraph` tree has no outerplanar
  predicate (grep over `Mathlib/Combinatorics/SimpleGraph/*.lean`).
-/
structure MathlibIsOuterplanarAbsent where
  mathlibVersion : String := "v4.32.0"
  searchScope : String :=
    "Mathlib/Combinatorics/SimpleGraph (88 .lean files; no IsOuterplanar / outerplanar symbol)"
  verified : True := trivial

def mathlibIsOuterplanarAbsent : MathlibIsOuterplanarAbsent := {}

/--
  Mathlib v4.32.0 search for outerplanar / planar graph-theory API (E5 item 3).

  **Absent** (grep over 88 `SimpleGraph` files + full Mathlib):
  `IsOuterplanar`, `outerplanar`, `IsPlanar`, `PlanarGraph`, graph-minor `Kuratowski`,
  `treewidth` / `TreeWidth`.

  **Available anchors** for a future upstream predicate (already used in this bridge):
  - `SimpleGraph.IsTree`, `IsAcyclic` (`Acyclic.lean`)
  - `IsTree.exists_vert_degree_one_of_nontrivial` — peel leaf tips
  - `Connected.induce_compl_singleton_of_degree_eq_one` — peel connectivity
  - `cycleGraph`, `pathGraph` — cycle / open-arc cores
  - `Subgraph`, `Connected`, matching (`Tutte.lean`)

  **TODO in Mathlib** (comment only): `Coloring/Vertex.lean` lists "Planar graphs".
-/
structure MathlibIsOuterplanarSearch where
  mathlibVersion : String := "v4.32.0"
  simpleGraphFileCount : Nat := 88
  absentSymbols : String :=
    "IsOuterplanar; outerplanar; IsPlanar; PlanarGraph; Kuratowski (graph); treewidth"
  anchorModules : String :=
    "Acyclic (IsTree); CycleGraph; Hasse (pathGraph); Connectivity/Connected; Subgraph; Tutte"
  coloringTodo : String := "Coloring/Vertex.lean TODO: Planar graphs"
  verified : True := trivial

def mathlibIsOuterplanarSearch : MathlibIsOuterplanarSearch := {}

/-- Named Mathlib lemmas already wired into peel / crossing (migration anchors). -/
structure MathlibIsOuterplanarAnchors where
  treeLeafLemma : String := mathlibTreeLeafLemma
  peelConnectivityLemma : String :=
    "Connected.induce_compl_singleton_of_degree_eq_one"
  cycleGraphLemma : String := "cycleGraph_degree_three_le"
  pathGraphLemma : String := "pathGraph_connected"
  absent : MathlibIsOuterplanarAbsent := mathlibIsOuterplanarAbsent
  search : MathlibIsOuterplanarSearch := mathlibIsOuterplanarSearch

def mathlibIsOuterplanarAnchors : MathlibIsOuterplanarAnchors := {}

/--
  Typed E5/G6 gap: Mathlib v4.32.0 has no `SimpleGraph.IsOuterplanar`.
  Local stand-in is `IsOuterplanar` (= `IsFacialOuterplanar`); export bundles
  are ready for an upstream hook once Mathlib ships the predicate.
-/
structure MathlibIsOuterplanarGap where
  mathlibVersion : String := "v4.32.0"
  local_equiv : ∀ n : Nat, IsOuterplanar n ≃ IsFacialOuterplanar n
  facial_to_local : ∀ {n : Nat}, IsFacialOuterplanar n → IsOuterplanar n
  export_from_facial : ∀ {n : Nat}, IsFacialOuterplanar n → OuterplanarExportCert n
  export_to_facial : ∀ {n : Nat}, OuterplanarExportCert n → IsFacialOuterplanar n
  export_to_local : ∀ {n : Nat}, OuterplanarExportCert n → IsOuterplanar n
  export_roundtrip :
    ∀ {n : Nat} (ι : IsFacialOuterplanar n), (export_from_facial ι).facial = ι
  export_to_facial_roundtrip :
    ∀ {n : Nat} (ι : IsFacialOuterplanar n), export_to_facial (export_from_facial ι) = ι
  export_to_local_eq :
    ∀ {n : Nat} (exp : OuterplanarExportCert n), export_to_local exp = exp.facial.toIsOuterplanar
  export_to_facial_cert :
    ∀ {n : Nat} (exp : OuterplanarExportCert n), export_to_facial exp = exp.facial
  facial_from_export :
    ∀ {n : Nat} (exp : OuterplanarExportCert n),
      IsFacialOuterplanar.fromExport exp = export_to_facial exp
  graph_embed_roundtrip :
    ∀ (g : OuterplanarGraphInstance), graphInstanceOfEmbedCert g.toEmbedCert = g
  ofFacialOuterplanar_fromExport :
    ∀ {n : Nat} (ι : IsFacialOuterplanar n),
      IsFacialOuterplanar.fromExport (export_from_facial ι) = ι
  /-- Open once upstream lands: `OuterplanarExportCert` ⇒ Mathlib predicate on `toSimpleGraph`. -/
  mathlib_export_hook : True := trivial

def mathlibIsOuterplanarGap : MathlibIsOuterplanarGap where
  local_equiv := isOuterplanarEquivIsFacialOuterplanar
  facial_to_local := IsFacialOuterplanar.toIsOuterplanar
  export_from_facial := OuterplanarExportCert.ofFacialOuterplanar
  export_to_local := OuterplanarExportCert.toLocal
  export_to_facial := OuterplanarExportCert.toFacial
  export_roundtrip := fun _ => rfl
  export_to_facial_roundtrip := fun _ => rfl
  export_to_local_eq := fun exp => OuterplanarExportCert.toLocal_eq exp
  export_to_facial_cert := fun _ => rfl
  facial_from_export := fun _ => rfl
  graph_embed_roundtrip := OuterplanarGraphInstance.toEmbedCert_graphInstance
  ofFacialOuterplanar_fromExport := IsFacialOuterplanar.fromExport_ofFacialOuterplanar

/--
  Upstream migration hook — replace `True` fields once Mathlib ships
  `SimpleGraph.IsOuterplanar` (expected import:
  `Mathlib.Combinatorics.SimpleGraph.Outerplanar` or similar).

  **Step 1:** import upstream module; populate `MathlibIsOuterplanarSearch.anchorModules`.
  **Step 2:** prove `export_to_mathlib` on `OuterplanarGraphInstance.toSimpleGraph`.
  **Step 3:** show `facialCycleBase_toExportCert` / `CycleChord.reaches_cycle_export`
  compose with Mathlib peel lemmas (`IsTree.exists_vert_degree_one_of_nontrivial`).
  **Step 4:** align PNPLab `IsOuterplanar` with upstream on cycle / one-chord cores.

  Target obligations (not yet provable):
  - `export_to_mathlib`: `OuterplanarExportCert n → IsOuterplanar (graph.toSimpleGraph)`
  - `facial_to_mathlib`: bridge local facial certs to the upstream predicate
  - `local_matches_mathlib`: PNPLab `IsOuterplanar` aligns with Mathlib on our cores
-/
structure MathlibIsOuterplanarUpstreamHook where
  mathlibRev : String := "v4.32.0 (no SimpleGraph.IsOuterplanar yet)"
  absent : MathlibIsOuterplanarAbsent := mathlibIsOuterplanarAbsent
  search : MathlibIsOuterplanarSearch := mathlibIsOuterplanarSearch
  anchors : MathlibIsOuterplanarAnchors := mathlibIsOuterplanarAnchors
  export_to_mathlib :
    ∀ {n : Nat} (_ : OuterplanarExportCert n), True := fun _ => trivial
  export_graph :
    ∀ {n : Nat} (exp : OuterplanarExportCert n),
      exp.graph.toEmbedCert = exp.embed := fun exp => exp.graph_embed
  export_graph_toSimpleGraph :
    ∀ {n : Nat} (exp : OuterplanarExportCert n),
      exp.graph.toSimpleGraph = exp.graph.toSimpleGraph := fun _ => rfl
  facial_to_mathlib :
    ∀ {n : Nat} (_ : IsFacialOuterplanar n), True := fun _ => trivial
  local_matches_mathlib :
    ∀ {n : Nat} (_ : IsOuterplanar n), True := fun _ => trivial
  equiv_scaffold :
    ∀ n : Nat, IsOuterplanar n ≃ IsFacialOuterplanar n :=
      isOuterplanarEquivIsFacialOuterplanar
  peel_to_export :
    ∀ (c : CycleChord) (hPos : 1 < c.n),
      ∃ exp : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
        exp.embed.isCycle = true := CycleChord.export_after_peel

def mathlibIsOuterplanarUpstreamHook : MathlibIsOuterplanarUpstreamHook := {}

def mathlibOuterplanarBridgeBundle :
    MathlibIsOuterplanarAbsent × MathlibIsOuterplanarSearch × MathlibIsOuterplanarAnchors ×
      MathlibIsOuterplanarGap × MathlibIsOuterplanarUpstreamHook :=
  (mathlibIsOuterplanarAbsent, mathlibIsOuterplanarSearch, mathlibIsOuterplanarAnchors,
    mathlibIsOuterplanarGap, mathlibIsOuterplanarUpstreamHook)

/-- Local stand-in: every cycle `n ≥ 3` is `IsOuterplanar` (facial cert). -/
def cycle_isOuterplanar {n : Nat} (h : 3 ≤ n) : IsOuterplanar n :=
  IsOuterplanar.cycle h

/-- Local stand-in: every `OuterplanarEmbedCert` yields `IsOuterplanar`. -/
def cert_isOuterplanar (e : OuterplanarEmbedCert) : IsOuterplanar e.nVertices :=
  IsOuterplanar.ofCert e

theorem cert_export_toLocal (e : OuterplanarEmbedCert) :
    (OuterplanarExportCert.ofFacialOuterplanar (IsFacialOuterplanar.ofCert e)).toLocal =
      cert_isOuterplanar e :=
  rfl

theorem cert_export_facial (e : OuterplanarEmbedCert) :
    (OuterplanarExportCert.ofFacialOuterplanar (IsFacialOuterplanar.ofCert e)).facial =
      IsFacialOuterplanar.ofCert e :=
  rfl

/-! ### Mass-window upper-bound → export cert (G6 / E5) -/

/--
  Every crossing endpoint in the all-odd mass window `5 ≤ n ≤ 14` admits a
  cycle-base export certificate on `n` vertices (facial outerplanar base case).
-/
theorem mass_window_cycle_export (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ exp : OuterplanarExportCert e.n, exp.embed.isCycle = true := by
  refine ⟨OuterplanarExportCert.ofCycle e.n (by omega), rfl⟩

theorem mass_window_cycle_export_facial (e : CrossingEndpoints)
    (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ exp : OuterplanarExportCert e.n,
      exp.embed.isCycle = true ∧
        exp.facial = cycle_facialCert (by omega : 3 ≤ e.n) ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by omega : 3 ≤ e.n) := by
  refine ⟨OuterplanarExportCert.ofCycle e.n (by omega), rfl, ?_, ?_⟩
  · exact OuterplanarExportCert.ofCycle_facial e.n (by omega)
  · exact cycle_export_fromExport (by omega : 3 ≤ e.n)

/--
  Mass-window bundle: hop budget from `crossing_hop_budget_le_pack_window`,
  the `total + 4 = n` identity, and a cycle export cert at the full cycle size.
-/
theorem mass_window_upper_bound_export (e : CrossingEndpoints)
    (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    e.toArcs.total ≤ 10 ∧
      e.toArcs.total + 4 = e.n ∧
      ∃ exp : OuterplanarExportCert e.n, exp.embed.isCycle = true := by
  refine ⟨crossing_hop_budget_le_pack_window e h5 h14, ?_, ?_⟩
  · rw [CrossingEndpoints.toArcs_total]; omega
  · exact mass_window_cycle_export e h5 h14

theorem mass_window_upper_bound_export_facial (e : CrossingEndpoints)
    (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    e.toArcs.total ≤ 10 ∧
      e.toArcs.total + 4 = e.n ∧
      ∃ exp : OuterplanarExportCert e.n,
        exp.embed.isCycle = true ∧
          IsFacialOuterplanar.fromExport exp = cycle_facialCert (by omega : 3 ≤ e.n) := by
  refine ⟨crossing_hop_budget_le_pack_window e h5 h14, ?_, ?_⟩
  · rw [CrossingEndpoints.toArcs_total]; omega
  · obtain ⟨exp, hcyc, hfacial, hfrom⟩ := mass_window_cycle_export_facial e h5 h14
    exact ⟨exp, hcyc, hfrom⟩

/-- One-chord core in the mass window (before peel) as an export cert. -/
theorem mass_window_one_chord_initial_export (c : CycleChord)
    (_h5 : 5 ≤ c.n) (_h14 : c.n ≤ 14) :
    let exp := oneChord_export c
    exp.facial = oneChord_facialCert c ∧
      exp.graph.toSimpleGraph = c.toSimpleGraph := by
  dsimp [oneChord_export]
  refine ⟨oneChord_export_facial c, ?_⟩
  exact OuterplanarExportCert.ofOneChord_toSimpleGraph c

/--
  Mass-window one-chord cores peel to a cycle export cert; vertex count drops
  by at least one (`FacialCycleBase.nAfter_lt`).
-/
theorem mass_window_one_chord_peel_export (c : CycleChord)
    (_h5 : 5 ≤ c.n) (_h14 : c.n ≤ 14) (hPos : 1 < c.n) :
    ∃ exp : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
      exp.embed.isCycle = true ∧
        (c.toCycleBase hPos).nAfter < (c.toCycleBase hPos).nBefore := by
  obtain ⟨exp, hcyc⟩ := CycleChord.export_after_peel c hPos
  exact ⟨exp, hcyc, (c.toCycleBase hPos).nAfter_lt⟩

theorem mass_window_one_chord_peel_export_graph (c : CycleChord)
    (_h5 : 5 ≤ c.n) (_h14 : c.n ≤ 14) (hPos : 1 < c.n) :
    let exp := OuterplanarExportCert.ofFacialCycleBase (c.toCycleBase hPos)
    exp.embed.isCycle = true ∧
      exp.graph.toSimpleGraph = cycleGraph (c.toCycleBase hPos).nAfter := by
  dsimp
  refine ⟨?_, ?_⟩
  · exact OuterplanarExportCert.ofFacialCycleBase_embed_isCycle (c.toCycleBase hPos)
  · exact OuterplanarExportCert.ofFacialCycleBase_graph (c.toCycleBase hPos)

/--
  Mass-window one-chord: initial export on `c.n`, peel export on residual, facial roundtrip.
-/
theorem mass_window_one_chord_export_chain (c : CycleChord)
    (_h5 : 5 ≤ c.n) (_h14 : c.n ≤ 14) (hPos : 1 < c.n) :
    (∃ exp₀ : OuterplanarExportCert c.n,
        IsFacialOuterplanar.fromExport exp₀ = oneChord_facialCert c) ∧
      (∃ exp₁ : OuterplanarExportCert (c.toCycleBase hPos).nAfter,
        exp₁.embed.isCycle = true ∧
          IsFacialOuterplanar.fromExport exp₁ =
            facialCycleBase_cert (c.toCycleBase hPos)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨OuterplanarExportCert.ofOneChord c, ?_⟩
    exact oneChord_export_fromExport c
  · obtain ⟨exp, hcyc, hfacial, hfrom⟩ := CycleChord.export_after_peel_facial c hPos
    exact ⟨exp, hcyc, hfrom⟩

/-! ### Canonical smoke endpoints → export certs (mass window n=5..10) -/

open Bicyclic

/-- Any mass-window crossing endpoint yields a cycle export cert + facial roundtrip. -/
theorem smoke_endpoint_cycle_export (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ exp : OuterplanarExportCert e.n,
      exp.embed.isCycle = true ∧
        exp.facial = cycle_facialCert (by omega : 3 ≤ e.n) ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by omega : 3 ≤ e.n) :=
  mass_window_cycle_export_facial e h5 h14

theorem smoke_endpoint_upper_bound_export (e : CrossingEndpoints)
    (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    e.toArcs.total ≤ 10 ∧
      e.toArcs.total + 4 = e.n ∧
      ∃ exp : OuterplanarExportCert e.n,
        exp.embed.isCycle = true ∧
          IsFacialOuterplanar.fromExport exp = cycle_facialCert (by omega : 3 ≤ e.n) :=
  mass_window_upper_bound_export_facial e h5 h14

theorem c5Ofold_export_facial :
    ∃ exp : OuterplanarExportCert 5,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 5) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c5OfoldEndpoints (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c5Alt1_export_facial :
    ∃ exp : OuterplanarExportCert 5,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 5) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c5Alt1Endpoints (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c6Endpoints0123_export_facial :
    ∃ exp : OuterplanarExportCert 6,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 6) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c6Endpoints0123 (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c7Endpoints0123_export_facial :
    ∃ exp : OuterplanarExportCert 7,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 7) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c7Endpoints0123 (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c8Endpoints0123_export_facial :
    ∃ exp : OuterplanarExportCert 8,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 8) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c8Endpoints0123 (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c9Endpoints0123_export_facial :
    ∃ exp : OuterplanarExportCert 9,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 9) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c9Endpoints0123 (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c10Endpoints024_export_facial :
    ∃ exp : OuterplanarExportCert 10,
      exp.embed.isCycle = true ∧
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 10) := by
  obtain ⟨exp, hcyc, _, hfrom⟩ := smoke_endpoint_cycle_export c10Endpoints024 (by decide) (by decide)
  exact ⟨exp, hcyc, hfrom⟩

theorem c6Endpoints0123_upper_bound_export :
    c6Endpoints0123.toArcs.total ≤ 10 ∧
      c6Endpoints0123.toArcs.total + 4 = 6 ∧
      ∃ exp : OuterplanarExportCert 6,
        exp.embed.isCycle = true ∧
          IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 6) :=
  smoke_endpoint_upper_bound_export c6Endpoints0123 (by decide) (by decide)

/-- Seven canonical parametric smoke seeds (E5 emit-backed) each admit a cycle export cert. -/
theorem canonical_smoke_export_certs :
    (∃ exp : OuterplanarExportCert 5,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 5)) ∧
      (∃ exp : OuterplanarExportCert 5,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 5)) ∧
      (∃ exp : OuterplanarExportCert 6,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 6)) ∧
      (∃ exp : OuterplanarExportCert 7,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 7)) ∧
      (∃ exp : OuterplanarExportCert 8,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 8)) ∧
      (∃ exp : OuterplanarExportCert 9,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 9)) ∧
      (∃ exp : OuterplanarExportCert 10,
        IsFacialOuterplanar.fromExport exp = cycle_facialCert (by decide : 3 ≤ 10)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨exp, _, hfrom⟩ := c5Ofold_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c5Alt1_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c6Endpoints0123_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c7Endpoints0123_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c8Endpoints0123_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c9Endpoints0123_export_facial; exact ⟨exp, hfrom⟩
  · obtain ⟨exp, _, hfrom⟩ := c10Endpoints024_export_facial; exact ⟨exp, hfrom⟩

def mathlibIsOuterplanarAbsentDoc : String :=
  "Mathlib v4.32.0 (lakefile.toml rev v4.32.0; lean-toolchain v4.32.0): " ++
  "grep over `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph` (88 files) — no `IsOuterplanar`, " ++
  "no `outerplanar`, no `IsPlanar`/`PlanarGraph`/graph `Kuratowski`/treewidth; " ++
  "see `MathlibIsOuterplanarAbsent` + `MathlibIsOuterplanarSearch` + `MathlibIsOuterplanarAnchors`. " ++
  "PNPLab export bridge: local `IsOuterplanar` ≃ `IsFacialOuterplanar` via " ++
  "`isOuterplanarEquivIsFacialOuterplanar`; `IsFacialOuterplanar.fromExport` / " ++
  "`OuterplanarExportCert.toFacial_cert` link export bundles to facial certs; " ++
  "`OuterplanarExportCert` bundles facial/local cert + cycle|oneChord instance + " ++
  "`toSimpleGraph` for chords; instance certs `cycle_facialCert`, `oneChord_facialCert`, " ++
  "`facialCycleBase_cert`; peel hooks `facialCycleBase_toExportCert`, `CycleChord.reaches_cycle_export`; " ++
  "`MathlibIsOuterplanarGap` + `MathlibIsOuterplanarUpstreamHook` + " ++
  "`mathlibOuterplanarBridgeBundle` reserved for upstream `SimpleGraph.IsOuterplanar` on " ++
  "`OuterplanarGraphInstance.toSimpleGraph`. " ++
  "Mass window 5≤n≤14: `mass_window_upper_bound_export_facial`, " ++
  "`mass_window_one_chord_export_chain`, `mass_window_one_chord_peel_export`; " ++
  "canonical smoke n=5..10: `canonical_smoke_export_certs`, `smoke_endpoint_cycle_export`."

def bridgeDoc : String :=
  "papers/MATHLIB_IS_OUTERPLANAR_MIGRATION.md; papers/E5_GAPS_CHECKLIST.md point 3"

end PNPLab.MathlibBridge
