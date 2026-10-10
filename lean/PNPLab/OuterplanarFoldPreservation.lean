/-
  Graph-level fold preservation for outerplanar Δ≤3 residuals (Category C / G6).

  Mathlib has no `IsOuterplanar`, so outerplanarity itself remains a certificate
  flag.  What *is* discharged here on `SimpleGraph`:

    * removing any vertex cannot increase degrees ⇒ `maxDegree ≤ 3` is preserved;
    * a deg-2 fold tip packages the triangle / shortcut dichotomy used by earLaw;
    * after deleting the tip, the vertex count drops by one;
    * odd-charge residual flags are preserved as a finitary certificate field.

  Also: `CycleChord.toSimpleGraph` / `toBlockCut` bridges the cycle+chord family
  into the constructive block-cut exposure API.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import PNPLab.OuterplanarUpperSketch
import PNPLab.OuterplanarBlockCut
import PNPLab.CycleChordEar

namespace PNPLab.Outerplanar

open SimpleGraph

/-- Degree of a vertex in an induced subgraph is at most its degree in `G`. -/
theorem degree_induce_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V)
    [DecidablePred (· ∈ s)] (v : s) :
    (G.induce s).degree v ≤ G.degree (v : V) := by
  classical
  simp_rw [← card_neighborFinset_eq_degree]
  have hsub :
      ((G.induce s).neighborFinset v).map (Function.Embedding.subtype (· ∈ s)) ⊆
        G.neighborFinset (v : V) := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨w, hw', rfl⟩
    have hadj : (G.induce s).Adj v w := (mem_neighborFinset _ _ _).1 hw'
    -- Induce adjacency is ambient adjacency on subtypes.
    exact (mem_neighborFinset G (v : V) (w : V)).2 hadj
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_map] using hcard

/-- Deleting any vertex preserves a global degree bound. -/
theorem maxDegree_le_induce_compl_singleton {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {k : Nat}
    (hΔ : G.maxDegree ≤ k) :
    (G.induce ({v}ᶜ : Set V)).maxDegree ≤ k := by
  classical
  apply maxDegree_le_of_forall_degree_le
  intro u
  exact (degree_induce_le G ({v}ᶜ) u).trans
    ((degree_le_maxDegree G (u : V)).trans hΔ)

/-- Specialization used by the outerplanar fold loop. -/
theorem maxDegree_le_three_after_delete_tip {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hΔ : G.maxDegree ≤ 3) :
    (G.induce ({v}ᶜ : Set V)).maxDegree ≤ 3 :=
  maxDegree_le_induce_compl_singleton G v hΔ

/-- Tip kinds matching the earLaw dichotomy at graph level. -/
inductive GraphFoldTipKind where
  | triangle
  | shortcut
  deriving DecidableEq, Repr

/--
  A degree-2 fold tip on a concrete `SimpleGraph`.

  Triangle: the two neighbors are adjacent.
  Shortcut: at least one neighbor has degree ≥ 3.
-/
structure Deg2FoldTip {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] where
  tip : V
  left : V
  right : V
  deg2 : G.degree tip = 2
  adjL : G.Adj tip left
  adjR : G.Adj tip right
  neLR : left ≠ right
  kind : GraphFoldTipKind
  triangleAdj : kind = .triangle → G.Adj left right
  shortcutBranch :
    kind = .shortcut → 3 ≤ G.degree left ∨ 3 ≤ G.degree right

/-- Map a graph tip to the sketch-level ear tip kind. -/
def Deg2FoldTip.toEarTipKind {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (t : Deg2FoldTip G) : EarTipKind :=
  match t.kind with
  | .triangle => .triangleEar
  | .shortcut => .shortcutDeg2NextToDeg3

/-- After deleting the tip, the ambient vertex type shrinks by one element. -/
theorem Deg2FoldTip.card_after {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (t : Deg2FoldTip G) :
    Fintype.card ↥({t.tip}ᶜ : Set V) = Fintype.card V - 1 := by
  classical
  change Fintype.card { x : V // x ≠ t.tip } = Fintype.card V - 1
  exact Fintype.card_subtype_compl (fun x : V => x = t.tip)

/-- Δ≤3 is preserved by deleting this tip. -/
theorem Deg2FoldTip.maxDegree_le_three_after {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (t : Deg2FoldTip G)
    (hΔ : G.maxDegree ≤ 3) :
    (G.induce ({t.tip}ᶜ : Set V)).maxDegree ≤ 3 :=
  maxDegree_le_three_after_delete_tip G t.tip hΔ

/--
  Graph-level fold preservation certificate.

  `outerplanarAfter` is still a certificate flag (no Mathlib outerplanar API).
  `deltaLe3After` is discharged by `maxDegree_le_three_after`.
-/
structure GraphFoldPreservation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  tip : Deg2FoldTip G
  deltaBefore : G.maxDegree ≤ 3
  outerplanarBefore : Bool := true
  oddChargeBefore : Bool := true
  outerplanarAfter : Bool := true
  oddChargeAfter : Bool := true

def GraphFoldPreservation.afterGraph {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) : SimpleGraph ↥({p.tip.tip}ᶜ : Set V) :=
  G.induce ({p.tip.tip}ᶜ)

instance GraphFoldPreservation.afterGraph.decidableAdj
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) : DecidableRel p.afterGraph.Adj :=
  inferInstanceAs (DecidableRel (G.induce ({p.tip.tip}ᶜ : Set V)).Adj)

theorem GraphFoldPreservation.deltaLe3After {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) :
    (p.afterGraph).maxDegree ≤ 3 :=
  p.tip.maxDegree_le_three_after p.deltaBefore

theorem GraphFoldPreservation.card_drops {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) (_hPos : 0 < Fintype.card V) :
    Fintype.card ↥({p.tip.tip}ᶜ : Set V) < Fintype.card V := by
  have h := p.tip.card_after
  have : 0 < Fintype.card V := _hPos
  omega

/-- Bridge to the existing sketch-level preservation flags. -/
def GraphFoldPreservation.toSketchFlags {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) : FoldPreservationSketch where
  outerplanar := p.outerplanarAfter
  deltaLe3 := true
  oddCharge := p.oddChargeAfter

theorem GraphFoldPreservation.toSketchFlags_delta
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservation G) :
    (p.toSketchFlags).deltaLe3 = true :=
  rfl

/-! ### Cycle + chord → SimpleGraph + block-cut certificate -/

theorem CycleChord.a_lt_n (c : CycleChord) : c.a < c.n := by
  have := c.gap
  have := c.b_lt_n
  omega

/-- Cycle graph plus one chord edge `{a,b}`. -/
def CycleChord.toSimpleGraph (c : CycleChord) : SimpleGraph (Fin c.n) :=
  cycleGraph c.n ⊔ edge (⟨c.a, c.a_lt_n⟩ : Fin c.n) ⟨c.b, c.b_lt_n⟩

instance (c : CycleChord) : DecidableRel c.toSimpleGraph.Adj :=
  inferInstanceAs
    (DecidableRel (cycleGraph c.n ⊔
      edge (⟨c.a, c.a_lt_n⟩ : Fin c.n) ⟨c.b, c.b_lt_n⟩).Adj)

theorem CycleChord.shorter_lt_n (c : CycleChord) : c.shorterInternals < c.n := by
  have hf := c.fwd_pos
  have hb := c.bwd_pos
  have hblt := c.b_lt_n
  have hgap := c.gap
  simp [CycleChord.shorterInternals, CycleChord.fwdInternals, CycleChord.bwdInternals]
  omega

/-- Single-block certificate from a cycle+chord (subcubic 2-core case). -/
def CycleChord.toBlockCut (c : CycleChord) : OuterplanarBlockCut where
  nCoreVertices := c.n
  corePos := Nat.zero_lt_of_lt c.a_lt_n
  nBlocks := 1
  blocksNonempty := Nat.zero_lt_one
  block := fun _ =>
    earBlock c.n c.toEarPath c.toEarPath_isLegal (by
      simpa [CycleChord.toEarPath] using c.shorter_lt_n)
  vertexCount := by
    -- One block of size `c.n`; no articulations to subtract.
    change c.n + (1 - 1) = (List.ofFn (fun _ : Fin 1 => c.n)).sum
    simp [List.ofFn_succ, List.ofFn_zero]
  blockSize_le_core := by
    intro i
    simp [earBlock]
  singleBlock_size := by
    intro _
    simp [earBlock]
  parent := fun _ => 0
  parent_root := rfl
  parent_lt := by
    intro i hi
    omega
  childArticulation := fun _ => 0
  childArticulation_lt := by
    intro i hi
    omega
  parentArticulation := fun _ => 0
  parentArticulation_lt := by
    intro i hi
    omega

theorem CycleChord.toBlockCut_not_cycleBase (c : CycleChord) :
    ¬ c.toBlockCut.isCycleBase := by
  intro h
  have := h.2
  simp [CycleChord.toBlockCut, earBlock, OuterplanarBlockCut.rootIndex,
    blockRootIndex] at this

theorem CycleChord.expose_ear (c : CycleChord) :
    ∃ w : SizedLegalOuterplanarEar c.n, c.toBlockCut.expose = .ear w :=
  c.toBlockCut.expose_ear_of_not_cycleBase (c.toBlockCut_not_cycleBase)

/-- C₄ diagonal: concrete graph + block-cut exposure. -/
theorem c4Diagonal_graph_expose :
    ∃ w : SizedLegalOuterplanarEar 4, c4Diagonal.toBlockCut.expose = .ear w :=
  c4Diagonal.expose_ear

def foldPreservationDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
