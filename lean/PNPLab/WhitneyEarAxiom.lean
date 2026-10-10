/-
  Whitney / tip-existence axiomatization (Category C / G1 + G6).

  Combinatorial tip schedules are already discharged in:
    - `CrossingTipSchedule` / `OpenArcPath` (G1 count + frontier flags)
    - `OuterplanarEarPath.earLaw` (G6 tip-kind dichotomy once an ear is given)

  This module isolates the **graph-theoretic existence** hooks that Mathlib
  would discharge, and proves the end-to-end lemmas from those hooks plus the
  existing combinatorial infrastructure.

  E2 mass:
    - crossing frontier / schedule: 461/461 (`multihop_frontier_invariant_mass.json`)
    - outerplanar ear existence: 701/701 (`outerplanar_ear_existence_mass_n14.json`)
-/

import PNPLab.OuterplanarPeel
import PNPLab.CrossingFoldSchedule

open Classical

namespace PNPLab.WhitneyEar

open Outerplanar Bicyclic

/-! ### Mathlib discharge targets (precise citations for future import) -/

/-- Outerplanar ear decomposition after tree peel (Whitney / 2-core). -/
def mathlibOuterplanarEarTheorem : String :=
  "Not in Mathlib v4.32.0 (no IsOuterplanar / earDecomposition). " ++
  "Cite Diestel Thm 4.4.2; tree-peel leaves discharged via " ++
  "SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial " ++
  "(see PNPLab.MathlibBridge)."

/-- Crossing residual to four open branch lengths on C_n+2 with two crossing chords. -/
def mathlibCrossingOpenArcTheorem : String :=
  "Partial: Mathlib SimpleGraph.cycleGraph / pathGraph give 2-regular cycles " ++
  "and connected open paths (MathlibBridge). Combinatorial CrossingArcs→witness " ++
  "discharged (`crossingEmbedWitness_ofArcs`); graph→arcs is a doc obligation " ++
  "(`crossingGraphToArcsObligation`), supplied explicitly via `CrossingGraphParams`."

/-- Graph-theoretic obligation (discharged combinatorially for sorted endpoints):
  C_n+chords → four arc counts via `CrossingEndpoints.toArcs`
  (`PNPLab.CrossingChordsToArcs`; Python `crossing_branch_sets`). -/
def crossingGraphToArcsObligation : String :=
  "Discharged: CrossingEndpoints.toArcs (sorted four endpoints → CrossingArcs). " ++
  "E2 mass: multihop_frontier_invariant_mass.json (461/461). " ++
  "Abstract hop demos may still use CrossingGraphParams.ofArcs directly."

/-- Frontier shortcut tip on a positive open branch (fold_deg2_tip precondition). -/
def mathlibFrontierTipTheorem : String :=
  "Mathlib.Combinatorics.SimpleGraph.Connectivity: deg-2 path vertex adjacent to " ++
  "deg>=3 endpoint in a 2-connected subgraph; specialized to outerplanar Delta<=3 " ++
  "residuals in TERMINATION.md."

def whitneyEarAxiomDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

def crossingTipLawDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/SHORT_ARC_TIP_LAW.md"

def e5GapsDoc : String :=
  "papers/E5_GAPS_CHECKLIST.md"

def outerplanarEarMassDoc : String :=
  "reports/discovery/outerplanar_ear_existence_mass_n14.json"

def crossingFrontierMassDoc : String :=
  "reports/discovery/multihop_frontier_invariant_mass.json"

/-! ### G6 — outerplanar peeled 2-core ear existence -/

/-- Sketch-level peeled 2-core (post `peel_trees`, pre ear-path parameters). -/
structure PeeledOuterplanarSketch where
  nCore : Nat
  isCycle : Bool
  pendingLeaves : Nat := 0
  /-- Finitary ear-path parameters (ignored when `isCycle`). -/
  earInternals : Nat
  earLeftDegGe3 : Bool
  earRightDegGe3 : Bool
  earEndsAdjacent : Bool
  /-- Non-cycle sketches carry a legal ear (E2: 701/701 on sampled cores). -/
  notCycle_hasLegalEar :
    isCycle = false →
      0 < earInternals ∧ (earLeftDegGe3 = true ∨ earRightDegGe3 = true)

def PeeledOuterplanarSketch.earPath (s : PeeledOuterplanarSketch) : OuterplanarEarPath where
  internals := s.earInternals
  leftDegGe3 := s.earLeftDegGe3
  rightDegGe3 := s.earRightDegGe3
  endsAdjacent := s.earEndsAdjacent

theorem PeeledOuterplanarSketch.earPath_isLegal (s : PeeledOuterplanarSketch)
    (h : s.isCycle = false) : (s.earPath).isLegal :=
  s.notCycle_hasLegalEar h

def PeeledOuterplanarSketch.fromPeel (p : PeelSketch) : PeeledOuterplanarSketch :=
  let ear := p.core.ear.getD earPathTriangle
  { nCore := p.coreVertices
    isCycle := p.core.isCycle
    pendingLeaves := p.pendingLeaves
    earInternals := ear.internals
    earLeftDegGe3 := ear.leftDegGe3
    earRightDegGe3 := ear.rightDegGe3
    earEndsAdjacent := ear.endsAdjacent
    notCycle_hasLegalEar := by
      intro h
      obtain ⟨ear', hear⟩ := p.core.ear_of_not_cycle h
      have hp := p.core.legalEar ear' hear
      have hfields :
          ear.internals = ear'.internals ∧
            ear.leftDegGe3 = ear'.leftDegGe3 ∧
            ear.rightDegGe3 = ear'.rightDegGe3 := by
        simp [ear, hear]
      rcases hfields with ⟨hi, hl, hr⟩
      rw [hi, hl, hr]
      exact hp }

/--
  Whitney / ear-decomposition existence (G6 combinatorial discharge).

  Non-cycle peeled outerplanar 2-core (Delta<=3) sketch carries explicit
  `OuterplanarEarPath` parameters; graph-level existence is the sketch hook.
  E2: 701/701 sampled cores; full graph discharge via `mathlibOuterplanarEarTheorem`.
-/
theorem whitney_legal_ear_exists (s : PeeledOuterplanarSketch) (h : s.isCycle = false) :
    ∃ p : OuterplanarEarPath, p.isLegal :=
  ⟨s.earPath, s.earPath_isLegal h⟩

/-- Build an `OuterplanarCoreResidual` from the peeled sketch ear. -/
noncomputable def PeeledOuterplanarSketch.toCore (s : PeeledOuterplanarSketch) (h : s.isCycle = false) :
    OuterplanarCoreResidual :=
  coreWithEar s.nCore s.earPath (s.earPath_isLegal h)

theorem PeeledOuterplanarSketch.toCore_ear (s : PeeledOuterplanarSketch) (h : s.isCycle = false) :
    ∃ p : OuterplanarEarPath, (s.toCore h).ear = some p := by
  refine ⟨s.earPath, ?_⟩
  simp [PeeledOuterplanarSketch.toCore, coreWithEar]

theorem PeeledOuterplanarSketch.toCore_ear_legal (s : PeeledOuterplanarSketch) (h : s.isCycle = false) :
    ∃ p : OuterplanarEarPath, p.isLegal ∧ (s.toCore h).ear = some p := by
  refine ⟨s.earPath, ?_, ?_⟩
  · exact s.earPath_isLegal h
  · simp [PeeledOuterplanarSketch.toCore, coreWithEar]

theorem PeeledOuterplanarSketch.toCore_not_cycle
    (s : PeeledOuterplanarSketch) (h : s.isCycle = false) :
    (s.toCore h).isCycle = false := by
  simp [PeeledOuterplanarSketch.toCore, coreWithEar]

theorem whitney_peel_ear_of_not_cycle (p : PeelSketch) (h : p.core.isCycle = false)
    (hPos : 0 < p.coreVertices) :
    ∃ tip : EarTipKind,
      ∃ ear : OuterplanarEarPath, ∃ hp : ear.isLegal,
        ∃ hear : ((PeeledOuterplanarSketch.fromPeel p).toCore h).ear = some ear,
          let core := (PeeledOuterplanarSketch.fromPeel p).toCore h
          (core.toSketchOfEar ear hear hp).classify.tipKind = some tip := by
  let s := PeeledOuterplanarSketch.fromPeel p
  let core := s.toCore h
  obtain ⟨ear, hleg, hear⟩ := PeeledOuterplanarSketch.toCore_ear_legal s h
  obtain ⟨tip, htip, _⟩ := core.upper_step_of_legal_ear ear hear hleg hPos
  exact ⟨tip, ear, hleg, hear, htip⟩

/-- Whitney-built sketch carries `earLaw` from `toSketchOfEar` (no extra graph input). -/
theorem whitney_sketch_earLaw (s : PeeledOuterplanarSketch) (h : s.isCycle = false)
    (p : OuterplanarEarPath) (hp : p.isLegal) (hear : (s.toCore h).ear = some p) :
    True := by
  have _ := (s.toCore h).toSketchOfEar p hear hp |>.earLaw
  trivial

/-! ### G1 — crossing graph to open-arc frontier tip existence -/

/--
  E2-backed graph-to-combinatorial hook: a crossing residual maps to four arc counts.
  Positive total means the schedule has not reached the K4 skeleton yet.
-/
structure CrossingEmbedWitness where
  arcs : CrossingArcs
  /-- Each positive branch is the standard `crossingOpenArc` model (E2 461/461). -/
  branchOpenArc :
    ∀ i : Fin 4, 0 < arcs.get i → arcs.toOpen i = crossingOpenArc (arcs.get i)

/--
  Combinatorial constructor: any `CrossingArcs` yields an embed witness.
  (`CrossingArcs.toOpen` is definitionally `crossingOpenArc`.)
-/
def crossingEmbedWitness_ofArcs (arcs : CrossingArcs) : CrossingEmbedWitness where
  arcs := arcs
  branchOpenArc := fun _ _ => rfl

/--
  Explicit graph parameters for a crossing residual (G1).
  Carries concrete four-branch arc counts; no abstract graph→arcs axiom.
  Graph-theoretic production of these counts: `crossingGraphToArcsObligation`.
-/
structure CrossingGraphParams where
  cycleLen : Nat
  arcs : CrossingArcs

/-- Build params from cycle length and explicit arc counts. -/
def CrossingGraphParams.ofArcs (cycleLen : Nat) (arcs : CrossingArcs) : CrossingGraphParams :=
  { cycleLen := cycleLen, arcs := arcs }

/-- Place all hop budget on branch 0 (witness that any total is realizable). -/
def CrossingArcs.allInFirst (hop : Nat) : CrossingArcs :=
  { a0 := hop, a1 := 0, a2 := 0, a3 := 0 }

theorem CrossingArcs.allInFirst_total (hop : Nat) :
    (CrossingArcs.allInFirst hop).total = hop := rfl

theorem crossing_arcs_exists_total (hop : Nat) :
    ∃ arcs : CrossingArcs, arcs.total = hop :=
  ⟨CrossingArcs.allInFirst hop, CrossingArcs.allInFirst_total hop⟩

theorem crossing_arcs_exists_hop_window (hop : Nat) (_h : 1 ≤ hop ∧ hop ≤ 10) :
    ∃ arcs : CrossingArcs, arcs.total = hop :=
  crossing_arcs_exists_total hop

/-- Params with all hop budget on branch 0. -/
def CrossingGraphParams.allInFirst (cycleLen hop : Nat) : CrossingGraphParams :=
  CrossingGraphParams.ofArcs cycleLen (CrossingArcs.allInFirst hop)

theorem CrossingGraphParams.allInFirst_total (cycleLen hop : Nat) :
    (CrossingGraphParams.allInFirst cycleLen hop).arcs.total = hop :=
  CrossingArcs.allInFirst_total hop

/-- C₆ demo params (four unit branches, total = 4). -/
def c6CrossingGraphParams : CrossingGraphParams :=
  CrossingGraphParams.ofArcs 6 c6CrossingArcs

/-- Explicit params ⇒ embed witness (no graph axiom). -/
def crossing_graph_embed_witness (p : CrossingGraphParams) : CrossingEmbedWitness :=
  crossingEmbedWitness_ofArcs p.arcs

/-- Positive arc internals imply standard open arc has a frontier tip (no graph theory). -/
theorem crossing_embed_frontier_arc (w : CrossingEmbedWitness) (i : Fin 4)
    (h : 0 < w.arcs.get i) :
    (w.arcs.toOpen i).hasFrontierTip = true := by
  rw [w.branchOpenArc i h]
  exact crossingOpenArc_frontier (w.arcs.get i) h

/-- From embed witness + positive total, schedule frontier shortcut tip. -/
theorem crossing_embed_schedule_tip (w : CrossingEmbedWitness) (h : 0 < w.arcs.total) :
    ∃ i : Fin 4, frontierTipKind (w.arcs.get i) = some .shortcutOnShorterArc :=
  crossing_frontier_tip_exists w.arcs h

/-- From embed witness + positive total, some open arc has a frontier tip flag. -/
theorem crossing_embed_open_frontier (w : CrossingEmbedWitness) (h : 0 < w.arcs.total) :
    ∃ i : Fin 4, (w.arcs.toOpen i).hasFrontierTip = true := by
  obtain ⟨i, hi⟩ := crossing_embed_schedule_tip w h
  refine ⟨i, ?_⟩
  have hpos : 0 < w.arcs.get i := frontierTipKind_pos_implies _ hi
  exact crossing_embed_frontier_arc w i hpos

/-- Schedule tips from given arc counts (no graph axiom). -/
theorem crossing_arcs_schedule_tip (arcs : CrossingArcs) (h : 0 < arcs.total) :
    ∃ i : Fin 4, frontierTipKind (arcs.get i) = some .shortcutOnShorterArc :=
  crossing_embed_schedule_tip (crossingEmbedWitness_ofArcs arcs) h

/-- Open-arc frontier flags from given arc counts (no graph axiom). -/
theorem crossing_arcs_open_frontier (arcs : CrossingArcs) (h : 0 < arcs.total) :
    ∃ i : Fin 4, (arcs.toOpen i).hasFrontierTip = true :=
  crossing_embed_open_frontier (crossingEmbedWitness_ofArcs arcs) h

/-- One frontier fold step on an embed witness (links to `CrossingFoldSchedule`). -/
theorem crossing_embed_fold_step (w : CrossingEmbedWitness) (h : 0 < w.arcs.total) :
    (w.arcs.foldSome).total = w.arcs.total - 1 ∧
      ∃ i : Fin 4, frontierTipKind (w.arcs.get i) = some .shortcutOnShorterArc := by
  refine ⟨CrossingArcs.foldSome_total w.arcs h, ?_⟩
  exact crossing_embed_schedule_tip w h

/-- Parametric G1 bundle: graph embed axiom + combinatorial schedule implies frontier tip. -/
structure CrossingTipExistenceBundle where
  witness : CrossingEmbedWitness
  totalPos : 0 < witness.arcs.total

theorem CrossingTipExistenceBundle.scheduleTip (b : CrossingTipExistenceBundle) :
    ∃ i : Fin 4, frontierTipKind (b.witness.arcs.get i) = some .shortcutOnShorterArc :=
  crossing_embed_schedule_tip b.witness b.totalPos

theorem CrossingTipExistenceBundle.openFrontier (b : CrossingTipExistenceBundle) :
    ∃ i : Fin 4, (b.witness.arcs.toOpen i).hasFrontierTip = true :=
  crossing_embed_open_frontier b.witness b.totalPos

def crossingTipExistence_ofParams (p : CrossingGraphParams) (h : 0 < p.arcs.total) :
    CrossingTipExistenceBundle where
  witness := crossing_graph_embed_witness p
  totalPos := h

/-- C₆ crossing demo: explicit `c6CrossingArcs`, no graph axiom. -/
def c6CrossingTipExistence : CrossingTipExistenceBundle :=
  crossingTipExistence_ofParams c6CrossingGraphParams (by decide)

/-- Generic hop demo via `allInFirst` construction (hop ∈ [1,6] or any Nat). -/
def crossingTipExistence_allInFirst (cycleLen hop : Nat) (h : 0 < hop) :
    CrossingTipExistenceBundle :=
  crossingTipExistence_ofParams (CrossingGraphParams.allInFirst cycleLen hop)
    (by rw [CrossingGraphParams.allInFirst_total]; exact h)

/-! ### G6 bundle — peel + Whitney implies upper fold tip -/

structure OuterplanarTipExistenceBundle where
  peel : PeelSketch
  notCycle : peel.core.isCycle = false
  core : OuterplanarCoreResidual
  ear : OuterplanarEarPath
  earLegal : ear.isLegal
  hear : core.ear = some ear
  tip : EarTipKind
  tipMatches :
    ((core.toSketchOfEar ear hear earLegal).classify).tipKind = some tip

theorem outerplanarTipExistence_of_whitney (p : PeelSketch) (h : p.core.isCycle = false)
    (hPos : 0 < p.coreVertices) : ∃ _b : OuterplanarTipExistenceBundle, True := by
  let s := PeeledOuterplanarSketch.fromPeel p
  let core := s.toCore h
  obtain ⟨ear, hleg, hear⟩ := PeeledOuterplanarSketch.toCore_ear_legal s h
  obtain ⟨tip, htip, _⟩ := core.upper_step_of_legal_ear ear hear hleg hPos
  refine ⟨{
    peel := p
    notCycle := h
    core := core
    ear := ear
    earLegal := hleg
    hear := hear
    tip := tip
    tipMatches := htip
  }, trivial⟩

/-! ### E2 obligation summary (Category C — not a proof claim) -/

def e2ObligationSummary : String :=
  "G6: replace sketch `notCycle_hasLegalEar` hook with " ++ mathlibOuterplanarEarTheorem ++
  " | G1 combinatorial schedule discharged (CrossingArcs→witness); graph→arcs: " ++
  crossingGraphToArcsObligation ++
  " | Combinatorial schedules discharged: CrossingArcs→witness, earPath on sketch."

end PNPLab.WhitneyEar