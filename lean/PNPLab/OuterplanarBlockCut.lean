/-
  Block-cut infrastructure for general outerplanar 2-cores (Category C / G6).

  Mathlib v4.32.0 has no `IsOuterplanar` or outerplanar block decomposition.
  This module therefore defines the *certificate interface* needed by the
  width proof, without pretending to derive it from a `SimpleGraph`.

  A block-cut certificate contains:
    * finitely many blocks, rooted at block 0;
    * a strictly earlier parent for every non-root block (hence no cycles);
    * valid child/parent articulation indices;
    * a local legal ear for every non-cycle 2-connected block;
    * size coherence so exposed ears fit the global fold measure.

  The public outcome is the data-valued `OuterplanarCoreExposure`
  (cycle base or sized legal ear).  `expose` is computational: no
  `Classical.choose`.  The maximal block index is a leaf.  If it is a cycle,
  its articulation exposes the cycle-minus-articulation path as an ear.  If
  it is non-cycle, its local certificate supplies an ear.
-/

import PNPLab.OuterplanarCoreResidual

namespace PNPLab.Outerplanar

/-- Legal ear whose internals fit strictly under a core size bound. -/
abbrev SizedLegalOuterplanarEar (n : Nat) :=
  { p : OuterplanarEarPath // p.isLegal ∧ p.internals < n }

/--
  Dichotomy after peeling: either a cycle base or a sized legal ear.
  Data-valued so clients can pattern-match without classical choice.
-/
inductive OuterplanarCoreExposure (n : Nat) where
  | cycleBase (size_ge_three : 3 ≤ n)
  | ear (witness : SizedLegalOuterplanarEar n)

/-- Bridge exposure → existing residual interface. -/
def OuterplanarCoreExposure.toCoreResidual {n : Nat} :
    OuterplanarCoreExposure n → OuterplanarCoreResidual
  | .cycleBase _ => coreCycle n
  | .ear w => coreWithEar n w.1 w.2.1

theorem OuterplanarCoreExposure.toCoreResidual_cycle
    {n : Nat} (h : 3 ≤ n) :
    (OuterplanarCoreExposure.cycleBase (n := n) h).toCoreResidual.isCycle = true :=
  rfl

theorem OuterplanarCoreExposure.toCoreResidual_ear
    {n : Nat} (w : SizedLegalOuterplanarEar n) :
    (OuterplanarCoreExposure.ear w).toCoreResidual.ear = some w.1 := by
  simp [OuterplanarCoreExposure.toCoreResidual, coreWithEar]

/-- The path exposed by a cycle block attached at one articulation. -/
def pendantCycleEar (n : Nat) : OuterplanarEarPath where
  internals := n - 1
  leftDegGe3 := true
  rightDegGe3 := false
  endsAdjacent := false

theorem pendantCycleEar_isLegal {n : Nat} (h : 3 ≤ n) :
    (pendantCycleEar n).isLegal := by
  constructor
  · simp [pendantCycleEar]
    omega
  · exact Or.inl rfl

theorem pendantCycleEar_internals_lt {n m : Nat} (h : 3 ≤ n) (hle : n ≤ m) :
    (pendantCycleEar n).internals < m := by
  simp [pendantCycleEar]
  omega

/--
  A 2-connected outerplanar block certificate.

  Cycle blocks need only the usual `n ≥ 3` bound.  Non-cycle blocks carry the
  local Whitney ear that a future graph-level outerplanarity theorem must
  construct, with internals strictly smaller than the block.
-/
structure OuterplanarBlock where
  nVertices : Nat
  isCycle : Bool
  cycleMin : isCycle = true → 3 ≤ nVertices
  localEar : OuterplanarEarPath
  nonCycleEarLegal : isCycle = false → localEar.isLegal
  nonCycleEarFits : isCycle = false → localEar.internals < nVertices

/-- Ear exposed when this block is a non-root leaf of the block-cut tree. -/
def OuterplanarBlock.leafEar (b : OuterplanarBlock) : OuterplanarEarPath :=
  if b.isCycle then pendantCycleEar b.nVertices else b.localEar

theorem OuterplanarBlock.leafEar_isLegal (b : OuterplanarBlock) :
    b.leafEar.isLegal := by
  cases h : b.isCycle with
  | false =>
      simp [OuterplanarBlock.leafEar, h]
      exact b.nonCycleEarLegal h
  | true =>
      simp [OuterplanarBlock.leafEar, h]
      exact pendantCycleEar_isLegal (b.cycleMin h)

theorem OuterplanarBlock.leafEar_internals_lt
    (b : OuterplanarBlock) {m : Nat} (hle : b.nVertices ≤ m) :
    b.leafEar.internals < m := by
  cases h : b.isCycle with
  | false =>
      simp [OuterplanarBlock.leafEar, h]
      have := b.nonCycleEarFits h
      omega
  | true =>
      simp [OuterplanarBlock.leafEar, h]
      exact pendantCycleEar_internals_lt (b.cycleMin h) hle

/-- Root index of a nonempty block-cut certificate. -/
def blockRootIndex {k : Nat} (hk : 0 < k) : Fin k :=
  ⟨0, hk⟩

/-- Maximal index of a nonempty block-cut certificate. -/
def blockLastIndex {k : Nat} (hk : 0 < k) : Fin k :=
  ⟨k - 1, by omega⟩

theorem blockLastIndex_ne_root {k : Nat} (hk : 1 < k) :
    (blockLastIndex (Nat.zero_lt_of_lt hk)).val ≠ 0 := by
  simp [blockLastIndex]
  omega

/--
  Rooted block-cut tree certificate for a connected outerplanar 2-core.

  `parent_lt` simultaneously validates each parent index and makes the parent
  relation well founded.  The two articulation fields record the local vertex
  on each side of an attachment.  Size fields keep exposed ears compatible
  with the global fold measure.
-/
structure OuterplanarBlockCut where
  nCoreVertices : Nat
  corePos : 0 < nCoreVertices
  nBlocks : Nat
  blocksNonempty : 0 < nBlocks
  block : Fin nBlocks → OuterplanarBlock
  /-- Identifying one articulation for each non-root attachment gives the core size. -/
  vertexCount :
    nCoreVertices + (nBlocks - 1) =
      (List.ofFn (fun i : Fin nBlocks => (block i).nVertices)).sum
  /-- Every block is no larger than the core. -/
  blockSize_le_core :
    ∀ i : Fin nBlocks, (block i).nVertices ≤ nCoreVertices
  /-- A single-block certificate is exactly the core. -/
  singleBlock_size :
    nBlocks = 1 →
      nCoreVertices = (block (blockRootIndex blocksNonempty)).nVertices
  parent : Fin nBlocks → Nat
  parent_root : parent (blockRootIndex blocksNonempty) = 0
  parent_lt :
    ∀ i : Fin nBlocks, i.val ≠ 0 → parent i < i.val
  childArticulation : Fin nBlocks → Nat
  childArticulation_lt :
    ∀ i : Fin nBlocks, i.val ≠ 0 →
      childArticulation i < (block i).nVertices
  parentArticulation : Fin nBlocks → Nat
  parentArticulation_lt :
    ∀ i : Fin nBlocks, ∀ h : i.val ≠ 0,
      parentArticulation i <
        (block ⟨parent i, Nat.lt_trans (parent_lt i h) i.isLt⟩).nVertices

def OuterplanarBlockCut.rootIndex (t : OuterplanarBlockCut) : Fin t.nBlocks :=
  blockRootIndex t.blocksNonempty

def OuterplanarBlockCut.lastIndex (t : OuterplanarBlockCut) : Fin t.nBlocks :=
  blockLastIndex t.blocksNonempty

/-- The only ear-free base is one cycle block. -/
def OuterplanarBlockCut.isCycleBase (t : OuterplanarBlockCut) : Prop :=
  t.nBlocks = 1 ∧ (t.block t.rootIndex).isCycle = true

instance (t : OuterplanarBlockCut) : Decidable t.isCycleBase := by
  unfold OuterplanarBlockCut.isCycleBase
  infer_instance

/-- No block can have the maximal block as parent, so it is a leaf. -/
theorem OuterplanarBlockCut.lastIndex_isLeaf
    (t : OuterplanarBlockCut)
    (child : Fin t.nBlocks)
    (hChild : child.val ≠ 0) :
    t.parent child ≠ t.lastIndex.val := by
  have hp := t.parent_lt child hChild
  have hc := child.isLt
  simp [OuterplanarBlockCut.lastIndex, blockLastIndex]
  omega

/-- A nontrivial block-cut tree has a non-root maximal (leaf) block. -/
theorem OuterplanarBlockCut.lastIndex_ne_root
    (t : OuterplanarBlockCut) (h : 1 < t.nBlocks) :
    t.lastIndex.val ≠ 0 := by
  exact blockLastIndex_ne_root h

/-- Sized legal ear extracted from a single non-cycle root block. -/
def OuterplanarBlockCut.rootSizedEar
    (t : OuterplanarBlockCut) (hOne : t.nBlocks = 1)
    (hNonCycle : (t.block t.rootIndex).isCycle = false) :
    SizedLegalOuterplanarEar t.nCoreVertices :=
  let p := (t.block t.rootIndex).localEar
  let hLegal := (t.block t.rootIndex).nonCycleEarLegal hNonCycle
  let hFitsBlock := (t.block t.rootIndex).nonCycleEarFits hNonCycle
  let hSize := t.singleBlock_size hOne
  ⟨p, hLegal, by
    -- `rootIndex` is definitionally `blockRootIndex`.
    change p.internals < t.nCoreVertices
    have hfit : p.internals < (t.block t.rootIndex).nVertices := hFitsBlock
    have hEq : t.nCoreVertices = (t.block t.rootIndex).nVertices := by
      simpa [OuterplanarBlockCut.rootIndex] using hSize
    omega⟩

/-- Sized legal ear extracted from the maximal (leaf) block. -/
def OuterplanarBlockCut.leafSizedEar
    (t : OuterplanarBlockCut) (_hMany : 1 < t.nBlocks) :
    SizedLegalOuterplanarEar t.nCoreVertices :=
  let b := t.block t.lastIndex
  ⟨b.leafEar, b.leafEar_isLegal,
    b.leafEar_internals_lt (t.blockSize_le_core t.lastIndex)⟩

/--
  Computational exposure of the block-cut certificate.
  Returns a cycle base or a sized legal ear; no classical choice.
-/
def OuterplanarBlockCut.expose (t : OuterplanarBlockCut) :
    OuterplanarCoreExposure t.nCoreVertices :=
  if hOne : t.nBlocks = 1 then
    if hCyc : (t.block t.rootIndex).isCycle = true then
      have hGe : 3 ≤ t.nCoreVertices := by
        have hMin := (t.block t.rootIndex).cycleMin hCyc
        have hEq : t.nCoreVertices = (t.block t.rootIndex).nVertices := by
          simpa [OuterplanarBlockCut.rootIndex] using t.singleBlock_size hOne
        omega
      .cycleBase hGe
    else
      .ear (t.rootSizedEar hOne (eq_false_of_ne_true hCyc))
  else
    have hPos := t.blocksNonempty
    have hMany : 1 < t.nBlocks := by omega
    .ear (t.leafSizedEar hMany)

theorem OuterplanarBlockCut.expose_cycle_of_cycleBase
    (t : OuterplanarBlockCut) (h : t.isCycleBase) :
    ∃ hge, t.expose = .cycleBase hge := by
  obtain ⟨hOne, hCyc⟩ := h
  cases hex : t.expose with
  | cycleBase hge =>
    exact ⟨hge, rfl⟩
  | ear w =>
    unfold OuterplanarBlockCut.expose at hex
    simp [hOne, hCyc] at hex

theorem OuterplanarBlockCut.expose_ear_of_not_cycleBase
    (t : OuterplanarBlockCut) (h : ¬ t.isCycleBase) :
    ∃ w : SizedLegalOuterplanarEar t.nCoreVertices, t.expose = .ear w := by
  by_cases hOne : t.nBlocks = 1
  · have hRootNonCycle : (t.block t.rootIndex).isCycle = false := by
      apply eq_false_of_ne_true
      intro hTrue
      exact h ⟨hOne, hTrue⟩
    refine ⟨t.rootSizedEar hOne hRootNonCycle, ?_⟩
    unfold OuterplanarBlockCut.expose
    simp [hOne, hRootNonCycle]
  · have hPos := t.blocksNonempty
    have hMany : 1 < t.nBlocks := by omega
    refine ⟨t.leafSizedEar hMany, ?_⟩
    unfold OuterplanarBlockCut.expose
    simp [hOne]

/-- Direct sized ear (computable) when the certificate is not a cycle base. -/
def OuterplanarBlockCut.legalEarOfNotCycleBase
    (t : OuterplanarBlockCut) (h : ¬ t.isCycleBase) :
    SizedLegalOuterplanarEar t.nCoreVertices :=
  if hOne : t.nBlocks = 1 then
    t.rootSizedEar hOne (by
      apply eq_false_of_ne_true
      intro hTrue
      exact h ⟨hOne, hTrue⟩)
  else
    have hPos := t.blocksNonempty
    have hMany : 1 < t.nBlocks := by omega
    t.leafSizedEar hMany

/-- Convert exposure to residual (computable, replaces Classical.choose). -/
def OuterplanarBlockCut.toCore (t : OuterplanarBlockCut) : OuterplanarCoreResidual :=
  t.expose.toCoreResidual

/-- Convert a certified non-cycle-base core to the residual interface. -/
def OuterplanarBlockCut.toCoreOfNotCycleBase
    (t : OuterplanarBlockCut) (h : ¬ t.isCycleBase) :
    OuterplanarCoreResidual :=
  coreWithEar t.nCoreVertices (t.legalEarOfNotCycleBase h).1
    (t.legalEarOfNotCycleBase h).2.1

theorem OuterplanarBlockCut.toCore_hasLegalEar
    (t : OuterplanarBlockCut) (h : ¬ t.isCycleBase) :
    ∃ p : OuterplanarEarPath,
      p.isLegal ∧ (t.toCoreOfNotCycleBase h).ear = some p := by
  refine ⟨(t.legalEarOfNotCycleBase h).1, (t.legalEarOfNotCycleBase h).2.1, ?_⟩
  simp [OuterplanarBlockCut.toCoreOfNotCycleBase, coreWithEar]

theorem OuterplanarBlockCut.toCore_dichotomy (t : OuterplanarBlockCut) :
    let c := t.toCore
    c.isCycle = true ∨
      ∃ p : OuterplanarEarPath, c.ear = some p ∧ p.isLegal := by
  by_cases h : t.isCycleBase
  · obtain ⟨hge, heq⟩ := t.expose_cycle_of_cycleBase h
    left
    simp [OuterplanarBlockCut.toCore, heq, OuterplanarCoreExposure.toCoreResidual,
      coreCycle]
  · obtain ⟨w, heq⟩ := t.expose_ear_of_not_cycleBase h
    right
    refine ⟨w.1, ?_, w.2.1⟩
    simp [OuterplanarBlockCut.toCore, heq, OuterplanarCoreExposure.toCoreResidual_ear]

/-- End-to-end bridge: a certified non-cycle-base core supplies an upper fold. -/
theorem OuterplanarBlockCut.upper_step
    (t : OuterplanarBlockCut) (h : ¬ t.isCycleBase) :
    ∃ tip : EarTipKind, ∃ p : OuterplanarEarPath,
      ∃ hp : p.isLegal,
        ∃ hear : (t.toCoreOfNotCycleBase h).ear = some p,
          ((t.toCoreOfNotCycleBase h).toSketchOfEar p hear hp).classify.tipKind =
            some tip := by
  obtain ⟨p, hp, hear⟩ := t.toCore_hasLegalEar h
  obtain ⟨tip, htip, _⟩ :=
    (t.toCoreOfNotCycleBase h).upper_step_of_legal_ear p hear hp t.corePos
  exact ⟨tip, p, hp, hear, htip⟩

/--
  Subcubic 2-core refinement.

  At an articulation, both incident 2-connected blocks contribute at least two
  edges. `attachmentSubcubic` records the Δ≤3 budget at that same vertex.
-/
structure SubcubicOuterplanarBlockCut extends OuterplanarBlockCut where
  childDegreeAt : Fin nBlocks → Nat
  parentDegreeAt : Fin nBlocks → Nat
  childDegree_ge_two :
    ∀ i : Fin nBlocks, i.val ≠ 0 → 2 ≤ childDegreeAt i
  parentDegree_ge_two :
    ∀ i : Fin nBlocks, i.val ≠ 0 → 2 ≤ parentDegreeAt i
  attachmentSubcubic :
    ∀ i : Fin nBlocks, i.val ≠ 0 →
      childDegreeAt i + parentDegreeAt i ≤ 3

/--
  A connected simple 2-core with Δ≤3 has no articulation between nontrivial
  blocks: two incident blocks would force degree at least four.
-/
theorem SubcubicOuterplanarBlockCut.nBlocks_eq_one
    (t : SubcubicOuterplanarBlockCut) : t.nBlocks = 1 := by
  have hPos := t.blocksNonempty
  have hLe : t.nBlocks ≤ 1 := by
    by_cases h : t.nBlocks ≤ 1
    · exact h
    · have hMany : 1 < t.nBlocks := by omega
      let i := t.lastIndex
      have hi : i.val ≠ 0 := t.lastIndex_ne_root hMany
      have hc := t.childDegree_ge_two i hi
      have hp := t.parentDegree_ge_two i hi
      have hd := t.attachmentSubcubic i hi
      omega
  omega

/-- In the subcubic setting the general block-cut certificate reduces to its root block. -/
theorem SubcubicOuterplanarBlockCut.rootBlock_nonCycle_of_not_cycleBase
    (t : SubcubicOuterplanarBlockCut) (h : ¬ t.toOuterplanarBlockCut.isCycleBase) :
    (t.block t.rootIndex).isCycle = false := by
  apply eq_false_of_ne_true
  intro hCycle
  exact h ⟨t.nBlocks_eq_one, hCycle⟩

/-- Subcubic non-cycle cores obtain the legal ear directly from the unique block. -/
theorem SubcubicOuterplanarBlockCut.rootLegalEar
    (t : SubcubicOuterplanarBlockCut) (h : ¬ t.toOuterplanarBlockCut.isCycleBase) :
    (t.block t.rootIndex).localEar.isLegal :=
  (t.block t.rootIndex).nonCycleEarLegal
    (t.rootBlock_nonCycle_of_not_cycleBase h)

/-- Concrete cycle block constructor (its local ear is unused at the root). -/
def cycleBlock (n : Nat) (h : 3 ≤ n) : OuterplanarBlock where
  nVertices := n
  isCycle := true
  cycleMin := fun _ => h
  localEar := pendantCycleEar n
  nonCycleEarLegal := by simp
  nonCycleEarFits := by simp

/-- Concrete non-cycle block constructor from a legal local ear that fits. -/
def earBlock (n : Nat) (p : OuterplanarEarPath) (hp : p.isLegal)
    (hfit : p.internals < n) :
    OuterplanarBlock where
  nVertices := n
  isCycle := false
  cycleMin := by simp
  localEar := p
  nonCycleEarLegal := fun _ => hp
  nonCycleEarFits := fun _ => hfit

/-- Two cycle blocks sharing an articulation (six vertices in total). -/
def twoCycleBlockCore : OuterplanarBlockCut where
  nCoreVertices := 6
  corePos := by decide
  nBlocks := 2
  blocksNonempty := by decide
  block := fun i =>
    if i.val = 0 then cycleBlock 4 (by decide) else cycleBlock 3 (by decide)
  vertexCount := by native_decide
  blockSize_le_core := by
    intro i
    match i with
    | ⟨0, _⟩ => simp [cycleBlock]
    | ⟨1, _⟩ => simp [cycleBlock]
    | ⟨n + 2, h⟩ => omega
  singleBlock_size := by
    intro h
    omega
  parent := fun _ => 0
  parent_root := rfl
  parent_lt := by
    intro i hi
    have := i.isLt
    omega
  childArticulation := fun _ => 0
  childArticulation_lt := by
    intro i hi
    simp [hi, cycleBlock]
  parentArticulation := fun _ => 0
  parentArticulation_lt := by
    intro i hi
    simp [cycleBlock]

theorem twoCycleBlockCore_not_cycleBase :
    ¬ twoCycleBlockCore.isCycleBase := by
  intro h
  have hn := h.1
  simp [twoCycleBlockCore] at hn

theorem twoCycleBlockCore_expose_ear :
    ∃ w : SizedLegalOuterplanarEar 6,
      twoCycleBlockCore.expose = .ear w :=
  twoCycleBlockCore.expose_ear_of_not_cycleBase
    twoCycleBlockCore_not_cycleBase

theorem twoCycleBlockCore_hasLegalEar :
    ∃ p : OuterplanarEarPath, p.isLegal := by
  obtain ⟨w, _⟩ := twoCycleBlockCore_expose_ear
  exact ⟨w.1, w.2.1⟩

theorem twoCycleBlockCore_upper_step :
    ∃ tip : EarTipKind, ∃ p : OuterplanarEarPath,
      ∃ hp : p.isLegal,
        ∃ hear :
          (twoCycleBlockCore.toCoreOfNotCycleBase
            twoCycleBlockCore_not_cycleBase).ear = some p,
          ((twoCycleBlockCore.toCoreOfNotCycleBase
            twoCycleBlockCore_not_cycleBase).toSketchOfEar p hear hp).classify.tipKind =
            some tip :=
  twoCycleBlockCore.upper_step twoCycleBlockCore_not_cycleBase

/-- Triangle ear path certified legal. -/
theorem earPathTriangle_isLegal : earPathTriangle.isLegal :=
  ⟨by decide, Or.inl rfl⟩

/-- Single C₄ triangle-ear block as a full certificate. -/
def c4TriangleBlockCore : OuterplanarBlockCut where
  nCoreVertices := 4
  corePos := by decide
  nBlocks := 1
  blocksNonempty := by decide
  block := fun _ =>
    earBlock 4 earPathTriangle earPathTriangle_isLegal
      (show earPathTriangle.internals < 4 by native_decide)
  vertexCount := by native_decide
  blockSize_le_core := by
    intro i
    decide
  singleBlock_size := by
    intro _
    rfl
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

theorem c4TriangleBlockCore_not_cycleBase :
    ¬ c4TriangleBlockCore.isCycleBase := by
  intro h
  have hcyc : (c4TriangleBlockCore.block c4TriangleBlockCore.rootIndex).isCycle = true :=
    h.2
  -- Definitionally an `earBlock`, so `isCycle = false`.
  have : (c4TriangleBlockCore.block c4TriangleBlockCore.rootIndex).isCycle = false :=
    rfl
  simp [this] at hcyc

theorem c4TriangleBlockCore_expose_ear :
    ∃ w : SizedLegalOuterplanarEar 4,
      c4TriangleBlockCore.expose = .ear w :=
  c4TriangleBlockCore.expose_ear_of_not_cycleBase c4TriangleBlockCore_not_cycleBase

def blockCutDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
