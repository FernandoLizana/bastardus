/-
  Bicyclic (θ-graph) fold scaffold (Category C).

  Parallel to Outerplanar.lean: residual classification for C_n + one chord
  with Δ≤3, matching `prove_bicyclic_pathfold_lemma` / PROOF_PATHFOLD.md.
  Chord-arc fold existence is axiomatized; not a full graph embedding theory.
-/

namespace PNPLab.Bicyclic

inductive ResidualStatus where
  | cycle : ResidualStatus
  | needsChordFold : ResidualStatus

structure FoldMeasure where
  nVertices : Nat

def FoldMeasure.succFold (m : FoldMeasure) : FoldMeasure :=
  { nVertices := m.nVertices - 1 }

theorem fold_measure_lt {n : Nat} (h : n > 0) :
    n - 1 < n := Nat.sub_lt h (Nat.zero_lt_one)

/-- Tip kinds on a θ-graph residual (one chord + cycle). -/
inductive ChordTipKind where
  | triangleEar : ChordTipKind
  | shortcutOnShorterArc : ChordTipKind

structure ChordFoldClaim where
  status : ResidualStatus
  tipKind : Option ChordTipKind
  coherent :
    (status = .cycle ∧ tipKind = none) ∨
    (status = .needsChordFold ∧ tipKind.isSome)

/-- Combinatorial sketch for C_n + one chord (bicyclic 2-core). -/
structure ThetaSketch where
  nVertices : Nat
  isCycle : Bool
  /-- Shorter chord-arc has an internal deg-2 tip (or triangle after prior folds). -/
  hasFoldTip : Bool
  /-- Classical: connected bicyclic Δ≤3 non-cycle ⇒ fold tip on a chord arc. -/
  chordFoldLaw :
    isCycle = true ∨ hasFoldTip = true

def ThetaSketch.classify (g : ThetaSketch) : ChordFoldClaim :=
  if h : g.isCycle = true then
    { status := .cycle
      tipKind := none
      coherent := by
        left
        exact ⟨rfl, rfl⟩ }
  else
    { status := .needsChordFold
      tipKind := some .shortcutOnShorterArc
      coherent := by
        right
        exact ⟨rfl, by decide⟩ }

def foldMeasureOf (g : ThetaSketch) : FoldMeasure :=
  { nVertices := g.nVertices }

theorem classify_cycle
    (g : ThetaSketch) (h : g.isCycle = true) :
    (g.classify).status = .cycle := by
  simp [ThetaSketch.classify, h]

theorem classify_needsFold
    (g : ThetaSketch) (h : g.isCycle = false) :
    (g.classify).status = .needsChordFold := by
  simp [ThetaSketch.classify, h]

theorem classify_coherent (g : ThetaSketch) :
    ((g.classify).status = .cycle ∧ (g.classify).tipKind = none) ∨
      ((g.classify).status = .needsChordFold ∧ (g.classify).tipKind.isSome = true) :=
  g.classify.coherent

theorem fold_step_decreases
    (g : ThetaSketch) (h : g.isCycle = false) (hn : g.nVertices > 0) :
    (g.classify).status = .needsChordFold ∧
      (FoldMeasure.succFold (foldMeasureOf g)).nVertices < g.nVertices := by
  constructor
  · exact classify_needsFold g h
  · exact fold_measure_lt hn

def sketchThetaNeedsFold (n : Nat) : ThetaSketch where
  nVertices := n
  isCycle := false
  hasFoldTip := true
  chordFoldLaw := by simp

def sketchCycle (n : Nat) : ThetaSketch where
  nVertices := n
  isCycle := true
  hasFoldTip := false
  chordFoldLaw := by simp

/-- Concrete θ-graph: C_5 + chord (0,2) has 5 vertices before fold. -/
def residualC5Chord : ThetaSketch := sketchThetaNeedsFold 5

theorem residualC5_needs_fold :
    residualC5Chord.classify.status = .needsChordFold :=
  classify_needsFold residualC5Chord rfl

theorem residualC5_fold_measure :
    (FoldMeasure.succFold (foldMeasureOf residualC5Chord)).nVertices = 4 := by
  native_decide

def chordFoldLawCitation : String :=
  "A connected bicyclic graph is a cycle with one chord (θ-graph) after \
   peeling trees. With Δ≤3, each chord creates two arcs; fold deg-2 internals \
   on the shorter arc (path-fold / triangle ear) until a cycle remains — \
   see papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md. \
   Lean discharge for all θ-residues: PNPLab.ThetaChordFold \
   (ThetaResidue.chordFoldLaw)."

def proofPathfoldDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/PROOF_PATHFOLD.md"

def massCertDoc : String :=
  "reports/discovery/bicyclic_pathfold_mass.json"

/-- Induction skeleton docs. -/
def inductionDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/INDUCTION_WIDTH_EQ_DELTA.md"

/-- From chordFoldLaw: non-cycle θ-sketch needs a fold tip. -/
theorem tip_of_not_cycle
    (g : ThetaSketch) (h : g.isCycle = false) :
    (g.classify).status = .needsChordFold ∧
      (g.classify).tipKind.isSome = true := by
  constructor
  · exact classify_needsFold g h
  · have hc := g.classify.coherent
    cases hc with
    | inl hcycle =>
      have : (g.classify).status = .cycle := hcycle.1
      have : (g.classify).status = .needsChordFold := classify_needsFold g h
      simp_all
    | inr hfold =>
      exact hfold.2

/-- Finite descent: after `n` folds the measure bottoms out (`folds` count). -/
def foldCountdown : Nat → Nat
  | 0 => 0
  | n + 1 => foldCountdown n

theorem foldCountdown_zero (n : Nat) : foldCountdown n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [foldCountdown] using ih

/-- Bundle: tip exists + measure drops + countdown hits 0 (induction shape). -/
theorem induction_shape_bundle
    (g : ThetaSketch) (h : g.isCycle = false) (hn : g.nVertices > 0) :
    (g.classify).tipKind.isSome = true ∧
      (FoldMeasure.succFold (foldMeasureOf g)).nVertices < g.nVertices ∧
      foldCountdown g.nVertices = 0 := by
  refine ⟨(tip_of_not_cycle g h).2, ?_, foldCountdown_zero g.nVertices⟩
  exact (fold_step_decreases g h hn).2

end PNPLab.Bicyclic
