/-
  Peeled outerplanar 2-core residual (Category C / G6).

  Packages Whitney ear existence as a single classical hook `earExists`:
    cycle ∨ some OuterplanarEarPath.

  When an ear is present with legal endpoints, `earLaw` on the induced
  `ResidualSketch` is discharged via `OuterplanarEarPath.earLaw` (not axiom).
  The Whitney existence statement itself remains classical (E2: 701/701).
-/

import PNPLab.OuterplanarEarPath
import PNPLab.OuterplanarUpperSketch

namespace PNPLab.Outerplanar

/-- Legal ear: positive internals and at least one deg≥3 attachment. -/
def OuterplanarEarPath.isLegal (p : OuterplanarEarPath) : Prop :=
  0 < p.internals ∧ (p.leftDegGe3 = true ∨ p.rightDegGe3 = true)

/-- Peeled 2-core: either a pure cycle or an ear path is supplied. -/
structure OuterplanarCoreResidual where
  nVertices : Nat
  isCycle : Bool
  ear : Option OuterplanarEarPath
  /-- Classical Whitney: peeled outerplanar 2-core non-cycle ⇒ ∃ ear. -/
  earExists : isCycle = true ∨ ear.isSome = true
  /-- When an ear is present, it is legal (positive internals + deg≥3 attachment). -/
  legalEar : ∀ p, ear = some p → p.isLegal

/-- Cycle core (base case). -/
def coreCycle (n : Nat) : OuterplanarCoreResidual where
  nVertices := n
  isCycle := true
  ear := none
  earExists := Or.inl rfl
  legalEar := fun _ h => by simp at h

/-- Non-cycle core with a concrete legal ear. -/
def coreWithEar (n : Nat) (p : OuterplanarEarPath) (hp : p.isLegal) :
    OuterplanarCoreResidual where
  nVertices := n
  isCycle := false
  ear := some p
  earExists := by
    right
    simp
  legalEar := fun q hear => by
    cases hear
    exact hp

/-- From a core with a legal ear, build a ResidualSketch with discharged earLaw. -/
def OuterplanarCoreResidual.toSketchOfEar
    (c : OuterplanarCoreResidual)
    (p : OuterplanarEarPath)
    (_hear : c.ear = some p)
    (hp : p.isLegal) : ResidualSketch :=
  p.toSketch c.nVertices hp.1 hp.2

theorem OuterplanarCoreResidual.toSketchOfEar_flags
    (c : OuterplanarCoreResidual)
    (p : OuterplanarEarPath)
    (hear : c.ear = some p)
    (hp : p.isLegal) :
    (c.toSketchOfEar p hear hp).isCycle = false ∧
      ((c.toSketchOfEar p hear hp).hasTriangleEar = true ∨
        (c.toSketchOfEar p hear hp).hasShortcutTip = true) := by
  refine ⟨rfl, ?_⟩
  exact p.earLaw hp.1 hp.2

/-- Non-cycle core ⇒ some ear is present (from `earExists`). -/
theorem OuterplanarCoreResidual.ear_of_not_cycle
    (c : OuterplanarCoreResidual) (h : c.isCycle = false) :
    ∃ p : OuterplanarEarPath, c.ear = some p := by
  cases c.earExists with
  | inl hc =>
    simp [h] at hc
  | inr hs =>
    exact (Option.isSome_iff_exists).mp (by simpa using hs)

/-- Bundle: non-cycle + legal ear ⇒ tip kind + measure drop available. -/
theorem OuterplanarCoreResidual.upper_step_of_legal_ear
    (c : OuterplanarCoreResidual)
    (p : OuterplanarEarPath)
    (hear : c.ear = some p)
    (hp : p.isLegal)
    (hPos : 0 < c.nVertices) :
    ∃ tip : EarTipKind,
      ((c.toSketchOfEar p hear hp).classify).tipKind = some tip ∧
      (FoldMeasure.succFold (foldMeasureOf (c.toSketchOfEar p hear hp))).nVertices
        < c.nVertices := by
  let g := c.toSketchOfEar p hear hp
  have hCyc : g.isCycle = false := rfl
  obtain ⟨tip, htip⟩ := foldTipWitness_of_not_cycle g hCyc
  refine ⟨tip, htip, ?_⟩
  exact fold_loop_decreases g.nVertices hPos

/-- Concrete: C₄ triangle-ear core. -/
def coreC4Triangle : OuterplanarCoreResidual :=
  coreWithEar 4 earPathTriangle ⟨by decide, Or.inl rfl⟩

theorem coreC4Triangle_tip :
    ∃ tip : EarTipKind,
      ((coreC4Triangle.toSketchOfEar earPathTriangle rfl
          ⟨by decide, Or.inl rfl⟩).classify).tipKind = some tip := by
  obtain ⟨tip, htip, _⟩ :=
    coreC4Triangle.upper_step_of_legal_ear earPathTriangle rfl
      ⟨by decide, Or.inl rfl⟩ (by decide)
  exact ⟨tip, htip⟩

/-- Concrete: shortcut ear of length 2. -/
def coreShortcut2 : OuterplanarCoreResidual :=
  coreWithEar 6 (earPathShortcut 2) ⟨by decide, Or.inl rfl⟩

def coreResidualDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

def earLawOutlineDocCore : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
