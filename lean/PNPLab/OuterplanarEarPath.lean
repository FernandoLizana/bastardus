/-
  Outerplanar ear-path model (Category C / G6).

  Finitary Whitney ear on a peeled 2-core (parallels OpenArcPath / ThetaResidue):
    left (deg≥3) — internals — right (deg≥3),
    with optional base edge (triangle when internals = 1).

  Discharges tip-kind dichotomy once ear-path parameters are given.
  Whitney existence (non-cycle ⇒ ∃ ear path) stays classical / axiomatized.
-/

import PNPLab.Outerplanar
import PNPLab.ThetaChordFold

namespace PNPLab.Outerplanar

/-- Ear path on a peeled outerplanar 2-core (Δ≤3). -/
structure OuterplanarEarPath where
  internals : Nat
  leftDegGe3 : Bool
  rightDegGe3 : Bool
  /-- Base edge between attachments (triangle when internals = 1). -/
  endsAdjacent : Bool

def OuterplanarEarPath.hasTriangleEar (p : OuterplanarEarPath) : Bool :=
  decide (p.internals = 1) && p.endsAdjacent

def OuterplanarEarPath.hasShortcutTip (p : OuterplanarEarPath) : Bool :=
  decide (0 < p.internals) &&
    (p.leftDegGe3 || p.rightDegGe3) &&
    !(decide (p.internals = 1) && p.endsAdjacent)

/-- Tip-kind dichotomy once an ear path with positive internals is given. -/
theorem OuterplanarEarPath.earLaw (p : OuterplanarEarPath)
    (hk : 0 < p.internals)
    (hEnd : p.leftDegGe3 = true ∨ p.rightDegGe3 = true) :
    p.hasTriangleEar = true ∨ p.hasShortcutTip = true := by
  by_cases h1 : p.internals = 1
  · by_cases hadj : p.endsAdjacent = true
    · left
      simp [OuterplanarEarPath.hasTriangleEar, h1, hadj]
    · right
      have hne : ¬ (decide (p.internals = 1) && p.endsAdjacent) = true := by
        simp [h1, hadj]
      simp [OuterplanarEarPath.hasShortcutTip, decide_eq_true hk, hne]
      exact hEnd
  · right
    have hne : ¬ (decide (p.internals = 1) && p.endsAdjacent) = true := by
      simp [h1]
    simp [OuterplanarEarPath.hasShortcutTip, decide_eq_true hk, hne]
    exact hEnd

/-- Bridge to `ResidualSketch` (discharges `earLaw` field for this family). -/
def OuterplanarEarPath.toSketch (p : OuterplanarEarPath) (n : Nat)
    (hk : 0 < p.internals)
    (hEnd : p.leftDegGe3 = true ∨ p.rightDegGe3 = true) : ResidualSketch where
  nVertices := n
  isCycle := false
  hasTriangleEar := p.hasTriangleEar
  hasShortcutTip := p.hasShortcutTip
  earLaw := by
    right
    exact p.earLaw hk hEnd

/-- Concrete triangle ear (C₄-style). -/
def earPathTriangle : OuterplanarEarPath where
  internals := 1
  leftDegGe3 := true
  rightDegGe3 := true
  endsAdjacent := true

theorem earPathTriangle_law :
    earPathTriangle.hasTriangleEar = true := by
  native_decide

/-- Longer ear ⇒ shortcut tip (ends not adjacent). -/
def earPathShortcut (k : Nat) : OuterplanarEarPath where
  internals := k
  leftDegGe3 := true
  rightDegGe3 := true
  endsAdjacent := false

theorem earPathShortcut_law {k : Nat} (hk : 1 < k) :
    (earPathShortcut k).hasShortcutTip = true := by
  dsimp [OuterplanarEarPath.hasShortcutTip, earPathShortcut]
  have hpos : decide (0 < k) = true := decide_eq_true (Nat.lt_trans Nat.zero_lt_one hk)
  have hne : decide (k = 1) = false := by
    apply decide_eq_false
    exact Nat.ne_of_gt hk
  simp [hpos, hne]

/-- Fold one internal tip on the ear. -/
def OuterplanarEarPath.foldEar (p : OuterplanarEarPath) : OuterplanarEarPath where
  internals := p.internals - 1
  leftDegGe3 := p.leftDegGe3
  rightDegGe3 := p.rightDegGe3
  endsAdjacent := p.endsAdjacent

theorem earPathShortcut_fold_or_done {k : Nat} (hk : 0 < k) :
    (earPathShortcut k).foldEar.internals = 0 ∨
      0 < (earPathShortcut k).foldEar.internals := by
  match k with
  | 0 => cases hk
  | 1 => left; rfl
  | _n + 2 => right; exact Nat.succ_pos _

/-- θ-residue as an ear path (unifies with ThetaChordFold). -/
def thetaToEarPath (t : Bicyclic.ThetaResidue) : OuterplanarEarPath where
  internals := t.shortInternals
  leftDegGe3 := true
  rightDegGe3 := true
  endsAdjacent := decide (t.shortInternals = 1)

theorem thetaToEarPath_law (t : Bicyclic.ThetaResidue) :
    (thetaToEarPath t).hasTriangleEar = true ∨
      (thetaToEarPath t).hasShortcutTip = true :=
  (thetaToEarPath t).earLaw t.shortInternals_ge_one (Or.inl rfl)

def earPathDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

def earMassDoc : String :=
  "reports/discovery/outerplanar_ear_existence_mass_n14.json"

end PNPLab.Outerplanar
