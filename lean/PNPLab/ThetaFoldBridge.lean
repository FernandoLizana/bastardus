/-
  Bridge: θ-residue tip law (ThetaChordFold) + bicyclic Width≤Δ pack (BicyclicC6).

  Category C — not P vs NP. Documents the inductive hop shape:
  tip exists on θ → fold measure drops → Closure₃ of θ-instance has □.
-/

import PNPLab.Bicyclic
import PNPLab.ThetaChordFold
import PNPLab.BicyclicC6Width3

namespace PNPLab.Bicyclic

/-- C₆ + chord span 2 (triangle ear on short arc). -/
def c6chordShort : ThetaResidue where
  n := 6
  a := 2
  hn := by decide
  ha1 := by decide
  ha2 := by decide

theorem c6chordShort_triangle :
    c6chordShort.hasTriangleEar = true ∧
      c6chordShort.tipKind = ChordTipKind.triangleEar := by
  constructor
  · native_decide
  · simp [ThetaResidue.tipKind, c6chordShort]
    native_decide

theorem c6chordShort_chordFoldLaw :
    c6chordShort.hasTriangleEar = true ∨ c6chordShort.hasShortcutTip = true :=
  ThetaResidue.chordFoldLaw c6chordShort

/-- Sketch for induction measure on the same residue. -/
def c6ShortSketch : ThetaSketch := c6chordShort.toSketch

theorem c6_induction_hop :
    (c6ShortSketch.classify).tipKind.isSome = true ∧
      (FoldMeasure.succFold (foldMeasureOf c6ShortSketch)).nVertices <
        c6ShortSketch.nVertices := by
  have h := induction_shape_bundle c6ShortSketch rfl (by decide : c6ShortSketch.nVertices > 0)
  exact ⟨h.1, h.2.1⟩

/-- Resolution upper bound for C₆+(0,2): □ ∈ Closure₃ (matches short-chord family). -/
theorem c6_width_le_delta_pack : Resolution.bi6Closure.mem [] :=
  Resolution.bi6_has_empty

/-- Combined witness: tip law + Width ≤ Δ pack for the C₆ θ-family. -/
theorem c6_theta_bridge_bundle :
    c6chordShort.hasTriangleEar = true ∧
      Resolution.bi6Closure.mem [] ∧
      foldCountdown 6 = 0 := by
  refine ⟨?_, Resolution.bi6_has_empty, foldCountdown_zero 6⟩
  exact c6chordShort_triangle.1

def thetaFoldBridgeDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-BICYCLIC-001/INDUCTION_WIDTH_EQ_DELTA.md"

end PNPLab.Bicyclic
