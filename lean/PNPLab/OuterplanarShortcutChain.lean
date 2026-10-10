/-
  One-chord facial chain: repeated fwd shortcuts then a triangle fold to the
  pure-cycle base (Category C / G6).

  For a cycle+chord whose shorter arc is the forward arc of length `k ≥ 2`,
  each `FwdShortcut` drops that length by 1 while staying `oneChord`.  After
  `k - 1` shortcuts the residual is a triangle ear; one more fold reaches the
  cycle base with odd charge preserved.
-/

import PNPLab.OuterplanarShortcutFold
import PNPLab.OuterplanarFacialInduction

namespace PNPLab.Outerplanar

/--
  Explicit length-3 fwd-ear chain: two shortcuts then a triangle fold.
  Concrete witness for the general `shorterInternals = 3` schedule.
-/
structure FacialFwdChain3 where
  start : CycleChord.FwdShortcut
  start_fwd3 : start.chord.fwdInternals = 3
  nPos : 1 < start.chord.n

namespace FacialFwdChain3

def mid1 (s : FacialFwdChain3) : CycleChord.FwdShortcut :=
  s.start.continue (by
    have h := s.start_fwd3
    omega)

def mid2Chord (s : FacialFwdChain3) : CycleChord :=
  (s.mid1).after

theorem mid1_fwd2 (s : FacialFwdChain3) :
    s.mid1.chord.fwdInternals = 2 := by
  have h := s.start_fwd3
  have hf := s.start.after_fwd
  simp only [mid1, CycleChord.FwdShortcut.continue] at *
  omega

theorem mid2_fwd1 (s : FacialFwdChain3) :
    s.mid2Chord.fwdInternals = 1 := by
  have h2 := s.mid1_fwd2
  have hf := s.mid1.after_fwd
  simp only [mid2Chord] at *
  omega

theorem mid2_n_eq (s : FacialFwdChain3) :
    s.mid2Chord.n = s.start.chord.n - 2 := by
  have hn := s.nPos
  simp only [mid2Chord, mid1, CycleChord.FwdShortcut.continue, CycleChord.FwdShortcut.after]
  omega

theorem mid2_triangle (s : FacialFwdChain3) :
    s.mid2Chord.shorterInternals = 1 := by
  have hf := s.mid2_fwd1
  have hb := s.mid1.after_bwd
  have hs := s.mid1.fwdShort
  have h2 := s.mid1_fwd2
  simp only [mid2Chord, CycleChord.shorterInternals] at *
  omega

theorem mid2_nPos (s : FacialFwdChain3) : 1 < s.mid2Chord.n := by
  have hf3 := s.start_fwd3
  have hb := s.start.chord.b_lt_n
  have hg := s.start.chord.gap
  have hn := s.mid2_n_eq
  -- fwd=3 ⇒ b = a+4 ⇒ n ≥ a+5 ≥ 5 ⇒ n-2 ≥ 3
  simp only [CycleChord.fwdInternals] at hf3
  omega

noncomputable def finalTriangle (s : FacialFwdChain3) : FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord s.mid2Chord s.mid2_triangle s.mid2_nPos

noncomputable def finalBase (s : FacialFwdChain3) : FacialCycleBase :=
  s.finalTriangle.toCycleBase

theorem mid_not_cycle (s : FacialFwdChain3) :
    (OuterplanarEmbedCert.oneChord s.mid1.chord).isCycle = false ∧
      (OuterplanarEmbedCert.oneChord s.mid2Chord).isCycle = false :=
  ⟨rfl, rfl⟩

theorem final_nAfter (s : FacialFwdChain3) :
    s.finalBase.nAfter = s.start.chord.n - 3 := by
  have hn := s.mid2_n_eq
  simp only [finalBase, FacialTriangleFoldStep.toCycleBase, finalTriangle,
    FacialTriangleFoldStep.ofTriangleChord]
  omega

theorem reaches_cycle (s : FacialFwdChain3) :
    s.finalBase.embedAfter.isCycle = true ∧
      gf2Sum s.finalBase.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle s.finalBase.nAfter) = 0 ∧
      s.finalBase.nAfter = s.start.chord.n - 3 :=
  ⟨s.finalBase.embed_cycle, s.finalBase.charges_odd,
    foldSteps_cycle s.finalBase.nAfter, s.final_nAfter⟩

end FacialFwdChain3

/-- C₈ `{0,4}`: shorter=3 → two shortcuts → triangle → C₅ base. -/
def c8Chord04Chain : FacialFwdChain3 where
  start := c8Chord04Fwd
  start_fwd3 := by native_decide
  nPos := by decide

theorem c8Chord04_chain_mids :
    c8Chord04Chain.mid1.chord.n = 7 ∧
      c8Chord04Chain.mid1.chord.b = 3 ∧
      c8Chord04Chain.mid2Chord.n = 6 ∧
      c8Chord04Chain.mid2Chord.b = 2 ∧
      c8Chord04Chain.mid2Chord.shorterInternals = 1 := by
  native_decide

theorem c8Chord04_chain_to_cycle :
    c8Chord04Chain.finalBase.embedAfter.isCycle = true ∧
      c8Chord04Chain.finalBase.nAfter = 5 ∧
      gf2Sum c8Chord04Chain.finalBase.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle 5) = 0 := by
  have h := c8Chord04Chain.reaches_cycle
  have hn : c8Chord04Chain.start.chord.n = 8 := rfl
  refine ⟨h.1, ?_, h.2.1, foldSteps_cycle 5⟩
  rw [h.2.2.2, hn]

/-- Bwd wrap shortcut then triangle (C₈ `{0,5}` → triangle on 7 → cycle on 6). -/
theorem c8Chord05_shortcut_then_triangle :
    c8Chord05Bwd.after.shorterInternals = 1 ∧
      (OuterplanarEmbedCert.foldTriangle c8Chord05Bwd.after
        (by native_decide)).isCycle = true ∧
      (OuterplanarEmbedCert.foldTriangle c8Chord05Bwd.after
        (by native_decide)).nVertices = 6 := by
  refine ⟨by native_decide, ?_, ?_⟩
  · exact OuterplanarEmbedCert.foldTriangle_isCycle _ (by native_decide)
  · rfl

def shortcutChainDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
