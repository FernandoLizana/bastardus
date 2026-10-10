/-
  Multi-chord residual after inner triangle fold (Category C / G6).

  Honesty fix: `NoncrossingChordDiagram.toEmbedCert` packages only the *derived
  ear* for tip existence.  Folding that ear on a **two-chord** diagram does
  **not** yield a pure cycle — the other chord remains.  For nested pairings
  with a length-2 inner ear `{p1, p1+2}`, deleting the unique internal tip at
  `p1 + 1` leaves the outer chord `{p0, p3}` on `n - 1` vertices (with `p3`
  shifted down by one).

  This module constructs that residual `CycleChord` and the two-step induction
  nested-triangle → outer-chord → cycle.
-/

import PNPLab.OuterplanarFacialInduction
import PNPLab.OddChargeFold

namespace PNPLab.Outerplanar

/-- Inner ear endpoints form a length-2 chord (one internal tip). -/
abbrev NoncrossingChordDiagram.innerLen2 (d : NoncrossingChordDiagram) : Prop :=
  d.earB = d.earA + 2

/--
  Outer chord residual after deleting the unique internal of a nested length-2
  ear.  Tip index is `earA + 1`; since `p0 < earA < tip < earB ≤ p3`, the outer
  right endpoint shifts: `p3 ↦ p3 - 1`.
-/
def NoncrossingChordDiagram.residualOuterChord (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen2 : d.innerLen2)
    (hOuterBwd : 0 < d.n - (d.p3 - d.p0) - 1) : CycleChord where
  n := d.n - 1
  a := d.p0
  b := d.p3 - 1
  gap := by
    have ord := d.ordered
    have em := d.ear_match
    simp [NoncrossingChordDiagram.innerLen2] at hlen2
    simp [hnest] at em
    -- p0 < p1 = earA, earB = earA+2, earB ≤ p3 (from ordered via ear_match)
    have : d.earA = d.p1 ∧ d.earB = d.p2 := em
    omega
  b_lt_n := by
    have := d.ordered
    omega
  bwd_pos := by
    -- residual bwd equals original outer-chord bwd
    have : (d.n - 1) - ((d.p3 - 1) - d.p0) - 1 = d.n - (d.p3 - d.p0) - 1 := by
      have := d.ordered
      omega
    simpa [this] using hOuterBwd

theorem NoncrossingChordDiagram.residualOuterChord_n
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen2 : d.innerLen2)
    (hOuterBwd : 0 < d.n - (d.p3 - d.p0) - 1) :
    (d.residualOuterChord hnest hlen2 hOuterBwd).n = d.n - 1 :=
  rfl

/-- Embed cert after the inner fold: still one chord (the outer), not a cycle. -/
def NoncrossingChordDiagram.afterInnerTriangle (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen2 : d.innerLen2)
    (hOuterBwd : 0 < d.n - (d.p3 - d.p0) - 1) : OuterplanarEmbedCert :=
  .oneChord (d.residualOuterChord hnest hlen2 hOuterBwd)

theorem NoncrossingChordDiagram.afterInnerTriangle_not_cycle
    (d : NoncrossingChordDiagram)
    (hnest : d.pairing = .nested)
    (hlen2 : d.innerLen2)
    (hOuterBwd : 0 < d.n - (d.p3 - d.p0) - 1) :
    (d.afterInnerTriangle hnest hlen2 hOuterBwd).isCycle = false :=
  rfl

/-- Two-step nested induction when the outer residual is also a triangle. -/
structure NestedTriangleInduction where
  diagram : NoncrossingChordDiagram
  nested : diagram.pairing = .nested
  innerLen2 : diagram.innerLen2
  outerBwd : 0 < diagram.n - (diagram.p3 - diagram.p0) - 1
  innerTri : diagram.toEar.shorterInternals = 1
  nPos : 1 < diagram.n
  outerTri : (diagram.residualOuterChord nested innerLen2 outerBwd).shorterInternals = 1
  outerNPos : 1 < (diagram.residualOuterChord nested innerLen2 outerBwd).n

noncomputable def NestedTriangleInduction.step1 (s : NestedTriangleInduction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord s.diagram.toEar s.innerTri (by
    simpa [NoncrossingChordDiagram.toEar] using s.nPos)

def NestedTriangleInduction.midEmbed (s : NestedTriangleInduction) :
    OuterplanarEmbedCert :=
  s.diagram.afterInnerTriangle s.nested s.innerLen2 s.outerBwd

noncomputable def NestedTriangleInduction.step2 (s : NestedTriangleInduction) :
    FacialTriangleFoldStep :=
  FacialTriangleFoldStep.ofTriangleChord
    (s.diagram.residualOuterChord s.nested s.innerLen2 s.outerBwd)
    s.outerTri s.outerNPos

theorem NestedTriangleInduction.mid_not_cycle (s : NestedTriangleInduction) :
    s.midEmbed.isCycle = false :=
  s.diagram.afterInnerTriangle_not_cycle s.nested s.innerLen2 s.outerBwd

theorem NestedTriangleInduction.final_is_cycle (s : NestedTriangleInduction) :
    s.step2.after.isCycle = true :=
  s.step2.after_is_cycle

theorem NestedTriangleInduction.bundle (s : NestedTriangleInduction) :
    s.midEmbed.isCycle = false ∧
      s.step2.after.isCycle = true ∧
      gf2Sum s.step2.chargesAfter.charges = 1 ∧
      foldSteps (sketchCycle (s.step2.chord.n - 1)) = 0 :=
  ⟨s.mid_not_cycle, s.final_is_cycle, s.step2.charges_remain_odd,
    foldSteps_cycle (s.step2.chord.n - 1)⟩

/-- C₈ nested: inner `{2,4}` then outer residual `{0,5}` on 7 verts. -/
def c8NestedInduction : NestedTriangleInduction where
  diagram := c8NestedDiagram
  nested := rfl
  innerLen2 := by native_decide
  outerBwd := by decide
  innerTri := by native_decide
  nPos := by decide
  outerTri := by native_decide
  outerNPos := by native_decide

theorem c8Nested_residual_outer :
    (c8NestedDiagram.residualOuterChord rfl (by native_decide) (by decide)).a = 0 ∧
      (c8NestedDiagram.residualOuterChord rfl (by native_decide) (by decide)).b = 5 ∧
      (c8NestedDiagram.residualOuterChord rfl (by native_decide) (by decide)).n = 7 := by
  native_decide

theorem c8Nested_two_step_to_cycle :
    c8NestedInduction.midEmbed.isCycle = false ∧
      c8NestedInduction.step2.after.isCycle = true ∧
      gf2Sum c8NestedInduction.step2.chargesAfter.charges = 1 :=
  ⟨c8NestedInduction.mid_not_cycle, c8NestedInduction.final_is_cycle,
    c8NestedInduction.step2.charges_remain_odd⟩

def nestedResidualDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
