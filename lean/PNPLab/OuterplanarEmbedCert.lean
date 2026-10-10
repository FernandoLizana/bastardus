/-
  Facial outerplanar embedding certificate (Category C / G6).

  Mathlib has no `IsOuterplanar`.  This module supplies the combinatorial
  stand-in used by the width proof:

    * a 2-core is certified as a facial cycle, or as a cycle plus one chord;
    * non-cycle certificates expose a legal Whitney ear (`CycleChord`);
    * folding a triangle ear returns a pure cycle certificate — outerplanarity
      is preserved *by construction*, not by an embedding theorem.

  Multi-chord diagrams enter via `NoncrossingChordDiagram.toEmbedCert` (derived
  ear for tip existence only).  Folding that ear on a two-chord diagram does
  **not** erase the other chord — see `NestedChordResidual` / `DisjointChordResidual`.
  Longer ears use `OuterplanarShortcutFold` (residual stays `oneChord`).
  Nested triples: `NestedTripleResidual`.
-/

import PNPLab.OuterplanarFoldPreservation
import PNPLab.ChordDiagramEar

namespace PNPLab.Outerplanar

/--
  Facial outerplanar 2-core.

  `cycle n`: pure outer cycle on `n ≥ 3` vertices.
  `oneChord c`: cycle + one non-boundary chord; short arc = Whitney ear.
-/
inductive OuterplanarEmbedCert where
  | cycle (n : Nat) (h : 3 ≤ n)
  | oneChord (c : CycleChord)

/-- Vertex count of the facial certificate. -/
def OuterplanarEmbedCert.nVertices : OuterplanarEmbedCert → Nat
  | .cycle n _ => n
  | .oneChord c => c.n

/-- Pure cycles are the fold base. -/
def OuterplanarEmbedCert.isCycle : OuterplanarEmbedCert → Bool
  | .cycle _ _ => true
  | .oneChord _ => false

/-- Extract the chord when present. -/
def OuterplanarEmbedCert.getChord : OuterplanarEmbedCert → Option CycleChord
  | .cycle _ _ => none
  | .oneChord c => some c

theorem OuterplanarEmbedCert.cycle_iff_no_chord (e : OuterplanarEmbedCert) :
    e.isCycle = true ↔ e.getChord = none := by
  cases e <;> simp [OuterplanarEmbedCert.isCycle, OuterplanarEmbedCert.getChord]

/-- Non-cycle embed cert ⇒ legal Whitney ear. -/
def OuterplanarEmbedCert.toEarPath (e : OuterplanarEmbedCert)
    (h : e.isCycle = false) : OuterplanarEarPath :=
  match e with
  | .cycle _ _ => by simp [OuterplanarEmbedCert.isCycle] at h
  | .oneChord c => c.toEarPath

theorem OuterplanarEmbedCert.toEarPath_isLegal (e : OuterplanarEmbedCert)
    (h : e.isCycle = false) :
    (e.toEarPath h).isLegal := by
  match e with
  | .cycle _ _ => simp [OuterplanarEmbedCert.isCycle] at h
  | .oneChord c => exact c.toEarPath_isLegal

/-- Bridge to the block-cut exposure layer. -/
def OuterplanarEmbedCert.toBlockCut (e : OuterplanarEmbedCert)
    (h : e.isCycle = false) : OuterplanarBlockCut :=
  match e with
  | .cycle _ _ => by simp [OuterplanarEmbedCert.isCycle] at h
  | .oneChord c => c.toBlockCut

theorem OuterplanarEmbedCert.expose_ear (c : CycleChord) :
    ∃ w : SizedLegalOuterplanarEar c.n,
      ((OuterplanarEmbedCert.oneChord c).toBlockCut rfl).expose = .ear w := by
  simpa [OuterplanarEmbedCert.toBlockCut] using c.expose_ear

/--
  Triangle facial fold: chord of short-arc length 1 becomes an outer edge,
  leaving a pure cycle on `n-1` vertices.  Outerplanarity is preserved by
  returning another `OuterplanarEmbedCert`.
-/
def OuterplanarEmbedCert.foldTriangle (c : CycleChord)
    (_htri : c.shorterInternals = 1) : OuterplanarEmbedCert :=
  .cycle (c.n - 1) (by
    have := c.gap
    have := c.b_lt_n
    have := c.bwd_pos
    have := c.fwd_pos
    omega)

theorem OuterplanarEmbedCert.foldTriangle_isCycle (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    (foldTriangle c htri).isCycle = true :=
  rfl

theorem OuterplanarEmbedCert.foldTriangle_nVertices (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    (foldTriangle c htri).nVertices = c.n - 1 :=
  rfl

theorem OuterplanarEmbedCert.foldTriangle_lt (c : CycleChord)
    (htri : c.shorterInternals = 1) (hPos : 1 < c.n) :
    (foldTriangle c htri).nVertices < c.n := by
  simp [foldTriangle_nVertices]
  omega

/--
  Outerplanarity preservation for the triangle fold: the residual is again a
  facial outerplanar certificate (a pure cycle).
-/
theorem OuterplanarEmbedCert.foldTriangle_preserves_embed (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    ∃ e' : OuterplanarEmbedCert,
      e' = foldTriangle c htri ∧ e'.isCycle = true :=
  ⟨foldTriangle c htri, rfl, rfl⟩

/-- From a noncrossing two-chord diagram, the derived ear yields a facial cert. -/
def NoncrossingChordDiagram.toEmbedCert (d : NoncrossingChordDiagram) :
    OuterplanarEmbedCert :=
  .oneChord d.toEar

theorem NoncrossingChordDiagram.toEmbedCert_not_cycle
    (d : NoncrossingChordDiagram) :
    (d.toEmbedCert).isCycle = false :=
  rfl

theorem NoncrossingChordDiagram.toEmbedCert_n
    (d : NoncrossingChordDiagram) :
    (d.toEmbedCert).nVertices = d.n :=
  rfl

/-- Concrete: C₄ diagonal embed cert folds to a 3-cycle. -/
theorem c4Diagonal_fold_to_cycle :
    (OuterplanarEmbedCert.foldTriangle c4Diagonal (by native_decide)).isCycle =
      true :=
  OuterplanarEmbedCert.foldTriangle_isCycle c4Diagonal (by native_decide)

/-- Concrete: C₆ short chord embed cert exposes an ear. -/
theorem c6Chord02_embed_expose :
    ∃ w : SizedLegalOuterplanarEar 6,
      ((OuterplanarEmbedCert.oneChord c6Chord02).toBlockCut rfl).expose =
        .ear w :=
  OuterplanarEmbedCert.expose_ear c6Chord02

/-- Bundle: one-chord facial cert ⇒ legal ear + triangle-fold preserves embed. -/
theorem OuterplanarEmbedCert.oneChord_upper_bundle (c : CycleChord)
    (htri : c.shorterInternals = 1) (hPos : 1 < c.n) :
    c.toEarPath.isLegal ∧
      (foldTriangle c htri).nVertices < c.n ∧
      (foldTriangle c htri).isCycle = true :=
  ⟨c.toEarPath_isLegal, foldTriangle_lt c htri hPos, foldTriangle_isCycle c htri⟩

def embedCertDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

end PNPLab.Outerplanar
