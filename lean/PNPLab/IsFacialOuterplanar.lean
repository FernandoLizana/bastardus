/-
  Project-local facial outerplanarity (Category C / G6).

  Mathlib v4.32.0 has no `IsOuterplanar`.  This packages `OuterplanarEmbedCert`
  as an explicit predicate without claiming a Mathlib embedding theorem.
-/

import PNPLab.OuterplanarEmbedCert

namespace PNPLab.Outerplanar

/--
  Facial outerplanarity certificate on `n` vertices.

  **Not** Mathlib `IsOuterplanar`: only the combinatorial 2-core used by the
  width upper bound (`cycle` or `oneChord`).
-/
structure IsFacialOuterplanar (n : Nat) where
  cert : OuterplanarEmbedCert
  n_eq : cert.nVertices = n

/-- Any embed cert is facial outerplanar on its vertex count. -/
def IsFacialOuterplanar.ofCert (e : OuterplanarEmbedCert) :
    IsFacialOuterplanar e.nVertices where
  cert := e
  n_eq := rfl

/-- Pure cycle base (`n ≥ 3`). -/
def IsFacialOuterplanar.cycle {n : Nat} (h : 3 ≤ n) : IsFacialOuterplanar n :=
  ofCert (.cycle n h)

theorem IsFacialOuterplanar.cycle_is_base {n : Nat} (h : 3 ≤ n) :
    (IsFacialOuterplanar.cycle h).cert.isCycle = true :=
  rfl

/-- Triangle fold of a one-chord core yields a facial cycle on `n - 1`. -/
def IsFacialOuterplanar.ofTriangleFold (c : CycleChord)
    (htri : c.shorterInternals = 1) : IsFacialOuterplanar (c.n - 1) :=
  ofCert (OuterplanarEmbedCert.foldTriangle c htri)

theorem IsFacialOuterplanar.ofTriangleFold_isCycle (c : CycleChord)
    (htri : c.shorterInternals = 1) :
    (IsFacialOuterplanar.ofTriangleFold c htri).cert.isCycle = true :=
  OuterplanarEmbedCert.foldTriangle_isCycle c htri

/-- One-chord cert exposes a Whitney ear. -/
theorem IsFacialOuterplanar.oneChord_exposes_ear (c : CycleChord) :
    ∃ w : SizedLegalOuterplanarEar c.n,
      ((IsFacialOuterplanar.ofCert (.oneChord c)).cert.toBlockCut rfl).expose =
        .ear w :=
  OuterplanarEmbedCert.expose_ear c

/-- Fold preserves facial outerplanarity (cycle after triangle fold). -/
theorem IsFacialOuterplanar.foldTriangle_preserves
    (c : CycleChord) (htri : c.shorterInternals = 1) :
    ∃ ι : IsFacialOuterplanar (c.n - 1), ι.cert.isCycle = true :=
  ⟨ofTriangleFold c htri, ofTriangleFold_isCycle c htri⟩

/--
  Local outerplanarity certificate (project stand-in for absent Mathlib `IsOuterplanar`).
  Carrier = facial embed cert (cycle / cycle+one chord). Not a geometric embedding.
  (Structure, not Prop — Mathlib has no outerplanar API in v4.32.0.)
-/
structure IsOuterplanar (n : Nat) where
  facial : IsFacialOuterplanar n

def IsFacialOuterplanar.toIsOuterplanar {n : Nat}
    (ι : IsFacialOuterplanar n) : IsOuterplanar n :=
  ⟨ι⟩

def IsOuterplanar.toFacial {n : Nat}
    (ι : IsOuterplanar n) : IsFacialOuterplanar n :=
  ι.facial

def IsOuterplanar.ofCert (e : OuterplanarEmbedCert) : IsOuterplanar e.nVertices :=
  (IsFacialOuterplanar.ofCert e).toIsOuterplanar

def IsOuterplanar.cycle {n : Nat} (h : 3 ≤ n) : IsOuterplanar n :=
  (IsFacialOuterplanar.cycle h).toIsOuterplanar

def isFacialOuterplanarDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/EAR_LAW_OUTLINE.md"

def isOuterplanarLocalDoc : String :=
  "Local IsOuterplanar ≡ IsFacialOuterplanar; Mathlib API absent (v4.32.0)"

end PNPLab.Outerplanar
