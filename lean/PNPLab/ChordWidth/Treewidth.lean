/-
  Treewidth for ChordWidth: real `TreeDecomp` / `HasTreeDecomp` (no `True` stubs).

  Mathlib v4.32.0 has no upstream `SimpleGraph.treeWidth` (PR #38334 open).
  ChordWidth vendors a minimal faithful API in `TreeDecomp/`.
-/

import PNPLab.ChordWidth.LineGraph
import PNPLab.ChordWidth.TreeDecomp.Basic
import PNPLab.ChordWidth.TreeDecomp.Smoke

namespace PNPLab.ChordWidth

open SimpleGraph

variable {V : Type*}

/--
  **Certified** treewidth upper bound: explicit tree decomposition of width ≤ `k`.

  Replaces the old `TreewidthWitness` stub (`documented : True`).
-/
abbrev TreewidthCertificate (V : Type*) [Fintype V] (G : SimpleGraph V) (k : Nat) : Prop :=
  TreeDecomp.HasTreeDecomp G k

/-- Backward-compatible alias (deprecated semantics: now requires real certificate). -/
abbrev TreewidthWitness (V : Type*) (G : SimpleGraph V) (k : Nat) [Fintype V] : Prop :=
  TreewidthCertificate V G k

/--
  Elimination order (scaffolding for future certificate export from Python/LibTW).
  Does **not** by itself prove `HasTreeDecomp` until elimination→decomposition lemma is added.
-/
structure EliminationOrder (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  order : List V
  length_eq : order.length = Fintype.card V
  nodup : order.Nodup

/--
  **Hipótesis condicional / dato experimental**: nominal tw bound without Lean decomposition.

  Used for line-graph tw on two-chord smoke where Python validates tw(L(G)) ∈ {3,4}
  but full `HasTreeDecomp` certificates are not yet formalized.
-/
structure ExperimentalTreewidthBound (V : Type*) [Fintype V] (G : SimpleGraph V) (k : Nat) where
  source : String
  note : String

structure LineGraphTreewidthExperimental (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : Nat) [Fintype G.edgeSet] [DecidableEq G.edgeSet] where
  bound : ExperimentalTreewidthBound G.edgeSet G.lineGraph k

/--
  Verified or experimental tw(L(G)) upper bound at `k`.
  All c5–c10 smokes use `.certified` via `CertificatesLine` + `CertificatesLineSmokes`.
-/
inductive LineGraphTwBound (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : Nat)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] where
  | certified (h : TreewidthCertificate G.edgeSet G.lineGraph k)
  | experimental (h : LineGraphTreewidthExperimental V G k)

def treewidthAtMost {V : Type*} [Fintype V] (G : SimpleGraph V) (k : Nat) : Prop :=
  TreeDecomp.HasTreeDecomp G k

def treewidthOf {V : Type*} [Fintype V] (G : SimpleGraph V) (k : Nat)
    (_h : TreewidthCertificate V G k) : Nat := k

def lineGraphTreewidthOf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : Nat)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (_h : TreewidthCertificate G.edgeSet G.lineGraph k) : Nat := k

theorem lineGraphTreewidthOf_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : Nat)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (h : TreewidthCertificate G.edgeSet G.lineGraph k) :
    lineGraphTreewidthOf G k h = k :=
  rfl

theorem k4TreewidthCertificate :
    TreewidthCertificate (Fin 4) (⊤ : SimpleGraph (Fin 4)) 3 :=
  k4_hasTreeDecomp_three

theorem fourCycleTreewidthCertificate :
    TreewidthCertificate (Fin 4) (cycleGraph 4) 3 :=
  fourCycle_hasTreeDecomp_at_most_three

def k4EliminationOrder : EliminationOrder (Fin 4) (⊤ : SimpleGraph (Fin 4)) where
  order := [0, 1, 2, 3]
  length_eq := by native_decide
  nodup := by native_decide

def fourCycleEliminationOrder : EliminationOrder (Fin 4) (cycleGraph 4) where
  order := [0, 1, 2, 3]
  length_eq := by native_decide
  nodup := by native_decide

def treewidthDoc : String :=
  "HasTreeDecomp + TreeDecomp (PR #38334 minimal vendored); " ++
  "TreewidthCertificate replaces True stub; LineGraphTwBound certified|experimental; " ++
  "K₄/C₄ smoke certificates proved; c5–c10 line-graph tw=4/3 via CertificatesLine + CertificatesLineSmokes."

end PNPLab.ChordWidth
