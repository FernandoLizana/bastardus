/-
  Literature hypothesis: resolution width of Tseitin formulas vs max(Δ(G), tw(L(G))).

  **LITERATURE HYPOTHESIS — NOT a PNPLab theorem.**

  Primary source: Galesi–Talebanfard–Torán (TOCT 2020).

  Refactored: `k` is an explicit parameter; no circular `TreewidthWitness` field
  that presupposes tw(L(G)) = k without proof.
-/

import PNPLab.ChordWidth.LineGraph
import PNPLab.ChordWidth.Treewidth
import PNPLab.Resolution
import PNPLab.ResolutionClosure
import PNPLab.XorCnf

namespace PNPLab.ChordWidth

open Resolution
open SimpleGraph

variable {V : Type*}

structure OddMarking (V : Type*) where
  charge : V → Nat

def OddMarking.totalCharge {V : Type*} [Fintype V] (φ : OddMarking V) : Nat :=
  (Finset.univ : Finset V).sum φ.charge

def OddMarking.isOdd {V : Type*} [Fintype V] (φ : OddMarking V) : Prop :=
  OddMarking.totalCharge φ % 2 = 1

abbrev OddMarkingOdd (V : Type*) [Fintype V] :=
  {φ : OddMarking V // OddMarking.isOdd φ}

def hasRefutationAtWidth (axioms : List Clause) (w : Nat) : Prop :=
  ∃ d : Derivation axioms [], derWidth d ≤ w

structure ResolutionWidth (axioms : List Clause) (w : Nat) : Prop where
  refutes : hasRefutationAtWidth axioms w
  minimal : ∀ w' < w, ¬ hasRefutationAtWidth axioms w'

/--
  **LITERATURE HYPOTHESIS** (not a PNPLab theorem).

  Assumes width = max(Δ, k) for nominal Δ and line-graph treewidth parameter `k`.
  Does **not** embed tw = k as a proved certificate.
-/
structure TseitinWidthTreewidthCharacterization (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ k : Nat) where
  tseitin : OddMarkingOdd V → List Clause
  width_eq :
    ∀ φ : OddMarkingOdd V,
      ResolutionWidth (tseitin φ) (max Δ k)

/--
  Optional certificate layer: literature char + proved tw(L(G)) ≤ k (when instances available).
-/
structure TseitinWidthWithTreewidthCertificate (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Δ k : Nat)
    [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    extends TseitinWidthTreewidthCharacterization V G Δ k where
  lineGraph_tw_cert : TreewidthCertificate G.edgeSet G.lineGraph k

theorem width_from_treewidth_of_characterization
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {Δ k : Nat}
    (hChar : TseitinWidthTreewidthCharacterization V G Δ k)
    (hΔ : Δ = 3)
    (φ : OddMarkingOdd V) :
    ResolutionWidth (hChar.tseitin φ) (max 3 k) := by
  simpa [hΔ] using hChar.width_eq φ

def literatureHypothesisDoc : String :=
  "LITERATURE HYPOTHESIS (Galesi–Talebanfard–Torán): width = max(Δ, tw(L(G))); " ++
  "TseitinWidthTreewidthCharacterization sin witness circular; certificado opcional aparte."

end PNPLab.ChordWidth
