/-
  Resolution derivations and width-bounded closures (lightweight, no Mathlib).
-/

import PNPLab.Resolution

namespace PNPLab.Resolution

/-- Inductive resolution derivation from an axiom list (by index). -/
inductive Derivation (axioms : List Clause) : Clause → Type where
  | ax (i : Nat) (h : i < axioms.length) :
      Derivation axioms axioms[i]
  | res (p : Lit) {C D R : Clause}
      (dC : Derivation axioms C) (dD : Derivation axioms D)
      (h : resolveOriented C D p = some R) :
      Derivation axioms R

/-- Maximum clause width appearing in a derivation. -/
def derWidth {axioms : List Clause} : {C : Clause} → Derivation axioms C → Nat
  | _, .ax i _ => clauseWidth axioms[i]
  | R, .res _ dC dD _ => max (clauseWidth R) (max (derWidth dC) (derWidth dD))

theorem derWidth_ge_conclusion {axioms : List Clause} {C : Clause}
    (d : Derivation axioms C) : clauseWidth C ≤ derWidth d := by
  induction d with
  | ax i h => simp [derWidth]
  | res p dC dD hR ihC ihD =>
    simp [derWidth]
    exact Nat.le_max_left _ _

/-- Complementary units derive the empty clause at width 1. -/
theorem units_derive_empty :
    ∃ d : Derivation [[(1 : Lit)], [(-1 : Lit)]] [], derWidth d ≤ 1 := by
  let d : Derivation [[(1 : Lit)], [(-1 : Lit)]] [] :=
    Derivation.res (p := (1 : Lit))
      (.ax 0 (by decide)) (.ax 1 (by decide)) (by native_decide)
  refine ⟨d, ?_⟩
  native_decide

/-- Absolute values of literals (variable ids). -/
def clauseVars (C : Clause) : List Nat :=
  C.map Int.natAbs

def supportedOn (C : Clause) (V : List Nat) : Bool :=
  (clauseVars C).all (fun v => V.contains v)

theorem empty_supportedOn (V : List Nat) :
    supportedOn ([] : Clause) V = true := by
  simp [supportedOn, clauseVars]

/-- Abstract width-w closure membership as a Prop (not computed). -/
structure WidthClosure (w : Nat) where
  axioms : List Clause
  mem : Clause → Prop
  axiom_mem : ∀ C, C ∈ axioms → clauseWidth C ≤ w → mem C
  closed :
    ∀ C D R p, mem C → mem D → resolveOriented C D p = some R →
      clauseWidth R ≤ w → mem R

/-- Projection inclusion hypothesis for the K₄ restriction argument. -/
structure ProjectionInclusion (w : Nat) where
  gClosure : WidthClosure w
  rClosure : WidthClosure w
  Vres : List Nat
  holds :
    ∀ C, gClosure.mem C → supportedOn C Vres = true → rClosure.mem C

/-- From projection inclusion + residual free of □, conclude G free of □. -/
theorem no_empty_of_projection
    {w : Nat}
    (P : ProjectionInclusion w)
    (hResNoEmpty : ¬ P.rClosure.mem []) :
    ¬ P.gClosure.mem [] := by
  intro hg
  have hsup : supportedOn ([] : Clause) P.Vres = true := empty_supportedOn _
  exact hResNoEmpty (P.holds [] hg hsup)

/-- One path-fold elimination step preserves projected membership. -/
structure EliminationStep (w : Nat) where
  before : WidthClosure w
  after : WidthClosure w
  V_after : List Nat
  preserves :
    ∀ C, before.mem C → supportedOn C V_after = true → after.mem C

/-- View a single elimination step as a projection inclusion. -/
def EliminationStep.toProjection {w : Nat} (s : EliminationStep w) :
    ProjectionInclusion w where
  gClosure := s.before
  rClosure := s.after
  Vres := s.V_after
  holds := s.preserves

/-- Support monotonicity in the variable set (Bool). -/
def varsSubset (Vsmall Vlarge : List Nat) : Bool :=
  Vsmall.all fun v => Vlarge.contains v

theorem supportedOn_of_subset
    {C : Clause} {Vsmall Vlarge : List Nat}
    (hNest : varsSubset Vsmall Vlarge = true)
    (hSup : supportedOn C Vsmall = true) :
    supportedOn C Vlarge = true := by
  simp only [supportedOn, clauseVars] at hSup ⊢
  apply List.all_eq_true.mpr
  intro v hv
  have hvSmall : Vsmall.contains v = true := (List.all_eq_true.mp hSup) v hv
  have hvMem : v ∈ Vsmall := (List.contains_iff_mem).mp hvSmall
  exact (List.all_eq_true.mp hNest) v hvMem

/-- Compose two elimination hops when residual variables nest (`V₂ ⊆ V₁`). -/
def composeElimination
    {w : Nat}
    (s1 s2 : EliminationStep w)
    (hBridge : s1.after = s2.before)
    (hNest : varsSubset s2.V_after s1.V_after = true) :
    EliminationStep w where
  before := s1.before
  after := s2.after
  V_after := s2.V_after
  preserves := by
    intro C hB hSup
    have hSup1 : supportedOn C s1.V_after = true :=
      supportedOn_of_subset hNest hSup
    have hMid : s1.after.mem C := s1.preserves C hB hSup1
    have hMid' : s2.before.mem C := by
      simpa [hBridge] using hMid
    exact s2.preserves C hMid' hSup

/-- Composite step → ProjectionInclusion on the finest residual var set. -/
def composeProjection
    {w : Nat}
    (s1 s2 : EliminationStep w)
    (hBridge : s1.after = s2.before)
    (hNest : varsSubset s2.V_after s1.V_after = true) :
    ProjectionInclusion w :=
  (composeElimination s1 s2 hBridge hNest).toProjection

/-- Transitivity of `varsSubset` (Bool). -/
theorem varsSubset_trans
    {Va Vb Vc : List Nat}
    (hAB : varsSubset Va Vb = true)
    (hBC : varsSubset Vb Vc = true) :
    varsSubset Va Vc = true := by
  simp only [varsSubset] at *
  apply List.all_eq_true.mpr
  intro v hv
  have hvB : Vb.contains v = true := (List.all_eq_true.mp hAB) v hv
  have hvMem : v ∈ Vb := (List.contains_iff_mem).mp hvB
  exact (List.all_eq_true.mp hBC) v hvMem

theorem varsSubset_self (V : List Nat) : varsSubset V V = true := by
  unfold varsSubset
  simp only [List.all_eq_true]
  intro v hv
  exact (List.contains_iff_mem).mpr hv

/-- Bridge + nested residual vars between consecutive elimination steps. -/
structure StepLink (w : Nat) (s t : EliminationStep w) where
  bridge : s.after = t.before
  nest : varsSubset t.V_after s.V_after = true

/-- Inductive witness that a step list is coherently linked. -/
inductive LinkedChain (w : Nat) : List (EliminationStep w) → Type where
  | singleton (s : EliminationStep w) : LinkedChain w [s]
  | cons (s t : EliminationStep w) (rest : List (EliminationStep w))
      (link : StepLink w s t) (tail : LinkedChain w (t :: rest)) :
      LinkedChain w (s :: t :: rest)

/-- Extend a linked chain by one hop. -/
def linkedChainCons
    {w : Nat} {s t : EliminationStep w} {rest : List (EliminationStep w)}
    (link : StepLink w s t) (tail : LinkedChain w (t :: rest)) :
    LinkedChain w (s :: t :: rest) :=
  LinkedChain.cons s t rest link tail

/-- Two-hop linked projection (special case of the generic fold). -/
def projectionOfLinkedTwo
    {w : Nat} (s t : EliminationStep w) (link : StepLink w s t) :
    ProjectionInclusion w :=
  composeProjection s t link.bridge link.nest

/-- First step of a linked chain. -/
def LinkedChain.headStep {w : Nat} :
    {steps : List (EliminationStep w)} → LinkedChain w steps → EliminationStep w
  | _, .singleton s => s
  | _, .cons s _ _ _ _ => s

/-- On a chain whose list starts with `t`, the head step is `t`. -/
theorem LinkedChain.head_of_cons {w : Nat} {t : EliminationStep w}
    {rest : List (EliminationStep w)} (ch : LinkedChain w (t :: rest)) :
    LinkedChain.headStep ch = t := by
  cases ch with
  | singleton _ => rfl
  | cons _ _ _ _ _ => rfl

/-- Final residual variable set of a linked chain. -/
def LinkedChain.finalV {w : Nat} :
    {steps : List (EliminationStep w)} → LinkedChain w steps → List Nat
  | _, .singleton s => s.V_after
  | _, .cons _ _ _ _ tail => LinkedChain.finalV tail

/-- Final after-closure of a linked chain. -/
def LinkedChain.finalAfter {w : Nat} :
    {steps : List (EliminationStep w)} → LinkedChain w steps → WidthClosure w
  | _, .singleton s => s.after
  | _, .cons _ _ _ _ tail => LinkedChain.finalAfter tail

/-- Final residual vars nest inside the head step's residual vars. -/
theorem LinkedChain.finalV_nested_in_head {w : Nat} :
    {steps : List (EliminationStep w)} → (ch : LinkedChain w steps) →
    varsSubset (LinkedChain.finalV ch) (LinkedChain.headStep ch).V_after = true
  | _, .singleton s => varsSubset_self s.V_after
  | _, .cons _s t _rest link tail => by
    have ih : varsSubset (LinkedChain.finalV tail) t.V_after = true := by
      simpa [LinkedChain.head_of_cons tail] using LinkedChain.finalV_nested_in_head tail
    exact varsSubset_trans ih link.nest

/--
  Generic fold: compose an arbitrary linked elimination chain into one step.
  Returns a dependent package witnessing that `before`/`after`/`V_after` match
  the chain head and final residual (G2/G3 schedule skeleton).
-/
def eliminationOfLinkedChain {w : Nat} :
    {steps : List (EliminationStep w)} → (ch : LinkedChain w steps) →
    { e : EliminationStep w //
      e.before = (LinkedChain.headStep ch).before ∧
      e.after = LinkedChain.finalAfter ch ∧
      e.V_after = LinkedChain.finalV ch }
  | _, .singleton s =>
    ⟨s, by simp [LinkedChain.headStep, LinkedChain.finalAfter, LinkedChain.finalV]⟩
  | _, .cons s t rest link tail =>
    let ⟨et, het⟩ := eliminationOfLinkedChain tail
    have hBridge : s.after = et.before := by
      have : et.before = t.before := by
        simpa [LinkedChain.head_of_cons tail] using het.1
      rw [this, link.bridge]
    have hNest : varsSubset et.V_after s.V_after = true := by
      have hv : et.V_after = LinkedChain.finalV tail := het.2.2
      have hn : varsSubset (LinkedChain.finalV tail) t.V_after = true := by
        simpa [LinkedChain.head_of_cons tail] using LinkedChain.finalV_nested_in_head tail
      simpa [hv] using varsSubset_trans hn link.nest
    let e := composeElimination s et hBridge hNest
    ⟨e, by
      simp [e, composeElimination, LinkedChain.headStep, LinkedChain.finalAfter,
        LinkedChain.finalV, het.2.1, het.2.2]⟩

/-- Projection inclusion for an arbitrary linked chain (generic G0→R fold). -/
def projectionOfLinkedChain {w : Nat}
    {steps : List (EliminationStep w)} (ch : LinkedChain w steps) :
    ProjectionInclusion w :=
  (eliminationOfLinkedChain ch).1.toProjection

/-- Singleton chain projects as the single step. -/
theorem projectionOfLinkedChain_singleton {w : Nat} (s : EliminationStep w) :
    projectionOfLinkedChain (LinkedChain.singleton s) = s.toProjection :=
  rfl

/-- Two-hop chain agrees with `projectionOfLinkedTwo`. -/
theorem projectionOfLinkedChain_two {w : Nat}
    (s t : EliminationStep w) (link : StepLink w s t) :
    projectionOfLinkedChain (linkedChainCons link (LinkedChain.singleton t)) =
      projectionOfLinkedTwo s t link :=
  rfl

/-- Empty-clause freeness lifts along any linked chain. -/
theorem no_empty_of_linkedChain {w : Nat}
    {steps : List (EliminationStep w)} (ch : LinkedChain w steps)
    (hFinal : ¬ (LinkedChain.finalAfter ch).mem []) :
    ¬ (LinkedChain.headStep ch).before.mem [] := by
  let ⟨e, he⟩ := eliminationOfLinkedChain ch
  have hR : ¬ e.after.mem [] := by
    simpa [he.2.1] using hFinal
  have hg : ¬ e.before.mem [] :=
    no_empty_of_projection e.toProjection hR
  simpa [he.1] using hg

def composeElimination3
    {w : Nat}
    (s1 s2 s3 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true) :
    EliminationStep w :=
  composeElimination
    (composeElimination s1 s2 h12 n12)
    s3
    (by simpa [composeElimination] using h23)
    n23

def composeProjection3
    {w : Nat}
    (s1 s2 s3 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true) :
    ProjectionInclusion w :=
  (composeElimination3 s1 s2 s3 h12 h23 n12 n23).toProjection

/-- Four-hop composition. -/
def composeElimination4
    {w : Nat}
    (s1 s2 s3 s4 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (h34 : s3.after = s4.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true)
    (n34 : varsSubset s4.V_after s3.V_after = true) :
    EliminationStep w :=
  composeElimination
    (composeElimination3 s1 s2 s3 h12 h23 n12 n23)
    s4
    (by simpa [composeElimination3, composeElimination] using h34)
    n34

def composeProjection4
    {w : Nat}
    (s1 s2 s3 s4 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (h34 : s3.after = s4.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true)
    (n34 : varsSubset s4.V_after s3.V_after = true) :
    ProjectionInclusion w :=
  (composeElimination4 s1 s2 s3 s4 h12 h23 h34 n12 n23 n34).toProjection

/-- Five-hop composition. -/
def composeElimination5
    {w : Nat}
    (s1 s2 s3 s4 s5 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (h34 : s3.after = s4.before)
    (h45 : s4.after = s5.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true)
    (n34 : varsSubset s4.V_after s3.V_after = true)
    (n45 : varsSubset s5.V_after s4.V_after = true) :
    EliminationStep w :=
  composeElimination
    (composeElimination4 s1 s2 s3 s4 h12 h23 h34 n12 n23 n34)
    s5
    (by simpa [composeElimination4, composeElimination3, composeElimination] using h45)
    n45

def composeProjection5
    {w : Nat}
    (s1 s2 s3 s4 s5 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (h34 : s3.after = s4.before)
    (h45 : s4.after = s5.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true)
    (n34 : varsSubset s4.V_after s3.V_after = true)
    (n45 : varsSubset s5.V_after s4.V_after = true) :
    ProjectionInclusion w :=
  (composeElimination5 s1 s2 s3 s4 s5 h12 h23 h34 h45 n12 n23 n34 n45).toProjection

/-- Transitive composition of two projections when residual vars nest
    (`V₂ ⊆ V₁`) and the intermediate closures coincide. -/
def composeProjection_trans
    {w : Nat}
    (P1 P2 : ProjectionInclusion w)
    (hNest : varsSubset P2.Vres P1.Vres = true)
    (hBridge : P1.rClosure = P2.gClosure) :
    ProjectionInclusion w where
  gClosure := P1.gClosure
  rClosure := P2.rClosure
  Vres := P2.Vres
  holds := by
    intro C hG hsup
    have hV1 : supportedOn C P1.Vres = true :=
      supportedOn_of_subset hNest hsup
    have hMid : P1.rClosure.mem C := P1.holds C hG hV1
    have hG2 : P2.gClosure.mem C := by simpa [hBridge] using hMid
    exact P2.holds C hG2 hsup

/-- Six-hop composition (five composed hops + final step). -/
def composeProjection6
    {w : Nat}
    (s1 s2 s3 s4 s5 s6 : EliminationStep w)
    (h12 : s1.after = s2.before)
    (h23 : s2.after = s3.before)
    (h34 : s3.after = s4.before)
    (h45 : s4.after = s5.before)
    (h56 : s5.after = s6.before)
    (n12 : varsSubset s2.V_after s1.V_after = true)
    (n23 : varsSubset s3.V_after s2.V_after = true)
    (n34 : varsSubset s4.V_after s3.V_after = true)
    (n45 : varsSubset s5.V_after s4.V_after = true)
    (n56 : varsSubset s6.V_after s5.V_after = true) :
    ProjectionInclusion w :=
  composeProjection
    (composeElimination5 s1 s2 s3 s4 s5 h12 h23 h34 h45 n12 n23 n34 n45)
    s6
    h56
    n56

/-- Finite chain of elimination steps from G toward residual R. -/
structure EliminationChain (w : Nat) where
  steps : List (EliminationStep w)
  certDoc : String :=
    "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/PROOF_PROJECTION_E4.md"

/-- Empty elimination chain (vacuous). Prefer `unitsEliminationChain` in
    `ConcreteClosures.lean` for a nonempty identity-step instance. -/
def eliminationChain_example : EliminationChain 3 :=
  { steps := [] }

end PNPLab.Resolution
