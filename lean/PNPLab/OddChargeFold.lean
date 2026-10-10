/-
  Odd-charge GF(2) invariant under deg-2 tip fold (Category C / G6).

  Mirrors Python `fold_deg2_tip`:
    χ'_foldInto := χ_foldInto ⊕ χ_tip
    delete tip

  Over GF(2), replacing `a` by `a ⊕ b` then erasing `b` leaves the total
  sum unchanged.  Hence odd parity is preserved.
-/

import PNPLab.XorObstruction
import PNPLab.OuterplanarFoldPreservation

namespace PNPLab.Outerplanar

open Resolution
open SimpleGraph

/-- GF(2) sum of a list (entries reduced mod 2). -/
def gf2Sum : List Nat → Nat
  | [] => 0
  | x :: xs => gf2Add (x % 2) (gf2Sum xs)

theorem gf2Sum_cons (x : Nat) (xs : List Nat) :
    gf2Sum (x :: xs) = gf2Add (x % 2) (gf2Sum xs) :=
  rfl

theorem gf2Sum_is_bit (xs : List Nat) : gf2Sum xs = 0 ∨ gf2Sum xs = 1 := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [gf2Sum_cons, gf2Add]
    omega

theorem gf2Add_self (a : Nat) : gf2Add a a = 0 := by
  simp [gf2Add]; omega

theorem gf2Add_cancel_left (a b : Nat) : gf2Add a (gf2Add a b) = b % 2 := by
  simp [gf2Add]; omega

theorem gf2Add_cancel_right (a b : Nat) : gf2Add (gf2Add a b) b = a % 2 := by
  simp [gf2Add]; omega

/-- Get-elem with default 0. -/
def listGet (xs : List Nat) (i : Nat) : Nat :=
  xs[i]?.getD 0

theorem listGet_cons_zero (x : Nat) (xs : List Nat) :
    listGet (x :: xs) 0 = x := by
  simp [listGet]

theorem listGet_cons_succ (x : Nat) (xs : List Nat) (i : Nat)
    (hi : i < xs.length) :
    listGet (x :: xs) (i + 1) = listGet xs i := by
  simp [listGet, List.getElem?_eq_getElem hi]

/-- Replacing index `i` by `y` xors out the old bit and xors in the new bit. -/
theorem gf2Sum_set (xs : List Nat) (i : Nat) (y : Nat) (hi : i < xs.length) :
    gf2Sum (xs.set i y) =
      gf2Add (gf2Sum xs) (gf2Add (listGet xs i % 2) (y % 2)) := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    match i with
    | 0 =>
      simp [List.set, gf2Sum_cons, listGet_cons_zero, gf2Add]
      have := gf2Sum_is_bit xs
      omega
    | i' + 1 =>
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      simp [List.set, gf2Sum_cons]
      rw [listGet_cons_succ x xs i' hi']
      have ih' := ih i' hi'
      rw [ih']
      simp [gf2Add]
      have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hs := gf2Sum_is_bit xs
      have hg := gf2Sum_is_bit (xs.set i' y)
      omega

/-- Erasing index `j` xors out that bit. -/
theorem gf2Sum_eraseIdx (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    gf2Sum (xs.eraseIdx j) = gf2Add (gf2Sum xs) (listGet xs j % 2) := by
  induction xs generalizing j with
  | nil => cases hj
  | cons x xs ih =>
    match j with
    | 0 =>
      simp [List.eraseIdx, gf2Sum_cons, listGet_cons_zero]
      -- gf2Sum xs = gf2Add (gf2Add (x%2) (gf2Sum xs)) (x%2)
      have hs := gf2Sum_is_bit xs
      simp [gf2Add]
      omega
    | j' + 1 =>
      have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
      simp [List.eraseIdx, gf2Sum_cons]
      rw [listGet_cons_succ x xs j' hj']
      have ih' := ih j' hj'
      rw [ih']
      simp [gf2Add]
      have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hs := gf2Sum_is_bit xs
      omega

/-- After `set` at `foldInto`, tip's value is unchanged when indices differ. -/
theorem listGet_set_ne (xs : List Nat) (foldInto tip : Nat) (y : Nat)
    (_hf : foldInto < xs.length) (ht : tip < xs.length) (hne : foldInto ≠ tip) :
    listGet (xs.set foldInto y) tip = listGet xs tip := by
  have hlen : tip < (xs.set foldInto y).length := by simpa [List.length_set] using ht
  simp [listGet, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hlen]
  exact List.getElem_set_ne (l := xs) (i := foldInto) (j := tip) hne (a := y) hlen

/-- Core invariant: absorb tip into foldInto, then erase tip — GF(2) sum unchanged. -/
theorem gf2Sum_foldTip (xs : List Nat) (foldInto tip : Nat)
    (hf : foldInto < xs.length) (ht : tip < xs.length) (hne : foldInto ≠ tip) :
    gf2Sum
        ((xs.set foldInto
          (gf2Add (listGet xs foldInto % 2) (listGet xs tip % 2))).eraseIdx tip) =
      gf2Sum xs := by
  set a := listGet xs foldInto % 2
  set b := listGet xs tip % 2
  set y := gf2Add a b
  have hlen : (xs.set foldInto y).length = xs.length := List.length_set
  have ht' : tip < (xs.set foldInto y).length := by simpa [hlen] using ht
  have htip :
      listGet (xs.set foldInto y) tip % 2 = b := by
    have := listGet_set_ne xs foldInto tip y hf ht hne
    simp [b, this]
  rw [gf2Sum_eraseIdx _ tip ht']
  rw [htip]
  rw [gf2Sum_set xs foldInto y hf]
  -- After set: S ⊕ a ⊕ (y%2).  y = gf2Add a b so y % 2 = (a+b)%2.
  have hy : y % 2 = gf2Add a b := by
    simp [y, gf2Add]
  -- a,b ∈ {0,1}
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  have hs := gf2Sum_is_bit xs
  -- S ⊕ a ⊕ (a⊕b) ⊕ b = S
  simp [hy, gf2Add, a, b] at *
  omega

/-- A finitary charge vector with odd GF(2) sum. -/
structure OddChargeVec where
  charges : List Nat
  odd : gf2Sum charges = 1

/-- Absorb tip charge into foldInto and delete the tip. -/
def OddChargeVec.foldTip (c : OddChargeVec) (foldInto tip : Nat)
    (hf : foldInto < c.charges.length) (ht : tip < c.charges.length)
    (hne : foldInto ≠ tip) : OddChargeVec where
  charges :=
    (c.charges.set foldInto
      (gf2Add (listGet c.charges foldInto % 2)
        (listGet c.charges tip % 2))).eraseIdx tip
  odd := by
    have := gf2Sum_foldTip c.charges foldInto tip hf ht hne
    simpa [this] using c.odd

theorem OddChargeVec.foldTip_preserves_odd (c : OddChargeVec)
    (foldInto tip : Nat)
    (hf : foldInto < c.charges.length) (ht : tip < c.charges.length)
    (hne : foldInto ≠ tip) :
    gf2Sum (c.foldTip foldInto tip hf ht hne).charges = 1 :=
  (c.foldTip foldInto tip hf ht hne).odd

theorem OddChargeVec.foldTip_length (c : OddChargeVec)
    (foldInto tip : Nat)
    (hf : foldInto < c.charges.length) (ht : tip < c.charges.length)
    (hne : foldInto ≠ tip) :
    (c.foldTip foldInto tip hf ht hne).charges.length = c.charges.length - 1 := by
  simp [OddChargeVec.foldTip, List.length_eraseIdx, List.length_set]
  omega

/-- Unit odd charge on `n` vertices (charge 1 at index 0). -/
def unitOddCharge (n : Nat) (hn : 0 < n) : OddChargeVec where
  charges := 1 :: List.replicate (n - 1) 0
  odd := by
    match n with
    | 0 => cases hn
    | n' + 1 =>
      simp [gf2Sum_cons, gf2Add]
      induction n' with
      | zero => simp [gf2Sum]
      | succ k ih =>
        simp [List.replicate_succ, gf2Sum_cons, gf2Add] at *
        exact ih

/-- Concrete: fold tip 1 into 0 on `[1,0,0]` preserves oddness → `[1,0]`. -/
theorem foldTip_example :
    let c : OddChargeVec := ⟨[1, 0, 0], by native_decide⟩
    gf2Sum (c.foldTip 0 1 (by decide) (by decide) (by decide)).charges = 1 ∧
      (c.foldTip 0 1 (by decide) (by decide) (by decide)).charges = [1, 0] := by
  native_decide

/-- Absorbing a tip of charge 1 into a 0 flips the survivor and keeps oddness. -/
theorem foldTip_flip_example :
    let c : OddChargeVec := ⟨[0, 1, 0], by native_decide⟩
    (c.foldTip 0 1 (by decide) (by decide) (by decide)).charges = [1, 0] ∧
      gf2Sum (c.foldTip 0 1 (by decide) (by decide) (by decide)).charges = 1 := by
  native_decide

/-- Bridge: graph fold preservation can carry a real odd-charge witness. -/
structure GraphFoldPreservationOdd {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    extends GraphFoldPreservation G where
  charges : OddChargeVec
  charges_len : charges.charges.length = Fintype.card V

theorem GraphFoldPreservationOdd.charges_after_card
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p : GraphFoldPreservationOdd G)
    (foldInto tip : Nat)
    (hf : foldInto < p.charges.charges.length)
    (ht : tip < p.charges.charges.length)
    (hne : foldInto ≠ tip) :
    (p.charges.foldTip foldInto tip hf ht hne).charges.length =
      Fintype.card V - 1 := by
  have := p.charges.foldTip_length foldInto tip hf ht hne
  simpa [p.charges_len] using this

def oddChargeFoldDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-OUTERPLANAR-001/TERMINATION.md"

end PNPLab.Outerplanar
