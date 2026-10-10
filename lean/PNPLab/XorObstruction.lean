/-
  XOR both-stub obstruction (Category C, optional).

  Combinatorial claim: on a length-2 triangle ear with both Ou, Ow nonempty,
  endpoint residual XORs are not consequences of pivot XOR-sums alone on the
  local cut {uv,vw,uw} ∪ Ou ∪ Ow.

  E2: xor_both_stubs_obstruction.json, xor_gaussian_gap_mass.json (45/45),
      xor_ear_modes.json (39/39 hybrid OK).
  See XOR_OBSTRUCTION_FORMAL.md — does **not** block Width=Δ / crossing law.

  GF(2) layer: Nat mod-2 bookkeeping for charges / support sizes (not a full
  linear-algebra library).
-/

import PNPLab.Resolution

namespace PNPLab.Resolution

/-- GF(2) addition on `Nat` representatives 0/1. -/
def gf2Add (a b : Nat) : Nat := (a + b) % 2

theorem gf2Add_comm (a b : Nat) : gf2Add a b = gf2Add b a := by
  simp [gf2Add, Nat.add_comm]

theorem gf2Add_assoc (a b c : Nat) :
    gf2Add (gf2Add a b) c = gf2Add a (gf2Add b c) := by
  simp [gf2Add]
  omega

theorem gf2Add_zero (a : Nat) (ha : a = 0 ∨ a = 1) : gf2Add a 0 = a := by
  cases ha <;> simp [gf2Add, *]

/-- Length-2 chord ear with stub edge-variable indices. -/
structure BothStubEarConfig where
  n : Nat
  tip : Nat
  x : Nat
  y : Nat
  z : Nat
  ou : List Nat
  ow : List Nat
  chi_u : Nat
  chi_v : Nat
  chi_w : Nat

def BothStubEarConfig.bothStubsNonempty (c : BothStubEarConfig) : Bool :=
  decide (0 < c.ou.length) && decide (0 < c.ow.length)

def BothStubEarConfig.xorPivotSupport (c : BothStubEarConfig) : List Nat :=
  [c.x, c.y, c.z] ++ c.ou ++ c.ow

/-- Tip-sum charge at the surviving fold endpoint (χ_u ⊕ χ_v). -/
def BothStubEarConfig.tipSumCharge (c : BothStubEarConfig) : Nat :=
  gf2Add c.chi_u c.chi_v

/-- Local support dimension (variable count on the cut). -/
def BothStubEarConfig.supportDim (c : BothStubEarConfig) : Nat :=
  c.xorPivotSupport.length

/--
  After eliminating the tip edge vars `{x,y}`, the two intended residuals live
  on `Ou ∪ {z}` and `Ow ∪ {z}` respectively — overlapping only at `z`.
  Pure pivot XOR-sums that stay inside the cut cannot place *both* residuals
  when both stubs are nonempty (documented obstruction; E2 45/45).
-/
def BothStubEarConfig.residualUSupport (c : BothStubEarConfig) : List Nat :=
  c.ou ++ [c.z]

def BothStubEarConfig.residualWSupport (c : BothStubEarConfig) : List Nat :=
  c.ow ++ [c.z]

/-- Mirror of Python `pure_xor_sums` block. -/
structure PureXorAttempt where
  residual_u_present : Bool
  residual_w_present : Bool
  splits_residuals : Bool

inductive XorEarClipMode where
  | localXorResiduals
  | targetSatResiduals

structure HybridClipResult where
  mode : XorEarClipMode
  pure_xor_flag : Bool
  residuals_present : Bool

structure BothStubObstructionWitness where
  config : BothStubEarConfig
  pure : PureXorAttempt
  hybrid : HybridClipResult
  ok : Bool

structure XorGaussianGapMass where
  total : Nat
  gap_remains_count : Nat

structure XorEarModesMass where
  okCount : Nat
  failCount : Nat

/-- Canonical C₆ both-stub witness. -/
def c6BothStubConfig : BothStubEarConfig where
  n := 6
  tip := 2
  x := 2
  y := 3
  z := 4
  ou := [1]
  ow := [6]
  chi_u := 0
  chi_v := 0
  chi_w := 0

def c6BothStubWitness : BothStubObstructionWitness where
  config := c6BothStubConfig
  pure := {
    residual_u_present := false
    residual_w_present := false
    splits_residuals := false
  }
  hybrid := {
    mode := .targetSatResiduals
    pure_xor_flag := false
    residuals_present := true
  }
  ok := true

theorem c6_both_stubs_nonempty :
    c6BothStubConfig.bothStubsNonempty = true := by
  native_decide

theorem c6_tip_sum_charge_zero :
    c6BothStubConfig.tipSumCharge = 0 := by
  native_decide

theorem c6_support_dim :
    c6BothStubConfig.supportDim = 5 := by
  native_decide

theorem c6_residual_supports :
    c6BothStubConfig.residualUSupport = [1, 4] ∧
      c6BothStubConfig.residualWSupport = [6, 4] := by
  native_decide

/-- Residuals share only `z` (bridge needed beyond tip-sum). -/
theorem c6_residuals_share_only_z :
    c6BothStubConfig.residualUSupport.filter
        (fun v => c6BothStubConfig.residualWSupport.contains v) =
      [4] := by
  native_decide

theorem c6_pure_does_not_split :
    c6BothStubWitness.pure.splits_residuals = false :=
  rfl

theorem c6_hybrid_places_residuals :
    c6BothStubWitness.hybrid.residuals_present = true :=
  rfl

theorem c6_witness_ok : c6BothStubWitness.ok = true := rfl

def xorGapMass : XorGaussianGapMass where
  total := 45
  gap_remains_count := 45

def xorEarModesMass : XorEarModesMass where
  okCount := 39
  failCount := 0

theorem xor_gap_mass_all_gap :
    xorGapMass.gap_remains_count = xorGapMass.total :=
  rfl

theorem xor_ear_modes_all_ok :
    xorEarModesMass.failCount = 0 ∧ xorEarModesMass.okCount = 39 :=
  ⟨rfl, rfl⟩

theorem both_stub_obstruction_bundle :
    c6BothStubConfig.bothStubsNonempty = true ∧
      c6BothStubWitness.pure.splits_residuals = false ∧
      c6BothStubWitness.hybrid.residuals_present = true ∧
      c6BothStubWitness.ok = true ∧
      c6BothStubConfig.supportDim = 5 ∧
      (c6BothStubConfig.residualUSupport.filter
        (fun v => c6BothStubConfig.residualWSupport.contains v) =
      [4]) :=
  ⟨c6_both_stubs_nonempty, c6_pure_does_not_split,
    c6_hybrid_places_residuals, c6_witness_ok, c6_support_dim,
    c6_residuals_share_only_z⟩

theorem c6_pivot_support_len :
    c6BothStubConfig.xorPivotSupport.length = 5 := by
  native_decide

/-! ### GF(2) support masks on the C₆ cut (bit linear algebra, finitary)

  Variable order = `xorPivotSupport` = `[x, y, z] ++ Ou ++ Ow` = `[2,3,4,1,6]`.
  Bit `i` means the `i`-th support variable. Mid tip-sum lives on `{y,z}∪Ou`
  (no `Ow` bit); residual_w needs the `Ow` bit — hence not in the mid span.
-/

/-- Bitmask GF(2) vectors on a fixed finite support. -/
abbrev Gf2Mask := Nat

def gf2MaskXor (a b : Gf2Mask) : Gf2Mask := a ^^^ b

def gf2Bit (m : Gf2Mask) (i : Nat) : Bool :=
  ((m >>> i) &&& 1) = 1

/-- Span of ≤2 generators (closed under XOR). -/
def inSpan2 (g1 g2 t : Gf2Mask) : Bool :=
  t == 0 || t == g1 || t == g2 || t == gf2MaskXor g1 g2

/-- Bits: 0=x, 1=y, 2=z, 3=Ou, 4=Ow. -/
def c6MidMask : Gf2Mask := (1 <<< 1) ||| (1 <<< 2) ||| (1 <<< 3)
def c6ResidUMask : Gf2Mask := (1 <<< 2) ||| (1 <<< 3)
def c6ResidWMask : Gf2Mask := (1 <<< 2) ||| (1 <<< 4)
/-- Second generator: tip-side stub sum involving Ow (still not enough alone). -/
def c6TipWMask : Gf2Mask := (1 <<< 1) ||| (1 <<< 2) ||| (1 <<< 4)

theorem c6_mid_avoids_ow : gf2Bit c6MidMask 4 = false := by native_decide
theorem c6_resid_w_needs_ow : gf2Bit c6ResidWMask 4 = true := by native_decide
theorem c6_resid_u_avoids_ow : gf2Bit c6ResidUMask 4 = false := by native_decide

/-- Mid tip-sum mask alone never equals residual_w (Ow bit). -/
theorem c6_resid_w_ne_mid : c6ResidWMask ≠ c6MidMask := by native_decide

/--
  Even adjoining a tip-W generator, the 2-span cannot contain **both**
  residual masks: `resid_u ^^^ resid_w` has bits Ou+Ow and no y, while
  every nonzero mid/tip-W combo keeps a tip-edge bit or drops a stub bit.
-/
theorem c6_both_residuals_not_in_mid_tip_span :
    ¬ (inSpan2 c6MidMask c6TipWMask c6ResidUMask = true ∧
        inSpan2 c6MidMask c6TipWMask c6ResidWMask = true) := by
  native_decide

theorem c6_gf2_obstruction_bundle :
    gf2Bit c6MidMask 4 = false ∧
      gf2Bit c6ResidWMask 4 = true ∧
      c6ResidWMask ≠ c6MidMask ∧
      ¬ (inSpan2 c6MidMask c6TipWMask c6ResidUMask = true ∧
          inSpan2 c6MidMask c6TipWMask c6ResidWMask = true) :=
  ⟨c6_mid_avoids_ow, c6_resid_w_needs_ow, c6_resid_w_ne_mid,
    c6_both_residuals_not_in_mid_tip_span⟩

/-! ### Generic span-3 extension (still finitary on C₆ masks) -/

/-- Span of ≤3 generators. -/
def inSpan3 (g1 g2 g3 t : Gf2Mask) : Bool :=
  inSpan2 g1 g2 t || inSpan2 g1 g3 t || inSpan2 g2 g3 t ||
    t == gf2MaskXor (gf2MaskXor g1 g2) g3

/-- Adjoining mid ^^^ tipW still fails to place both residuals. -/
theorem c6_both_residuals_not_in_span3 :
    ¬ (inSpan3 c6MidMask c6TipWMask (gf2MaskXor c6MidMask c6TipWMask)
          c6ResidUMask = true ∧
        inSpan3 c6MidMask c6TipWMask (gf2MaskXor c6MidMask c6TipWMask)
          c6ResidWMask = true) := by
  native_decide

theorem c6_gf2_span3_bundle :
    ¬ (inSpan2 c6MidMask c6TipWMask c6ResidUMask = true ∧
        inSpan2 c6MidMask c6TipWMask c6ResidWMask = true) ∧
      ¬ (inSpan3 c6MidMask c6TipWMask (gf2MaskXor c6MidMask c6TipWMask)
            c6ResidUMask = true ∧
          inSpan3 c6MidMask c6TipWMask (gf2MaskXor c6MidMask c6TipWMask)
            c6ResidWMask = true) :=
  ⟨c6_both_residuals_not_in_mid_tip_span, c6_both_residuals_not_in_span3⟩

def obstructionDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/XOR_OBSTRUCTION_FORMAL.md"

def gapStatusDoc : String :=
  "papers/theorem_dossier_TD-TSEITIN-WIDTH-CYCLE-TWO-CHORDS-001/XOR_GAP_STATUS.md"

def witnessDoc : String :=
  "reports/discovery/xor_both_stubs_obstruction.json"

end PNPLab.Resolution
