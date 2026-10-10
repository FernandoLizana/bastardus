/-
  Rename → closed-bool transport (Category C / G5).

  Progress:
  1. `sameClause` algebra + identity list-eq pilot
  2. Identity / pack / alt resolve-commute Bool grids
  3. **Prop lift (OneFold):** `List.Perm` invariance of `k4ClosedUnder`
     ⇒ `ofoldRClosed` inherits `k4_closed_bool` without re-deciding the grid
-/

import PNPLab.MembershipTransport
import PNPLab.K4Width3
import PNPLab.CatalogIsoTransport
import PNPLab.AltResidualWitnesses

namespace PNPLab.Resolution

theorem sameClause_refl (C : Clause) : sameClause C C = true := by
  simp [sameClause]

theorem sameClause_symm {C D : Clause} (h : sameClause C D = true) :
    sameClause D C = true := by
  simp only [sameClause, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

theorem sameClause_contains {C D : Clause} {ℓ : Lit}
    (h : sameClause C D = true) (hℓ : C.contains ℓ = true) :
    D.contains ℓ = true := by
  simp only [sameClause, Bool.and_eq_true] at h
  exact (List.all_eq_true.mp h.1) ℓ ((List.contains_iff_mem).mp hℓ)

theorem sameClause_mem {C D : Clause} {ℓ : Lit}
    (h : sameClause C D = true) (hℓ : ℓ ∈ C) : ℓ ∈ D :=
  (List.contains_iff_mem).mp (sameClause_contains h ((List.contains_iff_mem).mpr hℓ))

/-- Identity rename pilot: list-equal to `k4Closed` inherits closed-bool. -/
theorem k4ClosedUnder_of_eq (S : List Clause) (h : S = k4Closed) :
    k4ClosedUnder S 3 k4Pivots = true := by
  simpa [h] using k4_closed_bool

theorem k4_closed_via_transport_id :
    k4ClosedUnder k4Closed 3 k4Pivots = true :=
  k4ClosedUnder_of_eq k4Closed rfl

/-! ### Prop lift: `k4ClosedUnder` invariant under `List.Perm` -/

theorem perm_all_eq {α : Type} {l₁ l₂ : List α} (h : List.Perm l₁ l₂)
    (p : α → Bool) : l₁.all p = l₂.all p := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [List.all_cons, ih]
  | swap =>
    simp [List.all_cons]
    simp [Bool.and_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem perm_contains_eq {α : Type} [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} (h : List.Perm l₁ l₂) (x : α) :
    l₁.contains x = l₂.contains x := by
  simp [h.mem_iff]

/-- The per-pivot closedness predicate depends on the clause list only via `contains`. -/
def closedPred (S : List Clause) (w : Nat) (p : Lit) (C D : Clause) : Bool :=
  match resolveOriented C D p with
  | none => true
  | some R => decide (w < clauseWidth R) || S.contains R

theorem closedPred_of_perm {S T : List Clause} {w : Nat} {p : Lit}
    (h : List.Perm S T) (C D : Clause) :
    closedPred S w p C D = closedPred T w p C D := by
  unfold closedPred
  cases hR : resolveOriented C D p with
  | none => rfl
  | some R =>
    change
      (decide (w < clauseWidth R) || S.contains R) =
        (decide (w < clauseWidth R) || T.contains R)
    rw [perm_contains_eq h R]

theorem k4ClosedUnder_eq_closedPred (S : List Clause) (w : Nat) (pivots : List Lit) :
    k4ClosedUnder S w pivots =
      pivots.all fun p => S.all fun C => S.all fun D => closedPred S w p C D :=
  rfl

theorem k4ClosedUnder_of_perm {S T : List Clause} {w : Nat} {pivots : List Lit}
    (h : List.Perm S T) :
    k4ClosedUnder S w pivots = k4ClosedUnder T w pivots := by
  rw [k4ClosedUnder_eq_closedPred, k4ClosedUnder_eq_closedPred]
  refine congrArg (fun f : Lit → Bool => pivots.all f) ?_
  funext p
  have hP : ∀ C D, closedPred S w p C D = closedPred T w p C D :=
    fun C D => closedPred_of_perm h C D
  have hInner : ∀ C,
      (S.all fun D => closedPred S w p C D) =
        (T.all fun D => closedPred T w p C D) := by
    intro C
    have h1 := perm_all_eq h (fun D => closedPred S w p C D)
    have h2 :
        (T.all fun D => closedPred S w p C D) =
          (T.all fun D => closedPred T w p C D) := by
      refine congrArg (fun f : Clause → Bool => T.all f) ?_
      funext D
      exact hP C D
    exact h1.trans h2
  have hOuter1 :
      (S.all fun C => S.all fun D => closedPred S w p C D) =
        (S.all fun C => T.all fun D => closedPred T w p C D) := by
    refine congrArg (fun f : Clause → Bool => S.all f) ?_
    funext C
    exact hInner C
  have hOuter2 :=
    perm_all_eq h (fun C => T.all fun D => closedPred T w p C D)
  exact hOuter1.trans hOuter2

/-- OneFold residual is a permutation of the K₄ template (exact clauses, reordered). -/
theorem ofoldRClosed_perm_k4 : List.Perm ofoldRClosed k4Closed := by
  native_decide

/-- **Prop lift:** OneFold closed-bool via perm transport from `k4_closed_bool`. -/
theorem ofoldR_closed_via_perm :
    k4ClosedUnder ofoldRClosed 3 k4Pivots = true := by
  rw [k4ClosedUnder_of_perm ofoldRClosed_perm_k4]
  exact k4_closed_bool

/-- Clause lists equal as `sameClause` sets (order-insensitive). -/
def clauseListSetEq (S T : List Clause) : Bool :=
  S.all (fun C => T.any (sameClause C)) &&
    T.all (fun C => S.any (sameClause C))

theorem ofoldR_setEq_k4 :
    clauseListSetEq ofoldRClosed k4Closed = true := by
  native_decide

def identityFixesClause (C : Clause) : Bool :=
  match identityRename.renameClause C with
  | some C' => decide (C' = C)
  | none => false

theorem identity_fixes_k4Closed :
    k4Closed.all identityFixesClause = true := by
  native_decide

def resolveCommuteIdentity (C D : Clause) (p : Lit) : Bool :=
  match resolveOriented C D p with
  | none =>
    match identityRename.renameClause C, identityRename.renameClause D,
        identityRename.renameLit p with
    | some C', some D', some p' =>
      match resolveOriented C' D' p' with
      | none => true
      | some _ => false
    | _, _, _ => true
  | some R =>
    match identityRename.renameClause C, identityRename.renameClause D,
        identityRename.renameLit p, identityRename.renameClause R with
    | some C', some D', some p', some R' =>
      match resolveOriented C' D' p' with
      | some R2 => sameClause R2 R' && sameClause R R'
      | none => false
    | _, _, _, _ => false

def identityResolveCommutesOnK4 : Bool :=
  k4Pivots.all fun p =>
    k4Closed.all fun C =>
      k4Closed.all fun D => resolveCommuteIdentity C D p

theorem identityResolveCommutesOnK4_true :
    identityResolveCommutesOnK4 = true := by
  native_decide

def resolveCommuteRename (r : VarRename) (C D : Clause) (p : Lit) : Bool :=
  match resolveOriented C D p with
  | none =>
    match r.renameClause C, r.renameClause D, r.renameLit p with
    | some C', some D', some p' =>
      match resolveOriented C' D' p' with
      | none => true
      | some _ => false
    | _, _, _ => true
  | some R =>
    match r.renameClause C, r.renameClause D, r.renameLit p, r.renameClause R with
    | some C', some D', some p', some R' =>
      match resolveOriented C' D' p' with
      | some R2 => sameClause R2 R'
      | none => false
    | _, _, _, _ => false

def resolveCommutesOn (r : VarRename) (S : List Clause) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D => resolveCommuteRename r C D p

theorem identity_commutes_on_k4_via_generic :
    resolveCommutesOn identityRename k4Closed k4Pivots = true := by
  native_decide

theorem mfTopology_resolve_commutes :
    resolveCommutesOn mfTopologyRename mfRClosed k4Pivots = true := by
  native_decide

theorem tfTopology_resolve_commutes :
    resolveCommutesOn tfTopologyRename tfRClosed k4Pivots = true := by
  native_decide

theorem ffTopology_resolve_commutes :
    resolveCommutesOn ffTopologyRename ffRClosed k4Pivots = true := by
  native_decide

theorem xfTopology_resolve_commutes :
    resolveCommutesOn xfTopologyRename xfRClosed k4Pivots = true := by
  native_decide

theorem sfTopology_resolve_commutes :
    resolveCommutesOn sfTopologyRename sfRClosed k4Pivots = true := by
  native_decide

theorem all_pack_topology_resolve_commutes :
    resolveCommutesOn mfTopologyRename mfRClosed k4Pivots = true ∧
      resolveCommutesOn tfTopologyRename tfRClosed k4Pivots = true ∧
      resolveCommutesOn ffTopologyRename ffRClosed k4Pivots = true ∧
      resolveCommutesOn xfTopologyRename xfRClosed k4Pivots = true ∧
      resolveCommutesOn sfTopologyRename sfRClosed k4Pivots = true :=
  ⟨mfTopology_resolve_commutes, tfTopology_resolve_commutes,
    ffTopology_resolve_commutes, xfTopology_resolve_commutes,
    sfTopology_resolve_commutes⟩

theorem alt1Topology_resolve_commutes :
    resolveCommutesOn alt1TopologyRename alt1RClosed k4Pivots = true := by
  native_decide

theorem alt2Topology_resolve_commutes :
    resolveCommutesOn alt2TopologyRename alt2RClosed k4Pivots = true := by
  native_decide

theorem alt3Topology_resolve_commutes :
    resolveCommutesOn alt3TopologyRename alt3RClosed k4Pivots = true := by
  native_decide

theorem alt4Topology_resolve_commutes :
    resolveCommutesOn alt4TopologyRename alt4RClosed k4Pivots = true := by
  native_decide

theorem alt5Topology_resolve_commutes :
    resolveCommutesOn alt5TopologyRename alt5RClosed k4Pivots = true := by
  native_decide

theorem alt6Topology_resolve_commutes :
    resolveCommutesOn alt6TopologyRename alt6RClosed k4Pivots = true := by
  native_decide

theorem all_alt_topology_resolve_commutes :
    resolveCommutesOn alt1TopologyRename alt1RClosed k4Pivots = true ∧
      resolveCommutesOn alt2TopologyRename alt2RClosed k4Pivots = true ∧
      resolveCommutesOn alt3TopologyRename alt3RClosed k4Pivots = true ∧
      resolveCommutesOn alt4TopologyRename alt4RClosed k4Pivots = true ∧
      resolveCommutesOn alt5TopologyRename alt5RClosed k4Pivots = true ∧
      resolveCommutesOn alt6TopologyRename alt6RClosed k4Pivots = true :=
  ⟨alt1Topology_resolve_commutes, alt2Topology_resolve_commutes,
    alt3Topology_resolve_commutes, alt4Topology_resolve_commutes,
    alt5Topology_resolve_commutes, alt6Topology_resolve_commutes⟩

/-! ### VarRename list map + alt1 Prop pullback -/

/-- Map every clause; fail if any rename fails. -/
def renameList (r : VarRename) (S : List Clause) : Option (List Clause) :=
  S.foldl (fun acc C =>
    match acc, r.renameClause C with
    | none, _ => none
    | some _, none => none
    | some L, some C' => some (L ++ [C']))
    (some ([] : List Clause))

/-- Swap src ↔ dst (edge inverse). -/
def VarRename.inverse (r : VarRename) : VarRename where
  src := r.dst
  dst := r.src
  src_len := r.dst_len
  dst_len := r.src_len

/-- Exact resolvent equality under rename (stronger than `sameClause`). -/
def exactResolveCommute (r : VarRename) (S : List Clause) (pivots : List Lit) : Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R =>
          match r.renameClause C, r.renameClause D, r.renameLit p, r.renameClause R with
          | some C', some D', some p', some R' =>
            match resolveOriented C' D' p' with
            | some R2 => decide (R2 = R')
            | none => false
          | _, _, _, _ => false

theorem exact_commute_point
    {r : VarRename} {S : List Clause} {pivots : List Lit}
    (h : exactResolveCommute r S pivots = true)
    {C D : Clause} {p : Lit}
    (hC : C ∈ S) (hD : D ∈ S) (hp : p ∈ pivots)
    {R : Clause} (hRes : resolveOriented C D p = some R) :
    ∃ C' D' p' R',
      r.renameClause C = some C' ∧
        r.renameClause D = some D' ∧
        r.renameLit p = some p' ∧
        r.renameClause R = some R' ∧
        resolveOriented C' D' p' = some R' := by
  have hpt0 :=
    (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp h) p hp)) C hC)) D hD
  simp only [hRes] at hpt0
  cases hC' : r.renameClause C with
  | none => simp [hC'] at hpt0
  | some C' =>
    cases hD' : r.renameClause D with
    | none => simp [hC', hD'] at hpt0
    | some D' =>
      cases hp' : r.renameLit p with
      | none => simp [hC', hD', hp'] at hpt0
      | some p' =>
        cases hR' : r.renameClause R with
        | none => simp [hC', hD', hp', hR'] at hpt0
        | some R' =>
          simp [hC', hD', hp', hR'] at hpt0
          cases hR2 : resolveOriented C' D' p' with
          | none => simp [hR2] at hpt0
          | some R2 =>
            simp [hR2] at hpt0
            -- `cases hC' : renameClause C` rewrites the goal equations to `rfl`.
            have hEq : R2 = R' := hpt0
            exact ⟨C', D', p', R', rfl, rfl, rfl, rfl, hEq ▸ hR2⟩

def alt1Renamed : List Clause :=
  match renameList alt1TopologyRename alt1RClosed with
  | some L => L
  | none => []

theorem alt1_exact_resolve_commute :
    exactResolveCommute alt1TopologyRename alt1RClosed k4Pivots = true := by
  native_decide

theorem alt1_renameList_some :
    renameList alt1TopologyRename alt1RClosed = some alt1Renamed := by
  native_decide

theorem alt1Renamed_perm_k4 : List.Perm alt1Renamed k4Closed := by
  native_decide

theorem alt1_roundtrip :
    renameList alt1TopologyRename.inverse alt1Renamed = some alt1RClosed := by
  native_decide

theorem alt1Renamed_closed :
    k4ClosedUnder alt1Renamed 3 k4Pivots = true := by
  rw [k4ClosedUnder_of_perm alt1Renamed_perm_k4]
  exact k4_closed_bool

theorem alt1_rename_mem
    {C C' : Clause}
    (hC : C ∈ alt1RClosed) (hC' : alt1TopologyRename.renameClause C = some C') :
    C' ∈ alt1Renamed := by
  have h : (alt1RClosed.all fun A =>
      match alt1TopologyRename.renameClause A with
      | some A' => decide (A' ∈ alt1Renamed)
      | none => false) = true := by
    native_decide
  have := (List.all_eq_true.mp h) C hC
  simpa [hC'] using this

theorem alt1_inv_rename_mem
    {R' R : Clause}
    (hR' : R' ∈ alt1Renamed)
    (hR : alt1TopologyRename.inverse.renameClause R' = some R) :
    R ∈ alt1RClosed := by
  have h : (alt1Renamed.all fun A' =>
      match alt1TopologyRename.inverse.renameClause A' with
      | some A => decide (A ∈ alt1RClosed)
      | none => false) = true := by
    native_decide
  have := (List.all_eq_true.mp h) R' hR'
  simpa [hR] using this

theorem alt1_pivot_rename_closed :
    (k4Pivots.all fun p =>
      match alt1TopologyRename.renameLit p with
      | none => true
      | some p' => decide (p' ∈ k4Pivots)) = true := by
  native_decide

theorem alt1_resolvent_roundtrip :
    (k4Pivots.all fun p =>
      alt1RClosed.all fun C =>
        alt1RClosed.all fun D =>
          match resolveOriented C D p with
          | none => true
          | some R =>
            match alt1TopologyRename.renameClause R with
            | none => false
            | some R' =>
              decide (alt1TopologyRename.inverse.renameClause R' = some R)) = true := by
  native_decide

theorem alt1_renameLit_mem
    {p p' : Lit} (hp : p ∈ k4Pivots)
    (hp' : alt1TopologyRename.renameLit p = some p') :
    p' ∈ k4Pivots := by
  have := (List.all_eq_true.mp alt1_pivot_rename_closed) p hp
  simpa [hp'] using this

theorem alt1_resolvent_width :
    (k4Pivots.all fun p =>
      alt1RClosed.all fun C =>
        alt1RClosed.all fun D =>
          match resolveOriented C D p with
          | none => true
          | some R =>
            match alt1TopologyRename.renameClause R with
            | none => false
            | some R' => decide (clauseWidth R' = clauseWidth R)) = true := by
  native_decide

/-- **Prop pullback:** alt1 closed-bool via exact rename → Perm(k4) → `k4_closed_bool`. -/
theorem alt1R_closed_via_rename_transport :
    k4ClosedUnder alt1RClosed 3 k4Pivots = true := by
  refine (List.all_eq_true.mpr) fun p hp =>
    (List.all_eq_true.mpr) fun C hC =>
      (List.all_eq_true.mpr) fun D hD => ?_
  cases hRes : resolveOriented C D p with
  | none => rfl
  | some R =>
    obtain ⟨C', D', p', R', hC', hD', hp', hR', hRes'⟩ :=
      exact_commute_point alt1_exact_resolve_commute hC hD hp hRes
    have hC'mem := alt1_rename_mem hC hC'
    have hD'mem := alt1_rename_mem hD hD'
    have hp'mem := alt1_renameLit_mem hp hp'
    have hrt :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp
          ((List.all_eq_true.mp alt1_resolvent_roundtrip) p hp)) C hC)) D hD
    simp only [hRes, hR'] at hrt
    have hInv : alt1TopologyRename.inverse.renameClause R' = some R :=
      of_decide_eq_true hrt
    have hwEq :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp
          ((List.all_eq_true.mp alt1_resolvent_width) p hp)) C hC)) D hD
    simp only [hRes, hR'] at hwEq
    have hWidthEq : clauseWidth R' = clauseWidth R := of_decide_eq_true hwEq
    cases hw : decide (3 < clauseWidth R) with
    | true =>
      simp only [hw, Bool.true_or]
    | false =>
      have hwLe : clauseWidth R ≤ 3 := Nat.not_lt.mp (of_decide_eq_false hw)
      have hwLe' : clauseWidth R' ≤ 3 := by simpa [hWidthEq] using hwLe
      have hR'mem : R' ∈ alt1Renamed :=
        k4_mem_of_closed alt1Renamed_closed hC'mem hD'mem hRes' hwLe' hp'mem
      have hRmem := alt1_inv_rename_mem hR'mem hInv
      simp only [hw, Bool.false_or]
      exact (List.contains_iff_mem).mpr hRmem

structure RenameClosedTransportGoal where
  topology : Bool
  topology_ok : topology = true
  identityCommute : identityResolveCommutesOnK4 = true := identityResolveCommutesOnK4_true
  ofoldPermLift : k4ClosedUnder ofoldRClosed 3 k4Pivots = true := ofoldR_closed_via_perm
  alt1RenameLift : k4ClosedUnder alt1RClosed 3 k4Pivots = true :=
    alt1R_closed_via_rename_transport
  resolveCommutesDoc : String :=
    "ofold via Perm; packs/alts via exact or norm-rename Prop pullback (see RenameClosedTransportNorm)"
  targetDoc : String :=
    "Mathlib IsOuterplanar; parametric Closure3 synthesis beyond pack catalog"

def renameClosedTransportOpenDoc : String :=
  "ofoldR via List.Perm; packs mf..sf + alts 1..6 via exact/norm VarRename pullback; " ++
  "Mathlib IsOuterplanar still open."

theorem rename_closed_identity_bundle :
    List.Perm ofoldRClosed k4Closed ∧
      k4ClosedUnder ofoldRClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt1RClosed 3 k4Pivots = true ∧
      identityResolveCommutesOnK4 = true :=
  ⟨ofoldRClosed_perm_k4, ofoldR_closed_via_perm,
    alt1R_closed_via_rename_transport, identityResolveCommutesOnK4_true⟩

end PNPLab.Resolution
