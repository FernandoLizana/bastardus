/-
  Norm-aware VarRename closed-bool pullback (Category C / G5).

  Packs mf..sf and alts 2..6 rename to clauses that need `normClause` before
  they match `k4Closed` exactly.  This module packages that path:

  renameClauseNorm → renameListNorm → Perm(k4) → pullback `k4ClosedUnder`.
-/

import PNPLab.RenameClosedTransport

namespace PNPLab.Resolution

/-- Rename then normalize (canonical clause form). -/
def renameClauseNorm (r : VarRename) (C : Clause) : Option Clause :=
  match r.renameClause C with
  | some C' => some (normClause C')
  | none => none

def renameListNorm : VarRename → List Clause → Option (List Clause)
  | _, [] => some []
  | r, C :: rest =>
    match renameClauseNorm r C, renameListNorm r rest with
    | some C', some L => some (C' :: L)
    | _, _ => none

theorem renameListNorm_mem
    {r : VarRename} {S L : List Clause} {C C' : Clause}
    (hRen : renameListNorm r S = some L)
    (hC : C ∈ S) (hC' : renameClauseNorm r C = some C') :
    C' ∈ L := by
  induction S generalizing L with
  | nil => cases hC
  | cons A rest ih =>
    cases hC with
    | head =>
      cases hRest : renameListNorm r rest with
      | none => simp [renameListNorm, hC', hRest] at hRen
      | some Lr =>
        simp [renameListNorm, hC', hRest] at hRen
        cases hRen
        exact List.mem_cons_self
    | tail _ hTail =>
      cases hA : renameClauseNorm r A with
      | none => simp [renameListNorm, hA] at hRen
      | some A' =>
        cases hRest : renameListNorm r rest with
        | none => simp [renameListNorm, hA, hRest] at hRen
        | some Lr =>
          simp [renameListNorm, hA, hRest] at hRen
          cases hRen
          exact List.mem_cons_of_mem _ (ih hRest hTail)

/-- Exact resolvent equality after normalizing renamed clauses. -/
def exactResolveCommuteNorm (r : VarRename) (S : List Clause) (pivots : List Lit) :
    Bool :=
  pivots.all fun p =>
    S.all fun C =>
      S.all fun D =>
        match resolveOriented C D p with
        | none => true
        | some R =>
          match renameClauseNorm r C, renameClauseNorm r D, r.renameLit p,
              renameClauseNorm r R with
          | some C', some D', some p', some R' =>
            match resolveOriented C' D' p' with
            | some R2 => decide (R2 = R')
            | none => false
          | _, _, _, _ => false

theorem exact_commute_norm_point
    {r : VarRename} {S : List Clause} {pivots : List Lit}
    (h : exactResolveCommuteNorm r S pivots = true)
    {C D : Clause} {p : Lit}
    (hC : C ∈ S) (hD : D ∈ S) (hp : p ∈ pivots)
    {R : Clause} (hRes : resolveOriented C D p = some R) :
    ∃ C' D' p' R',
      renameClauseNorm r C = some C' ∧
        renameClauseNorm r D = some D' ∧
        r.renameLit p = some p' ∧
        renameClauseNorm r R = some R' ∧
        resolveOriented C' D' p' = some R' := by
  have hpt0 :=
    (List.all_eq_true.mp
      ((List.all_eq_true.mp
        ((List.all_eq_true.mp h) p hp)) C hC)) D hD
  simp only [hRes] at hpt0
  cases hCren : renameClauseNorm r C with
  | none => simp [hCren] at hpt0
  | some C' =>
    cases hDren : renameClauseNorm r D with
    | none => simp [hCren, hDren] at hpt0
    | some D' =>
      cases hpren : r.renameLit p with
      | none => simp [hCren, hDren, hpren] at hpt0
      | some p' =>
        cases hRren : renameClauseNorm r R with
        | none => simp [hCren, hDren, hpren, hRren] at hpt0
        | some R' =>
          simp [hCren, hDren, hpren, hRren] at hpt0
          cases hR2 : resolveOriented C' D' p' with
          | none => simp [hR2] at hpt0
          | some R2 =>
            simp [hR2] at hpt0
            exact ⟨C', D', p', R', rfl, rfl, rfl, rfl, hpt0 ▸ hR2⟩

/-- Bundle of finite witnesses for a norm-rename pullback instance. -/
structure ExactNormRenameWitness where
  r : VarRename
  S : List Clause
  L : List Clause
  exact : exactResolveCommuteNorm r S k4Pivots = true
  renSome : renameListNorm r S = some L
  perm : List.Perm L k4Closed
  renameMemOK :
    (S.all fun A =>
      match renameClauseNorm r A with
      | some A' => decide (A' ∈ L)
      | none => false) = true
  invMemOK :
    (L.all fun A' =>
      match renameClauseNorm r.inverse A' with
      | some A => decide (A ∈ S)
      | none => false) = true
  pivOK :
    (k4Pivots.all fun p =>
      match r.renameLit p with
      | none => true
      | some p' => decide (p' ∈ k4Pivots)) = true
  resRoundOK :
    (k4Pivots.all fun p =>
      S.all fun C =>
        S.all fun D =>
          match resolveOriented C D p with
          | none => true
          | some R =>
            match renameClauseNorm r R with
            | none => false
            | some R' =>
              decide (renameClauseNorm r.inverse R' = some R)) = true
  resWidthOK :
    (k4Pivots.all fun p =>
      S.all fun C =>
        S.all fun D =>
          match resolveOriented C D p with
          | none => true
          | some R =>
            match renameClauseNorm r R with
            | none => false
            | some R' => decide (clauseWidth R' = clauseWidth R)) = true

theorem ExactNormRenameWitness.L_closed (w : ExactNormRenameWitness) :
    k4ClosedUnder w.L 3 k4Pivots = true := by
  rw [k4ClosedUnder_of_perm w.perm]
  exact k4_closed_bool

theorem ExactNormRenameWitness.rename_mem
    (w : ExactNormRenameWitness) {C C' : Clause}
    (hC : C ∈ w.S) (hC' : renameClauseNorm w.r C = some C') :
    C' ∈ w.L := by
  have := (List.all_eq_true.mp w.renameMemOK) C hC
  simpa [hC'] using this

theorem ExactNormRenameWitness.inv_mem
    (w : ExactNormRenameWitness) {R' R : Clause}
    (hR' : R' ∈ w.L) (hR : renameClauseNorm w.r.inverse R' = some R) :
    R ∈ w.S := by
  have := (List.all_eq_true.mp w.invMemOK) R' hR'
  simpa [hR] using this

theorem ExactNormRenameWitness.pivot_mem
    (w : ExactNormRenameWitness) {p p' : Lit}
    (hp : p ∈ k4Pivots) (hp' : w.r.renameLit p = some p') :
    p' ∈ k4Pivots := by
  have := (List.all_eq_true.mp w.pivOK) p hp
  simpa [hp'] using this

/-- Core Prop pullback: image closed + exact norm-commute ⇒ source closed. -/
theorem ExactNormRenameWitness.closedUnder (w : ExactNormRenameWitness) :
    k4ClosedUnder w.S 3 k4Pivots = true := by
  refine (List.all_eq_true.mpr) fun p hp =>
    (List.all_eq_true.mpr) fun C hC =>
      (List.all_eq_true.mpr) fun D hD => ?_
  cases hRes : resolveOriented C D p with
  | none => rfl
  | some R =>
    obtain ⟨C', D', p', R', hC', hD', hp', hR', hRes'⟩ :=
      exact_commute_norm_point w.exact hC hD hp hRes
    have hC'mem := w.rename_mem hC hC'
    have hD'mem := w.rename_mem hD hD'
    have hp'mem := w.pivot_mem hp hp'
    have hrt :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp
          ((List.all_eq_true.mp w.resRoundOK) p hp)) C hC)) D hD
    simp only [hRes, hR'] at hrt
    have hInv : renameClauseNorm w.r.inverse R' = some R := of_decide_eq_true hrt
    have hwEq :=
      (List.all_eq_true.mp
        ((List.all_eq_true.mp
          ((List.all_eq_true.mp w.resWidthOK) p hp)) C hC)) D hD
    simp only [hRes, hR'] at hwEq
    have hWidthEq : clauseWidth R' = clauseWidth R := of_decide_eq_true hwEq
    cases hw : decide (3 < clauseWidth R) with
    | true => simp only [hw, Bool.true_or]
    | false =>
      have hwLe : clauseWidth R ≤ 3 := Nat.not_lt.mp (of_decide_eq_false hw)
      have hwLe' : clauseWidth R' ≤ 3 := by simpa [hWidthEq] using hwLe
      have hR'mem : R' ∈ w.L :=
        k4_mem_of_closed w.L_closed hC'mem hD'mem hRes' hwLe' hp'mem
      have hRmem := w.inv_mem hR'mem hInv
      simp only [hw, Bool.false_or]
      exact (List.contains_iff_mem).mpr hRmem

/-! ### Concrete witnesses -/

def mfNormRenamed : List Clause :=
  match renameListNorm mfTopologyRename mfRClosed with
  | some L => L
  | none => []

def mfNormWitness : ExactNormRenameWitness where
  r := mfTopologyRename
  S := mfRClosed
  L := mfNormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem mfR_closed_via_norm_rename :
    k4ClosedUnder mfRClosed 3 k4Pivots = true :=
  mfNormWitness.closedUnder

def tfNormRenamed : List Clause :=
  match renameListNorm tfTopologyRename tfRClosed with
  | some L => L
  | none => []

def tfNormWitness : ExactNormRenameWitness where
  r := tfTopologyRename
  S := tfRClosed
  L := tfNormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem tfR_closed_via_norm_rename :
    k4ClosedUnder tfRClosed 3 k4Pivots = true :=
  tfNormWitness.closedUnder

def ffNormRenamed : List Clause :=
  match renameListNorm ffTopologyRename ffRClosed with
  | some L => L
  | none => []

def ffNormWitness : ExactNormRenameWitness where
  r := ffTopologyRename
  S := ffRClosed
  L := ffNormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem ffR_closed_via_norm_rename :
    k4ClosedUnder ffRClosed 3 k4Pivots = true :=
  ffNormWitness.closedUnder

def xfNormRenamed : List Clause :=
  match renameListNorm xfTopologyRename xfRClosed with
  | some L => L
  | none => []

def xfNormWitness : ExactNormRenameWitness where
  r := xfTopologyRename
  S := xfRClosed
  L := xfNormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem xfR_closed_via_norm_rename :
    k4ClosedUnder xfRClosed 3 k4Pivots = true :=
  xfNormWitness.closedUnder

def sfNormRenamed : List Clause :=
  match renameListNorm sfTopologyRename sfRClosed with
  | some L => L
  | none => []

def sfNormWitness : ExactNormRenameWitness where
  r := sfTopologyRename
  S := sfRClosed
  L := sfNormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem sfR_closed_via_norm_rename :
    k4ClosedUnder sfRClosed 3 k4Pivots = true :=
  sfNormWitness.closedUnder

theorem all_pack_R_closed_via_norm_rename :
    k4ClosedUnder mfRClosed 3 k4Pivots = true ∧
      k4ClosedUnder tfRClosed 3 k4Pivots = true ∧
      k4ClosedUnder ffRClosed 3 k4Pivots = true ∧
      k4ClosedUnder xfRClosed 3 k4Pivots = true ∧
      k4ClosedUnder sfRClosed 3 k4Pivots = true :=
  ⟨mfR_closed_via_norm_rename, tfR_closed_via_norm_rename,
    ffR_closed_via_norm_rename, xfR_closed_via_norm_rename,
    sfR_closed_via_norm_rename⟩

/-- alt2..alt6 via the same norm-rename witness pattern. -/
def alt2NormRenamed : List Clause :=
  match renameListNorm alt2TopologyRename alt2RClosed with
  | some L => L
  | none => []

def alt2NormWitness : ExactNormRenameWitness where
  r := alt2TopologyRename
  S := alt2RClosed
  L := alt2NormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem alt2R_closed_via_norm_rename :
    k4ClosedUnder alt2RClosed 3 k4Pivots = true :=
  alt2NormWitness.closedUnder

def alt3NormRenamed : List Clause :=
  match renameListNorm alt3TopologyRename alt3RClosed with
  | some L => L
  | none => []

def alt3NormWitness : ExactNormRenameWitness where
  r := alt3TopologyRename
  S := alt3RClosed
  L := alt3NormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem alt3R_closed_via_norm_rename :
    k4ClosedUnder alt3RClosed 3 k4Pivots = true :=
  alt3NormWitness.closedUnder

def alt4NormRenamed : List Clause :=
  match renameListNorm alt4TopologyRename alt4RClosed with
  | some L => L
  | none => []

def alt4NormWitness : ExactNormRenameWitness where
  r := alt4TopologyRename
  S := alt4RClosed
  L := alt4NormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem alt4R_closed_via_norm_rename :
    k4ClosedUnder alt4RClosed 3 k4Pivots = true :=
  alt4NormWitness.closedUnder

def alt5NormRenamed : List Clause :=
  match renameListNorm alt5TopologyRename alt5RClosed with
  | some L => L
  | none => []

def alt5NormWitness : ExactNormRenameWitness where
  r := alt5TopologyRename
  S := alt5RClosed
  L := alt5NormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem alt5R_closed_via_norm_rename :
    k4ClosedUnder alt5RClosed 3 k4Pivots = true :=
  alt5NormWitness.closedUnder

def alt6NormRenamed : List Clause :=
  match renameListNorm alt6TopologyRename alt6RClosed with
  | some L => L
  | none => []

def alt6NormWitness : ExactNormRenameWitness where
  r := alt6TopologyRename
  S := alt6RClosed
  L := alt6NormRenamed
  exact := by native_decide
  renSome := by native_decide
  perm := by native_decide
  renameMemOK := by native_decide
  invMemOK := by native_decide
  pivOK := by native_decide
  resRoundOK := by native_decide
  resWidthOK := by native_decide

theorem alt6R_closed_via_norm_rename :
    k4ClosedUnder alt6RClosed 3 k4Pivots = true :=
  alt6NormWitness.closedUnder

theorem all_alt_R_closed_via_rename :
    k4ClosedUnder alt1RClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt2RClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt3RClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt4RClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt5RClosed 3 k4Pivots = true ∧
      k4ClosedUnder alt6RClosed 3 k4Pivots = true :=
  ⟨alt1R_closed_via_rename_transport, alt2R_closed_via_norm_rename,
    alt3R_closed_via_norm_rename, alt4R_closed_via_norm_rename,
    alt5R_closed_via_norm_rename, alt6R_closed_via_norm_rename⟩

def renameClosedTransportNormDoc : String :=
  "Pack mf..sf + alt2..6 closed via ExactNormRenameWitness Prop pullback"

end PNPLab.Resolution
