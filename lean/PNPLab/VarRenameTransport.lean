/-
  Variable rename transport for residual K₄ packs (Category C / G3).

  Given `VarRename` (src ↔ dst, both length 6), rename literals/clauses by
  index lookup. Proves: empty clause is fixed; OneFold uses identity rename;
  all pack renames target the K₄ template.

  Full Closure₃ membership transport under bijection remains per-pack.
-/

import PNPLab.K4ResidualID

namespace PNPLab.Resolution

/-- Index of `v` in `xs`, or `none`. -/
def indexOf : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, v => if x = v then some 0 else (indexOf xs v).map Nat.succ

/-- Safe list access by index. -/
def listGet : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet xs n

/-- Lookup `src[i] ↦ dst[i]` for a rename. -/
def VarRename.lookup (r : VarRename) (v : Nat) : Option Nat :=
  match indexOf r.src v with
  | none => none
  | some i => listGet r.dst i

/-- Rename a literal, preserving polarity. -/
def VarRename.renameLit (r : VarRename) (ℓ : Lit) : Option Lit :=
  match r.lookup ℓ.natAbs with
  | none => none
  | some w =>
    if ℓ < 0 then some (-(Int.ofNat w)) else some (Int.ofNat w)

/-- Rename a clause; fails if any literal is outside `src`. -/
def VarRename.renameClause (r : VarRename) (C : Clause) : Option Clause :=
  C.foldl (fun acc ℓ =>
    match acc, r.renameLit ℓ with
    | none, _ => none
    | some _D, none => none
    | some D, some ℓ' => some (D ++ [ℓ']))
    (some ([] : Clause))

/-- Empty clause always renames to empty. -/
theorem VarRename.renameClause_empty (r : VarRename) :
    r.renameClause [] = some [] :=
  rfl

/-- Identity rename on the K₄ template. -/
def identityRename : VarRename where
  src := k4TemplateVars
  dst := k4TemplateVars
  src_len := k4TemplateVars_length
  dst_len := k4TemplateVars_length

/-- Concrete identity lookups on template vars 1..6. -/
theorem identityRename_lookup_1 : identityRename.lookup 1 = some 1 := by native_decide
theorem identityRename_lookup_2 : identityRename.lookup 2 = some 2 := by native_decide
theorem identityRename_lookup_3 : identityRename.lookup 3 = some 3 := by native_decide
theorem identityRename_lookup_4 : identityRename.lookup 4 = some 4 := by native_decide
theorem identityRename_lookup_5 : identityRename.lookup 5 = some 5 := by native_decide
theorem identityRename_lookup_6 : identityRename.lookup 6 = some 6 := by native_decide

/-- Empty clause under identity rename. -/
theorem identityRename_empty : identityRename.renameClause [] = some [] :=
  VarRename.renameClause_empty _

/-- OneFold residual uses the identity rename (vars already = template). -/
def ofoldRename : VarRename :=
  renameOfShape ofoldResidualShape

/-- Index-order rename: `src[i] ↦ dst[i]` (both length 6). -/
def VarRename.indexMap (src dst : List Nat)
    (hsrc : src.length = 6) (hdst : dst.length = 6) : VarRename where
  src := src
  dst := dst
  src_len := hsrc
  dst_len := hdst

/-- Map global residual vars to K₄ template by index (works when iso is index-order). -/
def globalRenameIndex (src : List Nat) (h : src.length = 6) : VarRename :=
  VarRename.indexMap src k4TemplateVars h k4TemplateVars_length

theorem ofoldRename_eq_identity :
    ofoldRename.src = k4TemplateVars ∧ ofoldRename.dst = k4TemplateVars := by
  simp [ofoldRename, renameOfShape, ofoldResidualShape, ofoldVres_eq_template]

/-- Bundle: all pack renames target the same template. -/
theorem allPackRenames_dst :
    (allPackShapes.map renameOfShape).all
      (fun r => decide (r.dst = k4TemplateVars)) = true := by
  native_decide

/-- MultiFold rename: src length 6, dst = template. -/
theorem mfRename_shape :
    (renameOfShape mfResidualShape).src.length = 6 ∧
      (renameOfShape mfResidualShape).dst = k4TemplateVars :=
  ⟨mfResidualShape.vars_ok, rfl⟩

/-- MultiFold first variable maps to template var 1. -/
theorem mfRename_first :
    (renameOfShape mfResidualShape).lookup 2 = some 1 := by
  native_decide

/-- SixFold / FiveFold / TripleFold renames also target the template. -/
theorem tfRename_dst : (renameOfShape tfResidualShape).dst = k4TemplateVars := rfl
theorem xfRename_dst : (renameOfShape xfResidualShape).dst = k4TemplateVars := rfl
theorem sfRename_dst : (renameOfShape sfResidualShape).dst = k4TemplateVars := rfl

/-- Identity rename maps unit clauses on template vars to themselves. -/
theorem identityRename_unit_1 :
    identityRename.renameClause [1] = some [1] := by native_decide

theorem identityRename_unit_neg1 :
    identityRename.renameClause [-1] = some [-1] := by native_decide

/-!
Topology-aware K₄ edge bijections (found by exhaustive search over 6!).
Unlike index-order `renameOfShape`, these preserve the K₄ incidence roles.
Report: `signed_k4_pack_isomorphisms.json` (6/6; no sign flips needed).
-/

def mfTopologyRename : VarRename where
  src := mfVres
  dst := [1, 2, 3, 5, 6, 4]
  src_len := mfVres_length
  dst_len := by native_decide

def tfTopologyRename : VarRename where
  src := tfVres
  dst := [1, 2, 5, 4, 6, 3]
  src_len := tfVres_length
  dst_len := by native_decide

def ffTopologyRename : VarRename where
  src := ffVres
  dst := [1, 2, 5, 4, 6, 3]
  src_len := ffVres_length
  dst_len := by native_decide

def xfTopologyRename : VarRename where
  src := xfVres
  dst := [1, 2, 5, 4, 6, 3]
  src_len := xfVres_length
  dst_len := by native_decide

def sfTopologyRename : VarRename where
  src := sfVres
  dst := [1, 2, 4, 5, 6, 3]
  src_len := sfVres_length
  dst_len := by native_decide

def vfTopologyRename : VarRename where
  src := vfVres
  dst := [1, 2, 4, 5, 6, 3]
  src_len := vfVres_length
  dst_len := by native_decide

def efTopologyRename : VarRename where
  src := efVres
  dst := [1, 2, 4, 5, 6, 3]
  src_len := efVres_length
  dst_len := by native_decide

def nfTopologyRename : VarRename where
  src := nfVres
  dst := [1, 2, 4, 5, 6, 3]
  src_len := nfVres_length
  dst_len := by native_decide

def zfTopologyRename : VarRename where
  src := zfVres
  dst := [1, 2, 4, 5, 6, 3]
  src_len := zfVres_length
  dst_len := by native_decide

theorem topologyRenames_target_template :
    mfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      tfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      ffTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      xfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      sfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      vfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      efTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      nfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true ∧
      zfTopologyRename.dst.all (fun v => k4TemplateVars.contains v) = true := by
  native_decide

def signedIsoMassDoc : String :=
  "reports/discovery/signed_k4_pack_isomorphisms.json"

def renameTransportDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

def shapeMassDocRename : String :=
  "reports/discovery/multihop_k4_residual_shape_mass.json"

end PNPLab.Resolution
