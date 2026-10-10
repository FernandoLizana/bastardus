/-
  Closure₃ membership transport under variable rename (Category C / G3).

  OneFold: identity rename; residual closed set = `k4Closed` as sets.

  Multi/Triple/Four/Five/SixFold: topology-aware edge bijections map every
  residual clause onto the canonical `k4Closed` set. Witnesses were found by
  exhaustive search over 6! permutations (`signed_k4_pack_isomorphisms.json`).
-/

import PNPLab.VarRenameTransport

namespace PNPLab.Resolution

/-- Every OneFold residual clause is fixed by the identity rename. -/
def ofoldR_fixed_by_identity : Bool :=
  ofoldRClosed.all fun C =>
    match identityRename.renameClause C with
    | some C' => decide (C' = C)
    | none => false

theorem ofoldR_fixed_by_identity_true : ofoldR_fixed_by_identity = true := by
  native_decide

def ofoldR_in_k4Template : Bool :=
  ofoldRClosed.all fun C =>
    match identityRename.renameClause C with
    | some C' => k4Closed.contains C'
    | none => false

theorem ofoldR_in_k4Template_true : ofoldR_in_k4Template = true := by
  native_decide

def k4_in_ofoldR : Bool :=
  k4Closed.all fun C => ofoldRClosed.contains C

theorem k4_in_ofoldR_true : k4_in_ofoldR = true := by
  native_decide

/-- OneFold residual and K₄ template are the same set of 16 clauses. -/
theorem ofoldR_eq_k4_as_sets :
    ofoldR_in_k4Template = true ∧ k4_in_ofoldR = true :=
  ⟨ofoldR_in_k4Template_true, k4_in_ofoldR_true⟩

theorem ofold_no_empty_transport :
    identityRename.renameClause [] = some [] ∧
      ¬ ofoldRClosure.mem [] ∧
      ¬ k4Closure.mem [] :=
  ⟨identityRename_empty, ofoldR_no_empty, k4_no_empty⟩

/-- Rename totality on residual packs (domain = Vres). -/
def mfR_rename_succeeds : Bool :=
  mfRClosed.all fun C => ((renameOfShape mfResidualShape).renameClause C).isSome
def tfR_rename_succeeds : Bool :=
  tfRClosed.all fun C => ((renameOfShape tfResidualShape).renameClause C).isSome
def ffR_rename_succeeds : Bool :=
  ffRClosed.all fun C => ((renameOfShape ffResidualShape).renameClause C).isSome
def xfR_rename_succeeds : Bool :=
  xfRClosed.all fun C => ((renameOfShape xfResidualShape).renameClause C).isSome
def sfR_rename_succeeds : Bool :=
  sfRClosed.all fun C => ((renameOfShape sfResidualShape).renameClause C).isSome
def vfR_rename_succeeds : Bool :=
  vfRClosed.all fun C => ((renameOfShape vfResidualShape).renameClause C).isSome
def efR_rename_succeeds : Bool :=
  efRClosed.all fun C => ((renameOfShape efResidualShape).renameClause C).isSome
def nfR_rename_succeeds : Bool :=
  nfRClosed.all fun C => ((renameOfShape nfResidualShape).renameClause C).isSome
def zfR_rename_succeeds : Bool :=
  zfRClosed.all fun C => ((renameOfShape zfResidualShape).renameClause C).isSome

theorem mfR_rename_succeeds_true : mfR_rename_succeeds = true := by native_decide
theorem tfR_rename_succeeds_true : tfR_rename_succeeds = true := by native_decide
theorem ffR_rename_succeeds_true : ffR_rename_succeeds = true := by native_decide
theorem xfR_rename_succeeds_true : xfR_rename_succeeds = true := by native_decide
theorem sfR_rename_succeeds_true : sfR_rename_succeeds = true := by native_decide
theorem vfR_rename_succeeds_true : vfR_rename_succeeds = true := by native_decide
theorem efR_rename_succeeds_true : efR_rename_succeeds = true := by native_decide
theorem nfR_rename_succeeds_true : nfR_rename_succeeds = true := by native_decide
theorem zfR_rename_succeeds_true : zfR_rename_succeeds = true := by native_decide

theorem mfR_size_eq_k4 : mfRClosed.length = k4Closed.length := by native_decide
theorem tfR_size_eq_k4 : tfRClosed.length = k4Closed.length := by native_decide
theorem ffR_size_eq_k4 : ffRClosed.length = k4Closed.length := by native_decide
theorem xfR_size_eq_k4 : xfRClosed.length = k4Closed.length := by native_decide
theorem sfR_size_eq_k4 : sfRClosed.length = k4Closed.length := by native_decide
theorem vfR_size_eq_k4 : vfRClosed.length = k4Closed.length := by native_decide
theorem efR_size_eq_k4 : efRClosed.length = k4Closed.length := by native_decide
theorem nfR_size_eq_k4 : nfRClosed.length = k4Closed.length := by native_decide
theorem zfR_size_eq_k4 : zfRClosed.length = k4Closed.length := by native_decide

/-- Clauses equal as literal sets (order-insensitive; packs contain no duplicates). -/
def sameClause (C D : Clause) : Bool :=
  C.all (fun ℓ => D.contains ℓ) && D.all (fun ℓ => C.contains ℓ)

/-- Renamed source clauses all occur in target, order-insensitively. -/
def renamedSubset (r : VarRename) (source target : List Clause) : Bool :=
  source.all fun C =>
    match r.renameClause C with
    | none => false
    | some C' => target.any (sameClause C')

/-- Every target clause is hit by some renamed source clause. -/
def renamedSurjective (r : VarRename) (source target : List Clause) : Bool :=
  target.all fun T =>
    source.any fun C =>
      match r.renameClause C with
      | none => false
      | some C' => sameClause C' T

def mfTopologySetEq : Bool :=
  renamedSubset mfTopologyRename mfRClosed k4Closed &&
    renamedSurjective mfTopologyRename mfRClosed k4Closed
def tfTopologySetEq : Bool :=
  renamedSubset tfTopologyRename tfRClosed k4Closed &&
    renamedSurjective tfTopologyRename tfRClosed k4Closed
def ffTopologySetEq : Bool :=
  renamedSubset ffTopologyRename ffRClosed k4Closed &&
    renamedSurjective ffTopologyRename ffRClosed k4Closed
def xfTopologySetEq : Bool :=
  renamedSubset xfTopologyRename xfRClosed k4Closed &&
    renamedSurjective xfTopologyRename xfRClosed k4Closed
def sfTopologySetEq : Bool :=
  renamedSubset sfTopologyRename sfRClosed k4Closed &&
    renamedSurjective sfTopologyRename sfRClosed k4Closed
def vfTopologySetEq : Bool :=
  renamedSubset vfTopologyRename vfRClosed k4Closed &&
    renamedSurjective vfTopologyRename vfRClosed k4Closed
def efTopologySetEq : Bool :=
  renamedSubset efTopologyRename efRClosed k4Closed &&
    renamedSurjective efTopologyRename efRClosed k4Closed
def nfTopologySetEq : Bool :=
  renamedSubset nfTopologyRename nfRClosed k4Closed &&
    renamedSurjective nfTopologyRename nfRClosed k4Closed
def zfTopologySetEq : Bool :=
  renamedSubset zfTopologyRename zfRClosed k4Closed &&
    renamedSurjective zfTopologyRename zfRClosed k4Closed

theorem mfTopologySetEq_true : mfTopologySetEq = true := by native_decide
theorem tfTopologySetEq_true : tfTopologySetEq = true := by native_decide
theorem ffTopologySetEq_true : ffTopologySetEq = true := by native_decide
theorem xfTopologySetEq_true : xfTopologySetEq = true := by native_decide
theorem sfTopologySetEq_true : sfTopologySetEq = true := by native_decide
theorem vfTopologySetEq_true : vfTopologySetEq = true := by native_decide
theorem efTopologySetEq_true : efTopologySetEq = true := by native_decide
theorem nfTopologySetEq_true : nfTopologySetEq = true := by native_decide
theorem zfTopologySetEq_true : zfTopologySetEq = true := by native_decide

/-- G3 closed for all concrete packs 1–10: residual = K₄ template up to edge iso. -/
theorem all_packs_topology_set_eq :
    ofoldR_in_k4Template = true ∧ k4_in_ofoldR = true ∧
      mfTopologySetEq = true ∧ tfTopologySetEq = true ∧
      ffTopologySetEq = true ∧ xfTopologySetEq = true ∧
      sfTopologySetEq = true ∧ vfTopologySetEq = true ∧
      efTopologySetEq = true ∧ nfTopologySetEq = true ∧
      zfTopologySetEq = true :=
  ⟨ofoldR_in_k4Template_true, k4_in_ofoldR_true,
    mfTopologySetEq_true, tfTopologySetEq_true, ffTopologySetEq_true,
    xfTopologySetEq_true, sfTopologySetEq_true, vfTopologySetEq_true,
    efTopologySetEq_true, nfTopologySetEq_true, zfTopologySetEq_true⟩

/-- All packs: residual size 16 and rename-total. -/
theorem all_packs_residual_shape_and_rename :
    mfRClosed.length = k4Closed.length ∧
      tfRClosed.length = k4Closed.length ∧
      ffRClosed.length = k4Closed.length ∧
      xfRClosed.length = k4Closed.length ∧
      sfRClosed.length = k4Closed.length ∧
      vfRClosed.length = k4Closed.length ∧
      efRClosed.length = k4Closed.length ∧
      nfRClosed.length = k4Closed.length ∧
      zfRClosed.length = k4Closed.length ∧
      mfR_rename_succeeds = true ∧
      tfR_rename_succeeds = true ∧
      ffR_rename_succeeds = true ∧
      xfR_rename_succeeds = true ∧
      sfR_rename_succeeds = true ∧
      vfR_rename_succeeds = true ∧
      efR_rename_succeeds = true ∧
      nfR_rename_succeeds = true ∧
      zfR_rename_succeeds = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mfR_rename_succeeds_true,
    tfR_rename_succeeds_true, ffR_rename_succeeds_true, xfR_rename_succeeds_true,
    sfR_rename_succeeds_true, vfR_rename_succeeds_true, efR_rename_succeeds_true,
    nfR_rename_succeeds_true, zfR_rename_succeeds_true⟩
  · exact mfR_size_eq_k4
  · exact tfR_size_eq_k4
  · exact ffR_size_eq_k4
  · exact xfR_size_eq_k4
  · exact sfR_size_eq_k4
  · exact vfR_size_eq_k4
  · exact efR_size_eq_k4
  · exact nfR_size_eq_k4
  · exact zfR_size_eq_k4

/-- Bundle: OneFold set-eq + all packs size/rename. -/
theorem residual_membership_transport_bundle :
    ofoldR_in_k4Template = true ∧
      k4_in_ofoldR = true ∧
      mfR_rename_succeeds = true ∧
      tfR_rename_succeeds = true ∧
      ffR_rename_succeeds = true ∧
      xfR_rename_succeeds = true ∧
      sfR_rename_succeeds = true ∧
      vfR_rename_succeeds = true ∧
      efR_rename_succeeds = true ∧
      nfR_rename_succeeds = true ∧
      zfR_rename_succeeds = true ∧
      mfRClosed.length = 16 :=
  ⟨ofoldR_in_k4Template_true, k4_in_ofoldR_true,
    mfR_rename_succeeds_true, tfR_rename_succeeds_true, ffR_rename_succeeds_true,
    xfR_rename_succeeds_true, sfR_rename_succeeds_true, vfR_rename_succeeds_true,
    efR_rename_succeeds_true, nfR_rename_succeeds_true, zfR_rename_succeeds_true,
    by native_decide⟩

/-- Documented distinction: index-order rename is not the topology-aware iso. -/
def renameIsomorphismGapDoc : String :=
  "Index-order VarRename maps src[i]→dst[i] but residual edge roles may differ \
   from k4Template labeling. Topology renames close set-eq for packs 1–6."

def membershipTransportDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

end PNPLab.Resolution
