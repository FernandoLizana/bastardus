/-
  Parametric global VarRename from `residualGlobalVres` + E2 permutation dst.
-/

import PNPLab.CrossingEndpointsGlobalResidualXor
import PNPLab.CrossingChordsToArcs
import PNPLab.VarRenameTransport
import PNPLab.CatalogIsoTransport
import PNPLab.AltResidualWitnesses

namespace PNPLab.Bicyclic

open PNPLab.Resolution

/-- Index-order rename: `residualGlobalVres[i] ↦ template[i]`. -/
def globalRenameFromEndpoints (e : CrossingEndpoints)
    (h : (residualGlobalVres e).length = 6) : VarRename :=
  globalRenameIndex (residualGlobalVres e) h

/-- Topology rename from explicit permutation dst (Python `_find_signed_iso`). -/
def globalTopologyRename (src dst : List Nat)
    (hsrc : src.length = 6) (hdst : dst.length = 6) : VarRename :=
  VarRename.indexMap src dst hsrc hdst

def ofoldGlobalRenameDst : List Nat := [1, 2, 4, 5, 6, 3]

/-- Canonical E2 permutation dst for non-alt1 canonical seeds (n=5 ofold, c6..c10). -/
def canonicalTopologyRenameDst : List Nat := ofoldGlobalRenameDst

theorem canonicalTopologyRenameDst_len : canonicalTopologyRenameDst.length = 6 := by native_decide

def globalTopologyRenameCanonical (e : CrossingEndpoints)
    (hsrc : (residualGlobalVres e).length = 6) : VarRename :=
  globalTopologyRename (residualGlobalVres e) canonicalTopologyRenameDst hsrc
    (by native_decide)

def ofoldGlobalVres : List Nat := [1, 2, 4, 5, 6, 7]

theorem ofoldGlobalVres_len : ofoldGlobalVres.length = 6 := by native_decide

def ofoldGlobalTopologyRename : VarRename :=
  globalTopologyRename ofoldGlobalVres ofoldGlobalRenameDst
    (by native_decide) (by native_decide)

theorem ofoldGlobalVres_eq :
    residualGlobalVres c5OfoldEndpoints = ofoldGlobalVres := by native_decide

theorem ofoldGlobalTopologySetEq :
    topologySetEq ofoldGlobalTopologyRename (residualGlobalAxioms c5OfoldEndpoints) = true := by
  native_decide

theorem c5Alt1_globalRename_src :
    (globalRenameFromEndpoints c5Alt1Endpoints (by native_decide)).src = alt1Vres := by
  native_decide

theorem c5Alt1_globalRename_topology :
    topologySetEq (globalRenameFromEndpoints c5Alt1Endpoints (by native_decide))
      (residualGlobalAxioms c5Alt1Endpoints) = true := by
  native_decide

theorem c5Alt1_globalRename_eq_catalog :
    (globalRenameFromEndpoints c5Alt1Endpoints (by native_decide)).dst = k4TemplateVars := by
  native_decide

theorem c6_globalVres_eq_alt2_rename :
    (globalTopologyRename (residualGlobalVres c6Endpoints0123) [1, 2, 4, 5, 6, 3]
        (by native_decide) (by native_decide)).src = alt2Vres := by
  native_decide

theorem c6_globalTopologySetEq :
    topologySetEq alt2TopologyRename (residualGlobalAxioms c6Endpoints0123) = true := by
  native_decide

theorem c5Ofold_globalRename_index_not_topology :
    topologySetEq (globalRenameFromEndpoints c5OfoldEndpoints (by native_decide))
      (residualGlobalAxioms c5OfoldEndpoints) = false := by
  native_decide

def globalRenameFromEndpointsDoc : String :=
  "globalTopologyRename / ofoldGlobalTopologyRename; alt1 index; c6=alt2 perm"

def globalTopologyRenameFromPerm (e : CrossingEndpoints) (perm : List Nat)
    (hsrc : (residualGlobalVres e).length = 6) (hdst : perm.length = 6) : VarRename :=
  globalTopologyRename (residualGlobalVres e) perm hsrc hdst

/-- E2 catalog permutation classes (10 unique dst; 461/461 iso, 0 flips). -/
def catalogPerm123456 : List Nat := [1, 2, 3, 4, 5, 6]
def catalogPerm123465 : List Nat := [1, 2, 3, 4, 6, 5]
def catalogPerm123546 : List Nat := [1, 2, 3, 5, 4, 6]
def catalogPerm123564 : List Nat := [1, 2, 3, 5, 6, 4]
def catalogPerm123645 : List Nat := [1, 2, 3, 6, 4, 5]
def catalogPerm123654 : List Nat := [1, 2, 3, 6, 5, 4]
def catalogPerm124653 : List Nat := [1, 2, 4, 6, 5, 3]
def catalogPerm125463 : List Nat := [1, 2, 5, 4, 6, 3]
def catalogPerm126453 : List Nat := [1, 2, 6, 4, 5, 3]

theorem catalogPerm123456_len : catalogPerm123456.length = 6 := by native_decide
theorem catalogPerm126453_len : catalogPerm126453.length = 6 := by native_decide

def globalRenameFromEndpointsOpenDoc : String :=
  "globalTopologyRenameFromPerm + 10 E2 perm classes; e↦perm via CrossingTopologyPermLookup"

end PNPLab.Bicyclic

namespace PNPLab.Resolution

open Bicyclic

theorem global_topology_smokes_ok :
    topologySetEq ofoldGlobalTopologyRename (residualGlobalAxioms c5OfoldEndpoints) = true ∧
      topologySetEq alt1TopologyRename (residualGlobalAxioms c5Alt1Endpoints) = true ∧
      topologySetEq alt2TopologyRename (residualGlobalAxioms c6Endpoints0123) = true := by
  native_decide

end PNPLab.Resolution
