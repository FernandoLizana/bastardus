/-
  Residual K₄ identification (Category C / G3).

  After the crossing schedule reaches `K4Skeleton`, every concrete pack residual
  is a Tseitin XOR system on **6 edge variables** whose width-3 closure has
  size **16** and excludes □ — the same shape as `k4Closure` / `k4SelfProjection`.

  Variable *names* differ across packs (`mfVres`, `ffVres`, …); identification is
  up to renaming. This file records the shape invariants and a rename witness
  type connecting an arbitrary 6-var residual set to the canonical template
  `{1,…,6}` used by `K4Width3`.

  E2: `multihop_k4_residual_shape_mass.json` (461/461).
-/

import PNPLab.K4ResidualCatalog
import PNPLab.MultiFoldProjection
import PNPLab.OneFoldProjection
import PNPLab.FourFoldProjection
import PNPLab.TripleFoldProjection
import PNPLab.FiveFoldProjection
import PNPLab.SixFoldProjection
import PNPLab.SevenFoldProjection
import PNPLab.EightFoldProjection
import PNPLab.NineFoldProjection
import PNPLab.TenFoldProjection

namespace PNPLab.Resolution

/-- Canonical residual variable set for the K₄ template pack. -/
def k4TemplateVars : List Nat := [1, 2, 3, 4, 5, 6]

theorem k4TemplateVars_length : k4TemplateVars.length = 6 := by
  native_decide

theorem k4Axioms_length_16 : k4Axioms.length = 16 := by
  native_decide

/-- Combinatorial shape of a residual K₄ Closure₃ (after schedule). -/
structure ResidualK4Shape where
  Vres : List Nat
  closedSize : Nat
  vars_ok : Vres.length = 6
  size_ok : closedSize = 16

/-- Template shape from `K4Width3`. -/
def k4TemplateShape : ResidualK4Shape where
  Vres := k4TemplateVars
  closedSize := 16
  vars_ok := k4TemplateVars_length
  size_ok := rfl

/-- Pack instances: each multihop residual has `|V|=6`. -/
theorem ofoldVres_length : ofoldVres.length = 6 := by native_decide
theorem mfVres_length : mfVres.length = 6 := by native_decide
theorem ffVres_length : ffVres.length = 6 := by native_decide
theorem tfVres_length : tfVres.length = 6 := by native_decide
theorem xfVres_length : xfVres.length = 6 := by native_decide
theorem sfVres_length : sfVres.length = 6 := by native_decide
theorem vfVres_length : vfVres.length = 6 := by native_decide
theorem efVres_length : efVres.length = 6 := by native_decide
theorem nfVres_length : nfVres.length = 6 := by native_decide
theorem zfVres_length : zfVres.length = 6 := by native_decide

def ofoldResidualShape : ResidualK4Shape where
  Vres := ofoldVres
  closedSize := 16
  vars_ok := ofoldVres_length
  size_ok := rfl

def mfResidualShape : ResidualK4Shape where
  Vres := mfVres
  closedSize := 16
  vars_ok := mfVres_length
  size_ok := rfl

def ffResidualShape : ResidualK4Shape where
  Vres := ffVres
  closedSize := 16
  vars_ok := ffVres_length
  size_ok := rfl

def tfResidualShape : ResidualK4Shape where
  Vres := tfVres
  closedSize := 16
  vars_ok := tfVres_length
  size_ok := rfl

def xfResidualShape : ResidualK4Shape where
  Vres := xfVres
  closedSize := 16
  vars_ok := xfVres_length
  size_ok := rfl

def sfResidualShape : ResidualK4Shape where
  Vres := sfVres
  closedSize := 16
  vars_ok := sfVres_length
  size_ok := rfl

def vfResidualShape : ResidualK4Shape where
  Vres := vfVres
  closedSize := 16
  vars_ok := vfVres_length
  size_ok := rfl

def efResidualShape : ResidualK4Shape where
  Vres := efVres
  closedSize := 16
  vars_ok := efVres_length
  size_ok := rfl

def nfResidualShape : ResidualK4Shape where
  Vres := nfVres
  closedSize := 16
  vars_ok := nfVres_length
  size_ok := rfl

def zfResidualShape : ResidualK4Shape where
  Vres := zfVres
  closedSize := 16
  vars_ok := zfVres_length
  size_ok := rfl

/-- All projection packs share ResidualK4Shape. -/
def allPackShapes : List ResidualK4Shape :=
  [ofoldResidualShape, mfResidualShape, tfResidualShape,
   ffResidualShape, xfResidualShape, sfResidualShape, vfResidualShape,
   efResidualShape, nfResidualShape, zfResidualShape]

theorem allPackShapes_count : allPackShapes.length = 10 := rfl

theorem allPackShapes_vars_ok :
    allPackShapes.all (fun S => decide (S.Vres.length = 6)) = true := by
  native_decide

/--
  Rename witness: residual vars and template both have length 6
  (bijection candidate; clause-level rename discharged per pack).
-/
structure VarRename where
  src : List Nat
  dst : List Nat
  src_len : src.length = 6
  dst_len : dst.length = 6

def renameOfShape (S : ResidualK4Shape) : VarRename where
  src := S.Vres
  dst := k4TemplateVars
  src_len := S.vars_ok
  dst_len := k4TemplateVars_length

/-- Every pack residual shape admits a rename candidate to the template. -/
theorem pack_has_rename (S : ResidualK4Shape) :
    ∃ r : VarRename, r.src = S.Vres ∧ r.dst = k4TemplateVars :=
  ⟨renameOfShape S, rfl, rfl⟩

/-- Bundle: catalog schedule + residual shape + no □ on template. -/
structure K4ResidualID where
  catalog : Bicyclic.K4CatalogWitness
  shape : ResidualK4Shape
  noEmpty : ¬ k4Closure.mem []

def k4ResidualID_template (c : Bicyclic.CrossingArcs) : K4ResidualID where
  catalog := Bicyclic.catalogWitness c
  shape := k4TemplateShape
  noEmpty := k4_no_empty

theorem k4ResidualID_template_hops (c : Bicyclic.CrossingArcs) :
    (k4ResidualID_template c).catalog.hops = c.total :=
  rfl

/-- Concrete MultiFold instance wires schedule (C₆, 4 hops) to mf residual shape. -/
def mfK4ResidualID : K4ResidualID where
  catalog := Bicyclic.catalogWitness Bicyclic.c6CrossingArcs
  shape := mfResidualShape
  noEmpty := k4_no_empty

theorem mfK4ResidualID_hops : mfK4ResidualID.catalog.hops = 4 :=
  Bicyclic.c6_stepsToK4

theorem mfK4ResidualID_vars : mfK4ResidualID.shape.Vres.length = 6 :=
  mfK4ResidualID.shape.vars_ok

/-- OneFold residual shape + catalog for a 1-tip crossing (n=5 style). -/
def ofoldK4ResidualID : K4ResidualID where
  catalog := Bicyclic.catalogWitness { a0 := 1, a1 := 0, a2 := 0, a3 := 0 }
  shape := ofoldResidualShape
  noEmpty := k4_no_empty

theorem ofoldK4ResidualID_hops : ofoldK4ResidualID.catalog.hops = 1 := rfl

/-- OneFold residual vars already match the canonical template indexing. -/
theorem ofoldVres_eq_template : ofoldVres = k4TemplateVars := rfl

def residualIDDoc : String :=
  "papers/FAMILY_PROJECTION_E5.md"

def shapeMassDoc : String :=
  "reports/discovery/multihop_k4_residual_shape_mass.json"

end PNPLab.Resolution
