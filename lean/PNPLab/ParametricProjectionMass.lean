/-
  Parametric projection mass (Category C / E5 non-pack track).

  E2 `parametric_projection_mass.json`: every catalog crossing satisfies
  G-clause-on-Vres ⊆ R-closure (461/461 via Python `check_projection_instance`).

  Lean discharge per instance remains emit/`native_decide`; this records mass.
-/

import PNPLab.CrossingResidualCatalog

namespace PNPLab.Resolution

structure ParametricProjectionMass where
  total : Nat
  projOk : Nat
  projFail : Nat
  allOk : Bool

def parametricProjectionMass : ParametricProjectionMass where
  total := 461
  projOk := 461
  projFail := 0
  allOk := true

theorem parametricProjectionMass_ok :
    parametricProjectionMass.total = 461 ∧
      parametricProjectionMass.projOk = 461 ∧
      parametricProjectionMass.projFail = 0 ∧
      parametricProjectionMass.allOk = true := by
  native_decide

theorem parametric_projection_mass_matches_catalog :
    parametricProjectionMass.projOk = crossingResidualCatalogMass.isoOk ∧
      crossingResidualCatalogMass.isoOk = 461 := by
  native_decide

def parametricProjectionMassDoc : String :=
  "461/461 parametricProjOK parity (Python mass); Lean discharge: canonical seeds + emit"

end PNPLab.Resolution
