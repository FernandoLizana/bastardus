/-
  Fresh G₀→R obligation shape (Category C / G5).

  Pack routing discharges mass-window ProjectionInclusion by lookup.
  Beyond packs, each concrete seed must supply a real Closure₃(G₀) and
  a ProjectionInclusion into its residual WidthClosure.
-/

import PNPLab.ParametricResidualSynth
import PNPLab.ConcreteClosures
import PNPLab.AltFreshG0
import PNPLab.SampleFreshG0

namespace PNPLab.Resolution

/--
  What a fresh instance G₀→R witness must discharge for one crossing.
  Independent of pack-family routing.
-/
structure FreshG0Obligation where
  gClosure : WidthClosure 3
  rClosure : WidthClosure 3
  Vres : List Nat
  projection : ProjectionInclusion 3
  proj_g : projection.gClosure = gClosure
  proj_r : projection.rClosure = rClosure
  proj_vres : projection.Vres = Vres
  g_no_empty : ¬ projection.gClosure.mem []
  r_no_empty : ¬ rClosure.mem []

def freshG0_of_projection (P : ProjectionInclusion 3)
    (hr : ¬ P.rClosure.mem []) : FreshG0Obligation where
  gClosure := P.gClosure
  rClosure := P.rClosure
  Vres := P.Vres
  projection := P
  proj_g := rfl
  proj_r := rfl
  proj_vres := rfl
  g_no_empty := no_empty_of_projection P hr
  r_no_empty := hr

def freshG0_alt1 : FreshG0Obligation :=
  freshG0_of_projection alt1GProjection alt1R_closure_no_empty
def freshG0_samp1 : FreshG0Obligation :=
  freshG0_of_projection samp1GProjection samp1_closure_no_empty
def freshG0_samp14 : FreshG0Obligation :=
  freshG0_of_projection samp14GProjection samp14_closure_no_empty
def freshG0_samp19 : FreshG0Obligation :=
  freshG0_of_projection samp19GProjection samp19_closure_no_empty
def freshG0_samp24 : FreshG0Obligation :=
  freshG0_of_projection samp24GProjection samp24_closure_no_empty

theorem fresh_g0_seeds_no_empty :
    ¬ freshG0_alt1.projection.gClosure.mem [] ∧
      ¬ freshG0_samp1.projection.gClosure.mem [] ∧
      ¬ freshG0_samp14.projection.gClosure.mem [] ∧
      ¬ freshG0_samp19.projection.gClosure.mem [] ∧
      ¬ freshG0_samp24.projection.gClosure.mem [] :=
  ⟨freshG0_alt1.g_no_empty, freshG0_samp1.g_no_empty,
    freshG0_samp14.g_no_empty, freshG0_samp19.g_no_empty,
    freshG0_samp24.g_no_empty⟩

theorem beyond_pack_fresh_g0_layers_ok :
    sampleFreshG0Count = 34 ∧ altFreshG0Count = 6 ∧
      (¬ samp1GProjection.gClosure.mem []) ∧
      (¬ samp32GProjection.gClosure.mem []) ∧
      (¬ samp38GProjection.gClosure.mem []) ∧
      (¬ alt1GProjection.gClosure.mem []) :=
  ⟨sampleFreshG0Count_eq, altFreshG0Count_eq,
    samp1G_no_empty_of_projection, samp32G_no_empty_of_projection,
    samp38G_no_empty_of_projection, alt1G_no_empty_of_projection⟩

/-- Beyond-pack: 6 alts + 34 samples = 40. Packs via `PackFreshG0`. -/
def freshG0SeedCount : Nat := 40

theorem freshG0SeedCount_eq :
    freshG0SeedCount = 40 := rfl

theorem freshG0SeedCount_split :
    freshG0SeedCount = altFreshG0Count + sampleFreshG0Count := by
  native_decide

def freshG0ObligationDoc : String :=
  "FreshG0Obligation: alt/samp seeds + pack mass-window; " ++
  "CrossingEndpointsGraph + CrossingEndpointsTseitin (edgeVar/tseitinAxioms)"

def freshG0ObligationOpenDoc : String :=
  "parametric FreshG0 (ofold/alt1) via closure3+residualGlobal; c6 proj OK; open: ∀e + signed VarRename"

end PNPLab.Resolution
