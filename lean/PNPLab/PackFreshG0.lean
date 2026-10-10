/-
  Pack-routed FreshG0Obligation for the mass window n∈[5,14].

  Every crossing in the all-odd window has a pack family; each pack already
  supplies a real Closure₃(G₀)→R ProjectionInclusion.  This wraps that as
  `FreshG0Obligation` — still pack lookup, not a parametric G_e emitter.
-/

import PNPLab.FreshG0Obligation
import PNPLab.CrossingPackCatalog
import PNPLab.CrossingChordsToArcs
import PNPLab.CrossingEndpointsElim

namespace PNPLab.Resolution

open Bicyclic

def freshG0_of_pack (f : CrossingPackFamily) : FreshG0Obligation :=
  freshG0_of_projection (packProjection f) (pack_no_empty_residual f)

theorem freshG0_of_pack_no_empty (f : CrossingPackFamily) :
    ¬ (freshG0_of_pack f).projection.gClosure.mem [] :=
  (freshG0_of_pack f).g_no_empty

/-- Mass window: pack-routed FreshG0Obligation (G₀→R □-free). -/
theorem mass_window_has_fresh_g0
    (e : CrossingEndpoints) (h5 : 5 ≤ e.n) (h14 : e.n ≤ 14) :
    ∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem [] := by
  have hLo : 1 ≤ e.toArcs.total := by
    rw [CrossingEndpoints.toArcs_total]
    omega
  have hHi : e.toArcs.total ≤ 10 :=
    crossing_hop_budget_le_pack_window e h5 h14
  obtain ⟨f, _, _, _⟩ := crossing_pack_route hLo hHi
  exact ⟨freshG0_of_pack f, freshG0_of_pack_no_empty f⟩

theorem mass_window_fresh_g0_endpoints :
    (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) ∧
      (∃ w : FreshG0Obligation, ¬ w.projection.gClosure.mem []) :=
  ⟨mass_window_has_fresh_g0 c5Endpoints0123 (by decide) (by decide),
    mass_window_has_fresh_g0 c14Endpoints0123 (by decide) (by decide)⟩

def packFreshG0Doc : String :=
  "mass_window_has_fresh_g0 via packProjection; open: non-pack ∀e G₀"

end PNPLab.Resolution
