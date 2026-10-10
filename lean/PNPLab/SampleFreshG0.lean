/-
  Aggregate: sample fresh G₀→R ProjectionInclusions (samp1..32 hop-1..3
  + samp37/38 smallest hop-4).
-/

import PNPLab.Samp1FoldProjection
import PNPLab.Samp2FoldProjection
import PNPLab.Samp3FoldProjection
import PNPLab.Samp4FoldProjection
import PNPLab.Samp5FoldProjection
import PNPLab.Samp6FoldProjection
import PNPLab.Samp7FoldProjection
import PNPLab.Samp8FoldProjection
import PNPLab.Samp9FoldProjection
import PNPLab.Samp10FoldProjection
import PNPLab.Samp11FoldProjection
import PNPLab.Samp12FoldProjection
import PNPLab.Samp13FoldProjection
import PNPLab.Samp14FoldProjection
import PNPLab.Samp15FoldProjection
import PNPLab.Samp16FoldProjection
import PNPLab.Samp17FoldProjection
import PNPLab.Samp18FoldProjection
import PNPLab.Samp19FoldProjection
import PNPLab.Samp20FoldProjection
import PNPLab.Samp21FoldProjection
import PNPLab.Samp22FoldProjection
import PNPLab.Samp23FoldProjection
import PNPLab.Samp24FoldProjection
import PNPLab.Samp25FoldProjection
import PNPLab.Samp26FoldProjection
import PNPLab.Samp27FoldProjection
import PNPLab.Samp28FoldProjection
import PNPLab.Samp29FoldProjection
import PNPLab.Samp30FoldProjection
import PNPLab.Samp31FoldProjection
import PNPLab.Samp32FoldProjection
import PNPLab.Samp37FoldProjection
import PNPLab.Samp38FoldProjection

namespace PNPLab.Resolution

/-- samp1..32 + samp37/38. -/
def sampleFreshG0Count : Nat := 34

theorem sampleFreshG0Count_eq : sampleFreshG0Count = 34 := rfl

theorem all_sample_fresh_g0_hop1_no_empty :
    ¬ samp1GProjection.gClosure.mem [] ∧
      ¬ samp2GProjection.gClosure.mem [] ∧
      ¬ samp3GProjection.gClosure.mem [] :=
  ⟨samp1G_no_empty_of_projection, samp2G_no_empty_of_projection,
    samp3G_no_empty_of_projection⟩

theorem all_sample_fresh_g0_hop2_no_empty :
    ¬ samp4GProjection.gClosure.mem [] ∧ ¬ samp16GProjection.gClosure.mem [] :=
  ⟨samp4G_no_empty_of_projection, samp16G_no_empty_of_projection⟩

theorem all_sample_fresh_g0_hop3_no_empty :
    ¬ samp17GProjection.gClosure.mem [] ∧ ¬ samp32GProjection.gClosure.mem [] :=
  ⟨samp17G_no_empty_of_projection, samp32G_no_empty_of_projection⟩

theorem hop4_sample_fresh_g0_no_empty :
    ¬ samp37GProjection.gClosure.mem [] ∧ ¬ samp38GProjection.gClosure.mem [] :=
  ⟨samp37G_no_empty_of_projection, samp38G_no_empty_of_projection⟩

def sampleFreshG0Doc : String :=
  "samp1..32 (hop-1..3) + samp37/38 (hop-4); see FreshG0Obligation + AltFreshG0"

end PNPLab.Resolution
