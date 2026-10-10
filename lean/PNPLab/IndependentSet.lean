import PNPLab.Certificates

namespace PNPLab

theorem edgeless_empty_independent (n : Nat) :
    isIndependentSetCert ⟨n, []⟩ 0 [] = true :=
  empty_is_zero_independent ⟨n, []⟩

theorem edgeless_empty_cover (n : Nat) :
    isVertexCoverCert ⟨n, []⟩ 0 [] = true :=
  empty_cover_on_edgeless n

end PNPLab
