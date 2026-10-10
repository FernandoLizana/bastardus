"""Evidence policy guards."""

import pytest

from backend.core.evidence import EvidenceLevel, EvidenceTagged


def test_evidence_labels() -> None:
    assert "E2" in EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL.label
    assert not EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL.may_claim_p_vs_np_resolution()
    assert EvidenceLevel.E5_LEAN_VERIFIED.may_claim_p_vs_np_resolution()


def test_reject_premature_p_vs_np_tag() -> None:
    tagged = EvidenceTagged(
        value="purported",
        evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
        claim_type="p_vs_np_resolution",
    )
    with pytest.raises(ValueError):
        tagged.assert_not_p_vs_np_claim()
