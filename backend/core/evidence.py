"""Explicit evidence-level tagging for all scientific claims.

The platform MUST distinguish observation from proof. Experimental results
are at most E2; they never resolve P vs NP.
"""

from __future__ import annotations

from enum import IntEnum
from typing import Any, Generic, TypeVar

from pydantic import BaseModel, Field

T = TypeVar("T")


class EvidenceLevel(IntEnum):
    """Scientific evidence hierarchy used throughout the laboratory."""

    E0_INFORMAL = 0
    E1_OBSERVATION = 1
    E2_REPRODUCIBLE_COMPUTATIONAL = 2
    E3_FORMULATED_CONJECTURE = 3
    E4_MANUAL_PARTIAL_PROOF = 4
    E5_LEAN_VERIFIED = 5
    E6_EXTERNALLY_REVIEWED = 6

    @property
    def label(self) -> str:
        return {
            EvidenceLevel.E0_INFORMAL: "E0: informal idea",
            EvidenceLevel.E1_OBSERVATION: "E1: observation on examples",
            EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL: "E2: reproducible computational evidence",
            EvidenceLevel.E3_FORMULATED_CONJECTURE: "E3: clearly formulated conjecture",
            EvidenceLevel.E4_MANUAL_PARTIAL_PROOF: "E4: partially reviewed manual proof",
            EvidenceLevel.E5_LEAN_VERIFIED: "E5: Lean-verified formal proof",
            EvidenceLevel.E6_EXTERNALLY_REVIEWED: "E6: externally reviewed by specialists",
        }[self]

    def may_claim_p_vs_np_resolution(self) -> bool:
        """Necessary condition only: E5+.

        Sufficient presentation still requires a passing ``claim_gate`` dossier
        at E6 (independent review) — see ``backend.claim_gate.evaluate_gate``.
        """
        return self >= EvidenceLevel.E5_LEAN_VERIFIED


def resolution_presentation_allowed(
    evidence_level: EvidenceLevel, gate_may_present: bool
) -> bool:
    """Final lab policy: E6 ∧ claim-gate pass required to *present* a resolution candidate."""
    return (
        evidence_level >= EvidenceLevel.E6_EXTERNALLY_REVIEWED and gate_may_present
    )


class EvidenceTagged(BaseModel, Generic[T]):
    """Wrap a result with an explicit evidence level and caveats."""

    value: Any
    evidence_level: EvidenceLevel
    claim_type: str = Field(
        description=(
            "One of: observation_experimental | conjecture | lemma | "
            "partial_proof | formal_proof | known_result | apparently_new | "
            "error_or_inconclusive"
        )
    )
    caveats: list[str] = Field(default_factory=list)
    references: list[str] = Field(default_factory=list)

    def assert_not_p_vs_np_claim(self) -> None:
        if (
            self.evidence_level < EvidenceLevel.E5_LEAN_VERIFIED
            and "p_vs_np" in self.claim_type.lower()
        ):
            raise ValueError(
                "Evidence below E5 cannot be labelled as a P vs NP resolution. "
                f"Got {self.evidence_level.label}."
            )
