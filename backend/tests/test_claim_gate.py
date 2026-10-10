"""Claim gate rejects incomplete dossiers; experiments cannot resolve P vs NP."""

from __future__ import annotations

from backend.claim_gate import ClaimDossier, ClaimSide, empty_dossier_template, evaluate_gate
from backend.claim_gate.catalog import (
    APPROVAL_CHECKLIST,
    BARRIER_ITEMS,
    CONSEQUENCE_ITEMS_A,
    ERROR_DISCARDS,
    NPC_FAMILIES,
    PATH_A_REQUIREMENTS,
    PROBLEM_MODES,
)
from backend.claim_gate.schema import CheckStatus, ChecklistAnswer
from backend.core.evidence import EvidenceLevel, resolution_presentation_allowed


def _pass_all(ids: list[str], text: str = "addressed in manuscript section X with proof sketch") -> list[ChecklistAnswer]:
    return [
        ChecklistAnswer(item_id=i, status=CheckStatus.PASS, justification=text)
        for i in ids
    ]


def test_empty_dossier_fails() -> None:
    report = evaluate_gate(ClaimDossier())
    assert report.may_present_as_resolution is False
    assert "no_claim_side" in report.blocking_reasons


def test_template_has_all_error_discards() -> None:
    t = empty_dossier_template(ClaimSide.A_P_EQ_NP)
    assert len(t["error_discard_answers"]) == len(ERROR_DISCARDS)
    assert len(t["family_answers"]) == len(NPC_FAMILIES)


def test_experimental_e2_cannot_pass() -> None:
    d = ClaimDossier(
        claim_side=ClaimSide.A_P_EQ_NP,
        evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
        core_problem_id="3sat",
        reduction_polylog_note="x" * 50,
        machine_model="multitape Turing machine",
        input_size_definition="binary bit length of the encoding",
        literature_comparison="x" * 50,
        adversarial_campaign_ref="reports/adversarial.json",
        lean_artifact_ids=["Lean.Fake"],
        independent_reviewer_ids=["r1", "r2"],
        path_requirement_answers=_pass_all([x["id"] for x in PATH_A_REQUIREMENTS]),
        family_answers=_pass_all([x["id"] for x in NPC_FAMILIES]),
        problem_mode_answers=_pass_all([x["id"] for x in PROBLEM_MODES]),
        error_discard_answers=_pass_all([x["id"] for x in ERROR_DISCARDS]),
        barrier_answers=_pass_all([x["id"] for x in BARRIER_ITEMS]),
        consequence_answers=_pass_all([x["id"] for x in CONSEQUENCE_ITEMS_A]),
        approval_answers=_pass_all([x["id"] for x in APPROVAL_CHECKLIST]),
    )
    report = evaluate_gate(d)
    assert report.may_present_as_resolution is False
    assert any("E5" in f or "E6" in f for s in report.sections for f in s.failures)


def test_complete_e6_process_packet_may_present() -> None:
    """Process-complete packet: still not a mathematical proof of P vs NP."""
    d = ClaimDossier(
        claim_side=ClaimSide.A_P_EQ_NP,
        evidence_level=EvidenceLevel.E6_EXTERNALLY_REVIEWED,
        core_problem_id="3sat",
        reduction_polylog_note=(
            "Cook–Levin + Karp chain; each reduction poly-time and answer-preserving "
            "as formalized in Lean artifacts."
        ),
        machine_model="deterministic multitape Turing machine",
        input_size_definition="binary bit length of the input encoding",
        literature_comparison=(
            "Compared with Cook–Levin, Karp 21, Baker–Gill–Solovay, Razborov–Rudich, "
            "Aaronson–Wigderson; non-relativizing and non-algebrizing steps cited."
        ),
        adversarial_campaign_ref="reports/discovery/adversarial_latest.json",
        lean_artifact_ids=["PNPLab.Resolution.Main"],
        independent_reviewer_ids=["expert_alpha", "expert_beta"],
        path_requirement_answers=_pass_all([x["id"] for x in PATH_A_REQUIREMENTS]),
        family_answers=_pass_all([x["id"] for x in NPC_FAMILIES]),
        problem_mode_answers=_pass_all([x["id"] for x in PROBLEM_MODES]),
        error_discard_answers=_pass_all([x["id"] for x in ERROR_DISCARDS]),
        barrier_answers=_pass_all([x["id"] for x in BARRIER_ITEMS]),
        consequence_answers=_pass_all([x["id"] for x in CONSEQUENCE_ITEMS_A]),
        approval_answers=_pass_all([x["id"] for x in APPROVAL_CHECKLIST]),
    )
    report = evaluate_gate(d)
    assert report.may_present_as_resolution is True
    assert resolution_presentation_allowed(d.evidence_level, report.may_present_as_resolution)
    assert "process" in report.disclaimer.lower()


def test_e5_alone_not_enough_for_presentation() -> None:
    assert EvidenceLevel.E5_LEAN_VERIFIED.may_claim_p_vs_np_resolution()
    assert not resolution_presentation_allowed(EvidenceLevel.E5_LEAN_VERIFIED, True)
    assert not resolution_presentation_allowed(EvidenceLevel.E6_EXTERNALLY_REVIEWED, False)
