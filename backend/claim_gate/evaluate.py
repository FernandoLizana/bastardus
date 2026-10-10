"""Evaluate a purported P vs NP resolution dossier against the claim gate.

Never auto-approves from experiments. A blank or partial dossier always fails.
"""

from __future__ import annotations

from datetime import datetime, timezone
from typing import Any
from uuid import uuid4

from pydantic import BaseModel, Field

from backend.core.evidence import EvidenceLevel

from .catalog import (
    APPROVAL_CHECKLIST,
    BARRIER_ITEMS,
    CONSEQUENCE_ITEMS_A,
    CONSEQUENCE_ITEMS_B,
    ERROR_DISCARDS,
    NPC_FAMILIES,
    PATH_A_REQUIREMENTS,
    PATH_B_REQUIREMENTS,
    PROBLEM_MODES,
    ClaimSide,
)
from .schema import CheckStatus, ChecklistAnswer


def _ans_map(answers: list[ChecklistAnswer]) -> dict[str, ChecklistAnswer]:
    return {a.item_id: a for a in answers}


def _require_pass(
    answers: dict[str, ChecklistAnswer],
    item_ids: list[str],
    *,
    allow_na: bool = False,
) -> list[str]:
    missing: list[str] = []
    for iid in item_ids:
        a = answers.get(iid)
        if a is None or a.status == CheckStatus.UNANSWERED:
            missing.append(f"{iid}: unanswered")
            continue
        if a.status == CheckStatus.FAIL:
            missing.append(f"{iid}: FAIL")
            continue
        if a.status == CheckStatus.NA:
            if not allow_na or len(a.justification.strip()) < 20:
                missing.append(f"{iid}: NA requires ≥20-char justification")
            continue
        if a.status == CheckStatus.PASS and len(a.justification.strip()) < 8:
            missing.append(f"{iid}: PASS requires brief justification")
    return missing


class ClaimDossier(BaseModel):
    """Structured purported-resolution packet submitted to the gate."""

    dossier_id: str = Field(default_factory=lambda: f"PVNP-{uuid4().hex[:10]}")
    title: str = ""
    claim_side: ClaimSide | None = None
    evidence_level: EvidenceLevel = EvidenceLevel.E0_INFORMAL

    # Central path mechanical claims
    path_requirement_answers: list[ChecklistAnswer] = Field(default_factory=list)

    # NPC family coverage: which families are handled via the core problem + poly reductions
    family_answers: list[ChecklistAnswer] = Field(default_factory=list)
    core_problem_id: str = ""  # e.g. "3sat" — the solved / lower-bounded problem
    reduction_polylog_note: str = ""

    problem_mode_answers: list[ChecklistAnswer] = Field(default_factory=list)
    error_discard_answers: list[ChecklistAnswer] = Field(default_factory=list)
    barrier_answers: list[ChecklistAnswer] = Field(default_factory=list)
    consequence_answers: list[ChecklistAnswer] = Field(default_factory=list)
    approval_answers: list[ChecklistAnswer] = Field(default_factory=list)

    formal_defs_note: str = ""
    machine_model: str = ""
    input_size_definition: str = ""
    literature_comparison: str = ""
    adversarial_campaign_ref: str = ""
    lean_artifact_ids: list[str] = Field(default_factory=list)
    independent_reviewer_ids: list[str] = Field(default_factory=list)
    proof_text: str = ""


class GateSectionResult(BaseModel):
    section: str
    passed: bool
    failures: list[str] = Field(default_factory=list)


class GateReport(BaseModel):
    report_id: str = Field(default_factory=lambda: f"GATE-{uuid4().hex[:10]}")
    dossier_id: str
    evaluated_at: str = Field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )
    claim_side: ClaimSide | None = None
    sections: list[GateSectionResult] = Field(default_factory=list)
    evidence_level: EvidenceLevel = EvidenceLevel.E0_INFORMAL
    may_present_as_resolution: bool = False
    blocking_reasons: list[str] = Field(default_factory=list)
    disclaimer: str = (
        "Passing this gate only means the *process checklist* is complete. "
        "It does not by itself establish mathematical truth. "
        "The laboratory never treats experimental evidence as a P vs NP resolution."
    )
    evidence_tag: str = "E1_process_checklist"
    claim_type: str = "process_gate_report"

    def to_dict(self) -> dict[str, Any]:
        return self.model_dump(mode="json")


def empty_dossier_template(side: ClaimSide | None = None) -> dict[str, Any]:
    """Return a blank dossier skeleton with all required item ids."""

    def blanks(items: list[dict[str, Any]], key: str = "id") -> list[dict[str, str]]:
        return [{"item_id": it[key], "status": "unanswered", "justification": ""} for it in items]

    path_items = PATH_A_REQUIREMENTS if side == ClaimSide.A_P_EQ_NP else (
        PATH_B_REQUIREMENTS if side == ClaimSide.B_P_NE_NP else PATH_A_REQUIREMENTS + PATH_B_REQUIREMENTS
    )
    consequences = CONSEQUENCE_ITEMS_A if side == ClaimSide.A_P_EQ_NP else (
        CONSEQUENCE_ITEMS_B if side == ClaimSide.B_P_NE_NP else CONSEQUENCE_ITEMS_A + CONSEQUENCE_ITEMS_B
    )
    return {
        "claim_side": side.value if side else None,
        "path_requirement_answers": blanks(path_items),
        "family_answers": blanks(NPC_FAMILIES),
        "problem_mode_answers": blanks(PROBLEM_MODES),
        "error_discard_answers": blanks(ERROR_DISCARDS),
        "barrier_answers": blanks(BARRIER_ITEMS),
        "consequence_answers": blanks(consequences),
        "approval_answers": blanks(APPROVAL_CHECKLIST),
        "core_problem_id": "",
        "machine_model": "",
        "input_size_definition": "",
        "note": (
            "Fill every item with status=pass (or not_applicable + justification). "
            "Error-discard items: pass means the error mode is discarded / not used."
        ),
    }


def evaluate_gate(dossier: ClaimDossier) -> GateReport:
    """Evaluate checklist completeness and policy gates.

    ``may_present_as_resolution`` is True only if:
    - exactly one claim_side,
    - all required sections pass,
    - evidence_level ≥ E5,
    - Lean artifacts listed,
    - independent reviewers listed (E6 process flag),
    - no FAIL/UNANSWERED required items.
    """
    sections: list[GateSectionResult] = []
    blocking: list[str] = []

    # --- Side ---
    if dossier.claim_side is None:
        sections.append(
            GateSectionResult(
                section="claim_side",
                passed=False,
                failures=["Must assert exactly Camino A (P=NP) or Camino B (P≠NP)."],
            )
        )
        blocking.append("no_claim_side")
    else:
        sections.append(GateSectionResult(section="claim_side", passed=True))

    # --- Path mechanical requirements ---
    path_ids = (
        [x["id"] for x in PATH_A_REQUIREMENTS]
        if dossier.claim_side == ClaimSide.A_P_EQ_NP
        else [x["id"] for x in PATH_B_REQUIREMENTS]
        if dossier.claim_side == ClaimSide.B_P_NE_NP
        else []
    )
    path_map = _ans_map(dossier.path_requirement_answers)
    path_fail = _require_pass(path_map, path_ids) if path_ids else ["no side → no path checks"]
    sections.append(
        GateSectionResult(section="path_requirements", passed=not path_fail, failures=path_fail)
    )
    if path_fail:
        blocking.append("path_requirements")

    # --- NPC families: core problem required; each family pass or NA with reduction note ---
    fam_map = _ans_map(dossier.family_answers)
    fam_ids = [f["id"] for f in NPC_FAMILIES]
    fam_fail = _require_pass(fam_map, fam_ids, allow_na=True)
    if not dossier.core_problem_id:
        fam_fail.append("core_problem_id missing")
    elif dossier.core_problem_id not in fam_ids:
        fam_fail.append(f"unknown core_problem_id: {dossier.core_problem_id}")
    if len(dossier.reduction_polylog_note.strip()) < 40:
        fam_fail.append("reduction_polylog_note too short (need poly-size / answer-preserving argument)")
    # TAUT must be addressed specially (coNP) — cannot silently skip
    taut = fam_map.get("taut")
    if taut is None or taut.status == CheckStatus.UNANSWERED:
        fam_fail.append("taut: must address coNP-complete TAUT (forbid NP/coNP confusion)")
    sections.append(
        GateSectionResult(section="npc_families", passed=not fam_fail, failures=fam_fail)
    )
    if fam_fail:
        blocking.append("npc_families")

    # --- Decision / search / opt / YES-NO ---
    mode_map = _ans_map(dossier.problem_mode_answers)
    mode_fail = _require_pass(mode_map, [m["id"] for m in PROBLEM_MODES])
    sections.append(
        GateSectionResult(section="problem_modes", passed=not mode_fail, failures=mode_fail)
    )
    if mode_fail:
        blocking.append("problem_modes")

    # --- Error discards: every item must PASS (= discarded) ---
    err_map = _ans_map(dossier.error_discard_answers)
    err_fail = _require_pass(err_map, [e["id"] for e in ERROR_DISCARDS], allow_na=False)
    sections.append(
        GateSectionResult(section="error_discards", passed=not err_fail, failures=err_fail)
    )
    if err_fail:
        blocking.append("error_discards")

    # --- Barriers ---
    bar_map = _ans_map(dossier.barrier_answers)
    bar_fail = _require_pass(bar_map, [b["id"] for b in BARRIER_ITEMS], allow_na=True)
    sections.append(
        GateSectionResult(section="barriers", passed=not bar_fail, failures=bar_fail)
    )
    if bar_fail:
        blocking.append("barriers")

    # --- Consequences coherent with side ---
    cons_items = (
        CONSEQUENCE_ITEMS_A
        if dossier.claim_side == ClaimSide.A_P_EQ_NP
        else CONSEQUENCE_ITEMS_B
        if dossier.claim_side == ClaimSide.B_P_NE_NP
        else []
    )
    cons_map = _ans_map(dossier.consequence_answers)
    cons_fail = (
        _require_pass(cons_map, [c["id"] for c in cons_items])
        if cons_items
        else ["no side → no consequences"]
    )
    sections.append(
        GateSectionResult(section="consequences", passed=not cons_fail, failures=cons_fail)
    )
    if cons_fail:
        blocking.append("consequences")

    # --- Approval checklist ---
    appr_map = _ans_map(dossier.approval_answers)
    appr_fail = _require_pass(appr_map, [a["id"] for a in APPROVAL_CHECKLIST])
    if len(dossier.machine_model.strip()) < 10:
        appr_fail.append("machine_model missing")
    if "bit" not in dossier.input_size_definition.lower() and "binary" not in dossier.input_size_definition.lower():
        appr_fail.append("input_size_definition must specify binary/bit length")
    if len(dossier.literature_comparison.strip()) < 40:
        appr_fail.append("literature_comparison too short")
    if not dossier.adversarial_campaign_ref.strip():
        appr_fail.append("adversarial_campaign_ref missing")
    if not dossier.lean_artifact_ids:
        appr_fail.append("lean_artifact_ids empty (E5 formalization required)")
    if len(dossier.independent_reviewer_ids) < 2:
        appr_fail.append("independent_reviewer_ids: need ≥2 specialists (E6 process)")
    if dossier.evidence_level < EvidenceLevel.E5_LEAN_VERIFIED:
        appr_fail.append(
            f"evidence_level {dossier.evidence_level.name} < E5_LEAN_VERIFIED"
        )
    if dossier.evidence_level < EvidenceLevel.E6_EXTERNALLY_REVIEWED:
        appr_fail.append(
            "evidence_level must reach E6_EXTERNALLY_REVIEWED for resolution presentation"
        )
    sections.append(
        GateSectionResult(section="approval_checklist", passed=not appr_fail, failures=appr_fail)
    )
    if appr_fail:
        blocking.append("approval_checklist")

    all_pass = all(s.passed for s in sections)
    # Hard policy: even a "complete" packet does not auto-certify mathematical truth;
    # may_present only means laboratory process gates for *candidate* extraordinary claim.
    may_present = all_pass and dossier.claim_side is not None

    if may_present:
        blocking.append(
            "NOTE: process gates passed — mathematical correctness still requires "
            "community verification beyond this laboratory checklist."
        )

    return GateReport(
        dossier_id=dossier.dossier_id,
        claim_side=dossier.claim_side,
        sections=sections,
        evidence_level=dossier.evidence_level,
        may_present_as_resolution=may_present,
        blocking_reasons=blocking if not may_present else [
            "process_complete_pending_external_math_community"
        ],
    )
