"""Demonstrate that a Camino-B dossier based on resolution width FAILs the claim gate.

This is intentional: restricted proof-system lower bounds cannot settle P≠NP.
"""

from __future__ import annotations

import json
from pathlib import Path

from backend.claim_gate import ClaimDossier, ClaimSide, evaluate_gate
from backend.claim_gate.catalog import (
    APPROVAL_CHECKLIST,
    BARRIER_ITEMS,
    CONSEQUENCE_ITEMS_B,
    ERROR_DISCARDS,
    NPC_FAMILIES,
    PATH_B_REQUIREMENTS,
    PROBLEM_MODES,
)
from backend.claim_gate.schema import CheckStatus, ChecklistAnswer
from backend.core.evidence import EvidenceLevel

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "reports" / "discovery" / "claim_gate_camino_b_resolution_blocked.json"


def _ans(ids: list[str], status: CheckStatus, text: str) -> list[ChecklistAnswer]:
    return [ChecklistAnswer(item_id=i, status=status, justification=text) for i in ids]


def main() -> None:
    # Fill almost everything as PASS, but mark restricted_model as FAIL / honest.
    barrier_answers = []
    for b in BARRIER_ITEMS:
        if b["id"] == "restricted_model":
            barrier_answers.append(
                ChecklistAnswer(
                    item_id=b["id"],
                    status=CheckStatus.FAIL,
                    justification=(
                        "Resolution width lower bounds apply only to the resolution proof "
                        "system, not to general algorithms / general Boolean circuits. "
                        "Therefore this route cannot establish P≠NP."
                    ),
                )
            )
        else:
            barrier_answers.append(
                ChecklistAnswer(
                    item_id=b["id"],
                    status=CheckStatus.PASS,
                    justification="addressed in barrier notes (still insufficient alone)",
                )
            )

    d = ClaimDossier(
        title="Blocked Camino B attempt via Tseitin resolution width",
        claim_side=ClaimSide.B_P_NE_NP,
        evidence_level=EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL,
        core_problem_id="3sat",
        reduction_polylog_note=(
            "Tseitin formulas encode parity constraints; UNSAT when total charge odd. "
            "This does not yield a general circuit lower bound for 3-SAT."
        ),
        machine_model="resolution proof system (restricted)",
        input_size_definition="binary bit length of CNF / graph encoding",
        literature_comparison=(
            "Ben-Sasson–Wigderson, Atserias–Dalmau, Galesi et al.; "
            "known that resolution LBs do not lift to P≠NP."
        ),
        adversarial_campaign_ref="reports/discovery/mass_verify_frontier_latest.json",
        lean_artifact_ids=[],
        independent_reviewer_ids=[],
        path_requirement_answers=_ans(
            [x["id"] for x in PATH_B_REQUIREMENTS],
            CheckStatus.FAIL,
            "Resolution-only hardness does not rule out all deterministic poly-time algorithms.",
        ),
        family_answers=_ans(
            [x["id"] for x in NPC_FAMILIES],
            CheckStatus.NA,
            "Not applicable: we only studied resolution width of Tseitin, not NPC completeness here.",
        ),
        problem_mode_answers=_ans(
            [m["id"] for m in PROBLEM_MODES],
            CheckStatus.NA,
            "Proof-complexity metric, not a decision algorithm for NP.",
        ),
        error_discard_answers=_ans(
            [e["id"] for e in ERROR_DISCARDS],
            CheckStatus.PASS,
            "N/A to Camino B resolution LB narrative; discarded as algorithm biases.",
        ),
        barrier_answers=barrier_answers,
        consequence_answers=_ans(
            [c["id"] for c in CONSEQUENCE_ITEMS_B],
            CheckStatus.PASS,
            "Acknowledged: even real P≠NP would not imply these stronger claims.",
        ),
        approval_answers=_ans(
            [a["id"] for a in APPROVAL_CHECKLIST],
            CheckStatus.FAIL,
            "Cannot approve: restricted model + evidence < E6.",
        ),
    )
    report = evaluate_gate(d)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "intent": "Show Camino B via resolution width is BLOCKED by claim gate",
        "may_present_as_resolution": report.may_present_as_resolution,
        "blocking_reasons": report.blocking_reasons,
        "sections": [s.model_dump() for s in report.sections],
        "disclaimer": report.disclaimer,
    }
    OUT.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"may_present={report.may_present_as_resolution}")
    print(f"blocking={report.blocking_reasons}")
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
