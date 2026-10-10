"""Proof auditor and barrier checklist tests."""

from backend.core.evidence import EvidenceLevel
from backend.proof_auditor import audit_proof_text
from backend.research_barriers import BARRIER_CATALOG, run_barrier_checklist


def test_barrier_catalog_completeness() -> None:
    assert len(BARRIER_CATALOG) >= 10


def test_barrier_flags_experiments() -> None:
    report = run_barrier_checklist(
        "Our experiments show P = NP because SAT was fast in practice.",
        claims={"based_on_experiments": True, "average_case": True},
    )
    assert any("FINITE" in f or "AVERAGE" in f or "EXTRAORDINARY" in f for f in report.flags)


def test_auditor_catches_avg_as_worst() -> None:
    text = r"""
    Theorem. We prove P = NP.
    In practice our heuristic always finds a satisfying assignment in polynomial time,
    therefore SAT is in P and P = NP.
    """
    report = audit_proof_text(text)
    assert report.evidence_level == EvidenceLevel.E1_OBSERVATION
    assert any(f.severity == "critical" for f in report.findings)
    md = report.to_markdown()
    assert "NOT a mathematical certification" in md
