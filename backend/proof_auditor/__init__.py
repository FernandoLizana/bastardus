"""Heuristic audit of purported complexity proofs (Markdown / LaTeX text).

CRITICAL: Absence of detected issues does NOT imply the proof is correct.
LLMs and pattern matchers are fallible (scientific safety rule #12–13).
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from backend.core.evidence import EvidenceLevel
from backend.research_barriers import run_barrier_checklist


@dataclass
class AuditFinding:
    severity: str  # info | warning | critical
    category: str
    detail: str
    excerpt: str = ""


@dataclass
class ProofAuditReport:
    claim_analyzed: str
    assumptions: list[str]
    valid_steps: list[str]
    doubtful_steps: list[str]
    critical_step: str
    potential_counterexample: str
    relevant_barriers: list[str]
    evidence_level: EvidenceLevel
    provisional_conclusion: str
    findings: list[AuditFinding] = field(default_factory=list)
    ai_generated_notice: str = (
        "This audit was produced by automated heuristics and/or an AI assistant. "
        "It is NOT a mathematical certification. Independent human expert review "
        "is mandatory for any Category D/E claim."
    )

    def to_markdown(self) -> str:
        lines = [
            "# Proof Audit Report",
            "",
            f"**Evidence level of this audit:** {self.evidence_level.label}",
            "",
            f"> {self.ai_generated_notice}",
            "",
            "## Affirmation analyzed",
            "",
            self.claim_analyzed or "(not extracted)",
            "",
            "## Assumptions",
            "",
        ]
        lines.extend(f"- {a}" for a in self.assumptions or ["(none extracted)"])
        lines.extend(["", "## Steps that appear locally valid", ""])
        lines.extend(f"- {s}" for s in self.valid_steps or ["(none marked)"])
        lines.extend(["", "## Doubtful steps", ""])
        lines.extend(f"- {s}" for s in self.doubtful_steps or ["(none)"])
        lines.extend(
            [
                "",
                "## Critical step",
                "",
                self.critical_step,
                "",
                "## Potential counterexample / stress test",
                "",
                self.potential_counterexample,
                "",
                "## Relevant barriers",
                "",
            ]
        )
        lines.extend(f"- {b}" for b in self.relevant_barriers or ["(see research_barriers)"])
        lines.extend(["", "## Findings", ""])
        for f in self.findings:
            lines.append(f"- **[{f.severity}/{f.category}]** {f.detail}")
            if f.excerpt:
                lines.append(f"  - Excerpt: `{f.excerpt[:120]}`")
        lines.extend(
            [
                "",
                "## Provisional conclusion",
                "",
                self.provisional_conclusion,
                "",
                "**Never declare a proof correct solely because this auditor found no issues.**",
                "",
            ]
        )
        return "\n".join(lines)


_PATTERNS: list[tuple[str, str, str, re.Pattern[str]]] = [
    (
        "critical",
        "universal_from_examples",
        "Infers 'for all instances' from examples / experiments",
        re.compile(r"(for all|para todo).{0,40}(we (tested|observed|saw)|en los ejemplos)", re.I),
    ),
    (
        "critical",
        "circular_reasoning",
        "Possible circular appeal to P≠NP or NP-completeness",
        re.compile(r"(since|porque).{0,30}(p\s*≠\s*np|np-hard).{0,30}(therefore|por lo tanto)", re.I),
    ),
    (
        "warning",
        "quantifier_swap",
        "Possible quantifier swap (exists/forall)",
        re.compile(r"(for all|∀).{0,60}(there exists|∃).{0,60}(for all|∀)", re.I),
    ),
    (
        "critical",
        "heuristic_as_always",
        "Heuristic presented as always succeeding",
        re.compile(r"(heuristic|local search|greedy).{0,40}(always|siempre).{0,20}(finds|encuentra)", re.I),
    ),
    (
        "critical",
        "wrong_reduction_direction",
        "Possible confusion of reduction direction",
        re.compile(r"(reduce|reduc).{0,20}(from p to np|np to p)", re.I),
    ),
    (
        "warning",
        "pseudo_polynomial",
        "Pseudo-polynomial algorithm may be labelled polynomial",
        re.compile(r"(pseudo-?polynomial| knapsack ).{0,40}(therefore|hence).{0,20}p\s*=", re.I),
    ),
    (
        "warning",
        "exponential_preprocessing",
        "Possible exponential preprocessing / table",
        re.compile(r"(precomput|tabla|table).{0,40}(2\^|exponential)", re.I),
    ),
    (
        "critical",
        "np_vs_npc_confusion",
        "Possible confusion between NP and NP-complete",
        re.compile(r"(in np).{0,30}(therefore|hence).{0,20}(np-complete|p\s*=)", re.I),
    ),
    (
        "warning",
        "restricted_case_generalization",
        "Generalizes from a restricted case",
        re.compile(r"(planar|2-sat|horn).{0,50}(in general|arbitrary|general case)", re.I),
    ),
    (
        "critical",
        "avg_as_worst",
        "Average-case or practice treated as worst-case polynomial",
        re.compile(r"(in practice|average).{0,40}(polynomial|in p|∈ p)", re.I),
    ),
]


def audit_proof_text(text: str, source_name: str = "uploaded") -> ProofAuditReport:
    findings: list[AuditFinding] = []
    for severity, category, detail, pattern in _PATTERNS:
        for match in pattern.finditer(text):
            findings.append(
                AuditFinding(severity, category, detail, excerpt=match.group(0))
            )

    barrier = run_barrier_checklist(text[:2000], claims={"based_on_experiments": "experiment" in text.lower()})

    claim = ""
    for line in text.splitlines():
        if re.search(r"(theorem|theorem|afirmamos|we prove|demostramos)", line, re.I):
            claim = line.strip()
            break
    if not claim:
        claim = f"(No explicit theorem line found in {source_name})"

    critical = next((f for f in findings if f.severity == "critical"), None)
    provisional = (
        "Critical methodological red flags detected. Do not advance claim status."
        if critical
        else (
            "No automated red flags matched. This is NOT validation. "
            "Human adversarial review required before any status change."
        )
    )

    return ProofAuditReport(
        claim_analyzed=claim,
        assumptions=["(Assumptions must be extracted manually — automated stub)"],
        valid_steps=["(Local syntactic checks only — no semantic proof checking)"],
        doubtful_steps=[f.detail for f in findings if f.severity == "warning"],
        critical_step=critical.detail if critical else "(none auto-detected)",
        potential_counterexample=(
            "Construct adversarial instances for any universal algorithmic claim; "
            "check oracle relativizations for diagonalization-style arguments."
        ),
        relevant_barriers=[
            "Relativization (Baker–Gill–Solovay)",
            "Natural Proofs (Razborov–Rudich)",
            "Algebrization (Aaronson–Wigderson)",
            *barrier.flags,
        ],
        evidence_level=EvidenceLevel.E1_OBSERVATION,
        provisional_conclusion=provisional,
        findings=findings,
    )


def audit_proof_file(path: str | Path) -> ProofAuditReport:
    p = Path(path)
    text = p.read_text(encoding="utf-8")
    return audit_proof_text(text, source_name=p.name)
