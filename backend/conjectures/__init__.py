"""Conjecture registry with refutation-first workflow."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from enum import Enum
from pathlib import Path
from typing import Any
from uuid import uuid4

from backend.core.evidence import EvidenceLevel


class ConjectureStatus(str, Enum):
    IDEA = "idea"
    EXPERIMENTAL = "experimental"
    REFUTED = "refuted"
    REFORMULATED = "reformulated"
    PARTIALLY_PROVED = "parcialmente_demostrada"
    FORMALIZED = "formalizada"
    PREVIOUSLY_KNOWN = "conocida_previamente"
    PUBLICATION_CANDIDATE = "candidata_a_publicacion"


@dataclass
class Conjecture:
    identifier: str
    formal_statement: str
    motivation: str
    variables: list[str]
    domain: str
    evidence_for: list[str] = field(default_factory=list)
    evidence_against: list[str] = field(default_factory=list)
    minimal_counterexample: dict[str, Any] | None = None
    relation_to_known_results: str = ""
    theoretical_barriers: list[str] = field(default_factory=list)
    status: ConjectureStatus = ConjectureStatus.IDEA
    evidence_level: EvidenceLevel = EvidenceLevel.E0_INFORMAL
    proof_attempts: list[str] = field(default_factory=list)
    refutation_attempts: list[str] = field(default_factory=list)
    dependencies: list[str] = field(default_factory=list)
    created_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    author: str = "anonymous"
    code_commit: str = "unknown"
    barrier_report: str = ""

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["status"] = self.status.value
        d["evidence_level"] = self.evidence_level.name
        return d


class ConjectureStore:
    def __init__(self, path: Path | None = None) -> None:
        self.path = path or Path("datasets/conjectures.json")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._items: dict[str, Conjecture] = {}
        if self.path.exists():
            self.load()

    def load(self) -> None:
        raw = json.loads(self.path.read_text(encoding="utf-8"))
        self._items = {}
        for item in raw:
            c = Conjecture(
                identifier=item["identifier"],
                formal_statement=item["formal_statement"],
                motivation=item["motivation"],
                variables=item.get("variables", []),
                domain=item.get("domain", ""),
                evidence_for=item.get("evidence_for", []),
                evidence_against=item.get("evidence_against", []),
                minimal_counterexample=item.get("minimal_counterexample"),
                relation_to_known_results=item.get("relation_to_known_results", ""),
                theoretical_barriers=item.get("theoretical_barriers", []),
                status=ConjectureStatus(item.get("status", "idea")),
                evidence_level=EvidenceLevel[item.get("evidence_level", "E0_INFORMAL")],
                proof_attempts=item.get("proof_attempts", []),
                refutation_attempts=item.get("refutation_attempts", []),
                dependencies=item.get("dependencies", []),
                created_at=item.get("created_at", ""),
                author=item.get("author", "anonymous"),
                code_commit=item.get("code_commit", "unknown"),
                barrier_report=item.get("barrier_report", ""),
            )
            self._items[c.identifier] = c

    def save(self) -> None:
        data = [c.to_dict() for c in self._items.values()]
        self.path.write_text(json.dumps(data, indent=2), encoding="utf-8")

    def add(self, conjecture: Conjecture) -> Conjecture:
        if not conjecture.identifier:
            conjecture.identifier = f"C-{uuid4().hex[:8]}"
        if conjecture.status != ConjectureStatus.IDEA and not conjecture.barrier_report:
            raise ValueError(
                "Refuter gate: barrier checklist required before leaving 'idea' status."
            )
        # Extraordinary-claim gate: publication candidates that mention P vs NP
        stmt = conjecture.formal_statement.lower()
        if conjecture.status == ConjectureStatus.PUBLICATION_CANDIDATE and (
            "p=np" in stmt.replace(" ", "")
            or "p≠np" in stmt
            or "p!=np" in stmt.replace(" ", "")
            or "p vs np" in stmt
            or "p versus np" in stmt
        ):
            if "claim_gate:pass" not in conjecture.barrier_report.lower():
                raise ValueError(
                    "P vs NP publication candidate requires claim_gate:pass in "
                    "barrier_report (see docs/P_VS_NP_CLAIM_GATE.md / "
                    "POST /claims/p-vs-np/gate)."
                )
            if conjecture.evidence_level < EvidenceLevel.E6_EXTERNALLY_REVIEWED:
                raise ValueError(
                    "P vs NP publication candidate requires evidence_level E6."
                )
        self._items[conjecture.identifier] = conjecture
        self.save()
        return conjecture

    def refute(self, identifier: str, counterexample: dict[str, Any], note: str) -> Conjecture:
        c = self._items[identifier]
        c.status = ConjectureStatus.REFUTED
        c.minimal_counterexample = counterexample
        c.evidence_against.append(note)
        c.refutation_attempts.append(note)
        c.evidence_level = EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL
        self.save()
        return c

    def list(self) -> list[Conjecture]:
        return list(self._items.values())
