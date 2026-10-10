"""Shared reduction result types and graph NP-complete instance IR."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


@dataclass
class ReductionResult:
    source_problem: str
    target_problem: str
    source_size: dict[str, int]
    target_size: dict[str, int]
    transformation_time: float
    expected_answer: bool | None
    verified_answer: bool | None
    mapping_metadata: dict[str, Any] = field(default_factory=dict)
    certificate_mapping: dict[str, Any] = field(default_factory=dict)
    validation_status: str = "unchecked"
    evidence_level: str = "E2_reproducible_computational"
    caveats: list[str] = field(
        default_factory=lambda: [
            "Empirical agreement on finite instances does not replace a mathematical proof.",
            "Polynomial size growth on tested ranges does not prove poly-time for all n.",
        ]
    )

    def to_dict(self) -> dict[str, Any]:
        meta = dict(self.mapping_metadata)
        # Drop non-JSON objects for API responses
        meta.pop("instance", None)
        return {
            "source_problem": self.source_problem,
            "target_problem": self.target_problem,
            "source_size": self.source_size,
            "target_size": self.target_size,
            "transformation_time": self.transformation_time,
            "expected_answer": self.expected_answer,
            "verified_answer": self.verified_answer,
            "mapping_metadata": meta,
            "certificate_mapping": self.certificate_mapping,
            "validation_status": self.validation_status,
            "evidence_level": self.evidence_level,
            "caveats": self.caveats,
        }


@dataclass
class GraphDecisionInstance:
    """Undirected simple graph with an integer parameter k."""

    num_vertices: int
    edges: frozenset[tuple[int, int]]
    k: int
    problem: str
    metadata: dict[str, Any] = field(default_factory=dict)

    def has_edge(self, u: int, v: int) -> bool:
        a, b = (u, v) if u < v else (v, u)
        return (a, b) in self.edges

    def complement_edges(self) -> frozenset[tuple[int, int]]:
        all_e: set[tuple[int, int]] = set()
        for i in range(self.num_vertices):
            for j in range(i + 1, self.num_vertices):
                if (i, j) not in self.edges:
                    all_e.add((i, j))
        return frozenset(all_e)
