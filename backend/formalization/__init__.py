"""Linkage metadata between Lean theorems and Python artifacts."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class FormalizationLink:
    lean_decl: str
    lean_file: str
    software_artifact: str
    status: str  # stub | proven_local | pending
    evidence_target: str
    notes: str


LINKS: list[FormalizationLink] = [
    FormalizationLink(
        lean_decl="isCliqueCert",
        lean_file="lean/PNPLab/Certificates.lean",
        software_artifact="backend/reductions/sat_to_clique.py:verify_clique",
        status="proven_local",
        evidence_target="E5_partial",
        notes="Certificate checker formalized; Karp reduction proof still pending.",
    ),
    FormalizationLink(
        lean_decl="isVertexCoverCert",
        lean_file="lean/PNPLab/Certificates.lean",
        software_artifact="backend/reductions/graph_reductions.py:verify_vertex_cover",
        status="proven_local",
        evidence_target="E5_partial",
        notes="Includes empty-cover lemma on edgeless graphs.",
    ),
    FormalizationLink(
        lean_decl="edgeless_all_independent",
        lean_file="lean/PNPLab/IndependentSet.lean",
        software_artifact="backend/reductions/graph_reductions.py:verify_independent_set",
        status="proven_local",
        evidence_target="E5_partial",
        notes="Special case on edgeless graphs only.",
    ),
    FormalizationLink(
        lean_decl="three_sat_to_clique (correctness)",
        lean_file="lean/PNPLab/Certificates.lean",
        software_artifact="backend/reductions/sat_to_clique.py:three_sat_to_clique",
        status="pending",
        evidence_target="E5",
        notes="Software validated empirically (E2). Full Lean proof not yet done.",
    ),
]


def status_report() -> dict[str, object]:
    return {
        "links": [link.__dict__ for link in LINKS],
        "e5_complete": 0,
        "e5_partial": sum(1 for l in LINKS if l.status == "proven_local"),
        "pending": sum(1 for l in LINKS if l.status == "pending"),
        "caveat": "Partial Lean lemmas != resolution of P vs NP.",
    }
