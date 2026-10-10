"""Known theoretical barriers to resolving P vs NP.

This module provides checklists and automated heuristics that FLAG risks.
It does not prove that a claimed proof fails — only that it matches patterns
associated with relativization, natural proofs, or algebrization barriers.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


BARRIER_CATALOG: list[dict[str, Any]] = [
    {
        "id": "relativization",
        "name": "Relativization (Baker–Gill–Solovay, 1975)",
        "summary": (
            "There exist oracles A, B such that P^A = NP^A and P^B ≠ NP^B. "
            "Any proof technique that relativizes (works equally relative to "
            "every oracle) cannot settle P vs NP."
        ),
        "checklist": [
            "Does the argument work verbatim after adding an arbitrary oracle?",
            "Is the simulation of non-determinism via deterministic queries to a black box?",
            "Are diagonalization steps oracle-insensitive?",
        ],
        "references": [
            "Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P=?NP question. SIAM J. Comput.",
        ],
    },
    {
        "id": "natural_proofs",
        "name": "Natural Proofs (Razborov–Rudich, 1997)",
        "summary": (
            "Under standard cryptographic assumptions, 'natural' combinatorial "
            "properties usable for circuit lower bounds cannot separate P from NP."
        ),
        "checklist": [
            "Is the combinatorial property constructive (efficiently checkable)?",
            "Is it large (holds for a non-negligible fraction of functions)?",
            "Does the argument rely on a 'natural' property against poly-size circuits?",
        ],
        "references": [
            "Razborov, A. A., & Rudich, S. (1997). Natural proofs. J. Comput. Syst. Sci.",
        ],
    },
    {
        "id": "algebrization",
        "name": "Algebrization (Aaronson–Wigderson, 2008)",
        "summary": (
            "There are oracles relative to which algebraic extensions still "
            "leave P vs NP open in both directions; techniques that algebrize "
            "are insufficient."
        ),
        "checklist": [
            "Does the proof use arithmetization that still relativizes to algebraic oracles?",
            "Would the same argument apply in an algebrizing world?",
        ],
        "references": [
            "Aaronson, S., & Wigderson, A. (2008). Algebrization. ACM TOCT.",
        ],
    },
    {
        "id": "diagonalization_limits",
        "name": "Limits of diagonalization",
        "summary": "Simple diagonalization alone is known to be compatible with relativized worlds of both answers.",
        "checklist": [
            "Is diagonalization the sole separation engine?",
            "Is non-relativizing information (e.g. arithmetization + PCP specifics) used carefully?",
        ],
        "references": ["Arora & Barak (2009), Ch. 3 and relativization discussion."],
    },
    {
        "id": "restricted_vs_general_lower_bounds",
        "name": "Restricted vs general lower bounds",
        "summary": "Lower bounds for AC0, monotone circuits, etc. do not automatically lift to general Boolean circuits.",
        "checklist": [
            "Is the model restricted (bounded depth, monotone, formulas, …)?",
            "Is a lifting theorem stated and proved?",
        ],
        "references": ["Arora & Barak (2009), circuit complexity chapters."],
    },
    {
        "id": "average_vs_worst_case",
        "name": "Average-case vs worst-case",
        "summary": "Fast typical-case heuristics do not place a problem in P.",
        "checklist": [
            "Is the claim about expected runtime or worst-case?",
            "Is the distribution of instances specified?",
        ],
        "references": ["Impagliazzo, Levin, Luby — average-case complexity literature."],
    },
    {
        "id": "finite_vs_asymptotic",
        "name": "Finite instances vs asymptotic claims",
        "summary": "Any finite set of experiments is consistent with infinitely many asymptotic behaviours.",
        "checklist": [
            "Does the argument jump from finite n to all n?",
            "Are limits taken carefully with quantitative bounds?",
        ],
        "references": ["Standard scientific methodology / complexity asymptotics."],
    },
    {
        "id": "practice_vs_p",
        "name": "Practical performance vs membership in P",
        "summary": "Engineered SAT solvers can be fast on industry instances without implying P = NP.",
        "checklist": [
            "Is 'efficient in practice' conflated with 'polynomial worst-case'?",
        ],
        "references": ["Industrial SAT / CDCL literature."],
    },
    {
        "id": "hidden_constants",
        "name": "Hidden constants and exponents",
        "summary": "n^1000 or 2^{0.001 n} can look polynomial / linear on tiny n.",
        "checklist": [
            "Are exponents and constants tracked?",
            "Were experiments limited to small n where asymptotics are invisible?",
        ],
        "references": ["Standard algorithm analysis caveats."],
    },
    {
        "id": "small_n_illusion",
        "name": "Small-n polynomial illusion",
        "summary": "Curves fit on n≤40 may look polynomial while still exponential.",
        "checklist": [
            "What is the maximum n tested?",
            "Was out-of-sample larger-n validation performed?",
        ],
        "references": ["Empirical scaling methodology (this laboratory)."],
    },
]


@dataclass
class BarrierReport:
    proposal_summary: str
    answers: dict[str, str]
    flags: list[str] = field(default_factory=list)
    evidence_level: str = "E0_checklist_only"
    conclusion: str = (
        "Checklist complete. Flags are warnings, not refutations. "
        "No automatic tool can certify a P vs NP proof."
    )

    def to_markdown(self) -> str:
        lines = [
            "# Research Barriers Checklist Report",
            "",
            f"**Proposal:** {self.proposal_summary}",
            "",
            f"**Evidence level of this report:** {self.evidence_level}",
            "",
            "## Automated / guided answers",
            "",
        ]
        for q, a in self.answers.items():
            lines.append(f"- **{q}:** {a}")
        lines.extend(["", "## Flags", ""])
        if self.flags:
            for f in self.flags:
                lines.append(f"- {f}")
        else:
            lines.append("- (none raised by heuristics)")
        lines.extend(["", "## Conclusion", "", self.conclusion, ""])
        return "\n".join(lines)


def run_barrier_checklist(proposal: str, claims: dict[str, Any] | None = None) -> BarrierReport:
    """Heuristic checklist against known barriers.

    Parameters
    ----------
    proposal:
        Free-text description of the claimed approach.
    claims:
        Optional structured flags from author, e.g.
        ``{"uses_oracle_simulation": True, "based_on_experiments": True}``.
    """
    claims = claims or {}
    text = proposal.lower()
    answers: dict[str, str] = {}
    flags: list[str] = []

    answers["¿La propuesta relativiza?"] = (
        "Riesgo alto — menciona solo diagonalización/simulación"
        if any(w in text for w in ("diagonal", "oracle", "simulate nondetermin"))
        else "No evaluable automáticamente; revisar Baker–Gill–Solovay checklist."
    )
    answers["¿Parece una natural proof?"] = (
        "Posible — usa propiedad combinatoria 'natural' sobre circuitos"
        if any(w in text for w in ("natural proof", "combinatorial property", "most circuits"))
        else "Revisar constructivity + largeness manualmente."
    )
    answers["¿Depende de propiedades verificables y amplias?"] = str(
        claims.get("constructive_large_property", "desconocido")
    )
    answers["¿Solo funciona en circuitos restringidos?"] = str(
        claims.get("restricted_circuit_model", any(
            w in text for w in ("ac0", "monotone", "bounded depth", "formulas only")
        ))
    )
    answers["¿Asume indirectamente aquello que intenta demostrar?"] = str(
        claims.get("circular", "revisión humana requerida")
    )
    answers["¿Confunde promedio con peor caso?"] = (
        "Sí — lenguaje de caso promedio / heurísticas"
        if claims.get("average_case")
        or any(w in text for w in ("average", "typical", "heuristic always", "in practice"))
        else "No detectado en texto; verificar claims."
    )
    answers["¿Depende de muestras finitas?"] = (
        "Sí"
        if claims.get("based_on_experiments")
        or any(w in text for w in ("experiment", "benchmark", "we observed", "plot"))
        else "No declarado."
    )
    answers["¿Existe una familia adversarial conocida?"] = str(
        claims.get("known_adversarial_family", "consultar literatura")
    )
    answers["¿El coste de una subrutina fue omitido?"] = str(
        claims.get("hidden_subroutine_cost", "revisar")
    )
    answers["¿El tamaño de números o estructuras internas crece exponencialmente?"] = str(
        claims.get("exp_bit_complexity", "revisar representaciones")
    )

    if claims.get("based_on_experiments") or "experiment" in text:
        flags.append("FINITE_VS_ASYMPTOTIC: experimental evidence cannot settle P vs NP.")
    if claims.get("average_case") or "in practice" in text:
        flags.append("AVERAGE_VS_WORST: practical speed ≠ algorithm in P.")
    if claims.get("restricted_circuit_model"):
        flags.append("RESTRICTED_MODEL: lower bound may not lift to general circuits.")
    if "p = np" in text or "p=np" in text or "p ≠ np" in text or "p!=np" in text:
        flags.append(
            "EXTRAORDINARY_CLAIM: any purported resolution requires E5+ formalization "
            "and independent expert review (Category E gates)."
        )

    return BarrierReport(proposal_summary=proposal[:500], answers=answers, flags=flags)
