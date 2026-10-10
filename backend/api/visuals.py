"""JSON payloads for UI visualizations (evidence ≤ E2)."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import pandas as pd

from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import CNFFormula
from backend.reductions.sat_to_clique import three_sat_to_clique
from backend.solvers.dpll import DPLLSolver
from backend.solvers.pysat_adapter import PySATSolver


def reduction_graph_payload(dimacs: str, reduction: str = "3sat_to_clique") -> dict[str, Any]:
    """Build a force-layout-friendly graph for the Clique reduction."""
    formula = CNFFormula.from_dimacs(dimacs)
    if reduction != "3sat_to_clique":
        raise ValueError("MVP visualizer supports 3sat_to_clique only")
    red = three_sat_to_clique(formula)
    inst = red.mapping_metadata["instance"]
    vmap = inst.metadata.get("vertex_map", [])
    nodes = []
    for item in vmap:
        nodes.append(
            {
                "id": item["id"],
                "label": f"c{item['clause']}:{item['literal']}",
                "clause": item["clause"],
                "literal": item["literal"],
                "group": item["clause"],
            }
        )
    links = [{"source": u, "target": v} for u, v in sorted(inst.edges)]
    return {
        "reduction": "3sat_to_clique",
        "nodes": nodes,
        "links": links,
        "k": inst.k,
        "source_size": red.source_size,
        "target_size": red.target_size,
        "steps": [
            {
                "title": "1. Literales por cláusula",
                "detail": "Cada ocurrencia de literal en una cláusula se convierte en un vértice.",
            },
            {
                "title": "2. Aristas de compatibilidad",
                "detail": (
                    "Se conectan vértices de cláusulas distintas cuyos literales "
                    "no son complementarios."
                ),
            },
            {
                "title": "3. Pregunta Clique",
                "detail": f"¿Existe un clique de tamaño k = m = {inst.k} (#cláusulas)?",
            },
            {
                "title": "4. Evidencia",
                "detail": (
                    "Esta visualización es didáctica (E2). La corrección matemática "
                    "es un resultado conocido (Karp); Lean completo pendiente."
                ),
            },
        ],
        "evidence_level": "E2",
        "caveat": "Finite visualization ≠ proof of reduction correctness.",
    }


def live_phase_snapshot(
    *,
    num_variables: int = 12,
    instances_per_ratio: int = 8,
    seed: int = 42,
) -> dict[str, Any]:
    """Small on-demand phase-transition snapshot for the dashboard charts."""
    ratios = [2.0, 3.0, 3.5, 4.0, 4.2, 4.5, 5.0, 6.0]
    gen = RandomKSatGenerator()
    pysat = PySATSolver()
    dpll = DPLLSolver()
    series = []
    for ratio in ratios:
        sats = 0
        decided = 0
        decisions = []
        for i in range(instances_per_ratio):
            formula = gen.generate(
                RandomKSatParams(
                    num_variables=num_variables,
                    clause_variable_ratio=ratio,
                    k=3,
                    seed=seed + int(ratio * 100) + i,
                )
            )
            pr = pysat.solve(formula, timeout_seconds=1.0)
            dr = dpll.solve(formula, timeout_seconds=1.0)
            if pr.satisfiable is not None:
                decided += 1
                sats += int(pr.satisfiable)
            decisions.append(dr.metrics.decisions)
        series.append(
            {
                "ratio": ratio,
                "sat_rate": (sats / decided) if decided else None,
                "median_decisions": float(sorted(decisions)[len(decisions) // 2]),
            }
        )
    return {
        "n": num_variables,
        "instances_per_ratio": instances_per_ratio,
        "seed": seed,
        "series": series,
        "evidence_level": "E2",
        "claim_type": "observation_experimental",
        "disclaimer": (
            "Gráfico de muestra finita. No demuestra P=NP ni P≠NP, ni un umbral universal α*."
        ),
    }


def load_latest_experiment_series() -> dict[str, Any] | None:
    reports = Path("reports/experiments")
    csvs = sorted(reports.glob("phase_transition_*.csv"), reverse=True)
    if not csvs:
        return None
    df = pd.read_csv(csvs[0])
    usable = df[df["solver"] != "DISAGREEMENT"]
    preferred = "pysat" if (usable["solver"] == "pysat").any() else usable["solver"].iloc[0]
    sub = usable[usable["solver"] == preferred]
    sat = (
        sub.groupby("ratio")["satisfiable"]
        .mean()
        .reset_index()
        .rename(columns={"satisfiable": "sat_rate"})
    )
    dpll = usable[usable["solver"] == "dpll"]
    med = (
        dpll.groupby("ratio")["decisions"].median().reset_index()
        if len(dpll)
        else sat.assign(decisions=0).rename(columns={"sat_rate": "decisions"})
    )
    merged = sat.merge(med, on="ratio", how="left")
    series = [
        {
            "ratio": float(r.ratio),
            "sat_rate": float(r.sat_rate) if pd.notna(r.sat_rate) else None,
            "median_decisions": float(r.decisions) if pd.notna(r.decisions) else None,
        }
        for r in merged.itertuples()
    ]
    return {
        "source": str(csvs[0]),
        "series": series,
        "evidence_level": "E2",
        "disclaimer": "Series from saved experiment CSV — finite sample only.",
    }


HELP_TOPICS: list[dict[str, str]] = [
    {
        "id": "evidence",
        "title": "Niveles de evidencia",
        "body": (
            "E0 idea → E2 experimento reproducible → E3 conjetura → E5 Lean → E6 revisión. "
            "Nada por debajo de E5 puede etiquetarse resolución; presentar un candidato "
            "Category-E exige además el claim gate (Camino A o B) en /claims/p-vs-np/gate."
        ),
    },
    {
        "id": "claim_gate",
        "title": "Filtro P vs NP (Camino A/B)",
        "body": (
            "Una resolución debe ser exactamente P=NP o P≠NP, cubrir familias vía reducciones "
            "polinomiales, modos decisión/búsqueda/óptimo, descartar errores típicos, "
            "enfrentar relativización/natural proofs/algebrización, y coherencia de consecuencias. "
            "Ver docs/P_VS_NP_CLAIM_GATE.md."
        ),
    },
    {
        "id": "phase",
        "title": "Qué muestra el gráfico de α",
        "body": (
            "La tasa empírica de satisfacibilidad y el esfuerzo del solver frente a "
            "α=m/n. Es una observación de caso promedio finito, no una cota de peor caso."
        ),
    },
    {
        "id": "reduction",
        "title": "Cómo leer la reducción visual",
        "body": (
            "Cada nodo es una ocurrencia de literal. Las aristas unen literales compatibles "
            "de cláusulas distintas. Un clique de tamaño m correspondería a una asignación "
            "satisfactoria (idea de la reducción de Karp)."
        ),
    },
    {
        "id": "subsetsum",
        "title": "Subset Sum y lo pseudo-polinómico",
        "body": (
            "Un DP O(nT) puede parecer ‘polinómico’ si T es pequeño, pero T puede ser "
            "exponencial en el tamaño en bits. No implica Subset Sum ∈ P."
        ),
    },
    {
        "id": "barriers",
        "title": "Por qué las barreras importan",
        "body": (
            "Relativización, natural proofs y algebrización limitan muchas técnicas. "
            "El checklist no refuta automáticamente una prueba: solo señala riesgos."
        ),
    },
]
