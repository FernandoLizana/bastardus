"""FastAPI surface for the laboratory."""

from __future__ import annotations

from typing import Any

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field

from backend import __version__
from backend.claim_gate import (
    APPROVAL_CHECKLIST,
    BARRIER_ITEMS,
    CONSEQUENCE_ITEMS_A,
    CONSEQUENCE_ITEMS_B,
    ERROR_DISCARDS,
    NPC_FAMILIES,
    PROBLEM_MODES,
    ClaimDossier,
    ClaimSide,
    empty_dossier_template,
    evaluate_gate,
)
from backend.claim_gate.catalog import PATH_A_REQUIREMENTS, PATH_B_REQUIREMENTS
from backend.conjectures import ConjectureStore
from backend.conjectures.refute import (
    refute_all_random_3sat_always_sat,
    refute_solvers_always_agree,
)
from backend.core.evidence import EvidenceLevel
from backend.api.visuals import (
    HELP_TOPICS,
    live_phase_snapshot,
    load_latest_experiment_series,
    reduction_graph_payload,
)
from backend.formalization import status_report
from backend.generators import (
    CraftedHamiltonianParams,
    PigeonholeParams,
    SubsetSumParams,
    TseitinParams,
    generate_crafted_hamiltonian,
    generate_hard_subset_sum,
    generate_pigeonhole,
    generate_tseitin,
)
from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import CNFFormula, verify_assignment
from backend.proof_auditor import audit_proof_text
from backend.reductions import (
    hamiltonian_to_tsp,
    sat_to_3sat,
    three_sat_to_clique,
    three_sat_to_independent_set,
    three_sat_to_vertex_cover,
)
from backend.research_barriers import BARRIER_CATALOG, run_barrier_checklist
from backend.solvers.brute_force import BruteForceSAT
from backend.solvers.dpll import DPLLSolver
from backend.solvers.meta import MetaSolver
from backend.solvers.pysat_adapter import PySATSolver

app = FastAPI(
    title="PNP Research Laboratory",
    version=__version__,
    description=(
        "Computational research platform for NP-complete problems. "
        "Experimental results are evidence ≤ E2 and never resolve P vs NP."
    ),
)
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)


class SolveRequest(BaseModel):
    dimacs: str
    solver: str = Field(
        default="dpll", pattern="^(dpll|bruteforce|pysat|meta)$"
    )
    timeout_seconds: float | None = 5.0


class GenerateRequest(BaseModel):
    num_variables: int = Field(ge=1, le=200)
    ratio: float = Field(ge=0.0, le=20.0)
    seed: int = 0
    k: int = Field(default=3, ge=1, le=10)


class AuditRequest(BaseModel):
    text: str


class BarrierRequest(BaseModel):
    proposal: str
    claims: dict[str, Any] = Field(default_factory=dict)


class ClaimGateRequest(BaseModel):
    """Body is a ClaimDossier (see docs/P_VS_NP_CLAIM_GATE.md)."""

    dossier: dict[str, Any] = Field(default_factory=dict)


class ReduceRequest(BaseModel):
    dimacs: str
    reduction: str = Field(
        pattern="^(sat_to_3sat|3sat_to_clique|3sat_to_independent_set|3sat_to_vertex_cover)$"
    )


@app.get("/")
def root() -> dict[str, Any]:
    return {
        "name": "PNP Research Laboratory",
        "version": __version__,
        "policy": (
            "Never present evidence below E5 as a P vs NP resolution. "
            "Category-E candidates must pass /claims/p-vs-np/gate at E6."
        ),
        "max_evidence_for_experiments": EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL.label,
    }


@app.get("/health")
def health() -> dict[str, str]:
    return {"status": "ok"}


@app.get("/dashboard/summary")
def dashboard_summary() -> dict[str, Any]:
    store = ConjectureStore()
    conjectures = store.list()
    return {
        "evidence_policy": (
            "Nothing below E5 may resolve P vs NP; Category-E candidates must pass "
            "/claims/p-vs-np/gate at E6."
        ),
        "active_conjectures": [
            {
                "id": c.identifier,
                "status": c.status.value,
                "evidence_level": c.evidence_level.name,
                "statement": c.formal_statement[:160],
            }
            for c in conjectures
            if c.status.value not in {"refuted"}
        ],
        "refuted_conjectures": sum(1 for c in conjectures if c.status.value == "refuted"),
        "solvers": ["bruteforce", "dpll", "pysat", "meta"],
        "reductions": [
            "sat_to_3sat",
            "3sat_to_clique",
            "3sat_to_independent_set",
            "3sat_to_vertex_cover",
            "hamiltonian_to_tsp",
        ],
        "generators": [
            "random-k-sat",
            "pigeonhole",
            "tseitin",
            "hard_subset_sum",
            "crafted_hamiltonian",
        ],
        "barriers_count": len(BARRIER_CATALOG),
        "claim_gate": {
            "doc": "docs/P_VS_NP_CLAIM_GATE.md",
            "npc_families": len(NPC_FAMILIES),
            "error_discards": len(ERROR_DISCARDS),
            "approval_items": len(APPROVAL_CHECKLIST),
            "paths": ["A_P_eq_NP", "B_P_ne_NP"],
        },
        "alerts": [
            "Experimental results are at most E2.",
            "Meta-solver speedups are practical observations, not membership in P.",
            "Subset Sum DP is pseudo-polynomial — not evidence that Subset Sum ∈ P.",
            "Lean certificate lemmas are E5-partial; reduction correctness still pending.",
            "Mass native Tseitin checks are E2 certificates, not a P vs NP resolution.",
        ],
        "formalization_progress": status_report(),
    }


@app.post("/solve")
def solve(req: SolveRequest) -> dict[str, Any]:
    formula = CNFFormula.from_dimacs(req.dimacs)
    solvers = {
        "dpll": DPLLSolver(),
        "bruteforce": BruteForceSAT(),
        "pysat": PySATSolver(),
        "meta": MetaSolver(),
    }
    solver = solvers[req.solver]
    if req.solver == "bruteforce" and formula.num_variables > 20:
        raise HTTPException(400, "bruteforce limited to n≤20 via API")
    result = solver.solve(formula, timeout_seconds=req.timeout_seconds)
    if result.satisfiable and result.assignment is not None:
        # Meta may fill assignment; verify when present
        if not verify_assignment(formula, result.assignment):
            raise HTTPException(500, "Internal certificate verification failed")
    return result.to_dict()


@app.post("/solve/compare")
def solve_compare(req: SolveRequest) -> dict[str, Any]:
    formula = CNFFormula.from_dimacs(req.dimacs)
    return MetaSolver().compare_all(formula, timeout_seconds=req.timeout_seconds)


@app.post("/generate/random-ksat")
def generate(req: GenerateRequest) -> dict[str, Any]:
    formula = RandomKSatGenerator().generate(
        RandomKSatParams(
            num_variables=req.num_variables,
            clause_variable_ratio=req.ratio,
            k=req.k,
            seed=req.seed,
        )
    )
    return {
        "dimacs": formula.to_dimacs(),
        "num_variables": formula.num_variables,
        "num_clauses": formula.num_clauses,
        "ratio": formula.ratio,
        "hash": formula.content_hash(),
        "metadata": formula.metadata,
        "evidence_level": "E2_instance_provenance",
    }


@app.post("/reductions/apply")
def reductions_apply(req: ReduceRequest) -> dict[str, Any]:
    formula = CNFFormula.from_dimacs(req.dimacs)
    dispatch = {
        "sat_to_3sat": sat_to_3sat,
        "3sat_to_clique": three_sat_to_clique,
        "3sat_to_independent_set": three_sat_to_independent_set,
        "3sat_to_vertex_cover": three_sat_to_vertex_cover,
    }
    try:
        result = dispatch[req.reduction](formula)
    except ValueError as exc:
        raise HTTPException(400, str(exc)) from exc
    return result.to_dict()


@app.get("/conjectures")
def list_conjectures() -> list[dict[str, Any]]:
    return [c.to_dict() for c in ConjectureStore().list()]


@app.post("/conjectures/refute/demo-always-sat")
def refute_demo() -> dict[str, Any]:
    """Attempt to refute 'always SAT at α=4.2' (expected: counterexample exists)."""
    return refute_all_random_3sat_always_sat().to_dict()


@app.post("/conjectures/refute/solvers-agree")
def refute_agree() -> dict[str, Any]:
    return refute_solvers_always_agree().to_dict()


class AdversarialGenerateRequest(BaseModel):
    family: str = Field(
        pattern="^(pigeonhole|tseitin|hard_subset_sum|crafted_hamiltonian)$"
    )
    size: int = Field(default=4, ge=2, le=40)
    seed: int = 0
    unsat: bool = True


class HamiltonianReduceRequest(BaseModel):
    num_vertices: int = Field(ge=3, le=12)
    edges: list[list[int]]
    seed: int = 0


@app.post("/generate/adversarial")
def generate_adversarial(req: AdversarialGenerateRequest) -> dict[str, Any]:
    if req.family == "pigeonhole":
        f = generate_pigeonhole(PigeonholeParams(holes=req.size, seed=req.seed))
        return {
            "kind": "cnf",
            "dimacs": f.to_dimacs(),
            "metadata": f.metadata,
            "hash": f.content_hash(),
        }
    if req.family == "tseitin":
        n = req.size if req.size % 2 == 0 else req.size + 1
        n = max(n, 4)
        f = generate_tseitin(
            TseitinParams(num_vertices=n, seed=req.seed, charge_odd=req.unsat)
        )
        return {
            "kind": "cnf",
            "dimacs": f.to_dimacs(),
            "metadata": f.metadata,
            "hash": f.content_hash(),
        }
    if req.family == "hard_subset_sum":
        inst = generate_hard_subset_sum(
            SubsetSumParams(
                num_items=req.size,
                seed=req.seed,
                force_unsat_shift=req.unsat,
            )
        )
        return {
            "kind": "subset_sum",
            "numbers": list(inst.numbers),
            "target": inst.target,
            "metadata": inst.metadata,
        }
    ham = generate_crafted_hamiltonian(
        CraftedHamiltonianParams(
            num_vertices=req.size,
            seed=req.seed,
            make_nonhamiltonian=req.unsat,
        )
    )
    return {
        "kind": "hamiltonian",
        "num_vertices": ham.num_vertices,
        "edges": [list(e) for e in sorted(ham.edges)],
        "metadata": ham.metadata,
    }


@app.post("/reductions/hamiltonian-to-tsp")
def reduce_ham_tsp(req: HamiltonianReduceRequest) -> dict[str, Any]:
    edges = set()
    for pair in req.edges:
        if len(pair) != 2:
            raise HTTPException(400, "each edge must be [u,v]")
        u, v = int(pair[0]), int(pair[1])
        if u == v or u < 0 or v < 0 or u >= req.num_vertices or v >= req.num_vertices:
            raise HTTPException(400, "invalid edge")
        edges.add((u, v) if u < v else (v, u))
    from backend.reductions.hamiltonian_tsp import HamiltonianInstance

    ham = HamiltonianInstance(
        num_vertices=req.num_vertices,
        edges=frozenset(edges),
        metadata={"seed": req.seed},
    )
    return hamiltonian_to_tsp(ham).to_dict()


class VisualReduceRequest(BaseModel):
    dimacs: str
    reduction: str = "3sat_to_clique"


class PhaseSnapRequest(BaseModel):
    num_variables: int = Field(default=12, ge=6, le=18)
    instances_per_ratio: int = Field(default=8, ge=3, le=20)
    seed: int = 42


@app.get("/help/topics")
def help_topics() -> list[dict[str, str]]:
    return HELP_TOPICS


@app.post("/visual/reduction-graph")
def visual_reduction_graph(req: VisualReduceRequest) -> dict[str, Any]:
    try:
        return reduction_graph_payload(req.dimacs, req.reduction)
    except ValueError as exc:
        raise HTTPException(400, str(exc)) from exc


@app.post("/visual/phase-snapshot")
def visual_phase_snapshot(req: PhaseSnapRequest) -> dict[str, Any]:
    return live_phase_snapshot(
        num_variables=req.num_variables,
        instances_per_ratio=req.instances_per_ratio,
        seed=req.seed,
    )


@app.get("/visual/phase-latest")
def visual_phase_latest() -> dict[str, Any]:
    data = load_latest_experiment_series()
    if data is None:
        return {"series": [], "disclaimer": "No saved experiment yet — run a snapshot."}
    return data


@app.get("/formalization")
def formalization() -> dict[str, Any]:
    return status_report()


@app.post("/audit/proof")
def audit(req: AuditRequest) -> dict[str, Any]:
    report = audit_proof_text(req.text)
    return {
        "markdown": report.to_markdown(),
        "evidence_level": report.evidence_level.label,
        "provisional_conclusion": report.provisional_conclusion,
        "findings": [
            {"severity": f.severity, "category": f.category, "detail": f.detail}
            for f in report.findings
        ],
        "notice": report.ai_generated_notice,
    }


@app.get("/barriers")
def barriers() -> list[dict[str, Any]]:
    return BARRIER_CATALOG


@app.post("/barriers/checklist")
def barriers_checklist(req: BarrierRequest) -> dict[str, Any]:
    report = run_barrier_checklist(req.proposal, req.claims)
    return {
        "markdown": report.to_markdown(),
        "flags": report.flags,
        "answers": report.answers,
        "evidence_level": report.evidence_level,
    }


@app.get("/claims/p-vs-np/catalog")
def p_vs_np_catalog() -> dict[str, Any]:
    return {
        "paths": {
            "A_P_eq_NP": PATH_A_REQUIREMENTS,
            "B_P_ne_NP": PATH_B_REQUIREMENTS,
        },
        "problem_modes": PROBLEM_MODES,
        "npc_families": NPC_FAMILIES,
        "error_discards": ERROR_DISCARDS,
        "barriers": BARRIER_ITEMS,
        "consequences": {
            "A_P_eq_NP": CONSEQUENCE_ITEMS_A,
            "B_P_ne_NP": CONSEQUENCE_ITEMS_B,
        },
        "approval_checklist": APPROVAL_CHECKLIST,
        "doc": "docs/P_VS_NP_CLAIM_GATE.md",
        "policy": (
            "This catalog defines what a purported resolution must address. "
            "The laboratory currently holds no resolution of P vs NP."
        ),
    }


@app.get("/claims/p-vs-np/template")
def p_vs_np_template(side: str | None = None) -> dict[str, Any]:
    cs: ClaimSide | None = None
    if side:
        try:
            cs = ClaimSide(side)
        except ValueError as exc:
            raise HTTPException(
                status_code=400,
                detail="side must be A_P_eq_NP or B_P_ne_NP",
            ) from exc
    return empty_dossier_template(cs)


@app.post("/claims/p-vs-np/gate")
def p_vs_np_gate(req: ClaimGateRequest) -> dict[str, Any]:
    try:
        dossier = ClaimDossier.model_validate(req.dossier)
    except Exception as exc:  # noqa: BLE001
        raise HTTPException(status_code=400, detail=f"invalid dossier: {exc}") from exc
    report = evaluate_gate(dossier)
    return report.to_dict()
