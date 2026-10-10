"""Extra coverage for reductions, conjectures, API smoke."""

from __future__ import annotations

from fastapi.testclient import TestClient

from backend.api.main import app
from backend.complexity import asymptotic_disclaimer
from backend.conjectures import Conjecture, ConjectureStatus, ConjectureStore
from backend.core.evidence import EvidenceLevel
from backend.core.logging_config import configure_logging, get_logger
from backend.core.metrics import SolverMetrics, timed_call
from backend.models.cnf import CNFFormula, complete_assignment, assignment_from_list
from backend.proof_auditor import audit_proof_file
from backend.reductions.sat_to_clique import (
    solve_clique_bruteforce,
    three_sat_to_clique,
    verify_clique,
)
from backend.research_barriers import run_barrier_checklist
from backend.solvers.brute_force import BruteForceSAT
from pathlib import Path


def test_verify_clique_and_solver() -> None:
    f = CNFFormula.from_clauses([[1, 2, 3]], num_variables=3)
    red = three_sat_to_clique(f)
    inst = red.mapping_metadata["instance"]
    assert solve_clique_bruteforce(inst) is True
    # invalid certificate
    assert verify_clique(inst, []) is False


def test_bruteforce_refuses_large() -> None:
    f = CNFFormula.from_clauses([[1]], num_variables=30)
    r = BruteForceSAT().solve(f)
    assert r.satisfiable is None
    assert r.metrics.timed_out


def test_conjecture_store(tmp_path: Path) -> None:
    store = ConjectureStore(tmp_path / "c.json")
    c = Conjecture(
        identifier="C-test",
        formal_statement="forall finite samples, ...",
        motivation="test",
        variables=["n"],
        domain="test",
        status=ConjectureStatus.IDEA,
        evidence_level=EvidenceLevel.E0_INFORMAL,
    )
    store.add(c)
    store.refute("C-test", {"n": 1}, "found counterexample")
    assert store.list()[0].status == ConjectureStatus.REFUTED


def test_api_health_and_solve() -> None:
    client = TestClient(app)
    assert client.get("/health").json()["status"] == "ok"
    r = client.post(
        "/solve",
        json={"dimacs": "p cnf 1 1\n1 0\n", "solver": "dpll"},
    )
    assert r.status_code == 200
    assert r.json()["satisfiable"] is True
    g = client.post(
        "/generate/random-ksat",
        json={"num_variables": 5, "ratio": 3.0, "seed": 1},
    )
    assert g.status_code == 200
    a = client.post("/audit/proof", json={"text": "Theorem. Experiments show P = NP."})
    assert a.status_code == 200
    b = client.get("/barriers")
    assert len(b.json()) >= 10
    c = client.post(
        "/barriers/checklist",
        json={"proposal": "diagonalization only", "claims": {}},
    )
    assert "markdown" in c.json()


def test_helpers() -> None:
    assert "polynomial" in asymptotic_disclaimer().lower()
    configure_logging()
    get_logger("test")
    m = SolverMetrics()
    assert timed_call(lambda: 42, m) == 42
    assert assignment_from_list([True, False])[1] is True
    f = CNFFormula.from_clauses([[1]], num_variables=1)
    assert complete_assignment(f, {})[1] is False
    report = run_barrier_checklist("only AC0 circuits", claims={"restricted_circuit_model": True})
    assert report.flags
    # audit file
    p = Path("docs/PROOF_AUDIT_GUIDE.md")
    assert "Proof Audit" in audit_proof_file(p).to_markdown()
