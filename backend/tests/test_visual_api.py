"""API visual payload smoke tests."""

from fastapi.testclient import TestClient

from backend.api.main import app


def test_help_and_reduction_visual() -> None:
    client = TestClient(app)
    assert len(client.get("/help/topics").json()) >= 4
    dimacs = "p cnf 3 2\n1 2 3 0\n-1 -2 3 0\n"
    r = client.post(
        "/visual/reduction-graph",
        json={"dimacs": dimacs, "reduction": "3sat_to_clique"},
    )
    assert r.status_code == 200
    body = r.json()
    assert len(body["nodes"]) == 6
    assert body["k"] == 2
    assert body["steps"]


def test_phase_snapshot_endpoint() -> None:
    client = TestClient(app)
    r = client.post(
        "/visual/phase-snapshot",
        json={"num_variables": 8, "instances_per_ratio": 3, "seed": 1},
    )
    assert r.status_code == 200
    series = r.json()["series"]
    assert len(series) >= 5
    assert "disclaimer" in r.json()
