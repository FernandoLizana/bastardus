"""Ear-clip structural reduction tests."""

import networkx as nx

from backend.proof_complexity.ear_clip_certificates import (
    classify_residual,
    clip_length2_ears,
    prove_residual,
    run_family,
)
from backend.proof_complexity.constructive_proofs import verify_resolution_derivation


def test_c6_two_triangles_clips_to_cycle() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    charges = {v: int(v == 0) for v in g.nodes()}
    g2, c2, log = clip_length2_ears(g, charges)
    assert len(log) == 2
    assert classify_residual(g2) == "cycle"
    proof, kind = prove_residual(g2, c2)
    assert kind == "cycle"
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width == 2


def test_ear_clip_family_smoke() -> None:
    report = run_family(6, 8)
    assert report["failed"] == []
    assert report["ok"] == report["checked"]
    assert report["by_residual"].get("cycle", 0) == report["ok"]
