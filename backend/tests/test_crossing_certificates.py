"""Constructive / lower-bound certificates for the crossing law."""

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    certify_crossing_width_gt_delta,
    prove_noncrossing_two_chords_lemma,
    verify_resolution_derivation,
)


def test_noncrossing_constructive_c6() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    proof = prove_noncrossing_two_chords_lemma(g, {v: int(v == 0) for v in g.nodes()})
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta == 3


def test_noncrossing_rejects_crossing() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (1, 3)])
    try:
        prove_noncrossing_two_chords_lemma(g, {v: int(v == 0) for v in g.nodes()})
        raise AssertionError("expected ValueError")
    except ValueError as exc:
        assert "cross" in str(exc).lower()


def test_crossing_lower_bound_c6() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (1, 3)])
    cert = certify_crossing_width_gt_delta(g, {v: int(v == 0) for v in g.nodes()})
    assert cert["empty_at_delta"] is False
    assert cert["certified"] == "Width > Δ"
    assert cert["closure_size_at_delta"] > 0


def test_noncrossing_with_pendant() -> None:
    """Peel reduces pendant to a non-crossing C6+2chords core."""
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    g.add_node(6)
    g.add_edge(0, 6)
    charges = {v: 0 for v in g.nodes()}
    charges[6] = 1
    proof = prove_noncrossing_two_chords_lemma(g, charges)
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta
