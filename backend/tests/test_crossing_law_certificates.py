"""Constructive certificates for the C_n + 2 chords crossing law."""

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    certify_crossing_width_gt_delta,
    prove_noncrossing_two_chords_lemma,
    verify_resolution_derivation,
)


def test_noncrossing_constructive_witness() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    charges = {v: int(v == 0) for v in g.nodes()}
    proof = prove_noncrossing_two_chords_lemma(g, charges)
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta == 3


def test_noncrossing_rejects_crossing() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (1, 3)])
    try:
        prove_noncrossing_two_chords_lemma(g, {v: int(v == 0) for v in g.nodes()})
        raise AssertionError("expected ValueError for crossing chords")
    except ValueError as exc:
        assert "cross" in str(exc).lower()


def test_crossing_lower_bound_certificate() -> None:
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (1, 3)])
    cert = certify_crossing_width_gt_delta(g, {v: int(v == 0) for v in g.nodes()})
    assert cert["certified"] == "Width > Δ"
    assert cert["empty_at_delta_core"] is False
    assert cert["delta_core"] == 3
    assert cert["closure_size_at_delta_core"] > 0


def test_pendant_noncrossing_and_crossing_core() -> None:
    # Non-crossing core + leaf
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    g.add_edge(1, 6)
    proof = prove_noncrossing_two_chords_lemma(g, {v: int(v == 6) for v in g.nodes()})
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta

    # Crossing core + leaf attached to a deg-2 vertex ⇒ Δ stays 3 ⇒ Width > Δ
    g2 = nx.cycle_graph(6)
    g2.add_edges_from([(0, 2), (1, 3)])
    # vertex 4 has only cycle edges (deg 2)
    g2.add_edge(4, 6)
    cert = certify_crossing_width_gt_delta(g2, {v: int(v == 6) for v in g2.nodes()})
    assert cert["certified"] == "Width > Δ"
    assert cert["peeled_leaves"] == 1


def test_noncrossing_family_n6_n7() -> None:
    from itertools import combinations

    from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle

    for n in (6, 7):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        proved = 0
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            if chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            proof = prove_noncrossing_two_chords_lemma(
                g, {v: int(v == 0) for v in g.nodes()}
            )
            assert verify_resolution_derivation(proof) == []
            proved += 1
        assert proved >= 1


def test_len2_ears_resolution_proof_family() -> None:
    from itertools import combinations

    from backend.proof_complexity.chord_crossing_law import (
        chords_cross_on_cycle,
        circular_dist,
    )
    from backend.proof_complexity.constructive_proofs import (
        prove_noncrossing_len2_ears_lemma,
    )

    checked = 0
    for n in range(6, 9):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        for chords in combinations(non, 2):
            if len({*chords[0], *chords[1]}) < 4:
                continue
            if chords_cross_on_cycle(n, chords[0], chords[1]):
                continue
            if circular_dist(n, *chords[0]) != 2 or circular_dist(n, *chords[1]) != 2:
                continue
            g = base.copy()
            g.add_edges_from(chords)
            if max(d for _, d in g.degree()) > 3:
                continue
            proof = prove_noncrossing_len2_ears_lemma(
                g, {v: int(v == 0) for v in g.nodes()}
            )
            assert verify_resolution_derivation(proof) == []
            assert proof.max_width <= proof.delta
            checked += 1
    assert checked >= 3
