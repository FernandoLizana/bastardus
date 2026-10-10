"""Constructive proof verification tests."""

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    prove_bicyclic_lemma,
    prove_cycle_lemma,
    prove_tree_lemma,
    prove_unicyclic_lemma,
    verify_resolution_derivation,
)
from backend.proof_complexity.tseitin_family import (
    GraphInstance,
    make_cycle,
    make_path,
    make_tree_random,
    tseitin_cnf,
)
from backend.proof_complexity.width import min_resolution_width


def test_constructive_paths_match_exact_width() -> None:
    for n in range(2, 9):
        inst = make_path(n)
        charges = {v: inst.charges[v] for v in inst.graph.nodes()}
        proof = prove_tree_lemma(inst.graph, charges)
        assert verify_resolution_derivation(proof) == []
        exact = min_resolution_width(tseitin_cnf(inst)).claimed_min_width
        assert proof.max_width == exact == proof.delta


def test_constructive_random_trees() -> None:
    for n in range(3, 9):
        for seed in range(5):
            inst = make_tree_random(n, seed=seed)
            charges = {v: inst.charges[v] for v in inst.graph.nodes()}
            proof = prove_tree_lemma(inst.graph, charges)
            assert verify_resolution_derivation(proof) == []
            assert proof.max_width == proof.delta


def test_constructive_cycles() -> None:
    for n in range(3, 10):
        inst = make_cycle(n)
        charges = {v: inst.charges[v] for v in inst.graph.nodes()}
        proof = prove_cycle_lemma(inst.graph, charges)
        assert verify_resolution_derivation(proof) == []
        assert proof.max_width == 2


def _make_unicyclic(n: int, chord: tuple[int, int] | None = None) -> nx.Graph:
    """Path 0..n-1 plus a chord yielding a unique cycle."""
    g = nx.path_graph(n)
    if chord is None:
        if n == 3:
            g.add_edge(0, 2)
        else:
            g.add_edge(max(0, n - 3), n - 1)
    else:
        g.add_edge(*chord)
    assert g.number_of_edges() == n
    return g


def test_constructive_unicyclic_families() -> None:
    for n in range(3, 10):
        g = _make_unicyclic(n)
        charges = {v: 0 for v in g.nodes()}
        charges[0] = 1
        proof = prove_unicyclic_lemma(g, charges)
        assert verify_resolution_derivation(proof) == []
        assert proof.max_width <= proof.delta

    g = nx.cycle_graph(5)
    g.add_node(5)
    g.add_edge(0, 5)
    proof = prove_unicyclic_lemma(g, {v: int(v == 5) for v in g.nodes()})
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta


def test_constructive_unicyclic_matches_exact_width() -> None:
    for n in range(3, 8):
        g = _make_unicyclic(n)
        charges_t = tuple(1 if v == 0 else 0 for v in range(n))
        inst = GraphInstance(g, charges_t, "unicyclic", 0, {})
        proof = prove_unicyclic_lemma(g, {v: charges_t[v] for v in g.nodes()})
        exact = min_resolution_width(tseitin_cnf(inst)).claimed_min_width
        assert exact == proof.delta
        assert proof.max_width == exact


def _make_bicyclic(n: int) -> nx.Graph:
    """Cycle plus one chord ⇒ |E|=n+1."""
    g = nx.cycle_graph(n)
    g.add_edge(0, max(2, n // 2))
    assert g.number_of_edges() == n + 1
    return g


def test_constructive_bicyclic_families() -> None:
    for n in range(4, 8):
        g = _make_bicyclic(n)
        if max(d for _, d in g.degree()) > 3:
            continue
        charges = {v: int(v == 0) for v in g.nodes()}
        proof = prove_bicyclic_lemma(g, charges)
        assert verify_resolution_derivation(proof) == []
        assert proof.max_width <= proof.delta

    # Butterfly (figure-8): two triangles sharing a vertex
    g = nx.Graph([(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)])
    assert g.number_of_edges() == g.number_of_nodes() + 1
    proof = prove_bicyclic_lemma(g, {v: int(v == 0) for v in g.nodes()})
    assert verify_resolution_derivation(proof) == []
    assert proof.max_width <= proof.delta


def test_constructive_bicyclic_matches_exact_width() -> None:
    for n in range(4, 7):
        g = _make_bicyclic(n)
        if max(d for _, d in g.degree()) > 3:
            continue
        charges_t = tuple(1 if v == 0 else 0 for v in range(n))
        inst = GraphInstance(g, charges_t, "bicyclic", 0, {})
        proof = prove_bicyclic_lemma(g, {v: charges_t[v] for v in g.nodes()})
        exact = min_resolution_width(tseitin_cnf(inst)).claimed_min_width
        assert exact == proof.delta
        assert proof.max_width == exact


def test_tricyclic_can_equal_delta_witness() -> None:
    """C6 + antipodal length-2 chords: first known γ=3 instance with W=Δ."""
    g = nx.cycle_graph(6)
    g.add_edges_from([(0, 2), (3, 5)])
    assert g.number_of_edges() == 8  # γ = 3
    delta = max(d for _, d in g.degree())
    charges = {v: int(v == 0) for v in g.nodes()}
    inst = GraphInstance(g, tuple(charges[v] for v in range(6)), "tri_eq", 0, {})
    exact = min_resolution_width(tseitin_cnf(inst), max_width=8).claimed_min_width
    assert delta == 3
    assert exact == delta
