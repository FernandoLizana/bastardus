"""Tests for the C_n + 2 chords crossing ↔ Width>Δ law."""

import networkx as nx
from itertools import combinations

from backend.proof_complexity.chord_crossing_law import (
    chords_cross_on_cycle,
    predict_width_vs_delta_cycle_two_chords,
)
from backend.proof_complexity.chord_law_search import _bitsat_complete, _chord_config
from backend.proof_complexity.gpu_width_opencl import (
    batch_has_refutation_gpu,
    formula_to_bit_axioms,
)
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf


def _label(n: int, chords: tuple[tuple[int, int], tuple[int, int]]) -> str:
    g = nx.cycle_graph(n)
    g.add_edges_from(chords)
    delta = max(d for _, d in g.degree())
    charges = tuple(1 if i == 0 else 0 for i in range(n))
    bits = formula_to_bit_axioms(tseitin_cnf(GraphInstance(g, charges, "tri", 0, {})))
    if batch_has_refutation_gpu([bits], [delta])[0]:
        return "eq"
    ok, complete = _bitsat_complete(bits, delta)
    if ok:
        return "eq"
    assert complete
    return "gt"


def test_crossing_law_known_witnesses() -> None:
    assert not chords_cross_on_cycle(6, (0, 2), (3, 5))
    assert chords_cross_on_cycle(6, (0, 2), (1, 3))
    assert predict_width_vs_delta_cycle_two_chords(6, (0, 2), (3, 5)) == "eq"
    assert predict_width_vs_delta_cycle_two_chords(6, (0, 2), (1, 3)) == "gt"
    assert _label(6, ((0, 2), (3, 5))) == "eq"
    assert _label(6, ((0, 2), (1, 3))) == "gt"


def test_crossing_law_exhaustive_n6_to_8() -> None:
    for n in range(6, 9):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        for chords in combinations(non, 2):
            g = base.copy()
            g.add_edges_from(chords)
            if g.number_of_edges() != n + 2:
                continue
            if max(d for _, d in g.degree()) > 3:
                continue
            if len({*chords[0], *chords[1]}) < 4:
                continue
            pred = predict_width_vs_delta_cycle_two_chords(n, chords[0], chords[1])
            # agree with config helper
            assert _chord_config(n, chords[0], chords[1])["relation"] == (
                "crossing" if pred == "gt" else "disjoint"
            )
            assert _label(n, chords) == pred


def test_n5_all_crossing_all_gt() -> None:
    n = 5
    base = nx.cycle_graph(n)
    non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
    hits = 0
    for chords in combinations(non, 2):
        g = base.copy()
        g.add_edges_from(chords)
        if max(d for _, d in g.degree()) > 3:
            continue
        if len({*chords[0], *chords[1]}) < 4:
            continue
        assert chords_cross_on_cycle(n, chords[0], chords[1])
        assert _label(n, chords) == "gt"
        hits += 1
    assert hits == 5
