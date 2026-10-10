"""Bicyclic length-2 chord + K4 minor lower-bound tests."""

import networkx as nx

from backend.proof_complexity.constructive_proofs import (
    prove_bicyclic_len2_chord_lemma,
    verify_resolution_derivation,
)
from backend.proof_complexity.k4_minor_lower_bound import (
    has_k4_minor_crossing,
    k4_width_certificate,
    verify_all_crossing_have_k4_minor,
)


def test_bicyclic_len2_chord_family() -> None:
    checked = 0
    for n in range(4, 10):
        g = nx.cycle_graph(n)
        g.add_edge(0, 2)
        if max(d for _, d in g.degree()) > 3:
            continue
        proof = prove_bicyclic_len2_chord_lemma(g, {v: int(v == 0) for v in g.nodes()})
        assert verify_resolution_derivation(proof) == []
        assert proof.max_width <= proof.delta
        checked += 1
    assert checked >= 5


def test_k4_width_gt_delta() -> None:
    cert = k4_width_certificate()
    assert cert["certified_gt_delta"]
    assert cert["width"] == 4
    assert cert["delta"] == 3
    assert cert["empty_at_width_3"] is False
    assert cert["empty_at_width_4"] is True


def test_all_crossing_have_k4_minor() -> None:
    fam = verify_all_crossing_have_k4_minor(5, 10)
    assert fam["checked_crossing"] > 0
    assert fam["missing_k4_minor"] == []
    assert has_k4_minor_crossing(6, (0, 2), (1, 3))
    assert not has_k4_minor_crossing(6, (0, 2), (3, 5))


def test_k4_lift_charge_contraction_family() -> None:
    from backend.proof_complexity.k4_minor_lower_bound import (
        verify_lift_ingredients_family,
    )

    lift = verify_lift_ingredients_family(5, 8)
    assert lift["checked_ok"] > 0
    assert lift["bad_k4"] == []
    assert lift["bad_g_not_gt_delta"] == []
