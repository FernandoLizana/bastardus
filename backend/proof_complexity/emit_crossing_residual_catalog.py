"""E2 catalog: residual Closure₃ + signed iso to k4Axioms for all crossings n=5..10.

Closes the evidence gap between mass shape checks and per-instance identification:
every residual is set-isomorphic to k4Axioms under a signed edge bijection.

Feeds Lean `CrossingResidualCatalog` / ParametricClosure3 (G5).
"""

from __future__ import annotations

import ast
import itertools
import json
import re
from pathlib import Path

import networkx as nx

from backend.models.cnf import CNFFormula
from backend.proof_complexity.constructive_proofs import (
    _ProofBuilder,
    _all_axioms,
    _edge_var_map,
    _xor_clauses_for_vertex,
)
from backend.proof_complexity.k4_minor_lower_bound import crossing_branch_sets
from backend.proof_complexity.k4_path_contraction_derivation import _odd_charge_for_crossing
from backend.proof_complexity.k4_projection_restriction import _width_closure_clauses
from backend.proof_complexity.multihop_projection_mass import chord_pairs
from backend.proof_complexity.path_fold import fold_deg2_tip
from backend.proof_complexity.width import _norm

ROOT = Path(__file__).resolve().parents[2]
LEAN_K4 = ROOT / "lean" / "PNPLab" / "K4Width3.lean"
OUT = ROOT / "reports" / "discovery" / "crossing_residual_catalog.json"
OUT_SUMMARY = ROOT / "reports" / "discovery" / "crossing_residual_catalog_mass.json"


def _extract_k4_axioms() -> list[list[int]]:
    text = LEAN_K4.read_text(encoding="utf-8")
    pattern = (
        r"(?:def|abbrev)\s+k4Axioms\s*:\s*List Clause\s*:=\s*(\[.*?\n\s*\])"
    )
    m = re.search(pattern, text, re.S)
    if not m:
        raise ValueError("cannot extract k4Axioms")
    raw = re.sub(r"\(\s*(-?\d+)\s*:\s*Lit\s*\)", r"\1", m.group(1))
    return ast.literal_eval(raw)


def _clause_set(clauses: list[list[int]] | list[tuple[int, ...]]) -> frozenset[tuple[int, ...]]:
    return frozenset(tuple(sorted(c)) for c in clauses)


def _find_signed_iso(
    clauses: list[list[int]] | list[tuple[int, ...]],
    src: list[int],
    target: frozenset[tuple[int, ...]],
) -> dict | None:
    """Prefer permutation-only; fall back to signed flips."""
    src_t = tuple(src)
    clauses_t = [tuple(c) for c in clauses]

    def try_bits(bits: int) -> dict | None:
        for perm in itertools.permutations(range(1, 7)):
            mapping = {
                src_t[i]: perm[i] * (-1 if (bits >> i) & 1 else 1)
                for i in range(6)
            }
            mapped = frozenset(
                tuple(
                    sorted(
                        (1 if lit > 0 else -1) * mapping[abs(lit)]
                        for lit in clause
                    )
                )
                for clause in clauses_t
            )
            if mapped == target:
                return {
                    "src": list(src_t),
                    "dst_signed": [mapping[v] for v in src_t],
                    "permutation": list(perm),
                    "flips": [mapping[v] < 0 for v in src_t],
                    "needs_flips": bits != 0,
                }
        return None

    hit = try_bits(0)
    if hit is not None:
        return hit
    for bits in range(1, 64):
        hit = try_bits(bits)
        if hit is not None:
            return hit
    return None


def _xor_axioms(work, charges, e_index) -> list[tuple[int, ...]]:
    axs: list[tuple[int, ...]] = []
    for v in work.nodes():
        for raw in _xor_clauses_for_vertex(work, e_index, v, charges[v]):
            n = _norm(raw)
            if n is not None and n not in axs:
                axs.append(n)
    return axs


def _edge_vars(work, e_index) -> list[int]:
    return sorted(
        {
            e_index[tuple(sorted(e))]
            for e in work.edges()
            if tuple(sorted(e)) in e_index
        }
    )


def residual_of(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
    charges0 = _odd_charge_for_crossing(n, c1, c2)
    g0 = nx.cycle_graph(n)
    g0.add_edges_from([c1, c2])
    ends, arcs = crossing_branch_sets(n, c1, c2)
    e_index = _edge_var_map(g0)
    builder = _ProofBuilder(
        _all_axioms(g0, charges0, e_index),
        delta=max(d for _, d in g0.degree()),
    )
    work = g0.copy()
    charges = dict(charges0)
    tips = 0
    for arc in arcs:
        path = list(arc)
        while path:
            tip = path.pop(0)
            fold_deg2_tip(builder, work, charges, e_index, tip)
            tips += 1
    axioms = _xor_axioms(work, charges, e_index)
    form = CNFFormula.from_clauses(
        [list(c) for c in axioms],
        num_variables=max((abs(lit) for c in axioms for lit in c), default=1),
    )
    closed = sorted(
        _width_closure_clauses(form, 3),
        key=lambda c: (len(c), c),
    )
    vars_ = _edge_vars(work, e_index)
    return {
        "n": n,
        "chords": [list(c1), list(c2)],
        "tips": tips,
        "Vres": vars_,
        "RAxioms": [list(c) for c in closed],
        "closed_size": len(closed),
        "has_empty": () in closed or [] in closed,
        "shape_ok": (
            work.number_of_nodes() == 4
            and work.number_of_edges() == 6
            and len(vars_) == 6
            and len(closed) == 16
            and () not in closed
        ),
    }


def main() -> int:
    k4 = _extract_k4_axioms()
    target = _clause_set(k4)

    instances: list[dict] = []
    tip_hist: dict[str, int] = {str(i): 0 for i in range(1, 7)}
    iso_ok = 0
    shape_ok = 0
    flip_needed = 0
    fail_samples: list[dict] = []

    for n in range(5, 11):
        for c1, c2 in chord_pairs(n):
            res = residual_of(n, c1, c2)
            witness = None
            found = False
            if res["shape_ok"]:
                shape_ok += 1
                tip_hist[str(res["tips"])] = tip_hist.get(str(res["tips"]), 0) + 1
                witness = _find_signed_iso(res["RAxioms"], res["Vres"], target)
                found = witness is not None
                if found:
                    iso_ok += 1
                    if witness.get("needs_flips"):
                        flip_needed += 1
                else:
                    if len(fail_samples) < 5:
                        fail_samples.append(
                            {
                                "n": res["n"],
                                "chords": res["chords"],
                                "tips": res["tips"],
                                "Vres": res["Vres"],
                                "reason": "no_signed_iso",
                            }
                        )
            else:
                if len(fail_samples) < 5:
                    fail_samples.append(
                        {
                            "n": res["n"],
                            "chords": res["chords"],
                            "tips": res["tips"],
                            "reason": "bad_shape",
                            "closed_size": res["closed_size"],
                        }
                    )

            # Keep catalog lean: store iso witness + sizes, not full clause dump
            # (clause lists recoverable via residual_of; packs already hold Lean witnesses).
            instances.append(
                {
                    "n": res["n"],
                    "chords": res["chords"],
                    "tips": res["tips"],
                    "Vres": res["Vres"],
                    "closed_size": res["closed_size"],
                    "shape_ok": res["shape_ok"],
                    "iso_found": found,
                    "witness": witness,
                }
            )

    total = len(instances)
    mass = {
        "total": total,
        "shape_ok": shape_ok,
        "iso_ok": iso_ok,
        "iso_fail": total - iso_ok,
        "flip_needed_count": flip_needed,
        "tip_histogram": tip_hist,
        "all_shape_and_iso": shape_ok == total and iso_ok == total,
        "fail_samples": fail_samples,
        "claim": (
            "Every crossing n=5..10 residual Closure₃ is set-isomorphic to "
            "k4Axioms under a signed edge-variable bijection "
            "(permutation ± optional complementation)."
        ),
        "lean": "lean/PNPLab/CrossingResidualCatalog.lean",
        "catalog": "reports/discovery/crossing_residual_catalog.json",
    }

    catalog = {
        "total": total,
        "iso_ok": iso_ok,
        "shape_ok": shape_ok,
        "k4_template_vars": [1, 2, 3, 4, 5, 6],
        "instances": instances,
        "mass": "reports/discovery/crossing_residual_catalog_mass.json",
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(catalog, indent=2), encoding="utf-8")
    OUT_SUMMARY.write_text(json.dumps(mass, indent=2), encoding="utf-8")
    print(
        f"wrote {OUT} and {OUT_SUMMARY} "
        f"shape={shape_ok}/{total} iso={iso_ok}/{total} flips={flip_needed}"
    )
    return 0 if mass["all_shape_and_iso"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
