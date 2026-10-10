"""Adversarial and structured instance generators (reproducible).

These families are *motivated* by proof-complexity / hardness literature.
Generating them does not prove asymptotic hardness of SAT (≤ E2 provenance).
"""

from __future__ import annotations

import hashlib
import platform
import socket
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from typing import Any

import numpy as np

from backend import __version__
from backend.models.cnf import CNFFormula
from backend.reductions.hamiltonian_tsp import HamiltonianInstance


def _provenance(generator: str, params: dict[str, Any], extra: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = {
        "generator": generator,
        "parameters": params,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "host": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "code_version": __version__,
        "known_answer": None,
        "confirming_solver": None,
        "evidence_level": "E2_instance_provenance",
        "warnings": [
            "Structured generators do not by themselves prove worst-case hardness.",
            "Finite instances never settle asymptotic complexity claims.",
        ],
    }
    if extra:
        payload.update(extra)
    blob = repr(params).encode() + repr(extra).encode()
    payload["instance_hash_seed"] = hashlib.sha256(blob).hexdigest()
    return payload


@dataclass(frozen=True)
class PigeonholeParams:
    holes: int
    seed: int = 0


def generate_pigeonhole(params: PigeonholeParams) -> CNFFormula:
    """PHP^{n+1}_n: n+1 pigeons, n holes — classically unsatisfiable.

    Encoding: variables x_{p,h} (pigeon p in hole h).
    Clauses: each pigeon in some hole; at most one pigeon per hole.
    Reference: classic proof-complexity hard examples for resolution
    (Haken 1985 and follow-ups). Evidence for hardness here: literature
    known_result; our encoding is E2 provenance only.
    """
    n = params.holes
    pigeons = n + 1
    # var id: pigeon p in [0, pigeons), hole h in [0, n) → 1 + p*n + h
    def vid(p: int, h: int) -> int:
        return 1 + p * n + h

    clauses: list[list[int]] = []
    for p in range(pigeons):
        clauses.append([vid(p, h) for h in range(n)])
    for h in range(n):
        for p1 in range(pigeons):
            for p2 in range(p1 + 1, pigeons):
                clauses.append([-vid(p1, h), -vid(p2, h)])
    meta = _provenance(
        "pigeonhole",
        asdict(params),
        {
            "known_answer": False,
            "confirming_solver": "by_construction_unsat",
            "literature_cue": "Haken 1985 resolution lower bounds (PHP)",
        },
    )
    return CNFFormula.from_clauses(clauses, num_variables=pigeons * n, metadata=meta)


@dataclass(frozen=True)
class TseitinParams:
    """Tseitin formulas on a random 3-regular graph (even #vertices)."""

    num_vertices: int
    seed: int = 0
    charge_odd: bool = True


def generate_tseitin(params: TseitinParams) -> CNFFormula:
    """Tseitin encoding on a 3-regular graph.

    If the total charge is odd, the formula is unsatisfiable.
    Reference: Tseitin (1968/1970); Urquhart — hard for resolution on expanders.
    """
    n = params.num_vertices
    if n < 4 or n % 2 != 0:
        raise ValueError("Tseitin generator needs even num_vertices ≥ 4")
    rng = np.random.default_rng(params.seed)

    # Configuration model for 3-regular multigraph, then simplify
    stubs = []
    for v in range(n):
        stubs.extend([v, v, v])
    rng.shuffle(stubs)
    edges: set[tuple[int, int]] = set()
    for i in range(0, len(stubs), 2):
        a, b = stubs[i], stubs[i + 1]
        if a == b:
            continue
        e = (a, b) if a < b else (b, a)
        edges.add(e)
    # Ensure roughly regular simple graph; top-up with random edges if needed
    deg = {v: 0 for v in range(n)}
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    # Edge variables
    edge_list = sorted(edges)
    if not edge_list:
        raise RuntimeError("Failed to sample edges for Tseitin formula")
    e_index = {e: i + 1 for i, e in enumerate(edge_list)}

    charges = [0] * n
    if params.charge_odd:
        charges[0] = 1  # odd parity total

    clauses: list[list[int]] = []
    # For each vertex, XOR of incident edge vars equals charge.
    # For degree d, expand into 2^{d-1} clauses — for d=3: 4 clauses.
    for v in range(n):
        incident = [e_index[e] for e in edge_list if v in e]
        if len(incident) == 0:
            if charges[v] == 1:
                clauses.append([])  # empty → unsat
            continue
        d = len(incident)
        # All assignments to incident vars with parity != charge are forbidden
        for mask in range(1 << d):
            parity = bin(mask).count("1") % 2
            if parity == charges[v]:
                continue
            clause = []
            for i, litvar in enumerate(incident):
                bit = (mask >> i) & 1
                clause.append(litvar if bit == 0 else -litvar)
            clauses.append(clause)

    meta = _provenance(
        "tseitin",
        asdict(params),
        {
            "known_answer": False if params.charge_odd else None,
            "confirming_solver": "parity_argument" if params.charge_odd else None,
            "num_edges": len(edge_list),
            "literature_cue": "Tseitin / Urquhart expander hardness cues",
        },
    )
    return CNFFormula.from_clauses(clauses, num_variables=len(edge_list), metadata=meta)


@dataclass(frozen=True)
class SubsetSumParams:
    num_items: int
    seed: int = 0
    bits: int = 16
    force_unsat_shift: bool = False


@dataclass(frozen=True)
class SubsetSumInstance:
    numbers: tuple[int, ...]
    target: int
    metadata: dict[str, Any]


def generate_hard_subset_sum(params: SubsetSumParams) -> SubsetSumInstance:
    """Dense random Subset Sum instance (Pisinger-style density ≈ 1).

    Pseudo-polynomial DP still solves moderate sizes — documenting that
    "solvable" ≠ poly-time in the bit model (methodology barrier).
    """
    rng = np.random.default_rng(params.seed)
    hi = 1 << params.bits
    nums = tuple(int(x) for x in rng.integers(1, hi, size=params.num_items))
    # Plant a subset for sat, or shift target for unsat
    mask_bits = params.num_items // 2
    chosen = rng.choice(params.num_items, size=max(mask_bits, 1), replace=False)
    target = int(sum(nums[i] for i in chosen))
    known = True
    if params.force_unsat_shift:
        target += 1
        # May still accidentally be sat; mark unknown unless verified later
        known = False
    meta = _provenance(
        "hard_subset_sum",
        asdict(params),
        {
            "known_answer": known if not params.force_unsat_shift else None,
            "planted_indices": [int(i) for i in chosen] if not params.force_unsat_shift else None,
            "warning_pseudo_polynomial": (
                "Subset Sum has O(nT) DP — pseudo-polynomial, not Turing-poly."
            ),
        },
    )
    return SubsetSumInstance(numbers=nums, target=target, metadata=meta)


def verify_subset_sum(inst: SubsetSumInstance, subset_indices: list[int]) -> bool:
    if len(set(subset_indices)) != len(subset_indices):
        return False
    if any(i < 0 or i >= len(inst.numbers) for i in subset_indices):
        return False
    return sum(inst.numbers[i] for i in subset_indices) == inst.target


def subset_sum_dp_solvable(inst: SubsetSumInstance) -> bool:
    """Classic DP reachability — illustrates pseudo-polynomial behaviour."""
    achievable = {0}
    for x in inst.numbers:
        achievable |= {s + x for s in achievable if s + x <= inst.target}
    return inst.target in achievable


@dataclass(frozen=True)
class CraftedHamiltonianParams:
    num_vertices: int
    seed: int = 0
    make_nonhamiltonian: bool = False


def generate_crafted_hamiltonian(params: CraftedHamiltonianParams) -> HamiltonianInstance:
    """Cycle + random chords (sat) or disconnected almost-cycle (unsat)."""
    n = params.num_vertices
    if n < 3:
        raise ValueError("need n≥3")
    rng = np.random.default_rng(params.seed)
    edges: set[tuple[int, int]] = set()
    for i in range(n):
        a, b = i, (i + 1) % n
        edges.add((a, b) if a < b else (b, a))
    # add a few chords
    for _ in range(max(n // 2, 1)):
        u, v = int(rng.integers(0, n)), int(rng.integers(0, n))
        if u == v:
            continue
        edges.add((u, v) if u < v else (v, u))
    known = True
    if params.make_nonhamiltonian and n >= 4:
        # Remove a bridge-like cut: delete all edges incident to vertex 0 except one stub removed totally
        edges = {e for e in edges if 0 not in e}
        # isolate vertex 0
        known = False
    meta = _provenance(
        "crafted_hamiltonian",
        asdict(params),
        {"known_answer": known if not params.make_nonhamiltonian else False},
    )
    return HamiltonianInstance(num_vertices=n, edges=frozenset(edges), metadata=meta)
