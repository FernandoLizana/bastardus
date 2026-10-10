"""Tseitin formulas on explicit graph families + structural metrics."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import networkx as nx
import numpy as np

from backend.models.cnf import CNFFormula


def xor_cnf(literals: list[int], charge: int) -> list[list[int]]:
    """CNF encoding of XOR(literals) = charge (mod 2)."""
    k = len(literals)
    clauses: list[list[int]] = []
    for mask in range(1 << k):
        parity = bin(mask).count("1") % 2
        if parity == charge:
            continue
        clause = []
        for i, lit in enumerate(literals):
            bit = (mask >> i) & 1
            clause.append(lit if bit == 0 else -lit)
        clauses.append(clause)
    return clauses


@dataclass(frozen=True)
class GraphInstance:
    graph: nx.Graph
    charges: tuple[int, ...]
    family: str
    seed: int
    metadata: dict[str, Any]

    @property
    def n(self) -> int:
        return self.graph.number_of_nodes()


def tseitin_cnf(inst: GraphInstance) -> CNFFormula:
    g = inst.graph
    # Map edges to variables 1..m
    edges = sorted(tuple(sorted(e)) for e in g.edges())
    e_index = {e: i + 1 for i, e in enumerate(edges)}
    clauses: list[list[int]] = []
    for v in sorted(g.nodes()):
        incident = [e_index[tuple(sorted((v, u)))] for u in g.neighbors(v)]
        clauses.extend(xor_cnf(incident, inst.charges[v] % 2))
    return CNFFormula.from_clauses(
        clauses,
        num_variables=len(edges),
        metadata={
            "family": inst.family,
            "seed": inst.seed,
            "charges": list(inst.charges),
            "n_vertices": inst.n,
            "n_edges": len(edges),
            "known_unsat": (sum(inst.charges) % 2 == 1) and nx.is_connected(g),
        },
    )


def odd_charge_vector(n: int, seed: int = 0) -> tuple[int, ...]:
    """Single odd charge at vertex 0 (total odd)."""
    c = [0] * n
    c[0] = 1
    return tuple(c)


def graph_metrics(g: nx.Graph) -> dict[str, Any]:
    n = g.number_of_nodes()
    if n == 0:
        return {}
    # Exact treewidth is hard; use NetworkX approximations / heuristics safely labelled.
    tw_approx = None
    try:
        # min_fill_in heuristic upper-bounds treewidth via elimination order
        tw_approx = nx.approximation.treewidth_min_fill_in(g)[0]
    except Exception:  # noqa: BLE001
        tw_approx = None
    degrees = [d for _, d in g.degree()]
    is_cycle = (
        n >= 3
        and nx.is_connected(g)
        and g.number_of_edges() == n
        and degrees
        and max(degrees) == 2
        and min(degrees) == 2
    )
    return {
        "n": n,
        "m": g.number_of_edges(),
        "max_degree": max(degrees) if degrees else 0,
        "min_degree": min(degrees) if degrees else 0,
        "connected": nx.is_connected(g),
        "treewidth_min_fill_upper": tw_approx,
        "note_tw": (
            "treewidth_min_fill_upper is a HEURISTIC UPPER BOUND, not exact tw. "
            "Do not treat equality conjectures involving this number as proven."
        ),
        "edge_connectivity": nx.edge_connectivity(g) if n > 1 and nx.is_connected(g) else 0,
        "is_tree": nx.is_tree(g),
        "is_cycle": is_cycle,
    }


def make_path(n: int, seed: int = 0) -> GraphInstance:
    g = nx.path_graph(n)
    return GraphInstance(g, odd_charge_vector(n, seed), "path", seed, {})


def make_cycle(n: int, seed: int = 0) -> GraphInstance:
    g = nx.cycle_graph(n)
    return GraphInstance(g, odd_charge_vector(n, seed), "cycle", seed, {})


def make_tree_random(n: int, seed: int = 0) -> GraphInstance:
    rng = np.random.default_rng(seed)
    # Prefer NetworkX random spanning tree generators available across versions
    if hasattr(nx, "random_labeled_tree"):
        g = nx.random_labeled_tree(n, seed=int(rng.integers(0, 2**31 - 1)))
    else:
        g = nx.random_tree(n, seed=int(rng.integers(0, 2**31 - 1)))
    return GraphInstance(g, odd_charge_vector(n, seed), "random_tree", seed, {})


def make_grid(a: int, b: int, seed: int = 0) -> GraphInstance:
    g = nx.grid_2d_graph(a, b)
    mapping = {node: i for i, node in enumerate(sorted(g.nodes()))}
    g = nx.relabel_nodes(g, mapping)
    n = g.number_of_nodes()
    return GraphInstance(g, odd_charge_vector(n, seed), f"grid_{a}x{b}", seed, {})


def make_barbell(k: int, seed: int = 0) -> GraphInstance:
    """Two cliques of size k joined by a bridge."""
    g = nx.barbell_graph(k, 0)
    n = g.number_of_nodes()
    return GraphInstance(g, odd_charge_vector(n, seed), f"barbell_{k}", seed, {})


def make_random_regular(n: int, d: int, seed: int = 0) -> GraphInstance:
    if n * d % 2 != 0:
        n += 1
    g = nx.random_regular_graph(d, n, seed=seed)
    return GraphInstance(g, odd_charge_vector(n, seed), f"reg_{d}", seed, {})


def make_two_cycles_bridge(a: int, b: int, seed: int = 0) -> GraphInstance:
    """Bottleneck: cycles sharing one bridge edge endpoints connected by a single edge."""
    g = nx.Graph()
    # cycle A: 0..a-1
    for i in range(a):
        g.add_edge(i, (i + 1) % a)
    # cycle B: a..a+b-1
    base = a
    for i in range(b):
        u = base + i
        v = base + ((i + 1) % b)
        g.add_edge(u, v)
    g.add_edge(0, base)  # bridge
    n = a + b
    return GraphInstance(g, odd_charge_vector(n, seed), f"two_cycles_{a}_{b}", seed, {})
