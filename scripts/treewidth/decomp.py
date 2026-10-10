"""Tree decomposition export: elimination order → path decomp + verification."""

from __future__ import annotations

import random
from dataclasses import dataclass, asdict
from typing import Any

import networkx as nx

from treewidth.compute import (
    _elimination_width_graph,
    _exact_treewidth,
    _has_width_at_most_bits,
    _to_bit_adj,
    compute_treewidth,
    treewidth_lower_bound,
    _heuristic_upper_bound,
)


@dataclass
class TreeDecompCertificate:
    """Finite tree decomposition certificate for a simple undirected graph."""

    name: str
    n_vertices: int
    edges: list[list[int]]
    n_bags: int
    bags: list[list[int]]
    tree_edges: list[list[int]]
    width: int
    treewidth: int
    tw_method: str
    base_edges: list[list[int]] | None = None
    notes: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _canonical_edges(g: nx.Graph) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for u, v in g.edges():
        if u > v:
            u, v = v, u
        out.append((u, v))
    return sorted(out)


def _build_adj_matrix(n: int, edges: list[tuple[int, int]]) -> list[list[bool]]:
    adj = [[False] * n for _ in range(n)]
    for u, v in edges:
        adj[u][v] = True
        adj[v][u] = True
    return adj


def elimination_order_from_search(g: nx.Graph, k: int) -> tuple[int, ...] | None:
    """Reconstruct one elimination order of width ≤ k via bitset search."""
    adj = _to_bit_adj(g)
    n = len(adj)
    remaining = (1 << n) - 1
    order: list[int] = []

    def pick(state: tuple[int, ...], rem: int) -> tuple[int, ...] | None:
        if rem == 0:
            return tuple(order)
        candidates: list[tuple[int, int]] = []
        for v in range(n):
            if not (rem & (1 << v)):
                continue
            deg = (state[v] & rem).bit_count()
            if deg > k:
                continue
            candidates.append((deg, v))
        if not candidates:
            return None
        candidates.sort()
        for _, v in candidates:
            nbr_mask = state[v] & rem & ~(1 << v)
            new_state = list(state)
            u_mask = nbr_mask
            while u_mask:
                lsb = u_mask & -u_mask
                i = lsb.bit_length() - 1
                u_mask ^= lsb
                w_mask = nbr_mask
                while w_mask:
                    lsb2 = w_mask & -w_mask
                    j = lsb2.bit_length() - 1
                    w_mask ^= lsb2
                    if i < j:
                        new_state[i] |= 1 << j
                        new_state[j] |= 1 << i
            order.append(v)
            result = pick(tuple(new_state), rem & ~(1 << v))
            if result is not None:
                return result
            order.pop()
        return None

    return pick(adj, remaining)


def elimination_to_path_decomp(
    g: nx.Graph, order: tuple[int, ...]
) -> tuple[list[list[int]], list[tuple[int, int]], int]:
    """Classic elimination → path tree decomposition (with fill edges)."""
    h = g.copy()
    bags: list[list[int]] = []
    for v in order:
        if v not in h:
            continue
        nbrs = list(h.neighbors(v))
        bags.append(sorted({v, *nbrs}))
        for i, u in enumerate(nbrs):
            for w in nbrs[i + 1 :]:
                h.add_edge(u, w)
        h.remove_node(v)
    tree_edges = [(i, i + 1) for i in range(len(bags) - 1)]
    width = max(len(b) - 1 for b in bags) if bags else 0
    return bags, tree_edges, width


def _is_valid_elimination_order(g: nx.Graph, order: tuple[int, ...], k: int) -> bool:
    """Check that ``order`` eliminates ``g`` with fill width ≤ ``k``."""
    h = g.copy()
    for v in order:
        if v not in h:
            return False
        if h.degree(v) > k:
            return False
        nbrs = list(h.neighbors(v))
        for i, u in enumerate(nbrs):
            for w in nbrs[i + 1 :]:
                h.add_edge(u, w)
        h.remove_node(v)
    return h.number_of_nodes() == 0


def elimination_order_for_path_certificate(
    g: nx.Graph,
    k: int,
    *,
    max_random_attempts: int = 100_000,
    seed: int = 0,
) -> tuple[int, ...] | None:
    """Find an elimination order whose path decomp satisfies ``verify_certificate``."""
    order = elimination_order_from_search(g, k)
    if order is not None:
        bags, _, width = elimination_to_path_decomp(g, order)
        cert = TreeDecompCertificate(
            name="_probe",
            n_vertices=g.number_of_nodes(),
            edges=[[u, v] for u, v in _canonical_edges(g)],
            n_bags=len(bags),
            bags=bags,
            tree_edges=[[i, i + 1] for i in range(len(bags) - 1)],
            width=width,
            treewidth=k,
            tw_method="probe",
        )
        if verify_certificate(cert):
            return order

    rng = random.Random(seed)
    nodes = list(g.nodes())
    for _ in range(max_random_attempts):
        cand = tuple(rng.sample(nodes, len(nodes)))
        if not _is_valid_elimination_order(g, cand, k):
            continue
        bags, _, width = elimination_to_path_decomp(g, cand)
        if width > k:
            continue
        cert = TreeDecompCertificate(
            name="_probe",
            n_vertices=g.number_of_nodes(),
            edges=[[u, v] for u, v in _canonical_edges(g)],
            n_bags=len(bags),
            bags=bags,
            tree_edges=[[i, i + 1] for i in range(len(bags) - 1)],
            width=width,
            treewidth=k,
            tw_method="probe",
        )
        if verify_certificate(cert):
            return cand
    return None


def verify_certificate(cert: TreeDecompCertificate) -> bool:
    """Check vertex/edge cover, tree shape, bag width, and preconnected bag tree."""
    n = cert.n_vertices
    adj = _build_adj_matrix(n, [(e[0], e[1]) for e in cert.edges])

    # vertex cover
    for v in range(n):
        if not any(v in bag for bag in cert.bags):
            return False

    # edge cover
    for u in range(n):
        for v in range(u + 1, n):
            if not adj[u][v]:
                continue
            if not any(u in bag and v in bag for bag in cert.bags):
                return False

    # tree: connected + |E| = m-1 on bag indices
    m = cert.n_bags
    if m == 0:
        return n == 0
    tree_adj = [[False] * m for _ in range(m)]
    for a, b in cert.tree_edges:
        tree_adj[a][b] = True
        tree_adj[b][a] = True
    if len(cert.tree_edges) != max(0, m - 1):
        return False
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in range(m):
            if tree_adj[u][v] and v not in seen:
                seen.add(v)
                stack.append(v)
    if len(seen) != m:
        return False

    # width
    if max(len(b) - 1 for b in cert.bags) != cert.width:
        return False

    # preconnected induce: for each vertex v, bags containing v induce connected subtree
    for v in range(n):
        nodes = [i for i, bag in enumerate(cert.bags) if v in bag]
        if not nodes:
            return False
        sub_seen = {nodes[0]}
        sub_stack = [nodes[0]]
        node_set = set(nodes)
        while sub_stack:
            u = sub_stack.pop()
            for w in range(m):
                if w in node_set and tree_adj[u][w] and w not in sub_seen:
                    sub_seen.add(w)
                    sub_stack.append(w)
        if sub_seen != node_set:
            return False

    return True


SMOKE_GRAPH_SPECS: dict[str, tuple[int, list[tuple[int, int]]]] = {
    "c5Ofold_crossing": (5, [(0, 2), (1, 3)]),
    "c6Crossing_crossing": (6, [(0, 2), (1, 3)]),
    "c7Crossing_crossing": (7, [(0, 2), (1, 3)]),
    "c7Nested_noncrossing": (7, [(0, 3), (1, 2)]),
    "c8Crossing_crossing": (8, [(0, 2), (1, 3)]),
    "c8Nested_noncrossing": (8, [(0, 6), (2, 4)]),
    "c9Crossing_crossing": (9, [(0, 2), (1, 3)]),
    "c9Nested_noncrossing": (9, [(0, 5), (2, 3)]),
    "c10Crossing_crossing": (10, [(0, 2), (1, 3)]),
    "c10Nested_noncrossing": (10, [(0, 3), (1, 2)]),
}


def cubic_hamiltonian_graph(n: int, offset: int = 0) -> nx.Graph:
    """C_n with chord (i, i + n//2) for even n (perfect-matching style).

    Same construction as ``scripts/asymptotic_cubic_hamiltonian_family.py``.
    """
    if n < 4 or n % 2 != 0:
        raise ValueError(f"cubic_hamiltonian_graph requires even n >= 4, got {n}")
    g = nx.cycle_graph(n)
    half = n // 2
    for i in range(n):
        j = (i + half + offset) % n
        if i != j and not g.has_edge(i, j):
            g.add_edge(i, j)
    return g


def cubic_hamiltonian_certificate(
    n: int,
    *,
    exact_max_nodes: int = 20,
    memory_safe: bool = False,
    offset: int = 0,
) -> TreeDecompCertificate:
    """Tree-decomposition certificate for tw(L(G)) on the cubic Hamiltonian family D_n."""
    g = cubic_hamiltonian_graph(n, offset=offset)
    name = f"cubic_hamiltonian_n{n}"
    base_edges = [[u, v] for u, v in _canonical_edges(g)]
    lg = nx.line_graph(g)
    edge_index = {tuple(e): i for i, e in enumerate(base_edges)}

    def remap_node(node: tuple[int, int]) -> int:
        u, v = node
        if u > v:
            u, v = v, u
        return edge_index[(u, v)]

    lg2 = nx.Graph()
    lg2.add_nodes_from(range(len(base_edges)))
    for u, v in lg.edges():
        lg2.add_edge(remap_node(u), remap_node(v))

    lg_edges = sorted([sorted([remap_node(u), remap_node(v)]) for u, v in lg.edges()])

    tw, tw_method = compute_treewidth(
        lg2, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe
    )
    lb = treewidth_lower_bound(lg2)
    ub = _heuristic_upper_bound(lg2)
    if tw_method not in ("exact_bruteforce", "exact_width_search", "exact_confirmed"):
        tw = _exact_treewidth(lg2, lb=lb, ub=ub)

    max_attempts = max(100_000, len(base_edges) * 150_000)
    order = None
    cert_k = tw
    for k in range(tw, tw + 3):
        order = elimination_order_for_path_certificate(lg2, k, max_random_attempts=max_attempts)
        if order is not None:
            cert_k = k
            break
    if order is None:
        raise RuntimeError(f"no path-decomposition certificate order for {name} at tw={tw}")

    bags_raw, tree_edges_raw, width = elimination_to_path_decomp(lg2, order)
    tw_note = ""
    if width > tw:
        tw_note = f"; path cert width {width} > tw estimate {tw}"
    cert = TreeDecompCertificate(
        name=name,
        n_vertices=len(base_edges),
        edges=lg_edges,
        n_bags=len(bags_raw),
        bags=bags_raw,
        tree_edges=[[a, b] for a, b in tree_edges_raw],
        width=width,
        treewidth=max(tw, width),
        tw_method=tw_method,
        base_edges=base_edges,
        notes=f"line graph of cubic_hamiltonian_n{n}; tw={max(tw, width)}{tw_note}",
    )
    if not verify_certificate(cert):
        raise RuntimeError(f"certificate verification failed for {name}")
    if cert.width > cert.treewidth:
        raise RuntimeError(f"decomp width {cert.width} > tw {cert.treewidth} for {name}")
    return cert


def build_base_graph(name: str) -> nx.Graph:
    if name not in SMOKE_GRAPH_SPECS:
        raise ValueError(f"unknown smoke graph {name!r}")
    n, chords = SMOKE_GRAPH_SPECS[name]
    g = nx.cycle_graph(n)
    g.add_edges_from(chords)
    return g


def line_graph_certificate(
    name: str,
    *,
    exact_max_nodes: int = 20,
    memory_safe: bool = False,
) -> TreeDecompCertificate:
    g = build_base_graph(name)
    base_edges = [[u, v] for u, v in _canonical_edges(g)]
    lg = nx.line_graph(g)
    # Stable vertex order = canonical base edge list.
    edge_index = {tuple(e): i for i, e in enumerate(base_edges)}

    def remap_node(node: tuple[int, int]) -> int:
        u, v = node
        if u > v:
            u, v = v, u
        return edge_index[(u, v)]

    lg2 = nx.Graph()
    lg2.add_nodes_from(range(len(base_edges)))
    for u, v in lg.edges():
        lg2.add_edge(remap_node(u), remap_node(v))

    lg_edges = sorted([sorted([remap_node(u), remap_node(v)]) for u, v in lg.edges()])

    tw, tw_method = compute_treewidth(
        lg2, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe
    )
    lb = treewidth_lower_bound(lg2)
    ub = _heuristic_upper_bound(lg2)
    if tw_method not in ("exact_bruteforce", "exact_width_search", "exact_confirmed"):
        tw = _exact_treewidth(lg2, lb=lb, ub=ub)

    order = elimination_order_for_path_certificate(lg2, tw)
    if order is None:
        raise RuntimeError(f"no path-decomposition certificate order for {name} at tw={tw}")

    bags_raw, tree_edges_raw, width = elimination_to_path_decomp(lg2, order)
    cert = TreeDecompCertificate(
        name=name,
        n_vertices=len(base_edges),
        edges=lg_edges,
        n_bags=len(bags_raw),
        bags=bags_raw,
        tree_edges=[[a, b] for a, b in tree_edges_raw],
        width=width,
        treewidth=tw,
        tw_method=tw_method,
        base_edges=base_edges,
        notes=f"line graph of {name}; tw={tw}",
    )
    if not verify_certificate(cert):
        raise RuntimeError(f"certificate verification failed for {name}")
    if cert.width > tw:
        raise RuntimeError(f"decomp width {cert.width} > tw {tw} for {name}")
    return cert
