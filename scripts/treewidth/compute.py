"""Treewidth computation: exact for small graphs, NetworkX upper bounds otherwise.

``exact_width_search`` (bitset B&B for |V| > 8) is memory-heavy: a trial run on
representative line graphs with n=15..20 (|V(L(G))| ≈ 17..22) aborted with
``MemoryError`` after ~18 min.  Use ``memory_safe=True`` (default) to skip that
path when |V| > ``EXACT_WIDTH_SEARCH_MAX_NODES`` (14); exact validation boundary
remains n ≤ 14 (2870 gap configs in the exact sweep).
"""

from __future__ import annotations

import warnings
from functools import lru_cache
from itertools import permutations

import networkx as nx
from networkx.algorithms.approximation import treewidth_min_degree, treewidth_min_fill_in

# Bitset elimination search is safe through n=14 line graphs; n=15..20 OOM'd.
EXACT_WIDTH_SEARCH_MAX_NODES = 14


def treewidth_lower_bound(g: nx.Graph) -> int:
    if g.number_of_nodes() == 0:
        return 0
    omega = max((len(c) for c in nx.find_cliques(g)), default=1)
    return max(0, omega - 1)


def _heuristic_upper_bound(g: nx.Graph) -> int:
    tw_md, _ = treewidth_min_degree(g)
    tw_mf, _ = treewidth_min_fill_in(g)
    return min(int(tw_md), int(tw_mf))


def _elimination_width_graph(g: nx.Graph, order: tuple) -> int:
    h = g.copy()
    width = 0
    for v in order:
        if v not in h:
            continue
        nbrs = list(h.neighbors(v))
        width = max(width, len(nbrs))
        for i, u in enumerate(nbrs):
            for w in nbrs[i + 1:]:
                h.add_edge(u, w)
        h.remove_node(v)
    return width


def _to_bit_adj(g: nx.Graph) -> tuple[int, ...]:
    nodes = sorted(g.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [0] * len(nodes)
    for u, v in g.edges():
        i, j = idx[u], idx[v]
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return tuple(adj)


def _has_width_at_most_bits(adj: tuple[int, ...], remaining: int, k: int) -> bool:
    """Memoized backtracking elimination search on bitset adjacency."""

    @lru_cache(maxsize=None)
    def search(state: tuple[int, ...], rem: int) -> bool:
        if rem == 0:
            return True
        n = len(state)
        candidates: list[tuple[int, int]] = []
        for v in range(n):
            if not (rem & (1 << v)):
                continue
            deg = (state[v] & rem).bit_count()
            if deg > k:
                continue
            candidates.append((deg, v))
        if not candidates:
            return False
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
            new_rem = rem & ~(1 << v)
            if search(tuple(new_state), new_rem):
                return True
        return False

    return search(adj, remaining)


def _exact_bruteforce(g: nx.Graph) -> int:
    nodes = list(g.nodes())
    if len(nodes) <= 1:
        return 0
    return min(_elimination_width_graph(g, perm) for perm in permutations(nodes))


def _exact_treewidth(g: nx.Graph, *, lb: int, ub: int) -> int:
    if lb == ub:
        return lb
    adj = _to_bit_adj(g)
    remaining = (1 << len(adj)) - 1
    for k in range(lb, ub + 1):
        if _has_width_at_most_bits(adj, remaining, k):
            return k
    return ub


def compute_treewidth(
    g: nx.Graph,
    *,
    exact_max_nodes: int = 10,
    force_heuristic: bool = False,
    memory_safe: bool = True,
) -> tuple[int, str]:
    """Return ``(treewidth, method)`` for undirected graph ``g``."""
    n = g.number_of_nodes()
    if n == 0:
        return 0, "trivial"

    lb = treewidth_lower_bound(g)
    ub = _heuristic_upper_bound(g)

    if force_heuristic or exact_max_nodes <= 0 or n > exact_max_nodes:
        return ub, "networkx_upper_bound"

    if n <= 8:
        tw = max(lb, min(_exact_bruteforce(g), ub))
        method = "exact_bruteforce"
    elif memory_safe and n > EXACT_WIDTH_SEARCH_MAX_NODES:
        warnings.warn(
            f"Skipping exact_width_search: |V|={n} > {EXACT_WIDTH_SEARCH_MAX_NODES} "
            f"(memory guard; n=15..20 trial hit MemoryError). Using NetworkX upper bound.",
            stacklevel=2,
        )
        return ub, "memory_guard_heuristic"
    else:
        tw = _exact_treewidth(g, lb=lb, ub=ub)
        method = "exact_width_search"

    if tw == lb == ub:
        return tw, "exact_confirmed"
    return tw, method
