"""Constructive resolution refutations for Tseitin on trees and cycles.

Implements the inductive proof of Width = Δ for trees, and Width = 2 for cycles,
by *building* an explicit resolution derivation that is mechanically checked.

See: papers/theorem_dossier_TD-TSEITIN-WIDTH-TREES-001/PROOF.md
"""

from __future__ import annotations

from dataclasses import dataclass, field

import networkx as nx

from backend.proof_complexity.tseitin_family import xor_cnf
from backend.proof_complexity.width import _norm, resolve

Clause = tuple[int, ...]


@dataclass
class ResolutionProof:
    axioms: list[Clause]
    steps: list[Clause]
    parents: list[tuple[int, int] | None]
    max_width: int
    delta: int
    notes: list[str] = field(default_factory=list)


def verify_resolution_derivation(proof: ResolutionProof) -> list[str]:
    errors: list[str] = []
    if proof.max_width > proof.delta:
        errors.append(f"max_width {proof.max_width} > delta {proof.delta}")
    axiom_set = set(proof.axioms)
    for i, clause in enumerate(proof.steps):
        if len(clause) > proof.delta:
            errors.append(f"step {i} has width {len(clause)} > Δ={proof.delta}")
        p = proof.parents[i]
        if p is None:
            if clause not in axiom_set:
                errors.append(f"step {i} marked axiom but missing from axiom list: {clause}")
            continue
        j, k = p
        if not (0 <= j < i and 0 <= k < i):
            errors.append(f"step {i} has invalid parents {p}")
            continue
        r = resolve(proof.steps[j], proof.steps[k])
        if r != clause:
            errors.append(f"step {i}: resolve({j},{k})={r} != {clause}")
    if () not in proof.steps:
        errors.append("empty clause missing")
    return errors


def _edge_var_map(g: nx.Graph) -> dict[tuple[int, int], int]:
    edges = sorted(tuple(sorted(e)) for e in g.edges())
    return {e: i + 1 for i, e in enumerate(edges)}


def _xor_clauses_for_vertex(
    g: nx.Graph, e_index: dict[tuple[int, int], int], v: int, charge: int
) -> list[Clause]:
    incident = [e_index[tuple(sorted((v, u)))] for u in sorted(g.neighbors(v))]
    out: list[Clause] = []
    for c in xor_cnf(incident, charge % 2):
        n = _norm(c)
        if n is not None:
            out.append(n)
    return out


def _all_axioms(
    g: nx.Graph, charges: dict[int, int], e_index: dict[tuple[int, int], int]
) -> list[Clause]:
    axioms: list[Clause] = []
    seen: set[Clause] = set()
    for v in sorted(g.nodes()):
        for c in _xor_clauses_for_vertex(g, e_index, v, charges[v]):
            if c not in seen:
                seen.add(c)
                axioms.append(c)
    return axioms


class _ProofBuilder:
    def __init__(self, axioms: list[Clause], delta: int) -> None:
        self.delta = delta
        self.axioms = list(axioms)
        self.steps: list[Clause] = []
        self.parents: list[tuple[int, int] | None] = []
        self.index: dict[Clause, int] = {}
        for a in self.axioms:
            self._put(a, None)

    def _put(self, clause: Clause, parent: tuple[int, int] | None) -> int:
        if clause in self.index:
            return self.index[clause]
        if len(clause) > self.delta:
            raise ValueError(f"clause width {len(clause)} > Δ={self.delta}: {clause}")
        i = len(self.steps)
        self.steps.append(clause)
        self.parents.append(parent)
        self.index[clause] = i
        return i

    def ensure_axiom(self, clause: Clause) -> int:
        return self._put(clause, None)

    def resolve_to(self, j: int, k: int) -> int:
        r = resolve(self.steps[j], self.steps[k])
        if r is None:
            raise ValueError(f"cannot resolve {self.steps[j]} & {self.steps[k]}")
        return self._put(r, (j, k))

    def finish(self, note: str = "") -> ResolutionProof:
        mw = max((len(c) for c in self.steps), default=0)
        return ResolutionProof(
            axioms=self.axioms,
            steps=list(self.steps),
            parents=list(self.parents),
            max_width=mw,
            delta=self.delta,
            notes=[note] if note else [],
        )


def _derive_by_unit(builder: _ProofBuilder, clauses: list[Clause], unit: Clause) -> list[Clause]:
    """Resolve every clause containing the complementary literal of the unit."""
    if len(unit) != 1:
        raise ValueError("need unit")
    lit = unit[0]
    if unit not in builder.index:
        raise ValueError(f"unit not in proof: {unit}")
    u_i = builder.index[unit]
    out: list[Clause] = []
    for c in clauses:
        if -lit in c:
            if c not in builder.index:
                raise ValueError(f"clause not in proof: {c}")
            out.append(builder.steps[builder.resolve_to(builder.index[c], u_i)])
    return out


def build_tree_tseitin_refutation(tree: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    if not nx.is_tree(tree):
        raise ValueError("not a tree")
    if sum(charges[v] for v in tree.nodes()) % 2 == 0:
        raise ValueError("even total charge ⇒ satisfiable")

    e_index = _edge_var_map(tree)
    delta = max((d for _, d in tree.degree()), default=0)
    axioms = _all_axioms(tree, charges, e_index)

    # Degree-0 odd charge vertex: empty clause is the XOR encoding of 0=1
    if tree.number_of_nodes() == 1:
        # xor_cnf([], 1) → one empty clause
        axioms = [()]
        return _ProofBuilder(axioms, delta=0).finish("single odd-charge vertex")

    builder = _ProofBuilder(axioms, delta=max(delta, 1))
    g = tree.copy()
    c = {v: charges[v] % 2 for v in tree.nodes()}

    while g.number_of_nodes() >= 2:
        leaf = next(v for v, d in g.degree() if d == 1)
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            # must be among axioms (degree-1 XOR)
            builder.ensure_axiom(unit)

        if g.number_of_nodes() == 2:
            # Neighbor is also degree 1: its XOR is a unit on the same edge
            other_unit: Clause = (var,) if c[nbr] == 1 else (-var,)
            if other_unit not in builder.index:
                builder.ensure_axiom(other_unit)
            ui = builder.index[unit]
            oi = builder.index[other_unit]
            if unit == other_unit:
                raise RuntimeError("parity invariant violated on last edge")
            builder.resolve_to(ui, oi)  # ()
            return builder.finish("tree induction: conflicting units on last edge")

        # Derive reduced XOR at nbr (width drops by 1), witness of Unit–XOR lemma
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                builder.ensure_axiom(cl)
        _derive_by_unit(builder, xor_nbr, unit)

        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    raise RuntimeError("unreachable")


def build_cycle_tseitin_refutation(cycle: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    n = cycle.number_of_nodes()
    degs = [d for _, d in cycle.degree()]
    if not (
        n >= 3
        and cycle.number_of_edges() == n
        and max(degs) == 2
        and min(degs) == 2
        and nx.is_connected(cycle)
    ):
        raise ValueError("not a cycle")
    if sum(charges[v] for v in cycle.nodes()) % 2 == 0:
        raise ValueError("sat")

    e_index = _edge_var_map(cycle)
    axioms = _all_axioms(cycle, charges, e_index)
    # Width-2 saturation with parent pointers = constructive proof for Δ=2
    builder = _ProofBuilder(axioms, delta=2)
    pending = list(range(len(builder.steps)))
    seen_pair: set[tuple[int, int]] = set()
    while pending:
        i = pending.pop()
        nsteps = len(builder.steps)
        for j in range(nsteps):
            a, b = (i, j) if i < j else (j, i)
            if a == b or (a, b) in seen_pair:
                continue
            seen_pair.add((a, b))
            r = resolve(builder.steps[a], builder.steps[b])
            if r is None or len(r) > 2:
                continue
            if r not in builder.index:
                idx = builder._put(r, (a, b))
                pending.append(idx)
                if len(r) == 0:
                    return builder.finish("cycle: certified width-2 saturation proof")
    raise RuntimeError("cycle width-2 saturation failed")


def prove_tree_lemma(tree: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    proof = build_tree_tseitin_refutation(tree, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    return proof


def prove_cycle_lemma(cycle: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    proof = build_cycle_tseitin_refutation(cycle, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    return proof


def _is_unicyclic(g: nx.Graph) -> bool:
    n = g.number_of_nodes()
    return (
        n >= 3
        and nx.is_connected(g)
        and g.number_of_edges() == n
    )


def build_unicyclic_tseitin_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Width ≤ Δ for connected unicyclic graphs with odd total charge.

    Strategy: peel off-cycle leaves (tree induction), then width-2 saturate the residual cycle.
    Both phases stay within width Δ (cycle needs only width 2 ≤ Δ for n≥3 unicyclic).
    """
    if not _is_unicyclic(graph):
        raise ValueError("not unicyclic")
    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    axioms = _all_axioms(graph, charges, e_index)
    builder = _ProofBuilder(axioms, delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}

    # Peel degree-1 vertices until only the unique cycle remains.
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")

        if g.number_of_nodes() == 2:
            other: Clause = (var,) if c[nbr] == 1 else (-var,)
            if other not in builder.index:
                raise RuntimeError(f"final unit missing: {other}")
            if unit == other:
                raise RuntimeError("parity invariant broken")
            builder.resolve_to(builder.index[unit], builder.index[other])
            return builder.finish("unicyclic degenerate: conflict on last edge")

        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR clause missing before peel: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    degs = [d for _, d in g.degree()]
    if not (degs and min(degs) == 2 and max(degs) == 2 and g.number_of_edges() == g.number_of_nodes()):
        raise RuntimeError("residual after peel is not a cycle")

    # Residual cycle XORs with updated charges must already sit in the proof
    # (original axioms if no peel, else derived via Unit–XOR).
    for v in g.nodes():
        for cl in _xor_clauses_for_vertex(g, e_index, v, c[v]):
            if cl not in builder.index:
                raise RuntimeError(f"residual cycle XOR missing: {cl}")

    # Width-2 saturation on clauses of length ≤2 only (residual cycle lives there).
    pending = [i for i, cl in enumerate(builder.steps) if len(cl) <= 2]
    seen_pair: set[tuple[int, int]] = set()
    while pending:
        i = pending.pop()
        if len(builder.steps[i]) > 2:
            continue
        # Snapshot partners among current width-≤2 clauses
        partners = [j for j, cl in enumerate(builder.steps) if len(cl) <= 2]
        for j in partners:
            a, b = (i, j) if i < j else (j, i)
            if a == b or (a, b) in seen_pair:
                continue
            seen_pair.add((a, b))
            r = resolve(builder.steps[a], builder.steps[b])
            if r is None or len(r) > 2:
                continue
            if r not in builder.index:
                idx = builder._put(r, (a, b))
                pending.append(idx)
                if len(r) == 0:
                    return builder.finish("unicyclic: peel trees + width-2 cycle saturation")
    raise RuntimeError("unicyclic width-2 saturation failed")


def prove_unicyclic_lemma(graph: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    proof = build_unicyclic_tseitin_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def _is_bicyclic(g: nx.Graph) -> bool:
    n = g.number_of_nodes()
    return n >= 3 and nx.is_connected(g) and g.number_of_edges() == n + 1


def _saturate_to_empty(
    builder: _ProofBuilder, *, width_cap: int, note: str
) -> ResolutionProof:
    """Certify refutability by bounded-width resolution with parent pointers."""
    pending = list(range(len(builder.steps)))
    seen_pair: set[tuple[int, int]] = set()
    while pending:
        i = pending.pop()
        nsteps = len(builder.steps)
        for j in range(nsteps):
            a, b = (i, j) if i < j else (j, i)
            if a == b or (a, b) in seen_pair:
                continue
            seen_pair.add((a, b))
            r = resolve(builder.steps[a], builder.steps[b])
            if r is None or len(r) > width_cap:
                continue
            if r not in builder.index:
                idx = builder._put(r, (a, b))
                pending.append(idx)
                if len(r) == 0:
                    return builder.finish(note)
    raise RuntimeError(f"width-{width_cap} saturation failed to derive empty clause")


def build_bicyclic_tseitin_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Width ≤ Δ certificate for connected bicyclic graphs with odd total charge.

    Strategy: peel pendant trees (Unit–XOR), then width-Δ saturate the residual
    2-core. Empirically W=Δ on Δ≤3 bicyclics; this makes that computationally
    checkable as an explicit verified derivation (E2 constructive certificate).
    """
    if not _is_bicyclic(graph):
        raise ValueError("not bicyclic")
    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    axioms = _all_axioms(graph, charges, e_index)
    builder = _ProofBuilder(axioms, delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}

    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")

        if g.number_of_nodes() == 2:
            other: Clause = (var,) if c[nbr] == 1 else (-var,)
            if other not in builder.index:
                raise RuntimeError(f"final unit missing: {other}")
            if unit == other:
                raise RuntimeError("parity invariant broken")
            builder.resolve_to(builder.index[unit], builder.index[other])
            return builder.finish("bicyclic degenerate: conflict on last edge")

        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR clause missing before peel: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    if g.number_of_edges() != g.number_of_nodes() + 1:
        raise RuntimeError("residual after peel is not bicyclic")
    if min(d for _, d in g.degree()) < 2:
        raise RuntimeError("residual still has leaves")

    for v in g.nodes():
        for cl in _xor_clauses_for_vertex(g, e_index, v, c[v]):
            if cl not in builder.index:
                raise RuntimeError(f"residual bicyclic XOR missing: {cl}")

    return _saturate_to_empty(
        builder,
        width_cap=builder.delta,
        note="bicyclic: peel trees + width-Δ saturation of 2-core",
    )


def prove_bicyclic_lemma(graph: nx.Graph, charges: dict[int, int]) -> ResolutionProof:
    proof = build_bicyclic_tseitin_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def _cycle_and_two_chords(
    graph: nx.Graph,
) -> tuple[list[int], tuple[int, int], tuple[int, int]] | None:
    """If G is C_n plus exactly two chords, return (cycle_order, chord1, chord2)."""
    n = graph.number_of_nodes()
    if n < 4 or not nx.is_connected(graph) or graph.number_of_edges() != n + 2:
        return None

    def try_frame(order: list[int]) -> tuple[list[int], tuple[int, int], tuple[int, int]] | None:
        if len(order) != n:
            return None
        cyc_edges = {tuple(sorted((order[i], order[(i + 1) % n]))) for i in range(n)}
        if not all(graph.has_edge(*e) for e in cyc_edges):
            return None
        chords = [
            tuple(sorted(e))
            for e in graph.edges()
            if tuple(sorted(e)) not in cyc_edges
        ]
        if len(chords) != 2:
            return None
        return order, chords[0], chords[1]  # type: ignore[return-value]

    nodes = sorted(graph.nodes())
    if nodes == list(range(n)):
        hit = try_frame(list(range(n)))
        if hit is not None:
            return hit

    for cyc in nx.simple_cycles(graph):
        if len(cyc) != n:
            continue
        hit = try_frame(list(cyc))
        if hit is not None:
            return hit
    return None


def _chords_cross_in_cycle_order(
    order: list[int], c1: tuple[int, int], c2: tuple[int, int]
) -> bool:
    from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle

    pos = {v: i for i, v in enumerate(order)}
    return chords_cross_on_cycle(
        len(order),
        (pos[c1[0]], pos[c1[1]]),
        (pos[c2[0]], pos[c2[1]]),
    )


def build_noncrossing_two_chords_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Width ≤ Δ when the 2-core is non-crossing C_k + 2 chords (pendants allowed)."""
    if not nx.is_connected(graph):
        raise ValueError("disconnected")
    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    axioms = _all_axioms(graph, charges, e_index)
    builder = _ProofBuilder(axioms, delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        if g.number_of_nodes() == 2:
            other: Clause = (var,) if c[nbr] == 1 else (-var,)
            builder.resolve_to(builder.index[unit], builder.index[other])
            return builder.finish("degenerate peel conflict")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    parsed = _cycle_and_two_chords(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + two chords")
    cycle, c1, c2 = parsed
    if len({*c1, *c2}) < 4:
        raise ValueError("chords must have four distinct endpoints")
    if _chords_cross_in_cycle_order(cycle, c1, c2):
        raise ValueError("2-core chords cross ⇒ Width>Δ; no width-Δ upper cert")

    for v in g.nodes():
        for cl in _xor_clauses_for_vertex(g, e_index, v, c[v]):
            if cl not in builder.index:
                raise RuntimeError(f"residual XOR missing: {cl}")

    return _saturate_to_empty(
        builder,
        width_cap=builder.delta,
        note="non-crossing 2-core (C_k+2 chords): peel + width-Δ saturation",
    )


def prove_noncrossing_two_chords_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_noncrossing_two_chords_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


prove_noncrossing_cycle_two_chords = prove_noncrossing_two_chords_lemma


def certify_crossing_width_gt_delta(
    graph: nx.Graph, charges: dict[int, int]
) -> dict:
    """Lower bound Width>Δ: peel trees, require crossing 2-core, Δ-closure no empty."""
    from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf
    from backend.proof_complexity.width import has_width_refutation

    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    peeled = 0
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        c[nbr] = (c[nbr] + c[leaf]) % 2
        g.remove_node(leaf)
        del c[leaf]
        peeled += 1

    parsed = _cycle_and_two_chords(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + two chords")
    cycle, c1, c2 = parsed
    k = len(cycle)
    if not _chords_cross_in_cycle_order(cycle, c1, c2):
        raise ValueError("2-core chords do not cross")

    delta_full = max(d for _, d in graph.degree())
    delta_core = max(d for _, d in g.degree())
    node_list = sorted(g.nodes())
    mapping = {old: i for i, old in enumerate(node_list)}
    g2 = nx.relabel_nodes(g, mapping)
    charges2 = tuple(c[old] for old in node_list)
    form = tseitin_cnf(GraphInstance(g2, charges2, "cross", 0, {}))
    # Lower-bound against Δ_core (pendant may raise Δ_full without raising width)
    ok, _der, size = has_width_refutation(form, delta_core)
    if ok:
        raise AssertionError("empty clause derived at width Δ_core; core Width ≤ Δ_core")
    out = {
        "certified": "Width ≥ Δ_core + 1",
        "delta_full": delta_full,
        "delta_core": delta_core,
        "closure_size_at_delta_core": size,
        "empty_at_delta_core": False,
        "peeled_leaves": peeled,
        "core_n": k,
        "chords": [list(c1), list(c2)],
        "notes": [
            "After peeling trees, 2-core chords cross",
            "Complete width-Δ_core closure of core avoids empty clause",
            "Odd-charge connected Tseitin is UNSAT ⇒ Width ≥ Δ_core+1",
        ],
    }
    if delta_full == delta_core:
        out["certified"] = "Width > Δ"
        out["delta"] = delta_full
        out["notes"].append("Δ_full = Δ_core so Width > Δ for the original graph")
    else:
        out["notes"].append(
            f"Δ_full={delta_full} > Δ_core={delta_core}: Width>Δ_full not claimed "
            "(pendant may raise Δ without raising width)"
        )
    return out


def _saturate_until_targets(
    builder: _ProofBuilder, targets: list[Clause], *, width_cap: int, max_rounds: int = 400
) -> None:
    """Width-bounded saturation until every target clause is derived (or empty)."""
    missing = {t for t in targets if t not in builder.index}
    for _ in range(max_rounds):
        if not missing:
            return
        if () in builder.index:
            return
        n0 = len(builder.steps)
        changed = False
        for i in range(n0):
            for j in range(i + 1, n0):
                r = resolve(builder.steps[i], builder.steps[j])
                if r is None or len(r) > width_cap:
                    continue
                if r not in builder.index:
                    builder._put(r, (i, j))
                    changed = True
                    if r in missing:
                        missing.discard(r)
                    if len(r) == 0:
                        return
        if not changed:
            break
    still = [t for t in targets if t not in builder.index]
    if still:
        raise RuntimeError(f"failed to derive {len(still)} target clauses under width {width_cap}")


def _width2_saturate_to_empty(builder: _ProofBuilder, max_rounds: int = 800) -> None:
    for _ in range(max_rounds):
        if () in builder.index:
            return
        n0 = len(builder.steps)
        changed = False
        for i in range(n0):
            for j in range(i + 1, n0):
                r = resolve(builder.steps[i], builder.steps[j])
                if r is None or len(r) > 2:
                    continue
                if r not in builder.index:
                    builder._put(r, (i, j))
                    changed = True
                    if len(r) == 0:
                        return
        if not changed:
            break
    if () not in builder.index:
        raise RuntimeError("width-2 saturation failed to derive empty clause")


def build_noncrossing_len2_ears_resolution_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Search-structured Width≤Δ proof: tree peel → length-2 ear clips → width-2 finish.

    Each ear clip derives the residual XOR CNFs at the base endpoints by width-Δ
    saturation *aimed at those targets*, then deletes the tip. When both chords
    have circular length 2 and do not cross, the residual is a cycle and the
    empty clause appears via width-2 saturation (cycle lemma).
    """
    from backend.proof_complexity.chord_crossing_law import (
        chords_cross_on_cycle,
        circular_dist,
    )

    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")
    parsed = _cycle_and_two_chords(graph)
    if parsed is None:
        # allow pendants: peel first below; re-parse after peel
        pass

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    axioms = _all_axioms(graph, charges, e_index)
    builder = _ProofBuilder(axioms, delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}

    # Tree peels
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        if g.number_of_nodes() == 2:
            other: Clause = (var,) if c[nbr] == 1 else (-var,)
            builder.resolve_to(builder.index[unit], builder.index[other])
            return builder.finish("len2-ears: peel to conflict")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    parsed = _cycle_and_two_chords(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + two chords")
    order, c1, c2 = parsed
    k = len(order)
    if _chords_cross_in_cycle_order(order, c1, c2):
        raise ValueError("chords cross")
    pos = {v: i for i, v in enumerate(order)}
    if (
        circular_dist(k, pos[c1[0]], pos[c1[1]]) != 2
        or circular_dist(k, pos[c2[0]], pos[c2[1]]) != 2
    ):
        raise ValueError("both chords must have circular length 2")

    ear_log: list[int] = []
    while True:
        if () in builder.index:
            return builder.finish(
                f"len2-ears: empty during ear phase (clipped={ear_log})"
            )
        found = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                found = (v, u, w)
                break
        if found is None:
            break
        v, u, w = found
        c_new = dict(c)
        c_new[u] = (c_new[u] + c_new[v]) % 2
        g_new = g.copy()
        g_new.remove_node(v)
        targets = _xor_clauses_for_vertex(g_new, e_index, u, c_new[u]) + _xor_clauses_for_vertex(
            g_new, e_index, w, c_new[w]
        )
        _saturate_until_targets(builder, targets, width_cap=builder.delta)
        ear_log.append(v)
        g, c = g_new, c_new

    if () not in builder.index:
        _width2_saturate_to_empty(builder)

    return builder.finish(
        f"len2-ears: peel + ear-clips {ear_log} + width-2 finish on residual cycle"
    )


def prove_noncrossing_len2_ears_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_noncrossing_len2_ears_resolution_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def _is_cycle_plus_one_chord(
    graph: nx.Graph,
) -> tuple[list[int], tuple[int, int]] | None:
    n = graph.number_of_nodes()
    if n < 3 or not nx.is_connected(graph) or graph.number_of_edges() != n + 1:
        return None
    if sorted(graph.nodes()) == list(range(n)):
        order = list(range(n))
        cyc = {tuple(sorted((order[i], order[(i + 1) % n]))) for i in range(n)}
        if all(graph.has_edge(*e) for e in cyc):
            chords = [
                tuple(sorted(e))
                for e in graph.edges()
                if tuple(sorted(e)) not in cyc
            ]
            if len(chords) == 1:
                return order, chords[0]
    for cyc in nx.simple_cycles(graph):
        if len(cyc) != n:
            continue
        order = list(cyc)
        cyc_e = {tuple(sorted((order[i], order[(i + 1) % n]))) for i in range(n)}
        if not all(graph.has_edge(*e) for e in cyc_e):
            continue
        chords = [
            tuple(sorted(e)) for e in graph.edges() if tuple(sorted(e)) not in cyc_e
        ]
        if len(chords) == 1:
            return order, chords[0]
    return None


def build_bicyclic_len2_chord_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Bicyclic C_n + length-2 chord: one triangle ear clip, then width-2 finish."""
    from backend.proof_complexity.chord_crossing_law import circular_dist

    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    builder = _ProofBuilder(_all_axioms(graph, charges, e_index), delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    parsed = _is_cycle_plus_one_chord(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + one chord")
    order, chord = parsed
    k = len(order)
    pos = {v: i for i, v in enumerate(order)}
    if circular_dist(k, pos[chord[0]], pos[chord[1]]) != 2:
        raise ValueError("chord must have circular length 2")

    # Clip the unique length-2 ear tip(s); C_n+(i,i+2) has one triangle tip i+1;
    # on C4 both opposite tips may appear when two triangles share the chord.
    ear_log: list[int] = []
    while True:
        if () in builder.index:
            return builder.finish(f"bicyclic len2-chord: empty during ears {ear_log}")
        found = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                found = (v, u, w)
                break
        if found is None:
            break
        v, u, w = found
        c_new = dict(c)
        c_new[u] = (c_new[u] + c_new[v]) % 2
        g_new = g.copy()
        g_new.remove_node(v)
        targets = _xor_clauses_for_vertex(g_new, e_index, u, c_new[u]) + _xor_clauses_for_vertex(
            g_new, e_index, w, c_new[w]
        )
        _saturate_until_targets(builder, targets, width_cap=builder.delta)
        ear_log.append(v)
        g, c = g_new, c_new

    if () not in builder.index:
        degs = [d for _, d in g.degree()]
        is_cycle = (
            bool(degs)
            and g.number_of_edges() == g.number_of_nodes()
            and min(degs) == 2
            and max(degs) == 2
        )
        if is_cycle:
            _width2_saturate_to_empty(builder)
        else:
            _saturate_until_targets(builder, [()], width_cap=builder.delta)

    return builder.finish(f"bicyclic len2-chord: ears {ear_log} + residual finish")


def prove_bicyclic_len2_chord_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_bicyclic_len2_chord_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def _shorter_arc_internals(
    order: list[int], a: int, b: int
) -> tuple[int, list[int], int]:
    """Return (left, internals, right) along the shorter circular arc a→b."""
    from backend.proof_complexity.chord_crossing_law import circular_dist

    pos = {v: i for i, v in enumerate(order)}
    n = len(order)
    ia, ib = pos[a], pos[b]
    fwd = [(ia + k) % n for k in range(1, (ib - ia) % n)]
    # fwd are nodes strictly between a and b clockwise
    back = [(ib + k) % n for k in range(1, (ia - ib) % n)]
    # choose shorter; ties → clockwise
    if len(fwd) <= len(back):
        return a, [order[i] for i in fwd], b
    return b, [order[i] for i in back], a


def build_bicyclic_pathfold_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """C_n + one chord (any length): path-fold shorter arc → triangle ear → cycle lemma.

    Avoids global Δ-sat: only targeted residual XOR fills + width-2 finish.
    """
    from backend.proof_complexity.chord_crossing_law import circular_dist
    from backend.proof_complexity.path_fold import fold_deg2_tip, fold_open_arc_internals

    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    builder = _ProofBuilder(_all_axioms(graph, charges, e_index), delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    parsed = _is_cycle_plus_one_chord(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + one chord")
    order, chord = parsed
    left, internals, right = _shorter_arc_internals(order, chord[0], chord[1])
    if len(internals) > 1:
        # leave exactly one tip so the chord forms a triangle ear
        fold_open_arc_internals(
            builder, g, c, e_index, left, list(internals[:-1]), internals[-1]
        )
        # after this left — tip — right with tip=internals[-1], and chord left-right
    # Clip triangle ears
    ear_log: list[int] = []
    while True:
        if () in builder.index:
            return builder.finish(f"bicyclic pathfold: empty during ears {ear_log}")
        found = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                found = (v, u)
                break
        if found is None:
            break
        tip, into = found
        fold_deg2_tip(builder, g, c, e_index, tip, fold_into=into)
        ear_log.append(tip)

    if () not in builder.index:
        _width2_saturate_to_empty(builder)
    return builder.finish(f"bicyclic pathfold: folds+ears {ear_log} + width-2")


def prove_bicyclic_pathfold_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_bicyclic_pathfold_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def build_noncrossing_pathfold_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Noncrossing C_k+2 chords: triangle ears first, then single-step path-folds."""
    from backend.proof_complexity.path_fold import fold_deg2_tip

    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    builder = _ProofBuilder(_all_axioms(graph, charges, e_index), delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}
    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    parsed = _cycle_and_two_chords(g)
    if parsed is None:
        raise ValueError("2-core is not C_k + two chords")
    order, c1, c2 = parsed
    if _chords_cross_in_cycle_order(order, c1, c2):
        raise ValueError("chords cross")

    ear_log: list[int] = []
    while True:
        if () in builder.index:
            return builder.finish(f"noncrossing pathfold: empty {ear_log}")

        # Prefer triangle ears (handles nested chords safely)
        tip = None
        into = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                tip, into = v, u
                break
        if tip is not None:
            fold_deg2_tip(builder, g, c, e_index, tip, fold_into=into)
            ear_log.append(tip)
            continue

        # Single-step shortcut fold: any deg-2 tip on a chord's current shorter arc
        rem = [v for v in order if v in g]
        advanced = False
        for chord in (c1, c2):
            if chord[0] not in g or chord[1] not in g:
                continue
            left, internals, right = _shorter_arc_internals(rem, chord[0], chord[1])
            internals = [v for v in internals if v in g and g.degree(v) == 2]
            if not internals:
                continue
            # fold tip adjacent to left
            tip = next((v for v in internals if g.has_edge(left, v)), None)
            if tip is None:
                continue
            fold_deg2_tip(builder, g, c, e_index, tip, fold_into=left)
            ear_log.append(tip)
            advanced = True
            break
        if not advanced:
            break

    if () not in builder.index:
        _width2_saturate_to_empty(builder)
    return builder.finish(f"noncrossing pathfold: ears {ear_log} + width-2")


def prove_noncrossing_pathfold_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_noncrossing_pathfold_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof


def _is_pure_cycle(g: nx.Graph) -> bool:
    if g.number_of_nodes() < 3:
        return False
    degs = [d for _, d in g.degree()]
    return (
        g.number_of_edges() == g.number_of_nodes()
        and min(degs) == 2
        and max(degs) == 2
        and nx.is_connected(g)
    )


def build_outerplanar_pathfold_refutation(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    """Outerplanar Δ≤3: peel + repeated ear/shortcut folds + width-2 on residual cycle.

    Requires the input graph to be connected outerplanar with Δ≤3 and odd charge.
    Uses the same fold engine as the C_n+chords lemmas (triangle ears first).
    """
    from backend.proof_complexity.path_fold import fold_deg2_tip

    if not nx.is_connected(graph):
        raise ValueError("disconnected")
    if sum(charges[v] for v in graph.nodes()) % 2 == 0:
        raise ValueError("even charge (SAT)")
    # outerplanarity check (apex trick)
    h = graph.copy()
    apex = "__apex__"
    h.add_node(apex)
    for v in list(graph.nodes()):
        h.add_edge(apex, v)
    if not nx.check_planarity(h)[0]:
        raise ValueError("not outerplanar")

    e_index = _edge_var_map(graph)
    delta = max((d for _, d in graph.degree()), default=0)
    if delta > 3:
        raise ValueError("Δ>3")
    builder = _ProofBuilder(_all_axioms(graph, charges, e_index), delta=max(delta, 2))

    g = graph.copy()
    c = {v: charges[v] % 2 for v in graph.nodes()}

    while True:
        leaves = [v for v, d in g.degree() if d == 1]
        if not leaves:
            break
        leaf = leaves[0]
        nbr = next(iter(g.neighbors(leaf)))
        e = tuple(sorted((leaf, nbr)))
        var = e_index[e]
        chi = c[leaf]
        unit: Clause = (var,) if chi == 1 else (-var,)
        if unit not in builder.index:
            raise RuntimeError(f"leaf unit missing: {unit}")
        if g.number_of_nodes() == 2:
            other: Clause = (var,) if c[nbr] == 1 else (-var,)
            builder.resolve_to(builder.index[unit], builder.index[other])
            return builder.finish("outerplanar: peel to conflict")
        xor_nbr = _xor_clauses_for_vertex(g, e_index, nbr, c[nbr])
        for cl in xor_nbr:
            if cl not in builder.index:
                raise RuntimeError(f"XOR missing: {cl}")
        _derive_by_unit(builder, xor_nbr, unit)
        c[nbr] = (c[nbr] + chi) % 2
        g.remove_node(leaf)
        del c[leaf]

    ear_log: list[int] = []
    guard = 0
    while guard < 10_000:
        guard += 1
        if () in builder.index:
            return builder.finish(f"outerplanar pathfold: empty {ear_log}")
        if _is_pure_cycle(g):
            break

        # Triangle ear
        tip = into = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.has_edge(u, w):
                tip, into = v, u
                break
        if tip is not None:
            fold_deg2_tip(builder, g, c, e_index, tip, fold_into=into)
            ear_log.append(tip)
            continue

        # Shortcut fold: deg-2 tip adjacent to a deg≥3 vertex (ear attached to spine)
        tip = into = None
        for v, d in g.degree():
            if d != 2:
                continue
            u, w = list(g.neighbors(v))
            if g.degree(u) >= 3:
                tip, into = v, u
                break
            if g.degree(w) >= 3:
                tip, into = v, w
                break
        if tip is not None:
            fold_deg2_tip(builder, g, c, e_index, tip, fold_into=into)
            ear_log.append(tip)
            continue
        break

    if () not in builder.index:
        if not _is_pure_cycle(g):
            raise RuntimeError(
                f"outerplanar fold stuck: n={g.number_of_nodes()} m={g.number_of_edges()} "
                f"degs={sorted(d for _, d in g.degree())} clipped={ear_log}"
            )
        _width2_saturate_to_empty(builder)
    return builder.finish(f"outerplanar pathfold: {ear_log} + width-2")


def prove_outerplanar_pathfold_lemma(
    graph: nx.Graph, charges: dict[int, int]
) -> ResolutionProof:
    proof = build_outerplanar_pathfold_refutation(graph, charges)
    errs = verify_resolution_derivation(proof)
    if errs:
        raise AssertionError(errs)
    if proof.max_width > proof.delta:
        raise AssertionError(f"max_width {proof.max_width} > Δ={proof.delta}")
    return proof
