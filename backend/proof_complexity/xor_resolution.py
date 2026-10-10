"""Explicit XOR-sum derivation via resolution (no blind full saturation).

If XOR(A)=α and XOR(B)=β share exactly one variable p, resolving all opposite
pivot pairs yields CNF(XOR((A∪B)\\{p}) = α⊕β) at width ≤ max(|A|,|B|,|(A∪B)-p|).
"""

from __future__ import annotations

from backend.proof_complexity.constructive_proofs import Clause, _ProofBuilder, resolve
from backend.proof_complexity.tseitin_family import xor_cnf
from backend.proof_complexity.width import _norm, resolve as resolve_pairs


def xor_clauses(var_ids: list[int], charge: int) -> list[Clause]:
    out: list[Clause] = []
    for cl in xor_cnf(list(var_ids), charge % 2):
        n = _norm(cl)
        if n is not None:
            out.append(n)
    return out


def ensure_xor_in_builder(
    builder: _ProofBuilder, var_ids: list[int], charge: int
) -> list[Clause]:
    cls = xor_clauses(var_ids, charge)
    for cl in cls:
        if cl not in builder.index:
            # May appear as axiom; if missing, cannot proceed without sat
            raise RuntimeError(f"XOR clause not in proof: {cl} for vars={var_ids} χ={charge}")
    return cls


def derive_xor_sum_on_pivot(
    builder: _ProofBuilder,
    vars_a: list[int],
    chi_a: int,
    vars_b: list[int],
    chi_b: int,
    pivot: int,
) -> list[Clause]:
    """Derive XOR((A∪B)-{pivot}) = χ_a⊕χ_b by resolving on `pivot`.

    Completes the residual XOR CNF by iterated resolution supported only on
    vars in (A∪B) (structured XOR elim — not global formula saturation).
    """
    A, B = set(vars_a), set(vars_b)
    if pivot not in A or pivot not in B:
        raise ValueError("pivot must belong to both XOR variable sets")
    ensure_xor_in_builder(builder, vars_a, chi_a)
    ensure_xor_in_builder(builder, vars_b, chi_b)
    target_vars = sorted((A | B) - {pivot})
    target_chi = (chi_a + chi_b) % 2
    allowed = A | B
    targets = xor_clauses(target_vars, target_chi)

    # Round 1: resolve A-clauses against B-clauses on the pivot
    cls_a = xor_clauses(vars_a, chi_a)
    cls_b = xor_clauses(vars_b, chi_b)
    for ca in cls_a:
        sa = set(ca)
        for cb in cls_b:
            sb = set(cb)
            if pivot in sa and -pivot in sb:
                r = resolve(ca, cb)
            elif -pivot in sa and pivot in sb:
                r = resolve(ca, cb)
            else:
                continue
            if r is None or len(r) > builder.delta:
                continue
            if r not in builder.index:
                builder._put(r, (builder.index[ca], builder.index[cb]))

    # Iterate local closure on `allowed` until all target XOR clauses appear
    for _ in range(64):
        missing = [t for t in targets if t not in builder.index]
        if not missing:
            return targets
        n0 = len(builder.steps)
        changed = False
        for i in range(n0):
            ca = builder.steps[i]
            if any(abs(lit) not in allowed for lit in ca):
                continue
            for j in range(i + 1, n0):
                cb = builder.steps[j]
                if any(abs(lit) not in allowed for lit in cb):
                    continue
                r = resolve_pairs(ca, cb)
                if r is None or len(r) > builder.delta:
                    continue
                if any(abs(lit) not in allowed for lit in r):
                    continue
                if r not in builder.index:
                    builder._put(r, (i, j))
                    changed = True
        if not changed:
            break
    still = [t for t in targets if t not in builder.index]
    if still:
        raise RuntimeError(
            f"xor-sum incomplete: missing {len(still)} of {len(targets)} "
            f"target clauses for vars={target_vars} χ={target_chi}"
        )
    return targets


def fill_xor_by_local_sat(
    builder: _ProofBuilder, var_ids: list[int], charge: int, *, width_cap: int
) -> list[Clause]:
    """Derive missing XOR(var_ids)=χ by width-capped sat on those vars only.

    Pairwise XOR-sum on a pivot produces many resolvents but not always the full
    CNF of the residual XOR in one round; this fill is *local* (variable support
    restricted), not global empty-clause saturation. Eliminating it entirely
    would require a complete CNF-level Gaussian elimination routine.
    """
    targets = xor_clauses(var_ids, charge)
    allowed = set(var_ids)
    missing = {t for t in targets if t not in builder.index}
    for _ in range(200):
        if not missing:
            return targets
        n0 = len(builder.steps)
        changed = False
        for i in range(n0):
            ca = builder.steps[i]
            if any(abs(lit) not in allowed for lit in ca):
                continue
            for j in range(i + 1, n0):
                cb = builder.steps[j]
                if any(abs(lit) not in allowed for lit in cb):
                    continue
                r = resolve_pairs(ca, cb)
                if r is None or len(r) > width_cap:
                    continue
                if any(abs(lit) not in allowed for lit in r):
                    continue
                if r not in builder.index:
                    builder._put(r, (i, j))
                    changed = True
                    missing.discard(r)
        if not changed:
            break
    still = [t for t in targets if t not in builder.index]
    if still:
        raise RuntimeError(
            f"local XOR fill failed: missing {len(still)} for vars={var_ids} χ={charge}"
        )
    return targets


def derive_contradictory_xors_to_empty(
    builder: _ProofBuilder,
    vars_ids: list[int],
    chi_a: int,
    chi_b: int,
) -> Clause:
    """If XOR(V)=χ_a and XOR(V)=χ_b with χ_a≠χ_b, derive □ by resolving the CNFs."""
    if (chi_a % 2) == (chi_b % 2):
        raise ValueError("charges agree; not contradictory")
    ensure_xor_in_builder(builder, vars_ids, chi_a)
    ensure_xor_in_builder(builder, vars_ids, chi_b)
    # Resolving complementary XOR encodings of opposite charges eventually yields □.
    # One pivot round is not enough; close under resolution on vars_ids.
    allowed = set(vars_ids)
    for _ in range(64):
        if () in builder.index:
            return ()
        n0 = len(builder.steps)
        changed = False
        for i in range(n0):
            ca = builder.steps[i]
            if ca and any(abs(lit) not in allowed for lit in ca):
                continue
            for j in range(i + 1, n0):
                cb = builder.steps[j]
                if cb and any(abs(lit) not in allowed for lit in cb):
                    continue
                r = resolve_pairs(ca, cb)
                if r is None or len(r) > builder.delta:
                    continue
                if r and any(abs(lit) not in allowed for lit in r):
                    continue
                if r not in builder.index:
                    builder._put(r, (i, j))
                    changed = True
                    if r == ():
                        return ()
        if not changed:
            break
    if () not in builder.index:
        raise RuntimeError("failed to derive empty from contradictory XORs")
    return ()


def clip_triangle_ear_xor(
    builder: _ProofBuilder,
    *,
    x: int,
    y: int,
    z: int,
    ou: list[int],
    ow: list[int],
    chi_u: int,
    chi_v: int,
    chi_w: int,
) -> dict[str, list[Clause]]:
    """Eliminate deg-2 tip on triangle via structured XOR rewrites.

    Pure-XOR cases (no residual target-sat):
    - Ou=Ow=[] and α≠χ_w ⇒ contradictory XORs on {y,z} → □
    - Ow=[] and χ_w=0 ⇒ mid ⊕ eq_w on y yields residual_u = XOR({z}∪Ou)=α
    - Ou=[] and α=0 ⇒ mid ⊕ eq_w yields residual_w = XOR({z}∪Ow)=χ_w

    Otherwise: XOR-sums + targeted residual `_saturate_until_targets`.
    """
    from backend.proof_complexity.constructive_proofs import _saturate_until_targets

    def _sum_or_target(
        vars_a: list[int], chi_a: int, vars_b: list[int], chi_b: int, pivot: int
    ) -> list[Clause]:
        try:
            return derive_xor_sum_on_pivot(
                builder, vars_a, chi_a, vars_b, chi_b, pivot=pivot
            )
        except RuntimeError:
            target = xor_clauses(
                sorted((set(vars_a) | set(vars_b)) - {pivot}),
                (chi_a + chi_b) % 2,
            )
            _saturate_until_targets(builder, target, width_cap=builder.delta)
            return target

    mid = _sum_or_target([x, z, *ou], chi_u, [x, y], chi_v, x)
    alpha = (chi_u + chi_v) % 2
    chi_w = chi_w % 2

    if not ou and not ow:
        if alpha != chi_w:
            derive_contradictory_xors_to_empty(builder, [y, z], alpha, chi_w)
            return {
                "mid_uv": mid,
                "mode": "pure_xor_empty",
                "residual_u": [],
                "residual_w": [],
                "pure_xor": True,
            }
        raise RuntimeError("triangle face has even charge under odd Tseitin?")

    if not ow and chi_w == 0:
        resid_u = _sum_or_target([y, z, *ou], alpha, [y, z], 0, y)
        resid_w_cls = xor_clauses([z], 0)
        pure = all(t in builder.index for t in resid_w_cls)
        if not pure:
            _saturate_until_targets(builder, resid_w_cls, width_cap=builder.delta)
        return {
            "mid_uv": mid,
            "mode": "pure_resid_u_chi_w0" if pure else "pure_resid_u_sat_w",
            "residual_u": resid_u,
            "residual_w": resid_w_cls,
            "pure_xor": pure,
        }

    if not ou and alpha == 0:
        resid_w = _sum_or_target([y, z], 0, [y, z, *ow], chi_w, y)
        resid_u_cls = xor_clauses([z], 0)
        pure = all(t in builder.index for t in resid_u_cls)
        if not pure:
            _saturate_until_targets(builder, resid_u_cls, width_cap=builder.delta)
        return {
            "mid_uv": mid,
            "mode": "pure_resid_w_alpha0" if pure else "pure_resid_w_sat_u",
            "residual_u": resid_u_cls,
            "residual_w": resid_w,
            "pure_xor": pure,
        }

    glob = _sum_or_target([y, z, *ou], alpha, [y, z, *ow], chi_w, y)
    mid_w = _sum_or_target([y, z, *ow], chi_w, [x, y], chi_v, y)
    resid_u = xor_clauses([z, *ou], alpha)
    resid_w = xor_clauses([z, *ow], chi_w)
    # Prefer local XOR fill on residual vars; fall back to builder-global target sat.
    # Local fill alone is often insufficient (bridge vars); see XOR_EAR.md.
    mode = "local_xor_residuals"
    try:
        fill_xor_by_local_sat(
            builder, [z, *ou], alpha, width_cap=builder.delta
        )
        fill_xor_by_local_sat(
            builder, [z, *ow], chi_w, width_cap=builder.delta
        )
    except RuntimeError:
        _saturate_until_targets(builder, resid_u + resid_w, width_cap=builder.delta)
        mode = "target_sat_residuals"
    return {
        "mid_uv": mid,
        "global_cancel_z": glob,
        "mid_wv": mid_w,
        "mode": mode,
        "residual_u": resid_u,
        "residual_w": resid_w,
        "pure_xor": False,
    }


def demo_triangle_ear_xor() -> dict:
    """Self-check on a lone triangle with unit charge (Δ=2)."""
    from backend.proof_complexity.constructive_proofs import (
        _ProofBuilder,
        _all_axioms,
        _edge_var_map,
    )
    import networkx as nx

    g = nx.cycle_graph(3)
    charges = {0: 1, 1: 0, 2: 0}
    e_index = _edge_var_map(g)
    x = e_index[(0, 1)]
    y = e_index[(1, 2)]
    z = e_index[(0, 2)]
    builder = _ProofBuilder(_all_axioms(g, charges, e_index), delta=2)
    out = clip_triangle_ear_xor(
        builder,
        x=x,
        y=y,
        z=z,
        ou=[],
        ow=[],
        chi_u=charges[0],
        chi_v=charges[1],
        chi_w=charges[2],
    )
    return {
        "steps": len(builder.steps),
        "mode": out.get("mode"),
        "pure_xor": out.get("pure_xor", False),
        "empty_present": () in builder.index,
        "ok": out.get("pure_xor", False) and (() in builder.index),
    }
