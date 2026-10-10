"""Search a clean structural law: C_n + 2 chords, Δ≤3, unit charge → W=Δ vs W>Δ.

Features under Δ≤3 (chords must be vertex-disjoint — shared vertex ⇒ deg≥4):
  - chord circular lengths (len_a, len_b)
  - four arc lengths between the four endpoints around the cycle
  - separation = min circular distance between the two chords as arcs
  - crossing vs nested vs disjoint arcs on the circle

Usage:
  python -m backend.proof_complexity.chord_law_search
"""

from __future__ import annotations

import json
from collections import defaultdict
from itertools import combinations
from pathlib import Path

import networkx as nx

from backend.proof_complexity.characterize_tricyclic import _dist
from backend.proof_complexity.gpu_width_opencl import (
    batch_has_refutation_gpu,
    formula_to_bit_axioms,
)
from backend.proof_complexity.tseitin_family import GraphInstance, tseitin_cnf

OUT = Path("reports/discovery/chord_law_Cn_plus_2.json")


def _arc_gaps(n: int, chords: tuple[tuple[int, int], tuple[int, int]]) -> tuple[int, ...]:
    pts = sorted({chords[0][0], chords[0][1], chords[1][0], chords[1][1]})
    if len(pts) != 4:
        return ()
    gaps = [((pts[(i + 1) % 4] - pts[i]) % n) for i in range(4)]
    return tuple(sorted(gaps))


def _chord_config(n: int, c1: tuple[int, int], c2: tuple[int, int]) -> dict:
    """Classify how two disjoint chords sit on a cycle."""
    a, b = sorted(c1)
    c, d = sorted(c2)
    # Map to circle order
    pts = sorted([a, b, c, d])
    # Label which pair is a chord
    is_chord = {(a, b), (c, d)}
    # In circular order p0<p1<p2<p3: chords are either (p0p1)&(p2p3) adjacent,
    # (p0p2)&(p1p3) crossing, or (p0p3)&(p1p2) adjacent-other.
    pairs = [(pts[0], pts[1]), (pts[1], pts[2]), (pts[2], pts[3]), (pts[3], pts[0])]
    chord_pairs = []
    for u, v in [(pts[i], pts[j]) for i in range(4) for j in range(i + 1, 4)]:
        if (u, v) in is_chord or (v, u) in is_chord:
            chord_pairs.append((u, v))
    # Crossing: endpoints alternate around the circle
    order = pts
    idx = {p: i for i, p in enumerate(order)}

    def between(x, y):
        return (idx[x], idx[y])

    # Standard: chords (a,b),(c,d) cross iff exactly one of c,d is strictly between a and b on one arc
    def crosses(u, v, x, y) -> bool:
        def on_arc(p, s, t):
            # open arc s→t clockwise assuming sorted labels on cycle via index
            si, ti = idx[s], idx[t]
            pi = idx[p]
            if si < ti:
                return si < pi < ti
            return pi > si or pi < ti

        return on_arc(x, u, v) != on_arc(y, u, v)

    cross = crosses(a, b, c, d)
    lens = tuple(sorted((_dist(n, a, b), _dist(n, c, d))))
    gaps = _arc_gaps(n, (c1, c2))
    # separation: minimum number of cycle edges between the two chord "blocks"
    # = min of the four gaps that are not? use min gap among the 4 endpoint gaps
    sep = min(gaps) if gaps else -1
    # nested: both endpoints of one chord on the same arc determined by the other
    # For disjoint non-crossing chords on a circle, they are always "separated"
    relation = "crossing" if cross else "disjoint"
    return {
        "lens": list(lens),
        "gaps": list(gaps),
        "sep": sep,
        "relation": relation,
        "sum_lens": sum(lens),
        "max_lens": max(lens) if lens else 0,
    }


def classify_label(bits: list[tuple[int, int]], delta: int) -> str:
    """eq if refutable at Δ; gt if Δ-saturation completes with no empty (odd Tseitin ⇒ UNSAT)."""
    if batch_has_refutation_gpu([bits], [delta])[0]:
        return "eq"
    # CPU complete closure at Δ
    ok, complete = _bitsat_complete(bits, delta, max_c=100_000)
    if ok:
        return "eq"
    if complete:
        return "gt"  # closed without empty ⇒ W > Δ
    return "inconclusive"


def _bitsat_complete(
    axs: list[tuple[int, int]], wlim: int, max_c: int = 100_000
) -> tuple[bool, bool]:
    """Return (has_empty, completed_without_hitting_cap)."""
    from collections import deque

    def width(c: tuple[int, int]) -> int:
        return bin(c[0] | c[1]).count("1")

    def resolve(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int] | None:
        piv = (a[0] & b[1]) | (a[1] & b[0])
        if bin(piv).count("1") != 1:
            return None
        out = ((a[0] | b[0]) & ~piv, (a[1] | b[1]) & ~piv)
        if out[0] & out[1]:
            return None
        return out

    seen: set[tuple[int, int]] = set()
    lst: list[tuple[int, int]] = []
    pending: deque[int] = deque()

    def add(c: tuple[int, int]) -> bool:
        if width(c) > wlim or c in seen:
            return False
        seen.add(c)
        lst.append(c)
        pending.append(len(lst) - 1)
        return c == (0, 0)

    for a in axs:
        if width(a) <= wlim and add(a):
            return True, True
    while pending:
        if len(lst) > max_c:
            return False, False
        i = pending.popleft()
        a = lst[i]
        n = len(lst)
        for j in range(n):
            if i == j:
                continue
            r = resolve(a, lst[j])
            if r is None or width(r) > wlim:
                continue
            if add(r):
                return True, True
    return False, True


def enumerate_jobs(n_lo: int = 5, n_hi: int = 11):
    rows = []
    for n in range(n_lo, n_hi + 1):
        base = nx.cycle_graph(n)
        non = [(u, v) for u in range(n) for v in range(u + 1, n) if not base.has_edge(u, v)]
        batch_bits: list[list[tuple[int, int]]] = []
        batch_meta: list[dict] = []
        for chords in combinations(non, 2):
            g = base.copy()
            g.add_edges_from(chords)
            if g.number_of_edges() != n + 2:
                continue
            delta = max(d for _, d in g.degree())
            if delta > 3:
                continue
            if len({*chords[0], *chords[1]}) < 4:
                continue
            cfg = _chord_config(n, chords[0], chords[1])
            charges = tuple(1 if i == 0 else 0 for i in range(n))
            bits = formula_to_bit_axioms(tseitin_cnf(GraphInstance(g, charges, "tri", 0, {})))
            batch_bits.append(bits)
            batch_meta.append(
                {
                    "n": n,
                    "chords": [list(c) for c in chords],
                    "delta": delta,
                    **cfg,
                    "_bits": bits,
                }
            )
        # Fast GPU pass at Δ
        deltas = [m["delta"] for m in batch_meta]
        gpu_ok = batch_has_refutation_gpu(batch_bits, deltas) if batch_bits else []
        for meta, ok in zip(batch_meta, gpu_ok):
            bits = meta.pop("_bits")
            if ok:
                lab = "eq"
            else:
                found, complete = _bitsat_complete(bits, meta["delta"])
                if found:
                    lab = "eq"
                elif complete:
                    lab = "gt"
                else:
                    lab = "inconclusive"
            rows.append({**meta, "label": lab})
        n_rows = [r for r in rows if r["n"] == n]
        print(
            f"n={n} done ({len(n_rows)} graphs; "
            f"eq={sum(1 for r in n_rows if r['label']=='eq')} "
            f"gt={sum(1 for r in n_rows if r['label']=='gt')} "
            f"inc={sum(1 for r in n_rows if r['label']=='inconclusive')})",
            flush=True,
        )
    return rows


def score_predicates(rows: list[dict]) -> list[dict]:
    """Evaluate candidate boolean predicates for predicting label==eq."""
    clean = [r for r in rows if r["label"] in ("eq", "gt")]
    candidates = []

    def eval_pred(name, pred):
        tp = fp = tn = fn = 0
        for r in clean:
            p = bool(pred(r))
            y = r["label"] == "eq"
            if p and y:
                tp += 1
            elif p and not y:
                fp += 1
            elif (not p) and (not y):
                tn += 1
            else:
                fn += 1
        return {
            "name": name,
            "tp": tp,
            "fp": fp,
            "tn": tn,
            "fn": fn,
            "precision": tp / (tp + fp) if tp + fp else None,
            "recall": tp / (tp + fn) if tp + fn else None,
            "exact": fp == 0 and fn == 0,
            "safe_eq_rule": fp == 0 and tp > 0,  # pred ⇒ eq, no false positives
            "safe_gt_rule": fn == 0 and tn > 0,  # ~pred ⇒ gt? actually pred false ⇒ gt if fn=0
        }

    # Candidate laws (informed by prior gap observations)
    candidates.append(eval_pred("relation==crossing", lambda r: r["relation"] == "crossing"))
    candidates.append(eval_pred("relation==disjoint", lambda r: r["relation"] == "disjoint"))
    candidates.append(eval_pred("sep>=2", lambda r: r["sep"] >= 2))
    candidates.append(eval_pred("sep==1", lambda r: r["sep"] == 1))
    candidates.append(eval_pred("max_lens<=2", lambda r: r["max_lens"] <= 2))
    candidates.append(eval_pred("sum_lens<=4", lambda r: r["sum_lens"] <= 4))
    candidates.append(eval_pred("sum_lens<=5", lambda r: r["sum_lens"] <= 5))
    candidates.append(eval_pred("lens==(2,2)", lambda r: tuple(r["lens"]) == (2, 2)))
    candidates.append(eval_pred("sep>=2 & max_lens<=3", lambda r: r["sep"] >= 2 and r["max_lens"] <= 3))
    candidates.append(
        eval_pred(
            "disjoint & sep>=2 & max_lens<=2",
            lambda r: r["relation"] == "disjoint" and r["sep"] >= 2 and r["max_lens"] <= 2,
        )
    )
    candidates.append(
        eval_pred(
            "disjoint & gaps has two >=2",
            lambda r: r["relation"] == "disjoint" and sum(1 for g in r["gaps"] if g >= 2) >= 2,
        )
    )
    # gaps tuple patterns that were ALL_EQ before
    for gap_pat in {
        tuple(r["gaps"]) for r in clean if r["label"] == "eq"
    }:
        candidates.append(
            eval_pred(f"gaps=={list(gap_pat)}", lambda r, g=gap_pat: tuple(r["gaps"]) == g)
        )
    # Combinations with lens
    candidates.append(
        eval_pred(
            "disjoint & sep>=2",
            lambda r: r["relation"] == "disjoint" and r["sep"] >= 2,
        )
    )
    candidates.append(
        eval_pred(
            "crossing ⇒ gt? not-crossing",
            lambda r: r["relation"] != "crossing",
        )
    )

    # Search small boolean mixes on sep / max_lens / sum_lens / relation
    for sep_min in (1, 2, 3):
        for ml in (2, 3, 4):
            for sl in (4, 5, 6, 7):
                name = f"sep>={sep_min} & max_lens<={ml} & sum_lens<={sl}"
                candidates.append(
                    eval_pred(
                        name,
                        lambda r, s=sep_min, m=ml, u=sl: r["sep"] >= s
                        and r["max_lens"] <= m
                        and r["sum_lens"] <= u,
                    )
                )

    # Prefer exact / safe rules
    candidates.sort(key=lambda c: (not c["exact"], not c["safe_eq_rule"], -(c["tp"] or 0), c["fp"]))
    return candidates


def feature_table(rows: list[dict]) -> dict:
    """Contingency: feature value → {eq, gt}."""
    tables = defaultdict(lambda: defaultdict(lambda: {"eq": 0, "gt": 0}))
    for r in rows:
        if r["label"] not in ("eq", "gt"):
            continue
        for key in ("relation", "sep", "max_lens", "sum_lens"):
            tables[key][str(r[key])][r["label"]] += 1
        tables["lens"][str(r["lens"])][r["label"]] += 1
        tables["gaps"][str(r["gaps"])][r["label"]] += 1
        tables["n_sep"][f"n={r['n']}|sep={r['sep']}"][r["label"]] += 1
        tables["rel_sep"][f"{r['relation']}|sep={r['sep']}"][r["label"]] += 1
    return {k: dict(v) for k, v in tables.items()}


def main() -> int:
    rows = enumerate_jobs(5, 11)
    preds = score_predicates(rows)
    tables = feature_table(rows)
    by_n = defaultdict(lambda: {"eq": 0, "gt": 0, "inconclusive": 0})
    for r in rows:
        by_n[r["n"]][r["label"]] += 1

    exact = [p for p in preds if p["exact"]]
    safe = [p for p in preds if p["safe_eq_rule"]]
    report = {
        "family": "C_n + 2 chords, unit charge, Delta<=3",
        "checked": len(rows),
        "by_n": dict(by_n),
        "best_exact_predicates": exact[:10],
        "best_safe_eq_predicates": safe[:15],
        "top_predicates": preds[:25],
        "feature_tables": {
            k: tables[k]
            for k in ("relation", "sep", "lens", "rel_sep", "gaps")
            if k in tables
        },
        "eq_examples": [r for r in rows if r["label"] == "eq"][:12],
        "gt_examples": [r for r in rows if r["label"] == "gt"][:12],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({"by_n": report["by_n"], "exact": exact[:5], "safe": safe[:8]}, indent=2))
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
