#!/usr/bin/env python3
"""Verify line-graph treewidth on C_n + two chords (Δ=3, four distinct endpoints).

Conjecture (Phase 3 gate):
  - non-crossing chords  => tw(L(G)) = 3
  - crossing chords      => tw(L(G)) = 4

Reuses repo chord conventions from ``backend.proof_complexity.chord_crossing_law``.
Treewidth via local ``scripts/treewidth`` (NetworkX heuristics + exact B&B for small graphs).

Enumeration modes (mutually exclusive priority: representative > full-endpoints > gap):
  --representative (default)
      Fast C5/C6 witness shapes per n.  For n <= 16, gap-pattern sweep fills missing
      crossing/non-crossing witnesses.  For n > 16, **only** fast witnesses are used
      unless --full-endpoints is also given.  Never falls back to C(n,4) without
      --full-endpoints (prevents combinatorial explosion / orphan processes).
  --no-representative
      Gap-pattern sweep: rotation-normalized endpoints (0,a,a+b,a+b+c), O(n^3) per n.
      Complete up to cycle rotation; preferred for exact validation of small n.
  --full-endpoints
      Full C(n,4) x 3 pairings.  Only practical for n <= 16 (hard cap in iter_configs).
      Required to extend representative mode beyond fast witnesses when n > 16.

Timeouts (optional):
  --timeout SECS       Abort entire run after SECS seconds (global wall-clock limit).

Usage:
  python scripts/verify_chord_treewidth.py
  python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 20
  python scripts/verify_chord_treewidth.py --n-lo 5 --n-hi 14 --no-representative \\
      --exact-max-nodes 32 --csv reports/chord_treewidth_exact_n5_n14.csv
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, TimeoutError as FuturesTimeoutError
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from backend.proof_complexity.chord_crossing_law import chords_cross_on_cycle  # noqa: E402
from treewidth import compute_treewidth  # noqa: E402

CSV_OUT = ROOT / "reports" / "chord_treewidth_verification.csv"
MD_OUT = ROOT / "reports" / "CHORD_TREewidth_VERIFICATION.md"

# Representative mode: beyond fast witnesses, never scan C(n,4) unless --full-endpoints.
REPRESENTATIVE_GAP_FALLBACK_MAX_N = 16
# Full-endpoints mode: hard cap even with explicit flag.
FULL_ENDPOINTS_MAX_N = 16


@dataclass(frozen=True)
class ChordConfig:
    n: int
    p0: int
    p1: int
    p2: int
    p3: int
    pairing: str  # crossing | nested | disjoint

    @property
    def chord1(self) -> tuple[int, int]:
        if self.pairing == "crossing":
            return (self.p0, self.p2)
        if self.pairing == "nested":
            return (self.p0, self.p3)
        return (self.p0, self.p1)

    @property
    def chord2(self) -> tuple[int, int]:
        if self.pairing == "crossing":
            return (self.p1, self.p3)
        if self.pairing == "nested":
            return (self.p1, self.p2)
        return (self.p2, self.p3)

    @property
    def chord_spec(self) -> str:
        c1, c2 = self.chord1, self.chord2
        return f"({c1[0]},{c1[1]})+({c2[0]},{c2[1]})"

    @property
    def gap_pattern(self) -> tuple[int, int, int, int]:
        pts = [self.p0, self.p1, self.p2, self.p3]
        gaps = [((pts[(i + 1) % 4] - pts[i]) % self.n) for i in range(4)]
        return tuple(gaps)


def chord_pairing_from_name(name: str) -> str:
    if name not in {"crossing", "nested", "disjoint"}:
        raise ValueError(f"unknown pairing {name!r}")
    return name


def build_graph(cfg: ChordConfig) -> nx.Graph:
    g = nx.cycle_graph(cfg.n)
    g.add_edges_from([cfg.chord1, cfg.chord2])
    return g


def iter_gap_configs(n: int):
    """One representative per rotation: endpoints 0,a,a+b,a+b+c with positive gaps summing to n."""
    if n < 4:
        return
    for a in range(1, n - 2):
        for b in range(1, n - a - 1):
            for c in range(1, n - a - b):
                d = n - a - b - c
                if d < 1:
                    continue
                p0, p1, p2, p3 = 0, a, a + b, a + b + c
                for pairing in ("crossing", "nested", "disjoint"):
                    yield ChordConfig(n, p0, p1, p2, p3, pairing)


def iter_all_endpoint_configs(n: int):
    """Full C(n,4) enumeration (small n only; hard cap enforced here)."""
    if n > FULL_ENDPOINTS_MAX_N:
        raise ValueError(
            f"C(n,4) enumeration capped at n <= {FULL_ENDPOINTS_MAX_N}; got n={n}. "
            "Use --no-representative (gap sweep) or raise FULL_ENDPOINTS_MAX_N deliberately."
        )
    for p0, p1, p2, p3 in combinations(range(n), 4):
        for pairing in ("crossing", "nested", "disjoint"):
            yield ChordConfig(n, p0, p1, p2, p3, pairing)


def is_valid_delta3(cfg: ChordConfig, g: nx.Graph) -> bool:
    endpoints = {cfg.p0, cfg.p1, cfg.p2, cfg.p3}
    if len(endpoints) != 4:
        return False
    return max(dict(g.degree()).values()) == 3


def iter_representative_configs(n: int, *, full_endpoints: bool = False) -> list[ChordConfig]:
    """At least one crossing and one non-crossing Δ=3 instance per n when they exist.

    Fast C5/C6 witness shapes are always included.  For n > 16 without
    ``full_endpoints``, returns those witnesses only (no C(n,4) fallback).
    For n <= 16, gap-pattern sweep fills missing witnesses; C(n,4) only when
    ``full_endpoints`` is True.
    """
    out: list[ChordConfig] = []
    seen: set[tuple] = set()

    def add(cfg: ChordConfig) -> None:
        key = (cfg.p0, cfg.p1, cfg.p2, cfg.p3, cfg.pairing)
        if key in seen:
            return
        g = build_graph(cfg)
        if not is_valid_delta3(cfg, g):
            return
        seen.add(key)
        out.append(cfg)

    # Fast witnesses (match Lean smoke shapes).
    if n >= 5:
        add(ChordConfig(n, 0, 1, 2, 3, "crossing"))
    if n >= 6:
        add(ChordConfig(n, 0, 1, 2, 3, "nested"))
        add(ChordConfig(n, 0, 2, 4, 5, "crossing"))
        add(ChordConfig(n, 0, 2, 3, 5, "nested"))

    has_cross = any(chords_cross_on_cycle(n, c.chord1, c.chord2) for c in out)
    has_noncross = any(not chords_cross_on_cycle(n, c.chord1, c.chord2) for c in out)

    if has_cross and has_noncross and len(out) >= 2:
        return out[:4]

    # Hard cap: n > 16 without --full-endpoints => fast witnesses only.
    if n > REPRESENTATIVE_GAP_FALLBACK_MAX_N and not full_endpoints:
        return out[:4]

    crossing: ChordConfig | None = next(
        (c for c in out if chords_cross_on_cycle(n, c.chord1, c.chord2)), None
    )
    noncrossing: ChordConfig | None = next(
        (c for c in out if not chords_cross_on_cycle(n, c.chord1, c.chord2)), None
    )

    if full_endpoints and n > FULL_ENDPOINTS_MAX_N:
        # Hard cap: C(n,4) only for n <= FULL_ENDPOINTS_MAX_N even with --full-endpoints.
        return out[:4]

    search_iter = (
        iter_all_endpoint_configs(n)
        if full_endpoints
        else iter_gap_configs(n)
    )
    for cfg in search_iter:
        g = build_graph(cfg)
        if not is_valid_delta3(cfg, g):
            continue
        crosses = chords_cross_on_cycle(n, cfg.chord1, cfg.chord2)
        if crosses and crossing is None:
            crossing = cfg
            add(cfg)
        elif not crosses and noncrossing is None:
            noncrossing = cfg
            add(cfg)
        elif len(out) < 4:
            add(cfg)
        if crossing is not None and noncrossing is not None and len(out) >= 4:
            break

    result: list[ChordConfig] = []
    if crossing is not None:
        result.append(crossing)
    if noncrossing is not None and noncrossing not in result:
        result.append(noncrossing)
    for cfg in out:
        if cfg not in result:
            result.append(cfg)
        if len(result) >= 4:
            break
    return result


def iter_configs(
    n: int, *, exhaustive_endpoints: bool, representative: bool
) -> list[ChordConfig]:
    if representative:
        return iter_representative_configs(n, full_endpoints=exhaustive_endpoints)
    if exhaustive_endpoints:
        if n > FULL_ENDPOINTS_MAX_N:
            raise ValueError(
                f"--full-endpoints capped at n <= {FULL_ENDPOINTS_MAX_N}; got n={n}"
            )
        return list(iter_all_endpoint_configs(n))
    return list(iter_gap_configs(n))


def expected_tw(crosses: bool) -> int:
    return 4 if crosses else 3


def analyze_config(cfg: ChordConfig, *, exact_max_nodes: int, memory_safe: bool) -> dict | None:
    g = build_graph(cfg)
    if not is_valid_delta3(cfg, g):
        return None
    delta = 3
    crosses = chords_cross_on_cycle(cfg.n, cfg.chord1, cfg.chord2)
    lg = nx.line_graph(g)
    force_heuristic = lg.number_of_nodes() > exact_max_nodes or exact_max_nodes <= 0
    tw, tw_method = compute_treewidth(
        lg,
        exact_max_nodes=exact_max_nodes,
        force_heuristic=force_heuristic,
        memory_safe=memory_safe,
    )
    exp = expected_tw(crosses)
    return {
        "n": cfg.n,
        "p0": cfg.p0,
        "p1": cfg.p1,
        "p2": cfg.p2,
        "p3": cfg.p3,
        "pairing": cfg.pairing,
        "gap_pattern": str(cfg.gap_pattern),
        "chord_spec": cfg.chord_spec,
        "crosses": crosses,
        "delta": delta,
        "tw_line_graph": tw,
        "tw_expected": exp,
        "match": tw == exp,
        "tw_method": tw_method,
        "line_graph_order": lg.number_of_nodes(),
    }


def _analyze_config_worker(
    cfg: ChordConfig, exact_max_nodes: int, memory_safe: bool
) -> dict | None:
    """Module-level worker for ProcessPoolExecutor (Windows spawn-safe)."""
    return analyze_config(cfg, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe)


def analyze_config_timed(
    cfg: ChordConfig,
    *,
    exact_max_nodes: int,
    memory_safe: bool,
    timeout_s: float | None,
) -> dict | None:
    if timeout_s is None or timeout_s <= 0:
        return analyze_config(cfg, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe)
    with ProcessPoolExecutor(max_workers=1) as pool:
        future = pool.submit(_analyze_config_worker, cfg, exact_max_nodes, memory_safe)
        try:
            return future.result(timeout=timeout_s)
        except FuturesTimeoutError:
            future.cancel()
            crosses = chords_cross_on_cycle(cfg.n, cfg.chord1, cfg.chord2)
            return {
                "n": cfg.n,
                "p0": cfg.p0,
                "p1": cfg.p1,
                "p2": cfg.p2,
                "p3": cfg.p3,
                "pairing": cfg.pairing,
                "gap_pattern": str(cfg.gap_pattern),
                "chord_spec": cfg.chord_spec,
                "crosses": crosses,
                "delta": 3,
                "tw_line_graph": "",
                "tw_expected": expected_tw(crosses),
                "match": False,
                "tw_method": "timeout",
                "line_graph_order": "",
            }


def write_csv(rows: list[dict], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "n",
        "p0",
        "p1",
        "p2",
        "p3",
        "pairing",
        "gap_pattern",
        "chord_spec",
        "crosses",
        "delta",
        "tw_line_graph",
        "tw_expected",
        "match",
        "tw_method",
        "line_graph_order",
    ]
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)


def write_markdown(
    rows: list[dict],
    *,
    path: Path,
    runtime_s: float,
    n_lo: int,
    n_hi: int,
    exact_max_nodes: int,
    memory_safe: bool,
    skipped: int,
    timed_out: int = 0,
    global_timeout: float | None = None,
) -> None:
    total = len(rows)
    timeouts = [r for r in rows if r.get("tw_method") == "timeout"]
    mismatches = [r for r in rows if not r["match"] and r.get("tw_method") != "timeout"]
    by_cross = Counter((r["crosses"], r["tw_line_graph"]) for r in rows if r.get("tw_method") != "timeout")
    methods = Counter(r["tw_method"] for r in rows)

    lines = [
        "# Chord line-graph treewidth verification",
        "",
        f"**Generated:** {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())}",
        f"**Range:** n = {n_lo}..{n_hi}",
        f"**Runtime:** {runtime_s:.2f}s",
        f"**Valid Δ=3 configurations checked:** {total}",
        f"**Skipped (Δ≠3 or degenerate chords):** {skipped}",
        "",
        "## Conjecture",
        "",
        "For G = C_n + two chords (four distinct endpoints, Δ = 3):",
        "",
        "| Geometry | Expected tw(L(G)) |",
        "|----------|-------------------|",
        "| non-crossing | 3 |",
        "| crossing | 4 |",
        "",
        "## Summary",
        "",
        f"- **Matches:** {total - len(mismatches) - len(timeouts)} / {total}",
        f"- **Mismatches (counterexamples):** {len(mismatches)}",
        f"- **Timed out:** {len(timeouts)}",
        "",
        "### Observed tw(L(G)) by crossing flag",
        "",
        "| crosses | tw | count |",
        "|---------|----|-------|",
    ]
    for (crosses, tw), count in sorted(by_cross.items()):
        lines.append(f"| {crosses} | {tw} | {count} |")

    lines.extend(
        [
            "",
            "### Treewidth methods used",
            "",
            "| method | count |",
            "|--------|-------|",
        ]
    )
    for method, count in sorted(methods.items()):
        lines.append(f"| {method} | {count} |")

    lines.extend(
        [
            "",
            "## Sample results (first 12 rows)",
            "",
            "| n | pairing | crosses | tw | expected | match | method | chord_spec |",
            "|---|---------|---------|----|-----------|-------|--------|------------|",
        ]
    )
    for r in rows[:12]:
        lines.append(
            f"| {r['n']} | {r['pairing']} | {r['crosses']} | {r['tw_line_graph']} | "
            f"{r['tw_expected']} | {r['match']} | {r['tw_method']} | {r['chord_spec']} |"
        )

    if mismatches:
        lines.extend(
            [
                "",
                "## Counterexamples",
                "",
                "| n | pairing | crosses | tw | expected | method | chord_spec | gap_pattern |",
                "|---|---------|---------|----|-----------|--------|------------|-------------|",
            ]
        )
        for r in mismatches[:50]:
            lines.append(
                f"| {r['n']} | {r['pairing']} | {r['crosses']} | {r['tw_line_graph']} | "
                f"{r['tw_expected']} | {r['tw_method']} | {r['chord_spec']} | {r['gap_pattern']} |"
            )
        if len(mismatches) > 50:
            lines.append(f"\n_(Showing 50 of {len(mismatches)} mismatches; see CSV for full list.)_")
    else:
        lines.extend(["", "## Counterexamples", "", "None found in this run."])

    method_notes = [
        "",
        "## Method notes",
        "",
        "- Graph builder: `networkx.cycle_graph(n)` + two chord edges.",
        "- Crossing test: `backend.proof_complexity.chord_crossing_law.chords_cross_on_cycle`.",
        "- Line graph: `networkx.line_graph`.",
        f"- Exact treewidth (bruteforce elimination) when |V(L(G))| ≤ {exact_max_nodes}; "
        "otherwise NetworkX min-degree / min-fill-in **upper bound** (not exact).",
        f"- ``exact_width_search`` (|V| > 8) skipped when |V| > 14 and "
        f"``--memory-safe`` is on (default): n=15..20 trial hit MemoryError.",
        "- PyPI package `treewidth` is unavailable; local module `scripts/treewidth` is used.",
        "- Default: `--representative` (fast C5/C6 witnesses; gap fallback for n≤16 only).",
        "- Gap-pattern sweep (`--no-representative`): rotation-normalized, O(n³) per n.",
        "- Full C(n,4) (`--full-endpoints`): capped at n≤16 even with explicit flag.",
        f"- Representative mode never uses C(n,4) unless `--full-endpoints`; "
        f"n>{REPRESENTATIVE_GAP_FALLBACK_MAX_N} uses witnesses only.",
    ]
    if global_timeout:
        method_notes.append(f"- Global timeout: {global_timeout}s.")
    out_path = path if path.is_absolute() else ROOT / path
    method_notes.extend(["", f"CSV: `{out_path.relative_to(ROOT).as_posix()}`"])
    lines.extend(method_notes)

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run(
    n_lo: int,
    n_hi: int,
    *,
    exact_max_nodes: int,
    memory_safe: bool,
    exhaustive_endpoints: bool,
    representative: bool,
    global_timeout: float | None = None,
) -> tuple[list[dict], float, int, int]:
    rows: list[dict] = []
    skipped = 0
    timed_out = 0
    t0 = time.perf_counter()
    for n in range(n_lo, n_hi + 1):
        if global_timeout is not None and (time.perf_counter() - t0) >= global_timeout:
            print(f"Global timeout ({global_timeout}s) reached at n={n}", file=sys.stderr)
            break
        configs = iter_configs(
            n,
            exhaustive_endpoints=exhaustive_endpoints,
            representative=representative,
        )
        for cfg in configs:
            if global_timeout is not None and (time.perf_counter() - t0) >= global_timeout:
                break
            row = analyze_config(
                cfg, exact_max_nodes=exact_max_nodes, memory_safe=memory_safe
            )
            if row is None:
                skipped += 1
                continue
            if row.get("tw_method") == "timeout":
                timed_out += 1
            rows.append(row)
    return rows, time.perf_counter() - t0, skipped, timed_out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n-lo", type=int, default=5)
    parser.add_argument("--n-hi", type=int, default=100)
    parser.add_argument(
        "--exact-max-nodes",
        type=int,
        default=10,
        help="Exact bruteforce when |V(L(G))| <= this (0 = heuristics only). Default 10 (~ n<=8).",
    )
    parser.add_argument(
        "--memory-safe",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Skip exact_width_search when |V(L(G))| > 14 (default: on; n=15..20 OOM lesson).",
    )
    parser.add_argument(
        "--full-endpoints",
        action="store_true",
        help=f"Use full C(n,4) enumeration (capped at n<={FULL_ENDPOINTS_MAX_N}).",
    )
    parser.add_argument(
        "--representative",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="One crossing + one non-crossing witness per n (default).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=None,
        metavar="SECS",
        help="Global wall-clock limit: abort entire run after SECS seconds.",
    )
    parser.add_argument("--csv", type=Path, default=CSV_OUT)
    parser.add_argument("--md", type=Path, default=MD_OUT)
    args = parser.parse_args()

    if args.full_endpoints and args.n_hi > FULL_ENDPOINTS_MAX_N:
        parser.error(
            f"--full-endpoints is capped at n <= {FULL_ENDPOINTS_MAX_N}; "
            f"got --n-hi {args.n_hi}"
        )

    rows, runtime, skipped, timed_out = run(
        args.n_lo,
        args.n_hi,
        exact_max_nodes=args.exact_max_nodes,
        memory_safe=args.memory_safe,
        exhaustive_endpoints=args.full_endpoints,
        representative=args.representative,
        global_timeout=args.timeout,
    )
    write_csv(rows, args.csv)
    write_markdown(
        rows,
        path=args.md,
        runtime_s=runtime,
        n_lo=args.n_lo,
        n_hi=args.n_hi,
        exact_max_nodes=args.exact_max_nodes,
        memory_safe=args.memory_safe,
        skipped=skipped,
        timed_out=timed_out,
        global_timeout=args.timeout,
    )

    mismatches = sum(
        1 for r in rows if not r["match"] and r.get("tw_method") != "timeout"
    )
    print(f"Checked {len(rows)} configurations in {runtime:.2f}s")
    print(f"Matches: {len(rows) - mismatches - timed_out} / {len(rows)}")
    print(f"Mismatches: {mismatches}")
    if timed_out:
        print(f"Timed out: {timed_out}")
    print(f"CSV: {args.csv}")
    print(f"Report: {args.md}")
    return 1 if mismatches or timed_out else 0


if __name__ == "__main__":
    raise SystemExit(main())
