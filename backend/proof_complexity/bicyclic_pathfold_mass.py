"""Mass bicyclic pathfold certificates C_n + one chord, Δ≤3."""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx

from backend.proof_complexity.constructive_proofs import prove_bicyclic_pathfold_lemma

OUT = Path("reports/discovery/bicyclic_pathfold_mass.json")


def main() -> int:
    ok = fail = 0
    errs: list[dict] = []
    # denser: n≤12 (was n≤9)
    for n in range(4, 13):
        base = nx.cycle_graph(n)
        for a in range(n):
            for dist in range(2, n - 1):
                b = (a + dist) % n
                if a >= b:
                    continue
                g = base.copy()
                g.add_edge(a, b)
                if max(d for _, d in g.degree()) > 3:
                    continue
                try:
                    prove_bicyclic_pathfold_lemma(
                        g, {i: int(i == 0) for i in range(n)}
                    )
                    ok += 1
                except Exception as e:  # noqa: BLE001
                    fail += 1
                    if len(errs) < 12:
                        errs.append({"n": n, "chord": [a, b], "err": str(e)})
    report = {
        "ok": ok,
        "fail": fail,
        "errs": errs,
        "n_range": [4, 12],
        "claim": (
            "prove_bicyclic_pathfold_lemma succeeds for every C_n+chord "
            "with Δ≤3, unit odd, n=4..12."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({"ok": ok, "fail": fail, "n_range": [4, 12]}, indent=2))
    print(f"wrote {OUT}")
    return 0 if fail == 0 and ok > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
