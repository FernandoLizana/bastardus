"""Mass: XOR local-Gaussian residual split still fails on both-stub length-2 ears.

Documents `gap_remains` across n=5..10 (not a single C₆ witness).
"""

from __future__ import annotations

import json
from pathlib import Path

from backend.proof_complexity.xor_gaussian_residual_split import (
    _len2_both_stubs,
    attempt_gaussian_split,
)

OUT = Path("reports/discovery/xor_gaussian_gap_mass.json")


def main() -> int:
    rows: list[dict] = []
    gap = ok_pure = 0
    for n in range(5, 11):
        for a in range(n):
            s = _len2_both_stubs(n=n, a=a)
            if not s["ou"] or not s["ow"]:
                continue
            att = attempt_gaussian_split(s)
            pure = bool(att.get("splits_without_global_sat"))
            if pure:
                ok_pure += 1
            else:
                gap += 1
            rows.append(
                {
                    "n": n,
                    "a": a,
                    "pure": pure,
                    "mode": att.get("mode"),
                    "resid_u": att.get("resid_u"),
                    "resid_w": att.get("resid_w"),
                }
            )
    report = {
        "total": len(rows),
        "gap_remains_count": gap,
        "pure_local_gaussian_count": ok_pure,
        "samples": rows,
        "claim": (
            "Pure local-Gaussian residual fill after tip XOR-sum fails on every "
            "sampled length-2 both-stub ear (n=5..10); gap_remains is systematic, "
            "not a C6 quirk. Hybrid target-sat / clips still OK (xor_ear_modes)."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(
        f"wrote {OUT} total={len(rows)} gap={gap} pure={ok_pure}"
    )
    return 0 if ok_pure == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
