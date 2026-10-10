"""Merge all-odd crossing-law JSON slices into one report."""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DISC = ROOT / "reports" / "discovery"


def merge(paths: list[Path], out: Path) -> dict:
    by_n: dict = {}
    mismatches: list = []
    inconclusive: list = []
    checked = 0
    for p in paths:
        data = json.loads(p.read_text(encoding="utf-8"))
        by_n.update(data.get("by_n", {}))
        mismatches.extend(data.get("mismatches", []))
        inconclusive.extend(data.get("inconclusive", []))
        checked += int(data.get("checked", 0))
    report = {
        "family": "C_n+2 chords, Delta<=3, all (or capped) odd charges",
        "checked": checked,
        "by_n": dict(sorted(by_n.items(), key=lambda kv: int(kv[0]))),
        "mismatches": mismatches[:50],
        "inconclusive": inconclusive[:20],
        "law_holds": len(mismatches) == 0 and all(
            v.get("inconclusive", 0) == 0 for v in by_n.values()
        ),
        "sources": [str(p.relative_to(ROOT)).replace("\\", "/") for p in paths],
        "statement": (
            "crossing ⇒ Width>Δ and non-crossing ⇒ Width=Δ "
            "for odd charges in the enumerated range"
        ),
    }
    out.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({
        "wrote": str(out),
        "checked": checked,
        "law_holds": report["law_holds"],
        "ns": list(report["by_n"]),
    }, indent=2))
    return report


def main() -> int:
    slices = [
        DISC / "crossing_law_all_odd_n5_8.json",
        DISC / "crossing_law_all_odd_n9.json",
        DISC / "crossing_law_all_odd_n10.json",
        DISC / "crossing_law_all_odd_n11.json",
        DISC / "crossing_law_all_odd_n12.json",
        DISC / "crossing_law_all_odd_n13.json",
        DISC / "crossing_law_all_odd_n14.json",
    ]
    present = [p for p in slices if p.exists()]
    if len(present) < 1:
        raise SystemExit("no slices found")
    merge(present, DISC / "crossing_law_all_odd.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
