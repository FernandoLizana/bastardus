"""Find signed variable bijections from Lean residual packs to k4Axioms.

A signed bijection maps each source variable to ± one canonical K4 variable.
This captures both edge relabeling and variable complementation (charge gauge).
"""

from __future__ import annotations

import ast
import itertools
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "PNPLab"
OUT = ROOT / "reports" / "discovery" / "signed_k4_pack_isomorphisms.json"

PACKS = {
    "ofold": ("OneFoldProjection.lean", "ofoldRAxioms", "ofoldVres"),
    "mf": ("MultiFoldProjection.lean", "mfRAxioms", "mfVres"),
    "tf": ("TripleFoldProjection.lean", "tfRAxioms", "tfVres"),
    "ff": ("FourFoldProjection.lean", "ffRAxioms", "ffVres"),
    "xf": ("FiveFoldProjection.lean", "xfRAxioms", "xfVres"),
    "sf": ("SixFoldProjection.lean", "sfRAxioms", "sfVres"),
    "vf": ("SevenFoldProjection.lean", "vfRAxioms", "vfVres"),
    "ef": ("EightFoldProjection.lean", "efRAxioms", "efVres"),
    "nf": ("NineFoldProjection.lean", "nfRAxioms", "nfVres"),
    "zf": ("TenFoldProjection.lean", "zfRAxioms", "zfVres"),
}


def _extract_list(text: str, name: str, type_name: str) -> list:
    if type_name == "List Nat":
        pattern = rf"(?:def|abbrev)\s+{re.escape(name)}\s*:\s*List Nat\s*:=\s*(\[[^\]]*\])"
    else:
        pattern = (
            rf"(?:def|abbrev)\s+{re.escape(name)}\s*:\s*"
            rf"{re.escape(type_name)}\s*:=\s*(\[.*?\n\s*\])"
        )
    m = re.search(pattern, text, re.S)
    if not m:
        raise ValueError(f"cannot extract {name}")
    raw = re.sub(r"\(\s*(-?\d+)\s*:\s*Lit\s*\)", r"\1", m.group(1))
    return ast.literal_eval(raw)


def _clause_set(clauses: list[list[int]]) -> frozenset[tuple[int, ...]]:
    return frozenset(tuple(sorted(c)) for c in clauses)


def _find_signed_iso(
    clauses: list[list[int]], src: list[int], target: frozenset[tuple[int, ...]]
) -> dict | None:
    for perm in itertools.permutations(range(1, 7)):
        for bits in range(64):
            mapping = {
                src[i]: perm[i] * (-1 if (bits >> i) & 1 else 1)
                for i in range(6)
            }
            mapped = frozenset(
                tuple(
                    sorted(
                        (1 if lit > 0 else -1) * mapping[abs(lit)]
                        for lit in clause
                    )
                )
                for clause in clauses
            )
            if mapped == target:
                return {
                    "src": src,
                    "dst_signed": [mapping[v] for v in src],
                    "permutation": list(perm),
                    "flips": [mapping[v] < 0 for v in src],
                }
    return None


def main() -> int:
    k4_text = (LEAN / "K4Width3.lean").read_text(encoding="utf-8")
    k4 = _extract_list(k4_text, "k4Axioms", "List Clause")
    target = _clause_set(k4)

    results: dict[str, dict] = {}
    for pack, (filename, clauses_name, vars_name) in PACKS.items():
        text = (LEAN / filename).read_text(encoding="utf-8")
        clauses = _extract_list(text, clauses_name, "List Clause")
        src = _extract_list(text, vars_name, "List Nat")
        witness = _find_signed_iso(clauses, src, target)
        results[pack] = {
            "clauses": len(clauses),
            "vars": len(src),
            "found": witness is not None,
            "witness": witness,
        }

    report = {
        "total": len(results),
        "found": sum(r["found"] for r in results.values()),
        "results": results,
        "claim": (
            "Each residual pack is isomorphic to k4Axioms under a signed "
            "variable bijection (permutation + optional complementation)."
        ),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"wrote {OUT} found={report['found']}/{report['total']}")
    for name, result in results.items():
        print(name, result["witness"])
    return 0 if report["found"] == report["total"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
