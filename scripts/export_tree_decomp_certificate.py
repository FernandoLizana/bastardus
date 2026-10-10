#!/usr/bin/env python3
"""Export verified tree-decomposition certificates for ChordWidth smoke line graphs.

Generates JSON under ``reports/tree_decomp_certificates/`` and optional Lean snippets.

Usage:
  python scripts/export_tree_decomp_certificate.py
  python scripts/export_tree_decomp_certificate.py --lean-snippet
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from treewidth.decomp import TreeDecompCertificate, line_graph_certificate  # noqa: E402

OUT_DIR = ROOT / "reports" / "tree_decomp_certificates"
SMOKES = [
    "c5Ofold_crossing",
    "c6Crossing_crossing",
    "c7Crossing_crossing",
    "c7Nested_noncrossing",
    "c8Nested_noncrossing",
    "c8Crossing_crossing",
    "c9Crossing_crossing",
    "c9Nested_noncrossing",
    "c10Crossing_crossing",
    "c10Nested_noncrossing",
]


def write_json(cert: TreeDecompCertificate, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(cert.to_dict(), indent=2) + "\n", encoding="utf-8")


def lean_snippet(cert: TreeDecompCertificate) -> str:
    """Minimal data block for hand-off to TreeDecomp/Certificates.lean."""
    bags = cert.bags
    tree = cert.tree_edges
    edges = cert.edges
    lines = [
        f"-- Auto-generated from {cert.name}.json",
        f"-- tw={cert.treewidth}, width={cert.width}, |V|={cert.n_vertices}, bags={cert.n_bags}",
        f"def {cert.name}_n : Nat := {cert.n_vertices}",
        f"def {cert.name}_tw : Nat := {cert.treewidth}",
        f"def {cert.name}_width : Nat := {cert.width}",
        f"def {cert.name}_edges : List (Nat × Nat) := {edges}",
        f"def {cert.name}_bags : List (List Nat) := {bags}",
        f"def {cert.name}_treeEdges : List (Nat × Nat) := {tree}",
    ]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lean-snippet",
        action="store_true",
        help="Also write .lean.data snippets next to JSON files.",
    )
    parser.add_argument(
        "--skip-c8-crossing",
        action="store_true",
        help="Skip optional c8Crossing smoke (faster).",
    )
    args = parser.parse_args()

    names = SMOKES if not args.skip_c8_crossing else SMOKES[:2]
    summary: list[str] = []

    for name in names:
        print(f"Computing {name} ...", flush=True)
        cert = line_graph_certificate(name)
        json_path = OUT_DIR / f"{name}.json"
        write_json(cert, json_path)
        print(
            f"  tw={cert.treewidth} width={cert.width} "
            f"|V|={cert.n_vertices} bags={cert.n_bags} -> {json_path.relative_to(ROOT)}"
        )
        summary.append(
            f"| {name} | {cert.treewidth} | {cert.width} | {cert.n_vertices} | {cert.n_bags} |"
        )
        if args.lean_snippet:
            snippet_path = OUT_DIR / f"{name}.lean.data"
            snippet_path.write_text(lean_snippet(cert), encoding="utf-8")
            print(f"  snippet: {snippet_path.relative_to(ROOT)}")

    md = OUT_DIR / "README.md"
    md.write_text(
        "# Tree decomposition certificates (smoke line graphs)\n\n"
        "Generado por `scripts/export_tree_decomp_certificate.py`.\n\n"
        "| instance | tw | decomp width | |V(L(G))| | bags |\n"
        "|----------|----|--------------|---------|------|\n"
        + "\n".join(summary)
        + "\n",
        encoding="utf-8",
    )
    print(f"Summary: {md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
