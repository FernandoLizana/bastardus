#!/usr/bin/env python3
"""Export tree-decomposition certificates for the cubic Hamiltonian asymptotic family.

Generates JSON under ``reports/tree_decomp_certificates/asymptotic/`` for
n = 6, 8, 10, 12, 14 (even n). Exact tw via Python bitset search is feasible
for |V(L(G))| ≤ 15 (n ≤ 10); n = 12, 14 use heuristic tw with verified
decomposition at the reported width (see notes in each JSON).

Usage:
  PYTHONPATH=scripts python scripts/export_asymptotic_tree_decomp_certificates.py
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from treewidth.decomp import TreeDecompCertificate, cubic_hamiltonian_certificate  # noqa: E402

OUT_DIR = ROOT / "reports" / "tree_decomp_certificates" / "asymptotic"

# |V(L(G))| = 3n/2; exact bitset search safe up to 15 vertices (n=10).
DEFAULT_NS = [6, 8, 10, 12, 14]
EXACT_LINE_VERTICES_MAX = 15
LEAN_CERT_NS = {6, 8, 10}


def write_json(cert: TreeDecompCertificate, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(cert.to_dict(), indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ns",
        type=int,
        nargs="+",
        default=DEFAULT_NS,
        help=f"Even n values to export (default: {DEFAULT_NS}).",
    )
    args = parser.parse_args()

    summary: list[str] = []
    for n in args.ns:
        if n % 2 != 0:
            print(f"Skipping odd n={n}", flush=True)
            continue
        line_verts = 3 * n // 2
        memory_safe = line_verts > EXACT_LINE_VERTICES_MAX
        label = "exact" if not memory_safe else "heuristic tw + verified decomp"
        print(f"Computing cubic_hamiltonian_n{n} ({label}, |V(L)|={line_verts}) ...", flush=True)
        cert = cubic_hamiltonian_certificate(n, memory_safe=memory_safe)
        json_path = OUT_DIR / f"cubic_hamiltonian_n{n}.json"
        write_json(cert, json_path)
        lean_status = (
            "**certified** (`CertificatesAsymptotic.lean`)"
            if n in LEAN_CERT_NS
            else "JSON only"
        )
        print(
            f"  tw={cert.treewidth} width={cert.width} "
            f"|V|={cert.n_vertices} method={cert.tw_method} -> {json_path.relative_to(ROOT)}"
        )
        summary.append(
            f"| n={n} | {cert.treewidth} | {cert.width} | {cert.n_vertices} | "
            f"{cert.n_bags} | {cert.tw_method} | {lean_status} |"
        )

    md = OUT_DIR / "README.md"
    md.write_text(
        "# Asymptotic cubic Hamiltonian tree-decomposition certificates\n\n"
        "Generado por `scripts/export_asymptotic_tree_decomp_certificates.py`.\n\n"
        "Familia: C_n + cuerdas (i, i+n/2) para n par; certificado sobre L(G).\n\n"
        "n ≥ 12 Python: |V(L)| > 14 fuera de búsqueda exacta bitset; tw vía heurística, "
        "descomposición verificada al ancho reportado.\n\n"
        "Lean n=6,8,10: `emit_lean_tree_decomp_asymptotic.py` + `set_option maxHeartbeats 1600000`.\n\n"
        "| n | tw | decomp width | |V(L(G))| | bags | tw method | Lean |\n"
        "|---|----|--------------|---------|------|-----------|------|\n"
        + "\n".join(summary)
        + "\n",
        encoding="utf-8",
    )
    print(f"Summary: {md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
