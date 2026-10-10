#!/usr/bin/env python3
"""Optional LibTW (Java) adapter for tree-decomposition export.

If ``LIBTW_JAR`` points to a LibTW jar, attempts exact treewidth + decomposition
via external Java process. Otherwise falls back to the Python ``line_graph_certificate``
/ ``cubic_hamiltonian_certificate`` pipeline in ``treewidth.decomp``.

LibTW is **not required** for ChordWidth builds. See README § ChordWidth certificates.

Usage:
  LIBTW_JAR=/path/to/libtw.jar PYTHONPATH=scripts python scripts/libtw_adapter.py --name c5Ofold_crossing
  PYTHONPATH=scripts python scripts/libtw_adapter.py --cubic-n 6
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from treewidth.decomp import (  # noqa: E402
    TreeDecompCertificate,
    cubic_hamiltonian_certificate,
    line_graph_certificate,
)


def libtw_available() -> bool:
    jar = os.environ.get("LIBTW_JAR", "")
    return bool(jar and Path(jar).is_file())


def _write_dimacs(g_edges: list[list[int]], n: int, path: Path) -> None:
    """Minimal undirected graph DIMACS for LibTW-style tools."""
    lines = [f"p edge {n} {len(g_edges)}"]
    for u, v in g_edges:
        lines.append(f"e {u + 1} {v + 1}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def try_libtw_certificate(
    edges: list[list[int]],
    n_vertices: int,
    name: str,
    *,
    k_hint: int | None = None,
) -> TreeDecompCertificate | None:
    """Attempt LibTW export; return None if unavailable or invocation fails."""
    jar = os.environ.get("LIBTW_JAR")
    if not jar or not Path(jar).is_file():
        return None

    java = os.environ.get("JAVA", "java")
    with tempfile.TemporaryDirectory() as tmp:
        dimacs = Path(tmp) / "graph.dimacs"
        _write_dimacs(edges, n_vertices, dimacs)
        cmd = [java, "-jar", jar, str(dimacs)]
        if k_hint is not None:
            cmd.extend(["-k", str(k_hint)])
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            return None
        if result.returncode != 0:
            return None
        # LibTW output format varies by build; if JSON not produced, fall back.
        out_json = Path(tmp) / "decomposition.json"
        if not out_json.is_file():
            return None
        data = json.loads(out_json.read_text(encoding="utf-8"))
        cert = TreeDecompCertificate(
            name=name,
            n_vertices=n_vertices,
            edges=edges,
            n_bags=data["n_bags"],
            bags=data["bags"],
            tree_edges=data["tree_edges"],
            width=data["width"],
            treewidth=data["treewidth"],
            tw_method="libtw",
            notes=data.get("notes", "LibTW export"),
        )
        return cert


def certificate_for_smoke(name: str) -> tuple[TreeDecompCertificate, str]:
    """Return certificate and backend label (libtw or python)."""
    if libtw_available():
        py_cert = line_graph_certificate(name)
        libtw_cert = try_libtw_certificate(
            py_cert.edges, py_cert.n_vertices, name, k_hint=py_cert.treewidth
        )
        if libtw_cert is not None:
            return libtw_cert, "libtw"
    return line_graph_certificate(name), "python"


def certificate_for_cubic(n: int) -> tuple[TreeDecompCertificate, str]:
    if libtw_available():
        py_cert = cubic_hamiltonian_certificate(n, memory_safe=n > 10)
        libtw_cert = try_libtw_certificate(
            py_cert.edges, py_cert.n_vertices, py_cert.name, k_hint=py_cert.treewidth
        )
        if libtw_cert is not None:
            return libtw_cert, "libtw"
    return cubic_hamiltonian_certificate(n, memory_safe=n > 10), "python"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", help="Smoke graph name (e.g. c5Ofold_crossing)")
    parser.add_argument("--cubic-n", type=int, help="Cubic Hamiltonian even n")
    args = parser.parse_args()

    if args.name:
        cert, backend = certificate_for_smoke(args.name)
    elif args.cubic_n is not None:
        cert, backend = certificate_for_cubic(args.cubic_n)
    else:
        parser.error("Provide --name or --cubic-n")

    print(f"backend={backend} tw={cert.treewidth} width={cert.width} method={cert.tw_method}")
    print(json.dumps(cert.to_dict(), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
