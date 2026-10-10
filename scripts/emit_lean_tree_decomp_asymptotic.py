#!/usr/bin/env python3
"""Emit Lean certificate modules for cubic Hamiltonian asymptotic family (n=6,8,10).

Line graphs have |V| = 3n/2 ≤ 15 — same scale as smoke certificates.
Regenerate after JSON export: ``PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_asymptotic.py``

Usage:
  PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_asymptotic.py
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from treewidth.decomp import cubic_hamiltonian_certificate  # noqa: E402

LEAN_OUT = ROOT / "lean" / "PNPLab" / "ChordWidth" / "TreeDecomp"

# n even; line graph order = 3n/2. Lean certified n=6,8,10 (|V(L)| ≤ 15; maxHeartbeats 1600000).
ASYMPTOTIC_LEAN_NS = [6, 8, 10]


def lean_list_pairs(pairs: list[list[int]]) -> str:
    inner = ", ".join(f"({a}, {b})" for a, b in pairs)
    return f"[{inner}]"


def lean_bags(bags: list[list[int]], m: int) -> str:
    lines = []
    for i, bag in enumerate(bags):
        elems = ", ".join(str(x) for x in bag)
        lines.append(f"  | {i} => {{{elems}}}")
    return "\n".join(lines)


def bag_intervals(bags: list[list[int]], n_vertices: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for x in range(n_vertices):
        idxs = [i for i, b in enumerate(bags) if x in b]
        if not idxs:
            raise RuntimeError(f"vertex {x} not covered by any bag")
        out.append((min(idxs), max(idxs)))
    return out


def emit_graph_of_edge_list(n: int) -> str:
    return f"""def graphOfEdgeList{n}Adj (edges : List (Nat × Nat)) (i j : Fin {n}) : Prop :=
  i ≠ j ∧ ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges)

instance graphOfEdgeList{n}Adj_symmInst (edges : List (Nat × Nat)) :
    Std.Symm (graphOfEdgeList{n}Adj edges) where
  symm := fun _ _ h => by
    rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by simpa [or_comm] using h⟩

instance graphOfEdgeList{n}Adj_irreflInst (edges : List (Nat × Nat)) :
    Std.Irrefl (graphOfEdgeList{n}Adj edges) where
  irrefl := fun i h => by rcases h with ⟨hne, _⟩; exact hne rfl

def graphOfEdgeList{n} (edges : List (Nat × Nat)) : SimpleGraph (Fin {n}) where
  Adj := graphOfEdgeList{n}Adj edges
  symm := inferInstance
  loopless := inferInstance
"""


def emit_cert_path_graph_theorems(ns: set[int]) -> str:
    chunks = []
    for n in sorted(ns):
        chunks.append(
            f"""theorem certPathGraph{n}_isTree : (certPathGraph {n}).IsTree := by
  classical
  rw [isTree_iff_connected_and_card]
  refine ⟨(certPathGraph_eq_pathGraph {n}).symm ▸ pathGraph_connected {n - 1}, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_edgeSet, Fintype.card_fin]
  native_decide

"""
        )
    return "".join(chunks)


def is_tree_ref(lv: int) -> str:
    """Reference certPathGraph IsTree lemma (smokes namespace or asymptotic)."""
    if lv in (9, 12):
        return f"SmokeLineGraphCert.certPathGraph{lv}_isTree"
    return f"certPathGraph{lv}_isTree"


def emit_certificates_asymptotic() -> str:
    certs = []
    line_ns: set[int] = set()
    for n in ASYMPTOTIC_LEAN_NS:
        cert = cubic_hamiltonian_certificate(n)
        certs.append((n, cert))
        line_ns.add(cert.n_vertices)

    header = """/-
  Auto-generated Fin-indexed tree-decomposition certificates for the cubic
  Hamiltonian asymptotic family D_n (n = 6, 8, 10 Lean-certified; n ≥ 12 JSON-only).

  Regenerate: `PYTHONPATH=scripts python scripts/emit_lean_tree_decomp_asymptotic.py`
-/

import PNPLab.ChordWidth.TreeDecomp.Certificates
import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphAsymptotic

set_option maxHeartbeats 1600000

namespace PNPLab.ChordWidth

open SimpleGraph
open TreeDecomp

namespace AsymptoticLineGraphCert

open SmokeLineGraphCert (bagSupWidth certPathGraph certPathGraphInterval
  certPathGraph_induce_interval_preconnected)

"""
    body = "\n".join(emit_graph_of_edge_list(n) for n in sorted(line_ns))
    chunks = [header, body]

    for n, cert in certs:
        p = f"cubicHam{n}"
        lv = cert.n_vertices
        tw = cert.treewidth
        gol = f"graphOfEdgeList{lv}"
        intervals = bag_intervals(cert.bags, lv)
        chunks.append(f"/-! ### D_{n}: tw(L(G)) = {tw}, |V(L)| = {lv} -/\n")
        chunks.append(f"def {p}_lineEdges : List (Nat × Nat) :=\n  {lean_list_pairs(cert.edges)}\n")
        chunks.append(f"def {p}_lineGraphFin : SimpleGraph (Fin {lv}) :=\n  {gol} {p}_lineEdges\n")
        chunks.append(f"def {p}_bag : Fin {lv} → Finset (Fin {lv})\n{lean_bags(cert.bags, lv)}\n")
        chunks.append(
            f"""theorem {p}_edgeCover :
    ∀ ⦃a b : Fin {lv}⦄, {p}_lineGraphFin.Adj a b →
      ∃ w : Fin {lv}, a ∈ {p}_bag w ∧ b ∈ {p}_bag w := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [{p}_lineGraphFin, {gol}, {gol}Adj, {p}_lineEdges, {p}_bag] at h ⊢ <;>
    first | contradiction | decide

theorem {p}_preconnected_bag (x : Fin {lv}) (a b : Nat)
    (ha : a < {lv}) (hb : b < {lv}) (hab : a ≤ b)
    (hset : {{w : Fin {lv} | x ∈ {p}_bag w}} = certPathGraphInterval {lv} a b) :
    (certPathGraph {lv}).induce {{w : Fin {lv} | x ∈ {p}_bag w}} |>.Preconnected := by
  rw [hset]
  exact certPathGraph_induce_interval_preconnected {lv} a b ha hb hab

noncomputable def {p}_fin_decomp : TreeDecomp {p}_lineGraphFin {lv} where
  bag := {p}_bag
  tree := certPathGraph {lv}
  isTree := {is_tree_ref(lv)}
  vertexCover := by intro x; fin_cases x <;> native_decide
  edgeCover := {p}_edgeCover
  preconnected_induce_T := by
    intro x
    fin_cases x
"""
        )
        for x, (a, b) in enumerate(intervals):
            chunks.append(
                f"    · exact {p}_preconnected_bag {x} {a} {b} (by decide) (by decide) (by decide)\n"
                f"        (by ext w; fin_cases w <;> simp [certPathGraphInterval, {p}_bag] <;> decide)\n"
            )
        chunks.append(
            f"""theorem {p}_fin_bagSupWidth : bagSupWidth {p}_bag ≤ {tw} := by native_decide

theorem {p}_fin_hasTreeDecomp_{tw} : HasTreeDecomp {p}_lineGraphFin {tw} := by
  refine ⟨{lv}, {p}_fin_decomp, ?_⟩
  have hw : {p}_fin_decomp.width = bagSupWidth {p}_bag := by
    dsimp [TreeDecomp.width, {p}_fin_decomp, {p}_bag, bagSupWidth]
    native_decide
  exact hw ▸ {p}_fin_bagSupWidth

"""
        )

    chunks.append(
        'def certificatesAsymptoticDoc : String :=\n  '
        '"HasTreeDecomp Lean-certified for cubic Hamiltonian D_n (n=6,8,10); '
        'n=12,14 JSON verified in reports/tree_decomp_certificates/asymptotic/."\n'
    )
    chunks.append("end AsymptoticLineGraphCert\n\nend PNPLab.ChordWidth\n")
    return "".join(chunks)


def main() -> int:
    line_ns = {cubic_hamiltonian_certificate(n).n_vertices for n in ASYMPTOTIC_LEAN_NS}

    cert_asym_path = LEAN_OUT / "CertificatesAsymptotic.lean"
    cert_path_path = LEAN_OUT / "CertPathGraphAsymptotic.lean"

    # Only emit isTree lemmas not already in CertPathGraphSmokes (9, 12 exist there).
    needed_path_ns = line_ns - {9, 12}
    cert_path_path.write_text(
        f"""/-
  Auto-generated certPathGraph IsTree lemmas for asymptotic line-graph orders.
-/

import PNPLab.ChordWidth.TreeDecomp.CertPathGraph
import PNPLab.ChordWidth.TreeDecomp.CertPathGraphSmokes

namespace PNPLab.ChordWidth

namespace AsymptoticLineGraphCert

open SimpleGraph
open SmokeLineGraphCert (certPathGraph certPathGraph_eq_pathGraph)

{emit_cert_path_graph_theorems(needed_path_ns)}end AsymptoticLineGraphCert

end PNPLab.ChordWidth
""",
        encoding="utf-8",
    )

    cert_asym_path.write_text(emit_certificates_asymptotic(), encoding="utf-8")

    print(f"Wrote {cert_asym_path.relative_to(ROOT)}")
    print(f"Wrote {cert_path_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
