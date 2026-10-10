"""SAT → 3-SAT polynomial reduction (textbook; known_result)."""

from __future__ import annotations

import time
from typing import Any

from backend.models.cnf import Clause, CNFFormula, ThreeCNF
from backend.reductions.base import ReductionResult


def sat_to_3sat(formula: CNFFormula) -> ReductionResult:
    """Convert CNF to equisatisfiable 3-CNF with auxiliary variables."""
    t0 = time.perf_counter()
    next_var = formula.num_variables + 1
    out_clauses: list[tuple[int, ...]] = []
    aux_map: list[dict[str, Any]] = []

    for c_idx, clause in enumerate(formula.clauses):
        lits = list(clause.literals)
        t = len(lits)
        if t == 0:
            out_clauses.append(())
            aux_map.append({"clause": c_idx, "kind": "empty"})
            continue
        if t == 1:
            a, b = next_var, next_var + 1
            next_var += 2
            lit = lits[0]
            out_clauses.extend(
                [
                    (lit, a, b),
                    (lit, a, -b),
                    (lit, -a, b),
                    (lit, -a, -b),
                ]
            )
            aux_map.append({"clause": c_idx, "kind": "width1", "aux": [a, b]})
            continue
        if t == 2:
            y = next_var
            next_var += 1
            out_clauses.append((lits[0], lits[1], y))
            out_clauses.append((lits[0], lits[1], -y))
            aux_map.append({"clause": c_idx, "kind": "width2", "aux": [y]})
            continue
        if t == 3:
            out_clauses.append(tuple(lits))
            aux_map.append({"clause": c_idx, "kind": "width3"})
            continue
        aux_vars: list[int] = []
        y = next_var
        next_var += 1
        aux_vars.append(y)
        out_clauses.append((lits[0], lits[1], y))
        for i in range(2, t - 2):
            y_next = next_var
            next_var += 1
            aux_vars.append(y_next)
            out_clauses.append((-y, lits[i], y_next))
            y = y_next
        out_clauses.append((-y, lits[t - 2], lits[t - 1]))
        aux_map.append({"clause": c_idx, "kind": f"width{t}", "aux": aux_vars})

    n_out = max(next_var - 1, 0)
    built = tuple(Clause(c) for c in out_clauses)
    # Empty clause allowed → not a ThreeCNF; wrap carefully
    if all(len(c) == 3 for c in built):
        three: CNFFormula = ThreeCNF(built, num_variables=n_out, metadata={})
    else:
        three = CNFFormula(built, num_variables=n_out, metadata={})
    three_meta = {
        "reduction": "sat_to_3sat",
        "aux_map": aux_map,
        "source_hash": formula.content_hash(),
        "references": [
            "Arora, S., & Barak, B. (2009). Computational Complexity.",
            "Garey, M. R., & Johnson, D. S. (1979).",
        ],
    }
    object.__setattr__(three, "metadata", three_meta)

    elapsed = time.perf_counter() - t0
    src_bits = formula.num_variables + sum(len(c) for c in formula.clauses)
    tgt_bits = three.num_variables + sum(len(c) for c in three.clauses)
    return ReductionResult(
        source_problem="sat",
        target_problem="3sat",
        source_size={
            "variables": formula.num_variables,
            "clauses": formula.num_clauses,
            "bits_estimate": src_bits,
        },
        target_size={
            "variables": three.num_variables,
            "clauses": three.num_clauses,
            "bits_estimate": tgt_bits,
        },
        transformation_time=elapsed,
        expected_answer=None,
        verified_answer=None,
        mapping_metadata={
            "instance": three,
            "poly_size_check_local": tgt_bits <= max(4 * src_bits + formula.num_clauses * 4, 1),
            "aux_map": aux_map,
        },
        certificate_mapping={"original_vars": list(range(1, formula.num_variables + 1))},
        validation_status="constructed",
    )
