"""Phase-transition style experiment for random 3-SAT (empirical, E2).

IMPORTANT METHODOLOGICAL NOTICE
--------------------------------
This experiment studies how the empirical satisfiability rate and solver
effort vary with the clause/variable ratio α = m/n on finite random 3-SAT
ensembles. It does **not**:

* prove that a sharp threshold exists for all n;
* identify a universal critical constant α*;
* place 3-SAT in P or outside P;
* resolve P vs NP in either direction.

Literature (e.g. Mitchell–Selman–Levesque 1992; Friedgut 1999 on sharp
thresholds; Mézard–Zecchina / statistical physics conjectures near ≈4.26)
motivates *where to look* experimentally. Those are external references —
our plots are finite-sample observations (Evidence Level E2).
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

from backend.core.evidence import EvidenceLevel
from backend.generators.random_ksat import RandomKSatGenerator, RandomKSatParams
from backend.models.cnf import verify_assignment
from backend.solvers.dpll import BranchingHeuristic, DPLLSolver
from backend.solvers.pysat_adapter import PySATSolver


@dataclass
class PhaseTransitionConfig:
    num_variables: int = 20
    ratios: tuple[float, ...] = (2.0, 3.0, 3.5, 4.0, 4.2, 4.5, 5.0, 6.0)
    instances_per_ratio: int = 30
    seed: int = 12345
    solvers: tuple[str, ...] = ("dpll", "pysat")
    timeout_seconds: float = 2.0
    output_dir: str = "reports/experiments"


def _get_solver(name: str) -> Any:
    if name == "dpll":
        return DPLLSolver(branching=BranchingHeuristic.DLIS)
    if name == "pysat":
        return PySATSolver()
    raise ValueError(f"Unknown solver: {name}")


def run_phase_transition(config: PhaseTransitionConfig) -> pd.DataFrame:
    gen = RandomKSatGenerator()
    rows: list[dict[str, Any]] = []
    out = Path(config.output_dir)
    out.mkdir(parents=True, exist_ok=True)

    for ratio in config.ratios:
        for i in range(config.instances_per_ratio):
            seed = config.seed + int(ratio * 1000) + i
            params = RandomKSatParams(
                num_variables=config.num_variables,
                clause_variable_ratio=ratio,
                k=3,
                seed=seed,
            )
            formula = gen.generate(params)
            # Cross-validate solvers when multiple provided
            answers: dict[str, bool | None] = {}
            for solver_name in config.solvers:
                solver = _get_solver(solver_name)
                result = solver.solve(formula, timeout_seconds=config.timeout_seconds)
                if result.satisfiable and result.assignment is not None:
                    assert verify_assignment(formula, result.assignment)
                answers[solver_name] = result.satisfiable
                rows.append(
                    {
                        "ratio": ratio,
                        "num_variables": config.num_variables,
                        "num_clauses": formula.num_clauses,
                        "instance_index": i,
                        "seed": seed,
                        "instance_hash": formula.content_hash(),
                        "solver": solver_name,
                        "satisfiable": result.satisfiable,
                        "wall_time_seconds": result.metrics.wall_time_seconds,
                        "cpu_time_seconds": result.metrics.cpu_time_seconds,
                        "decisions": result.metrics.decisions,
                        "backtracks": result.metrics.backtracks,
                        "propagations": result.metrics.propagations,
                        "conflicts": result.metrics.conflicts,
                        "peak_memory_bytes": result.metrics.peak_memory_bytes,
                        "timed_out": result.metrics.timed_out,
                        "evidence_level": EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL.name,
                        "claim_type": "observation_experimental",
                    }
                )
            # Agreement check
            definitive = [v for v in answers.values() if v is not None]
            if len(set(definitive)) > 1:
                rows.append(
                    {
                        "ratio": ratio,
                        "num_variables": config.num_variables,
                        "num_clauses": formula.num_clauses,
                        "instance_index": i,
                        "seed": seed,
                        "instance_hash": formula.content_hash(),
                        "solver": "DISAGREEMENT",
                        "satisfiable": None,
                        "wall_time_seconds": 0.0,
                        "cpu_time_seconds": 0.0,
                        "decisions": 0,
                        "backtracks": 0,
                        "propagations": 0,
                        "conflicts": 0,
                        "peak_memory_bytes": 0,
                        "timed_out": False,
                        "evidence_level": EvidenceLevel.E2_REPRODUCIBLE_COMPUTATIONAL.name,
                        "claim_type": "error_or_inconclusive",
                    }
                )

    df = pd.DataFrame(rows)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    parquet_path = out / f"phase_transition_{stamp}.parquet"
    csv_path = out / f"phase_transition_{stamp}.csv"
    try:
        df.to_parquet(parquet_path, index=False)
    except Exception:  # noqa: BLE001
        parquet_path = out / f"phase_transition_{stamp}.parquet.skipped"
        parquet_path.write_text("parquet unavailable; see csv\n", encoding="utf-8")
    df.to_csv(csv_path, index=False)

    _write_plots(df, out, stamp, config)
    report_path = out / f"phase_transition_report_{stamp}.md"
    report_path.write_text(render_phase_transition_report(df, config, stamp), encoding="utf-8")
    stable = out / "phase_transition_latest.md"
    stable.write_text(report_path.read_text(encoding="utf-8"), encoding="utf-8")
    meta = {
        "config": asdict(config),
        "timestamp": stamp,
        "report": str(report_path),
        "csv": str(csv_path),
        "evidence_level": "E2",
        "does_not_resolve_p_vs_np": True,
    }
    (out / f"phase_transition_{stamp}_meta.json").write_text(
        json.dumps(meta, indent=2), encoding="utf-8"
    )
    return df


def _write_plots(
    df: pd.DataFrame, out: Path, stamp: str, config: PhaseTransitionConfig
) -> None:
    usable = df[df["solver"] != "DISAGREEMENT"].copy()
    # Prefer pysat for sat-rate if present
    preferred = "pysat" if "pysat" in set(usable["solver"]) else usable["solver"].iloc[0]
    sub = usable[usable["solver"] == preferred]
    sat_rate = (
        sub.groupby("ratio")["satisfiable"]
        .apply(lambda s: np.mean([x for x in s if x is not None] or [np.nan]))
        .reset_index(name="sat_rate")
    )
    effort = (
        usable.groupby(["ratio", "solver"])["decisions"].median().reset_index(name="median_decisions")
    )

    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    axes[0].plot(sat_rate["ratio"], sat_rate["sat_rate"], marker="o")
    axes[0].set_xlabel("α = m/n (clause/variable ratio)")
    axes[0].set_ylabel(f"Empirical sat. rate ({preferred})")
    axes[0].set_title(
        f"Random 3-SAT sat. rate (n={config.num_variables}, E2 — not a proof)"
    )
    axes[0].set_ylim(-0.05, 1.05)
    axes[0].axvline(4.0, color="gray", linestyle="--", alpha=0.5, label="literature cue ≈4")
    axes[0].legend(fontsize=8)

    for solver_name, grp in effort.groupby("solver"):
        axes[1].plot(grp["ratio"], grp["median_decisions"], marker="o", label=solver_name)
    axes[1].set_xlabel("α = m/n")
    axes[1].set_ylabel("Median decisions")
    axes[1].set_title("Search effort (finite n; no asymptotic claim)")
    axes[1].legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(out / f"phase_transition_{stamp}.png", dpi=140)
    fig.savefig(out / "phase_transition_latest.png", dpi=140)
    plt.close(fig)


def render_phase_transition_report(
    df: pd.DataFrame, config: PhaseTransitionConfig, stamp: str
) -> str:
    usable = df[df["solver"] != "DISAGREEMENT"]
    disagreements = int((df["solver"] == "DISAGREEMENT").sum())
    lines = [
        "# Phase Transition Experiment Report (Evidence Level E2)",
        "",
        f"**Timestamp (UTC):** {stamp}",
        f"**n (variables):** {config.num_variables}",
        f"**Ratios α tested:** {list(config.ratios)}",
        f"**Instances per ratio:** {config.instances_per_ratio}",
        f"**Base seed:** {config.seed}",
        f"**Solvers:** {list(config.solvers)}",
        f"**Solver disagreements:** {disagreements}",
        "",
        "## Claim type",
        "",
        "`observation_experimental` — **not** a lemma, **not** a proof.",
        "",
        "## What we measured",
        "",
        "For each α = m/n we generated uniform-ish random 3-CNF instances "
        "(no tautological clauses) and ran independent solvers, recording "
        "satisfiability (when decided), wall/CPU time, decisions, backtracks, "
        "and memory proxies.",
        "",
        "## Summary table (empirical sat. rate)",
        "",
        "| α | sat. rate (pysat if available) | median decisions (dpll) |",
        "|---|---|---|",
    ]
    preferred = "pysat" if "pysat" in set(usable["solver"]) else (
        usable["solver"].iloc[0] if len(usable) else "dpll"
    )
    for ratio in config.ratios:
        sub_p = usable[(usable["ratio"] == ratio) & (usable["solver"] == preferred)]
        sub_d = usable[(usable["ratio"] == ratio) & (usable["solver"] == "dpll")]
        rate = sub_p["satisfiable"].mean() if len(sub_p) else float("nan")
        med = sub_d["decisions"].median() if len(sub_d) else float("nan")
        lines.append(f"| {ratio} | {rate:.3f} | {med} |")

    lines.extend(
        [
            "",
            "## Why this does **not** demonstrate P = NP or P ≠ NP",
            "",
            "1. **Finite n only.** Asymptotic class membership is a statement about "
            "all sufficiently large inputs. Any experiment on fixed n is consistent "
            "with infinitely many asymptotic regimes (barrier: finite vs asymptotic).",
            "2. **Distributional, not worst-case.** Random 3-SAT at a given α is an "
            "*average-case* ensemble. Hardness or easiness here does not place the "
            "worst-case decision problem in P or outside P "
            "(barrier: average vs worst case; practice vs P).",
            "3. **No universal α* proved here.** A dip in sat. rate or peak in effort "
            "near α≈4 is a *reproducible observation* under our parameters. It does "
            "not prove a sharp threshold theorem, nor identify a constant that "
            "separates complexity classes.",
            "4. **Solver runtime ≠ complexity class.** Even if a solver were fast on "
            "all tested samples, hidden exponents, timeouts, and untested adversarial "
            "families remain (barriers: hidden constants; small-n illusion).",
            "5. **Evidence ceiling.** Under laboratory policy this report is at most "
            "**E2**. Resolving P vs NP would require Category E gates including "
            "E5 Lean verification and independent expert review — which this "
            "experiment does not attempt.",
            "",
            "## Reproducibility command",
            "",
            "```bash",
            "python -m backend.experiments.run --problem 3sat "
            "--generator random-k-sat "
            f"--variables {config.num_variables} "
            "--experiment phase-transition "
            f"--seed {config.seed} "
            f"--instances {config.instances_per_ratio}",
            "```",
            "",
            "## References motivating the search region (not proved by us)",
            "",
            "- Mitchell, D., Selman, B., & Levesque, H. (1992). Hard and easy "
            "distributions of SAT problems. AAAI.",
            "- Friedgut, E. (1999). Sharp thresholds of graph properties, and the "
            "k-sat problem. J. Amer. Math. Soc.",
            "- Achlioptas, D., & Moore, C. (various). Threshold surveys for random k-SAT.",
            "- Mézard, M., Parisi, G., & Zecchina, R. (2002). Analytic and algorithmic "
            "solution of random satisfiability problems. Science.",
            "",
            "## Methodological alerts",
            "",
            "- Negative / messy outcomes (timeouts, disagreements) are retained in the CSV.",
            "- Curve fitting to claim polynomial runtime is **disabled by policy**.",
            "- AI-generated narrative in tooling must be audited (safety rule #13).",
            "",
        ]
    )
    return "\n".join(lines)
