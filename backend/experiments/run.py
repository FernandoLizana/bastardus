"""CLI entrypoint for reproducible experiments.

Example:
  python -m backend.experiments.run --problem 3sat --generator random-k-sat \\
    --variables 20 --experiment phase-transition --seed 12345 --instances 20
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Optional

import typer

from backend.experiments.phase_transition import PhaseTransitionConfig, run_phase_transition

app = typer.Typer(add_completion=False, no_args_is_help=True)


@app.command()
def main(
    problem: str = typer.Option("3sat", help="Problem id"),
    generator: str = typer.Option("random-k-sat", help="Generator id"),
    variables: int = typer.Option(20, help="Number of Boolean variables"),
    ratio: Optional[float] = typer.Option(None, help="Single ratio override (optional)"),
    instances: int = typer.Option(20, help="Instances per ratio"),
    seed: int = typer.Option(12345, help="Base RNG seed"),
    solvers: str = typer.Option("dpll,pysat", help="Comma-separated solver names"),
    experiment: str = typer.Option("phase-transition", help="Experiment name"),
    timeout: float = typer.Option(2.0, help="Per-instance timeout seconds"),
) -> None:
    """Run a registered experiment and write a reproducible report."""
    if problem != "3sat":
        raise typer.BadParameter("MVP supports problem=3sat only")
    if generator != "random-k-sat":
        raise typer.BadParameter("MVP supports generator=random-k-sat only")
    if experiment != "phase-transition":
        raise typer.BadParameter("MVP supports experiment=phase-transition only")

    ratios: tuple[float, ...]
    if ratio is not None:
        ratios = (ratio,)
    else:
        ratios = (2.0, 3.0, 3.5, 4.0, 4.2, 4.5, 5.0, 6.0)

    config = PhaseTransitionConfig(
        num_variables=variables,
        ratios=ratios,
        instances_per_ratio=instances,
        seed=seed,
        solvers=tuple(s.strip() for s in solvers.split(",") if s.strip()),
        timeout_seconds=timeout,
    )
    print(
        "PNP Research Lab — experiment runner "
        "(evidence <= E2; does not resolve P vs NP)"
    )
    df = run_phase_transition(config)
    print(f"Wrote {len(df)} rows. See reports/experiments/phase_transition_latest.md")
    repro = {
        "command": (
            f"python -m backend.experiments.run --problem {problem} "
            f"--generator {generator} --variables {variables} "
            f"--instances {instances} --seed {seed} --solvers {solvers} "
            f"--experiment {experiment} --timeout {timeout}"
        ),
        "does_not_resolve_p_vs_np": True,
    }
    Path("reports/experiments/last_repro_command.json").write_text(
        json.dumps(repro, indent=2), encoding="utf-8"
    )


if __name__ == "__main__":
    app()
