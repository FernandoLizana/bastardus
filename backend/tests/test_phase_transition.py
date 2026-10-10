"""Smoke test for phase-transition experiment (tiny)."""

from backend.experiments.phase_transition import PhaseTransitionConfig, run_phase_transition


def test_phase_transition_smoke(tmp_path) -> None:  # type: ignore[no-untyped-def]
    cfg = PhaseTransitionConfig(
        num_variables=8,
        ratios=(2.0, 4.0, 6.0),
        instances_per_ratio=3,
        seed=7,
        solvers=("dpll", "pysat"),
        timeout_seconds=1.0,
        output_dir=str(tmp_path),
    )
    df = run_phase_transition(cfg)
    assert len(df) >= 3 * 2 * 3  # ratios * solvers * instances (approx)
    assert (tmp_path / "phase_transition_latest.md").exists()
