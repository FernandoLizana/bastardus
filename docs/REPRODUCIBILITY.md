# Reproducibility

## Experiment contract

Every run should record:

- seed(s), generator, parameters, timestamp, host, platform, code version
- instance content hash
- solver name + version/backend
- metrics, timeouts, raw table (CSV/Parquet)
- exact CLI replay command
- evidence level and caveats

## Canonical CLI

```bash
python -m backend.experiments.run \
  --problem 3sat \
  --generator random-k-sat \
  --variables 20 \
  --instances 30 \
  --seed 12345 \
  --solvers dpll,pysat \
  --experiment phase-transition
```

Artifacts under `reports/experiments/`:

- `phase_transition_*.csv` / `.parquet`
- `phase_transition_*.png`
- `phase_transition_report_*.md`
- `phase_transition_latest.md` (stable pointer)
- `last_repro_command.json`

## Policy

Fitting a polynomial to timing data **does not** imply the algorithm is in P.
Document out-of-sample checks and retain negative results.
