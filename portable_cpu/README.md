# Portable CPU farm (ChordWidth + repo)

Todo vive **dentro de esta carpeta + el repo**. Copia el proyecto completo al notebook Ubuntu, ejecuta setup una vez, luego corre jobs con checkpoint/log.

## Requisitos Ubuntu

- Python 3.11+
- `curl`, `git`, `build-essential`
- [Elan](https://github.com/leanprover/elan) + Lake (Lean 4) para jobs `lean_*`

## Setup (una vez)

```bash
cd /path/to/bastardus
bash portable_cpu/bin/setup_ubuntu.sh
```

Crea venv en `portable_cpu/.venv`, instala deps Python, verifica Lean.

## Uso rápido

```bash
# Ver cola y estado
python portable_cpu/lib/job_runner.py status

# Correr TODOS los jobs pendientes (respeta dependencias, paraleliza donde se puede)
bash portable_cpu/bin/run_all.sh

# Correr un job concreto (reanuda si hay checkpoint)
bash portable_cpu/bin/run_job.sh tw_exact_n15_n24

# Solo build Lean ChordWidth (reintentos automáticos)
bash portable_cpu/bin/resume_lean_chordwidth.sh

# Reanudar orquestador tras caída
bash portable_cpu/bin/run_all.sh --resume

# Notebook Ubuntu con mucha RAM (≥32 GB)
bash portable_cpu/bin/run_all.sh --profile high_ram
```

## Perfil high-RAM

Para máquinas con **≥32 GB RAM** (p. ej. el notebook Ubuntu con RAM amplia):

```bash
bash portable_cpu/bin/run_all.sh --profile high_ram
# o manualmente:
set -a; source portable_cpu/profiles/high_ram.env; set +a
bash portable_cpu/bin/run_all.sh
```

El perfil carga `portable_cpu/profiles/high_ram.env` y fusiona `jobs.manifest.high_ram.json`.

| Ajuste | Default conservador | High-RAM |
|--------|---------------------|----------|
| `PORTABLE_CPU_JOBS` | núcleos − 1 | 6 o `max(6, nproc−1)` |
| `LEAN_THREADS` | 0 (todos) | 0 = todos los cores en `lake build` |
| TW `--memory-safe` | activo en n≥15 | **desactivable** (`--no-memory-safe`) |
| TW `--exact-max-nodes` | 14–16 | **18–20** en jobs exploratorios |

Recomendaciones:

- **TW sweeps:** omitir `--memory-safe` acelera mucho; vigilar RAM. Jobs `tw_exact_n15_n24_push_exact18` y `tw_exact_n19_n24_highram` ya vienen sin memory-safe.
- **Boundary push:** `--exact-max-nodes 18` (hasta 20 si cabe); ver `EXACT_MAX_NODES` / `MEMORY_SAFE=0` documentados en el `.env`.
- **Paralelismo Python:** 3–4 jobs TW en paralelo (grupos distintos de `n`) vía `PORTABLE_CPU_JOBS=4` o el runner; el orquestador respeta `parallel_group` (solo uno por grupo).
- **Lean:** `LEAN_THREADS=0` usa todos los cores; en build pesado conviene no correr TW exact en paralelo con Lean.

## Carpetas (backup = copiar `portable_cpu/` + `experiments/` + `reports/`)

| Carpeta | Contenido |
|---------|-----------|
| `portable_cpu/logs/` | Log por job (`{job_id}.log`) |
| `portable_cpu/state/` | Checkpoints JSON, lock, orchestrator state |
| `portable_cpu/results/` | Symlinks/copias de artefactos finales |
| `experiments/` | CSV/JSON de sweeps (repo root) |
| `lean/build-chordwidth-resume.log` | Log build Lean |

## Paralelismo

- Variable `PORTABLE_CPU_JOBS=4` (default: núcleos − 1)
- Jobs con `"parallel_group": "lean"` → **1 a la vez** (memoria)
- Jobs con `"parallel_group": "python_tw"` → hasta N en paralelo (rangos de `n` distintos)

## Lista exhaustiva de jobs

Ver **`portable_cpu/TASKS.md`**.
