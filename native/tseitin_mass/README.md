# Native mass verification (`tseitin_mass`)

## Compute policy (CPU vs GPU)

Your Task Manager showed **CPU ~98%** / **GPU ~24%** because Rayon was using all cores.

**Native Rust (default now):**
```powershell
& "$env:LOCALAPPDATA\tseitin_mass_target\release\tseitin_mass.exe" --profile classify --threads 4
```
- Default threads = `logical_cpus - 2` (headroom for UI + GPU driver)
- Bitmask width oracle (much less CPU time per instance)

**GPU OpenCL (NVIDIA RTX via drivers):**
```powershell
pip install pyopencl
python -m backend.proof_complexity.gpu_width_opencl --demo --limit 500
```
Batches independent Width=Δ checks on the discrete GPU. Native `wgpu` needs MSVC `dlltool` on this host, so OpenCL is the working GPU path.



## What it verifies (variants)

| Id | Family | Group action on charges | Claim checked |
|----|--------|-------------------------|---------------|
| V1 | All labeled trees (Prüfer) × all odd charges | — | Width = Δ via leaf induction certificate |
| V1b | Labeled trees × Aut-orbit odd charges | Aut(G) ≤ Sym(V) | Same, orbit-reduced |
| V2 | Paths | ℤ₂ (reversal) | Width = Δ |
| V3 | Stars | Sₙ₋₁ on leaves (sorted canonical) | Width = Δ = n−1 |
| V4 | Cycles | Dihedral Dₙ | Width = 2 (saturation certificate) |
| V5 | Trees × unit charges | — | Stress flood |
| V6 | Paths × weight-3 charges | — | Odd-weight patterns |
| V7 | Caterpillars | — | Trees with Δ ≥ 3 |

Evidence level: **E2** (machine-checked constructive certificates).  
This is **not** a P vs NP claim.

## Build / run

Rust GNU toolchain required. Artifacts go to `%LOCALAPPDATA%\tseitin_mass_target` (avoids OneDrive locking `target/`).

```powershell
cd native\tseitin_mass
$env:Path = "$env:USERPROFILE\.cargo\bin;" + $env:Path
$env:CARGO_TARGET_DIR = "$env:LOCALAPPDATA\tseitin_mass_target"
cargo build --release
& "$env:CARGO_TARGET_DIR\release\tseitin_mass.exe" --profile laptop --out-dir ..\..\reports\discovery
```

Or from Python:

```powershell
python -m backend.proof_complexity.mass_verify --profile laptop
```

Profiles: `smoke` | `laptop` | `heavy`.

Reports: `reports/discovery/mass_verify_<profile>_latest.json`.
