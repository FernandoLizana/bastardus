"""Launch native mass verification of Tseitin width variants.

Builds (release) and runs ``native/tseitin_mass`` with a chosen profile.
Writes JSON under ``reports/discovery/``.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CRATE = ROOT / "native" / "tseitin_mass"
OUT = ROOT / "reports" / "discovery"


def cargo_bin() -> str:
    cargo = Path.home() / ".cargo" / "bin" / "cargo.exe"
    return str(cargo) if cargo.exists() else "cargo"


def target_dir() -> Path:
    # OneDrive/sync folders often delete or lock ``target/``; keep artifacts local.
    return Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "tseitin_mass_target"


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", choices=["smoke", "laptop", "heavy", "frontier", "classify"], default="laptop")
    p.add_argument("--threads", type=int, default=None, help="Cap Rayon threads (default: cpus-2)")
    p.add_argument("--gpu-demo", action="store_true", help="Also run OpenCL NVIDIA Width=Δ demo")
    p.add_argument("--skip-build", action="store_true")
    args = p.parse_args()

    env = os.environ.copy()
    cargo_home = Path.home() / ".cargo" / "bin"
    env["PATH"] = str(cargo_home) + os.pathsep + env.get("PATH", "")
    env["CARGO_TARGET_DIR"] = str(target_dir())

    if not args.skip_build:
        print("Building release binary...", flush=True)
        r = subprocess.run(
            [cargo_bin(), "build", "--release"],
            cwd=CRATE,
            env=env,
        )
        if r.returncode != 0:
            return r.returncode

    exe = target_dir() / "release" / "tseitin_mass.exe"
    if not exe.exists():
        exe = target_dir() / "release" / "tseitin_mass"
    OUT.mkdir(parents=True, exist_ok=True)
    cmd = [str(exe), "--profile", args.profile, "--out-dir", str(OUT)]
    if args.threads is not None:
        cmd.extend(["--threads", str(args.threads)])
    print(f"Running {' '.join(cmd)} ...", flush=True)
    r = subprocess.run(cmd, cwd=CRATE, env=env)
    if args.gpu_demo:
        print("OpenCL GPU demo...", flush=True)
        subprocess.run(
            [sys.executable, "-m", "backend.proof_complexity.gpu_width_opencl", "--demo", "--limit", "300"],
            cwd=ROOT,
        )
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
