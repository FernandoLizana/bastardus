#!/usr/bin/env python3
"""Orchestrate portable_cpu jobs with dependencies, locks, logs, and resume.

Usage (from repo root):
  python portable_cpu/lib/job_runner.py status
  python portable_cpu/lib/job_runner.py run [--resume] [--job ID] [--max-parallel N]
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
PORTABLE = ROOT / "portable_cpu"
MANIFEST = PORTABLE / "jobs.manifest.json"
STATE_DIR = PORTABLE / "state"
LOG_DIR = PORTABLE / "logs"
RESULTS_DIR = PORTABLE / "results"
ORCH_STATE = STATE_DIR / "orchestrator.json"
LOCK_FILE = STATE_DIR / ".orchestrator.lock"


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def load_manifest() -> dict[str, Any]:
    manifest_path = Path(os.environ.get("PORTABLE_CPU_MANIFEST", MANIFEST))
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    extra = os.environ.get("PORTABLE_CPU_EXTRA_MANIFEST")
    if extra:
        extra_path = Path(extra)
        if not extra_path.is_absolute():
            extra_path = ROOT / extra_path
        extra_data = json.loads(extra_path.read_text(encoding="utf-8"))
        seen = {j["id"] for j in data["jobs"]}
        for job in extra_data.get("jobs", []):
            if job["id"] not in seen:
                data["jobs"].append(job)
                seen.add(job["id"])
    return data


def load_orch_state() -> dict[str, Any]:
    if ORCH_STATE.exists():
        return json.loads(ORCH_STATE.read_text(encoding="utf-8"))
    return {"jobs": {}, "started_at": None, "updated_at": None}


def save_orch_state(state: dict[str, Any]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    state["updated_at"] = utc_now()
    ORCH_STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")


def job_state_path(job_id: str) -> Path:
    return STATE_DIR / "jobs" / f"{job_id}.json"


def load_job_state(job_id: str) -> dict[str, Any]:
    p = job_state_path(job_id)
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return {"status": "pending", "attempts": 0, "last_exit": None, "last_error": None}


def save_job_state(job_id: str, data: dict[str, Any]) -> None:
    p = job_state_path(job_id)
    p.parent.mkdir(parents=True, exist_ok=True)
    data["updated_at"] = utc_now()
    p.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


@dataclass
class Job:
    id: str
    title: str
    command: list[str]
    depends_on: list[str] = field(default_factory=list)
    parallel_group: str = "default"
    checkpoint: bool = False
    category: str = "misc"
    estimated_cpu_hours: float = 0.0


def parse_jobs(manifest: dict[str, Any]) -> dict[str, Job]:
    jobs: dict[str, Job] = {}
    for raw in manifest["jobs"]:
        jobs[raw["id"]] = Job(
            id=raw["id"],
            title=raw.get("title", raw["id"]),
            command=raw["command"],
            depends_on=list(raw.get("depends_on", [])),
            parallel_group=raw.get("parallel_group", "default"),
            checkpoint=bool(raw.get("checkpoint", False)),
            category=raw.get("category", "misc"),
            estimated_cpu_hours=float(raw.get("estimated_cpu_hours", 0)),
        )
    return jobs


def deps_satisfied(job: Job, orch: dict[str, Any]) -> bool:
    for dep in job.depends_on:
        st = orch["jobs"].get(dep, {}).get("status") or load_job_state(dep).get("status")
        if st != "success":
            return False
    return True


def acquire_lock() -> bool:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    if LOCK_FILE.exists():
        try:
            pid = int(LOCK_FILE.read_text().strip())
            os.kill(pid, 0)
            return False
        except (OSError, ValueError):
            LOCK_FILE.unlink(missing_ok=True)
    LOCK_FILE.write_text(str(os.getpid()), encoding="ascii")
    return True


def release_lock() -> None:
    LOCK_FILE.unlink(missing_ok=True)


@dataclass
class ActiveJob:
    proc: subprocess.Popen[Any]
    job: Job
    log: Any
    log_path: Path


def job_env() -> dict[str, str]:
    env = os.environ.copy()
    env["PORTABLE_CPU_ROOT"] = str(PORTABLE)
    env["PYTHONPATH"] = os.pathsep.join([str(ROOT), str(ROOT / "scripts")])
    return env


def start_job(job: Job, log_path: Path) -> ActiveJob:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log = log_path.open("a", encoding="utf-8")
    log.write(f"\n=== {utc_now()} START {job.id} ===\n")
    log.write(f"cmd: {' '.join(job.command)}\n")
    log.flush()
    proc = subprocess.Popen(
        job.command,
        cwd=str(ROOT),
        env=job_env(),
        stdout=log,
        stderr=subprocess.STDOUT,
    )
    return ActiveJob(proc=proc, job=job, log=log, log_path=log_path)


def finalize_job(jid: str, active: ActiveJob, orch: dict[str, Any]) -> tuple[int, bool]:
    code = active.proc.wait()
    active.log.write(f"\n=== {utc_now()} END {jid} exit={code} ===\n")
    active.log.close()

    st = load_job_state(jid)
    st["last_exit"] = code
    st["finished_at"] = utc_now()
    failed = code != 0
    if failed:
        st["status"] = "failed"
        st["last_error"] = f"exit code {code}"
        orch["jobs"][jid] = {"status": "failed", "exit": code}
    else:
        st["status"] = "success"
        orch["jobs"][jid] = {"status": "success", "exit": 0}
    save_job_state(jid, st)
    save_orch_state(orch)
    return code, failed


def status_table(jobs: dict[str, Job]) -> None:
    orch = load_orch_state()
    print(f"{'ID':<36} {'STATUS':<10} {'ATT':<4} {'DEPS_OK':<8} TITLE")
    print("-" * 100)
    for jid, job in jobs.items():
        st = load_job_state(jid)
        status = st.get("status", "pending")
        att = st.get("attempts", 0)
        ok = "yes" if deps_satisfied(job, orch) else "no"
        print(f"{jid:<36} {status:<10} {att:<4} {ok:<8} {job.title[:40]}")


def run_jobs(
    jobs: dict[str, Job],
    *,
    resume: bool,
    only_job: str | None,
    max_parallel: int,
) -> int:
    if not acquire_lock():
        print("Another orchestrator is running (lock file). Exit.", file=sys.stderr)
        return 2

    try:
        orch = load_orch_state()
        if orch.get("started_at") is None:
            orch["started_at"] = utc_now()
        orch.setdefault("jobs", {})

        if only_job:
            todo = [only_job] if only_job in jobs else []
            if not todo:
                print(f"Unknown job: {only_job}", file=sys.stderr)
                return 1
        else:
            todo = list(jobs.keys())

        active: dict[str, ActiveJob] = {}
        failures = 0
        only_exit: int | None = None

        for jid in todo:
            st = load_job_state(jid)
            if st.get("status") == "running":
                st["status"] = "pending"
                st["last_error"] = "stale running state reset"
                save_job_state(jid, st)

        def running_groups() -> set[str]:
            return {active[j].job.parallel_group for j in active}

        def eligible_pending() -> list[str]:
            pending: list[str] = []
            groups = running_groups()
            for jid in todo:
                if jid in active:
                    continue
                job = jobs[jid]
                st = load_job_state(jid)
                status = st.get("status", "pending")
                if status == "success":
                    orch["jobs"][jid] = {"status": "success"}
                    continue
                if not deps_satisfied(job, orch):
                    continue
                if job.parallel_group in groups:
                    continue
                pending.append(jid)
            return pending

        while True:
            finished: list[str] = []
            for jid, aj in active.items():
                code = aj.proc.poll()
                if code is None:
                    continue
                finished.append(jid)
                exit_code, failed = finalize_job(jid, aj, orch)
                if failed:
                    failures += 1
                if only_job:
                    only_exit = exit_code

            for jid in finished:
                del active[jid]

            if only_job and only_exit is not None and not active:
                return only_exit

            pending = eligible_pending()
            if not pending and not active:
                break

            for jid in pending:
                if len(active) >= max_parallel:
                    break
                job = jobs[jid]
                if job.parallel_group in running_groups():
                    continue
                log_path = LOG_DIR / f"{jid}.log"
                st = load_job_state(jid)
                st["status"] = "running"
                st["attempts"] = int(st.get("attempts", 0)) + 1
                st["started_at"] = utc_now()
                save_job_state(jid, st)
                orch["jobs"][jid] = {"status": "running"}
                save_orch_state(orch)
                active[jid] = start_job(job, log_path)
                print(f"[run] {jid} (attempt {st['attempts']}, active={len(active)})")

            time.sleep(1 if active else 2)

        return 1 if failures else 0
    finally:
        release_lock()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status", help="Show job statuses")
    run_p = sub.add_parser("run", help="Run pending jobs")
    run_p.add_argument("--resume", action="store_true", help="Skip already-successful jobs")
    run_p.add_argument("--job", dest="only_job", default=None, help="Run single job id")
    run_p.add_argument(
        "--max-parallel",
        type=int,
        default=int(os.environ.get("PORTABLE_CPU_JOBS", max(1, (os.cpu_count() or 4) - 1))),
    )
    args = parser.parse_args()

    manifest = load_manifest()
    jobs = parse_jobs(manifest)
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    if args.cmd == "status":
        status_table(jobs)
        return 0
    return run_jobs(
        jobs,
        resume=args.resume,
        only_job=args.only_job,
        max_parallel=args.max_parallel,
    )


if __name__ == "__main__":
    raise SystemExit(main())
