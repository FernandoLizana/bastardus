# Monitor `lake build PNPLab` / resume_pnplab_build.ps1 every N minutes.
#
# Usage (from repo root):
#   powershell -ExecutionPolicy Bypass -File scripts/monitor_pnplab_build.ps1
#   powershell -ExecutionPolicy Bypass -File scripts/monitor_pnplab_build.ps1 -Once
#   powershell -ExecutionPolicy Bypass -File scripts/monitor_pnplab_build.ps1 -IntervalMinutes 10
#
# Logs: lean/build-monitor.log
# State (progress deltas): lean/build-monitor.state.json

param(
    [int]$IntervalMinutes = 10,
    [switch]$Once
)

$ErrorActionPreference = "Continue"

$RepoRoot = Split-Path $PSScriptRoot -Parent
$LeanDir = Join-Path $RepoRoot "lean"
$ResumeLog = Join-Path $LeanDir "build-resume.log"
$ResumeState = Join-Path $LeanDir "build-resume.state.json"
$LockFile = Join-Path $LeanDir ".build-resume.lock"
$MonitorLog = Join-Path $LeanDir "build-monitor.log"
$MonitorState = Join-Path $LeanDir "build-monitor.state.json"
$PnplabOlean = Join-Path $LeanDir ".lake/build/lib/lean/PNPLab.olean"
$KeyOleans = @(
    "ParametricDischargePart2.olean",
    "ParametricDischargePart3.olean",
    "ParametricCombinatorialDischarge.olean"
)

function Write-MonitorLog([string]$Level, [string]$Message) {
    $line = "[$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')] [$Level] $Message"
    Add-Content -Path $MonitorLog -Value $line -Encoding utf8
    Write-Host $line
}

function Read-JsonFile([string]$Path) {
    if (-not (Test-Path $Path)) { return $null }
    try {
        return (Get-Content $Path -Raw -Encoding utf8 | ConvertFrom-Json)
    } catch {
        return $null
    }
}

function Get-OleanSnapshot {
    $snap = @{}
    foreach ($name in $KeyOleans) {
        $path = Join-Path $LeanDir ".lake/build/lib/lean/PNPLab/$name"
        if (Test-Path $path) {
            $item = Get-Item $path
            $snap[$name] = @{
                exists = $true
                mtime = $item.LastWriteTime.ToString("o")
            }
        } else {
            $snap[$name] = @{ exists = $false; mtime = $null }
        }
    }
    if (Test-Path $PnplabOlean) {
        $root = Get-Item $PnplabOlean
        $snap["PNPLab.olean"] = @{
            exists = $true
            mtime = $root.LastWriteTime.ToString("o")
        }
    } else {
        $snap["PNPLab.olean"] = @{ exists = $false; mtime = $null }
    }
    return $snap
}

function Test-ResumeLockAlive {
    if (-not (Test-Path $LockFile)) { return $false }
    try {
        $lockPid = [int](Get-Content $LockFile -Raw).Trim()
        return $null -ne (Get-Process -Id $lockPid -ErrorAction SilentlyContinue)
    } catch {
        return $false
    }
}

function Invoke-BuildCheck {
    $leanLake = @(Get-Process lean, lake, leanc -ErrorAction SilentlyContinue)
    $procCount = $leanLake.Count
    $topLean = $leanLake | Where-Object { $_.ProcessName -eq "lean" } |
        Sort-Object CPU -Descending | Select-Object -First 1

    $resume = Read-JsonFile $ResumeState
    $resumeStatus = if ($null -ne $resume -and $resume.status) { [string]$resume.status } else { "unknown" }
    $lockAlive = Test-ResumeLockAlive

    $logLen = if (Test-Path $ResumeLog) { (Get-Item $ResumeLog).Length } else { 0 }
    $logMtime = if (Test-Path $ResumeLog) { (Get-Item $ResumeLog).LastWriteTime.ToString("o") } else { $null }
    $oleanSnap = Get-OleanSnapshot

    $prev = Read-JsonFile $MonitorState
    $stalled = $false
    $progressNote = "first sample"

    if ($null -ne $prev) {
        $sameLog = ($prev.logLength -eq $logLen)
        $sameOlean = ($prev.oleanSnapshot.PSObject.Properties.Name.Count -gt 0) -and
            (($prev.oleanSnapshot | ConvertTo-Json -Compress) -eq ($oleanSnap | ConvertTo-Json -Compress))
        if ($procCount -gt 0 -and $sameLog -and $sameOlean) {
            $stalled = $true
            $progressNote = "no log/olean change since last check"
        } elseif (-not $sameLog -or -not $sameOlean) {
            $progressNote = "progress detected"
        } else {
            $progressNote = "idle between attempts"
        }
    }

    $verdict = "OK"
    $detail = @()

    if ($resumeStatus -eq "success") {
        $verdict = "SUCCESS"
        $detail += "build-resume.state=success"
    } elseif ($resumeStatus -match "fail|stopped") {
        if ($procCount -eq 0) {
            $verdict = "FAILED"
            $detail += "status=$resumeStatus, no lean/lake processes"
        } else {
            $verdict = "WARN"
            $detail += "status=$resumeStatus but processes still running"
        }
    } elseif ($procCount -eq 0 -and $resumeStatus -eq "running") {
        $verdict = "WARN"
        $detail += "state=running but 0 lean/lake processes (crashed?)"
    } elseif ($procCount -gt 0 -and -not $lockAlive) {
        $verdict = "WARN"
        $detail += "lean/lake active but resume lock missing/stale"
    } elseif ($stalled) {
        $verdict = "WARN"
        $detail += "possible stall (>10 min without log/olean change)"
    } else {
        $detail += "processes=$procCount lock=$lockAlive status=$resumeStatus"
    }

    $cpuNote = if ($null -ne $topLean) {
        "top_lean_cpu_s=$([math]::Round($topLean.CPU, 1))"
    } else {
        "top_lean=none"
    }

    $oleanLines = ($oleanSnap.GetEnumerator() | ForEach-Object {
        if ($_.Value.exists) { "$($_.Key)=$($_.Value.mtime)" } else { "$($_.Key)=missing" }
    }) -join "; "

    Write-MonitorLog $verdict (
        "$progressNote | $($detail -join '; ') | $cpuNote | $oleanLines"
    )

    @{
        updatedAt = (Get-Date).ToString("o")
        verdict = $verdict
        procCount = $procCount
        resumeStatus = $resumeStatus
        lockAlive = $lockAlive
        logLength = $logLen
        logMtime = $logMtime
        oleanSnapshot = $oleanSnap
        stalled = $stalled
    } | ConvertTo-Json -Depth 6 | Set-Content -Path $MonitorState -Encoding utf8

    return $verdict
}

# --- main ---
if (-not (Test-Path $LeanDir)) {
    Write-Error "lean/ not found at $LeanDir"
    exit 1
}

Write-MonitorLog "INFO" "========== monitor_pnplab_build start (interval=${IntervalMinutes}m, once=$Once) =========="

do {
    $result = Invoke-BuildCheck
    if ($result -eq "SUCCESS") {
        Write-MonitorLog "INFO" "Build SUCCESS detected; monitor exiting."
        exit 0
    }
    if ($Once) { break }
    Start-Sleep -Seconds ($IntervalMinutes * 60)
} while ($true)

Write-MonitorLog "INFO" "========== monitor_pnplab_build done (Once mode) =========="
