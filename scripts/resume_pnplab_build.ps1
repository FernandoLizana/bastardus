# Unsupervised, resumable `lake build PNPLab`.
# - Single instance (lock file)
# - Kills stray lean/lake before each attempt
# - Retries on failure; Lake reuses .olean cache between runs
# - Logs to lean/build-resume.log
#
# Usage (from repo root):
#   powershell -ExecutionPolicy Bypass -File scripts/resume_pnplab_build.ps1
#
# Options:
#   -MaxAttempts 0     infinite retries until green (default)
#   -MaxAttempts 5     stop after 5 failures
#   -RetryDelaySec 180 wait between attempts
#   -LeanThreads 2     lower memory pressure (default)

param(
    [int]$MaxAttempts = 0,
    [int]$RetryDelaySec = 120,
    [int]$LeanThreads = 2,
    [switch]$SkipCacheGet
)

$ErrorActionPreference = "Continue"

$RepoRoot = Split-Path $PSScriptRoot -Parent
$LeanDir = Join-Path $RepoRoot "lean"
$LogFile = Join-Path $LeanDir "build-resume.log"
$StateFile = Join-Path $LeanDir "build-resume.state.json"
$LockFile = Join-Path $LeanDir ".build-resume.lock"

function Write-Log([string]$Message) {
    $line = "[$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')] $Message"
    Add-Content -Path $LogFile -Value $line -Encoding utf8
    Write-Host $line
}

function Save-State([hashtable]$Data) {
    $Data | ConvertTo-Json | Set-Content -Path $StateFile -Encoding utf8
}

function Stop-LeanLake {
    $procs = @(Get-Process lean, lake -ErrorAction SilentlyContinue)
    if ($procs.Count -gt 0) {
        Write-Log "Stopping $($procs.Count) lean/lake process(es)..."
        $procs | Stop-Process -Force -ErrorAction SilentlyContinue
        Start-Sleep -Seconds 8
    }
}

function Test-LockStale {
    if (-not (Test-Path $LockFile)) { return $true }
    try {
        $pidText = Get-Content $LockFile -Raw
        $lockPid = [int]$pidText.Trim()
        $p = Get-Process -Id $lockPid -ErrorAction SilentlyContinue
        if ($null -eq $p) { return $true }
        return $false
    } catch {
        return $true
    }
}

function Acquire-Lock {
    if (-not (Test-LockStale)) {
        Write-Log "Another resume_pnplab_build instance is running (lock: $LockFile). Exit."
        exit 2
    }
    $PID | Set-Content -Path $LockFile -Encoding ascii -NoNewline
}

function Release-Lock {
    if (Test-Path $LockFile) { Remove-Item $LockFile -Force -ErrorAction SilentlyContinue }
}

function Invoke-CacheGet {
    if ($SkipCacheGet) { return }
    Push-Location $LeanDir
    try {
        Write-Log "lake exe cache get (repair Mathlib cache if needed)..."
        $out = lake exe cache get 2>&1
        $out | ForEach-Object { Write-Log "  $_" }
    } catch {
        Write-Log "cache get warning: $_"
    } finally {
        Pop-Location
    }
}

function Invoke-PNPLabBuild {
    Push-Location $LeanDir
    try {
        $env:LEAN_NUM_THREADS = "$LeanThreads"
        Write-Log "lake build PNPLab (LEAN_NUM_THREADS=$LeanThreads)..."
        $start = Get-Date
        $output = & lake build PNPLab 2>&1
        $code = $LASTEXITCODE
        foreach ($line in @($output)) { Write-Log "  $line" }
        $elapsed = ((Get-Date) - $start).TotalMinutes
        Write-Log "Build finished exit_code=$code elapsed_min=$([math]::Round($elapsed, 1))"
        return $code
    } finally {
        Pop-Location
    }
}

# --- main ---
if (-not (Test-Path $LeanDir)) {
    Write-Error "lean/ not found at $LeanDir"
    exit 1
}

Acquire-Lock
try {
    Write-Log "========== resume_pnplab_build start (pid=$PID) =========="
    $attempt = 0

    while ($true) {
        $attempt++
        if ($MaxAttempts -gt 0 -and $attempt -gt $MaxAttempts) {
            Write-Log "MaxAttempts ($MaxAttempts) reached. Giving up."
            Save-State @{
                lastAttempt = $attempt - 1
                lastExitCode = 1
                status = 'failed_max_attempts'
                updatedAt = (Get-Date).ToString('o')
            }
            exit 1
        }

        Write-Log "--- attempt $attempt ---"
        Save-State @{
            lastAttempt = $attempt
            status = 'running'
            updatedAt = (Get-Date).ToString('o')
        }

        Stop-LeanLake
        if ($attempt -eq 1 -or $attempt % 3 -eq 0) {
            Invoke-CacheGet
        }

        $exitCode = Invoke-PNPLabBuild

        if ($exitCode -eq 0) {
            $olean = Join-Path $LeanDir ".lake/build/lib/lean/PNPLab.olean"
            $oleanTime = if (Test-Path $olean) { (Get-Item $olean).LastWriteTime.ToString('o') } else { 'missing' }
            Write-Log "SUCCESS - PNPLab.olean LastWriteTime=$oleanTime"
            Save-State @{
                lastAttempt = $attempt
                lastExitCode = 0
                status = 'success'
                pnplabOlean = $oleanTime
                updatedAt = (Get-Date).ToString('o')
            }
            Write-Log "========== resume_pnplab_build done =========="
            exit 0
        }

        Write-Log "Build failed (exit $exitCode). Retry in ${RetryDelaySec}s..."
        Save-State @{
            lastAttempt = $attempt
            lastExitCode = $exitCode
            status = 'retry_wait'
            updatedAt = (Get-Date).ToString('o')
        }
        Start-Sleep -Seconds $RetryDelaySec
    }
} finally {
    Release-Lock
}
