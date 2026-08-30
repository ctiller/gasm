# Copyright 2026 Craig Tiller
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

param(
    [Parameter(Mandatory = $true)]
    [string[]] $LakeArgs,

    [int] $SampleMilliseconds = 500
)

$ErrorActionPreference = 'Stop'

$lake = (Get-Command lake).Source
$stdoutPath = [System.IO.Path]::GetTempFileName()
$stderrPath = [System.IO.Path]::GetTempFileName()

try {
    $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()
    $process = Start-Process `
        -FilePath $lake `
        -ArgumentList $LakeArgs `
        -WorkingDirectory (Get-Location).Path `
        -WindowStyle Hidden `
        -PassThru `
        -RedirectStandardOutput $stdoutPath `
        -RedirectStandardError $stderrPath

    $peakBytes = 0L
    while (-not $process.HasExited) {
        $allProcesses = Get-CimInstance Win32_Process
        $descendantIds = [System.Collections.Generic.HashSet[int]]::new()
        [void] $descendantIds.Add($process.Id)

        $changed = $true
        while ($changed) {
            $changed = $false
            foreach ($candidate in $allProcesses) {
                if ($descendantIds.Contains([int] $candidate.ParentProcessId) -and
                    -not $descendantIds.Contains([int] $candidate.ProcessId)) {
                    [void] $descendantIds.Add([int] $candidate.ProcessId)
                    $changed = $true
                }
            }
        }

        $sampleBytes = 0L
        foreach ($processId in $descendantIds) {
            $sample = Get-Process -Id $processId -ErrorAction SilentlyContinue
            if ($sample) {
                $sampleBytes += $sample.WorkingSet64
            }
        }
        if ($sampleBytes -gt $peakBytes) {
            $peakBytes = $sampleBytes
        }

        Start-Sleep -Milliseconds $SampleMilliseconds
        $process.Refresh()
    }
    $stopwatch.Stop()

    $stdout = Get-Content -Raw $stdoutPath
    $stderr = Get-Content -Raw $stderrPath
    $combined = $stdout + $stderr
    Write-Output $combined

    $builtJobs = ([regex]::Matches(
        $combined,
        '(?m)^(?:✔|⚠) \[[0-9]+/[0-9]+\] Built '
    )).Count
    Write-Output ('MEASURE seconds={0:N3} peak_mib={1:N1} built_jobs={2} sample_ms={3} exit={4}' -f `
        $stopwatch.Elapsed.TotalSeconds,
        ($peakBytes / 1MB),
        $builtJobs,
        $SampleMilliseconds,
        $process.ExitCode)

    exit $process.ExitCode
}
finally {
    Remove-Item -LiteralPath $stdoutPath, $stderrPath -Force -ErrorAction SilentlyContinue
}
