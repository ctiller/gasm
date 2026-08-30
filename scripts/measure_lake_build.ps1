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

    [string] $Executable = 'lake',

    [int] $SampleMilliseconds = 500
)

$ErrorActionPreference = 'Stop'

$measuredExecutable = (Get-Command $Executable).Source
$python = (Get-Command python).Source
$measurementScript = Join-Path $PSScriptRoot 'measure_process_tree.py'
$measurementArgs = @(
    $measurementScript,
    '--sample-ms',
    $SampleMilliseconds,
    '--',
    $measuredExecutable
) + $LakeArgs

# The Python sampler follows only this child tree. The previous implementation enumerated every
# Win32_Process through CIM every 500ms and itself failed with OutOfMemoryException during a host
# pressure incident. Keep this PowerShell entry point for compatibility, but delegate immediately.
& $python @measurementArgs
exit $LASTEXITCODE
