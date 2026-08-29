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
  [double]$AutoCloseSeconds = 0
)

$ErrorActionPreference = 'Stop'
$workspaceRoot = Split-Path -Parent $PSScriptRoot
$project = Join-Path $workspaceRoot 'Spikes\GraphicsFoundation\NativeCubeProbe\NativeCubeProbe.csproj'

Write-Host '[probe] NONNORMATIVE: restores third-party packages and runs a managed Vulkan adapter.'
Write-Host '[probe] It cannot discharge SPIR-V, Vulkan, Win32 ABI, artifact, or VerifiedProgram obligations.'

$arguments = @('run', '--project', $project, '--configuration', 'Release', '--')
if ($AutoCloseSeconds -gt 0) {
  $arguments += @('--auto-close-seconds', $AutoCloseSeconds.ToString([Globalization.CultureInfo]::InvariantCulture))
}

& dotnet @arguments
exit $LASTEXITCODE
