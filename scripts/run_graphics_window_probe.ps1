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

# Nonnormative opt-in behavior probe. This script is not part of Lean's verified
# emission path and cannot discharge a model, ABI, callback-entry, or artifact theorem.
param(
    [int]$AutoCloseSeconds = 0
)

Add-Type -AssemblyName System.Windows.Forms
Add-Type -AssemblyName System.Drawing

$probeForm = New-Object System.Windows.Forms.Form
$probeForm.Text = "gasm graphics foundation - unverified input probe"
$probeForm.ClientSize = New-Object System.Drawing.Size(800, 500)
$probeForm.StartPosition = [System.Windows.Forms.FormStartPosition]::CenterScreen
$probeForm.KeyPreview = $true

$probeLabel = New-Object System.Windows.Forms.Label
$probeLabel.AutoSize = $false
$probeLabel.Dock = [System.Windows.Forms.DockStyle]::Fill
$probeLabel.TextAlign = [System.Drawing.ContentAlignment]::MiddleCenter
$probeLabel.Font = New-Object System.Drawing.Font("Consolas", 14)
$probeLabel.Text = "Move/click the mouse, type, or resize.`r`nPress Escape to close."
$probeForm.Controls.Add($probeLabel)

$writeProbeEvent = {
    param([string]$Message)
    $timestamp = [DateTimeOffset]::Now.ToString("HH:mm:ss.fff")
    Write-Host "[$timestamp] $Message"
    $probeLabel.Text = "$Message`r`n`r`nPress Escape to close."
}

$probeForm.Add_Shown({ & $writeProbeEvent "shown $($probeForm.ClientSize.Width)x$($probeForm.ClientSize.Height)" })
$probeForm.Add_Resize({ & $writeProbeEvent "resize $($probeForm.ClientSize.Width)x$($probeForm.ClientSize.Height)" })
$probeForm.Add_MouseMove({ param($sender, $eventArgs) & $writeProbeEvent "mouse move $($eventArgs.X),$($eventArgs.Y)" })
$probeForm.Add_MouseDown({ param($sender, $eventArgs) & $writeProbeEvent "mouse down $($eventArgs.Button)" })
$probeForm.Add_MouseUp({ param($sender, $eventArgs) & $writeProbeEvent "mouse up $($eventArgs.Button)" })
$probeForm.Add_MouseWheel({ param($sender, $eventArgs) & $writeProbeEvent "mouse wheel $($eventArgs.Delta)" })
$probeForm.Add_KeyDown({
    param($sender, $eventArgs)
    & $writeProbeEvent "key down $($eventArgs.KeyCode)"
    if ($eventArgs.KeyCode -eq [System.Windows.Forms.Keys]::Escape) {
        $probeForm.Close()
    }
})
$probeForm.Add_KeyUp({ param($sender, $eventArgs) & $writeProbeEvent "key up $($eventArgs.KeyCode)" })
$probeForm.Add_FormClosing({ & $writeProbeEvent "close requested" })
$probeForm.Add_FormClosed({ Write-Host "[probe] destroyed" })

$probeTimer = $null
if ($AutoCloseSeconds -gt 0) {
    $probeTimer = New-Object System.Windows.Forms.Timer
    $probeTimer.Interval = $AutoCloseSeconds * 1000
    $probeTimer.Add_Tick({
        $probeTimer.Stop()
        $probeForm.Close()
    })
    $probeTimer.Start()
}

Write-Host "[probe] NONNORMATIVE: native behavior evidence only; no verified authority"
[System.Windows.Forms.Application]::Run($probeForm)

if ($null -ne $probeTimer) {
    $probeTimer.Dispose()
}
$probeForm.Dispose()
