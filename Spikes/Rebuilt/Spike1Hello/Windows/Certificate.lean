/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Spikes.Rebuilt.Spike1Hello.Windows.Witnesses

/-!
Private whole-artifact authority for the Spike 1 rebuild experiment. This is intentionally
stronger than an emission token: it fixes the emitted PE, quantifies safety and terminal refinement
over every admitted exact execution, retains the source progress theorem, and requires exact
machine witnesses for success, missing stdout, and short-write retry.
-/

namespace Spikes.Rebuilt.Spike1Hello.Windows.Certificate

open Spikes.Rebuilt.Spike1Hello
open Spikes.Rebuilt.Spike1Hello.RelationalExperiment
open Spikes.Rebuilt.Spike1Hello.Windows
open Spikes.Rebuilt.Spike1Hello.Windows.RelationalExecution
open Spikes.Rebuilt.Spike1Hello.Windows.Witnesses

structure VerifiedArtifact where
  artifact : Gasm.Targets.Windows.WindowsExecutable
  artifactExact : artifact = executable
  sourceProgress : VerifiedExperiment
  sourceProgressExact : sourceProgress = spike1VerifiedExperiment
  prefixSafety : ∀ {profile events after},
    Execution profile initial events after → after.logical.Safe
  terminalRefinement : ∀ {profile events after},
    Execution profile initial events after → after.terminalCause.isSome →
      ∃ observation, after.logical.block = .terminal observation ∧ Accepts observation
  progressTransfer : ∀ {profile events after},
    Execution profile initial events after → EligiblePlan (providerResponses events) →
      after.logical.IsTerminal
  fullWriteReachable : ∃ after,
    Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider (.accepted message.length)] ++
        List.replicate 10 .isa ++ [.exit 0]) after ∧ after.terminalCause.isSome
  noStdoutReachable : ∃ after,
    Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .noStdout] ++
        List.replicate 3 .isa ++ [.exit 1]) after ∧ after.terminalCause.isSome
  shortWriteRetries : ∃ before,
    Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider (.accepted shortCount)] ++
        List.replicate 14 .isa) before ∧
      before.machine.rip = (BoundarySite.writeFile.rip.get (boundary_sites_exist .writeFile)) ∧
      before.logical.remaining = message.drop shortCount

def verifiedArtifact : VerifiedArtifact where
  artifact := executable
  artifactExact := rfl
  sourceProgress := spike1VerifiedExperiment
  sourceProgressExact := rfl
  prefixSafety := fun execution => (execution.preservesAgreement initial_agrees).1
  terminalRefinement := terminal_execution_refines
  progressTransfer := eligible_execution_reaches_logical_terminal
  fullWriteReachable := full_write_execution
  noStdoutReachable := no_stdout_execution
  shortWriteRetries := short_write_retries

/-- Serialization is possible only after constructing the stronger private authority above. -/
def emitVerified (verified : VerifiedArtifact) : ByteArray :=
  verified.artifact.emit

theorem emitted_bytes_are_exact :
    emitVerified verifiedArtifact = executable.emit := by
  rfl

end Spikes.Rebuilt.Spike1Hello.Windows.Certificate
