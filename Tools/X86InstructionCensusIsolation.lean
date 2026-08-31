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

import Gasm

/-!
Compiled environment-isolation audit for the hostile x86 census controls.

This root imports the actual production `Gasm` umbrella and then validates its complete compiled
instance environment.  If the hostile control reaches that umbrella through any direct or
transitive import—including a route outside the `Gasm/` source tree—the extra normalized wrapper
instance makes this module fail.  The hostile control itself remains a separate default target.
-/

open Lean
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.InstructionCensus

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
run_cmd do
  let env ← Lean.getEnv
  Lean.Elab.Command.liftTermElabM do
    let candidates ← classCandidates env ``X86_64Instruction
    validateCanonicalWrapper env candidates

