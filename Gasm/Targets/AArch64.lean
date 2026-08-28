/-
Copyright 2026 Google LLC

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

import Gasm.Targets.AArch64.Registers
import Gasm.Targets.AArch64.Addressing
import Gasm.Targets.AArch64.MemoryCell
import Gasm.Targets.AArch64.Machine
import Gasm.Targets.AArch64.Instructions
import Gasm.Targets.AArch64.Decoder
import Gasm.Targets.AArch64.Roundtrip
import Gasm.Targets.AArch64.RoundtripGate
import Gasm.Targets.AArch64.Semantics
import Gasm.Targets.AArch64.Uop
import Gasm.Targets.AArch64.Performance

namespace Gasm.Targets.AArch64

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Top-level umbrella alias for the AArch64 machine state. -/
abbrev Machine := AArch64MachineState

/- REF: docs/TARGETS/ARM64.md#machine-state -/
/-- Version string for the AArch64 target implementation. -/
def targetVersion : String := "0.1.0"

end Gasm.Targets.AArch64
