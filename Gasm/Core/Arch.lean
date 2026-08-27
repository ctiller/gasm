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

import Lean

namespace Gasm.Core

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
/-- Architecture-specific typeclass defining native machine state representation, word width, open instruction AST, and pure operational stepping. -/
class TargetArch (Arch : Type) where
  wordWidth    : Nat
  MachineState : Type
  Instruction  : Type 1
  stepPure     : Instruction → MachineState → MachineState

/- REF: docs/TARGETS/TARGET_MODEL.md#1-vertical-slice-target-structure -/
/-- Architecture-specific typeclass defining binary decoding and stream disassembly. -/
class DisassemblableArch (Arch : Type) [TargetArch Arch] where
  decodeInstr : ByteArray → Nat → Except String (TargetArch.Instruction Arch × Nat)
  disassemble : ByteArray → Except String (List (TargetArch.Instruction Arch))

end Gasm.Core
