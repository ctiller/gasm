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
import Gasm.Core.Types
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base

namespace Gasm.Targets.X86_64.Instructions

open Gasm.Core
open Gasm.Targets.X86_64

/- REF: intel-sdm#vol=2;instr=OUT;part=description -/
/-- OUT imm8, AL instruction: output byte from AL to 8-bit immediate I/O port. -/
structure OutImm8Al where
  port : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OUT;part=operation -/
instance : X86_64Instruction OutImm8Al where
  encode i := ByteArray.mk #[0xE6, i.port]

  step _ s :=
    -- Pure model step: advances RIP by 2 bytes (port I/O intercepted by platform device model)
    { s with rip := s.rip + 2 }

  toUops _ := [
    { mnemonic := "OUT.port8", uopClass := .storeData, eligiblePorts := [.p2, .p3, .p4, .p7], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"out 0x{String.ofList (Nat.toDigits 16 i.port.toNat)}, al"
  toLean i := s!"out_imm8_al {formatHex8 i.port}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "OUT writes an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [OutImm8Al.mk 0x00, OutImm8Al.mk 0x80, OutImm8Al.mk 0xFF]

/- REF: intel-sdm#vol=2;instr=OUT;part=description -/
/-- OUT DX, AL instruction: output byte from AL to I/O port specified in DX. -/
structure OutDxAl where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OUT;part=operation -/
instance : X86_64Instruction OutDxAl where
  encode _ := ByteArray.mk #[0xEE]

  step _ s :=
    -- Pure model step: advances RIP by 1 byte (port I/O intercepted by platform device model)
    { s with rip := s.rip + 1 }

  toUops _ := [
    { mnemonic := "OUT.portDx", uopClass := .storeData, eligiblePorts := [.p2, .p3, .p4, .p7], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "out dx, al"
  toLean _ := "out_dx_al"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "OUT writes an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [OutDxAl.mk]

/- REF: intel-sdm#vol=2;instr=OUT;part=description -/
/-- OUT imm8, EAX instruction: output doubleword from EAX to 8-bit immediate I/O port. -/
structure OutImm8Eax where
  port : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OUT;part=operation -/
instance : X86_64Instruction OutImm8Eax where
  encode i := ByteArray.mk #[0xE7, i.port]

  step _ s :=
    -- Pure model step: advances RIP by 2 bytes
    { s with rip := s.rip + 2 }

  toUops _ := [
    { mnemonic := "OUT.portImm32", uopClass := .storeData, eligiblePorts := [.p2, .p3, .p4, .p7], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"out 0x{String.ofList (Nat.toDigits 16 i.port.toNat)}, eax"
  toLean i := s!"out_imm8_eax {formatHex8 i.port}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "OUT writes an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [OutImm8Eax.mk 0x00, OutImm8Eax.mk 0x80, OutImm8Eax.mk 0xFF]

/- REF: intel-sdm#vol=2;instr=OUT;part=description -/
/-- OUT DX, EAX instruction: output doubleword from EAX to I/O port specified in DX. -/
structure OutDxEax where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=OUT;part=operation -/
instance : X86_64Instruction OutDxEax where
  encode _ := ByteArray.mk #[0xEF]

  step _ s :=
    -- Pure model step: advances RIP by 1 byte
    { s with rip := s.rip + 1 }

  toUops _ := [
    { mnemonic := "OUT.portDx32", uopClass := .storeData, eligiblePorts := [.p2, .p3, .p4, .p7], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "out dx, eax"
  toLean _ := "out_dx_eax"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "OUT writes an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [OutDxEax.mk]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OUT imm8, AL helper. -/
def out_imm8_al (port : UInt8) : AnyX86_64Instruction :=
  ⟨OutImm8Al.mk port⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OUT DX, AL helper. -/
def out_dx_al : AnyX86_64Instruction :=
  ⟨OutDxAl.mk⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OUT imm8, EAX helper. -/
def out_imm8_eax (port : UInt8) : AnyX86_64Instruction :=
  ⟨OutImm8Eax.mk port⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- OUT DX, EAX helper. -/
def out_dx_eax : AnyX86_64Instruction :=
  ⟨OutDxEax.mk⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-design-only-not-implemented-by-this-change -/
/-- Co-located decoder for the OUT family: `0xE6` (OUT imm8, AL), `0xE7` (OUT imm8, EAX),
    `0xEE` (OUT DX, AL), `0xEF` (OUT DX, EAX). Errors for any other byte pattern. -/
def outTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, opOffset) =>
    if opcode == 0xE6 then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok port => .ok (out_imm8_al port, (opOffset + 1) - offset)
    else if opcode == 0xE7 then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok port => .ok (out_imm8_eax port, (opOffset + 1) - offset)
    else if opcode == 0xEE then
      .ok (out_dx_al, opOffset - offset)
    else if opcode == 0xEF then
      .ok (out_dx_eax, opOffset - offset)
    else
      .error s!"outTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not OUT"

end Gasm.Targets.X86_64.Instructions
