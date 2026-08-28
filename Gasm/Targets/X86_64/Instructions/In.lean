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

/- REF: intel-sdm#vol=2;instr=IN;part=description -/
/-- IN AL, imm8 instruction: input byte from 8-bit immediate I/O port into AL. -/
structure InAlImm8 where
  port : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IN;part=operation -/
instance : X86_64Instruction InAlImm8 where
  encode i := ByteArray.mk #[0xE4, i.port]

  step _ s :=
    -- Pure model step: advances RIP by 2 bytes (port I/O intercepted by platform device model)
    { s with rip := s.rip + 2 }

  toUops _ := [
    { mnemonic := "IN.port8", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"in al, 0x{String.ofList (Nat.toDigits 16 i.port.toNat)}"
  toLean i := s!"in_al_imm8 {formatHex8 i.port}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "IN reads an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [InAlImm8.mk 0x00, InAlImm8.mk 0x80, InAlImm8.mk 0xFF]

/- REF: intel-sdm#vol=2;instr=IN;part=description -/
/-- IN AL, DX instruction: input byte from I/O port specified in DX into AL. -/
structure InAlDx where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IN;part=operation -/
instance : X86_64Instruction InAlDx where
  encode _ := ByteArray.mk #[0xEC]

  step _ s :=
    -- Pure model step: advances RIP by 1 byte (port I/O intercepted by platform device model)
    { s with rip := s.rip + 1 }

  toUops _ := [
    { mnemonic := "IN.portDx", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "in al, dx"
  toLean _ := "in_al_dx"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "IN reads an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [InAlDx.mk]

/- REF: intel-sdm#vol=2;instr=IN;part=description -/
/-- IN EAX, imm8 instruction: input doubleword from 8-bit immediate I/O port into EAX. -/
structure InEaxImm8 where
  port : UInt8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IN;part=operation -/
instance : X86_64Instruction InEaxImm8 where
  encode i := ByteArray.mk #[0xE5, i.port]

  step _ s :=
    -- Pure model step: advances RIP by 2 bytes
    { s with rip := s.rip + 2 }

  toUops _ := [
    { mnemonic := "IN.portImm32", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM i := s!"in eax, 0x{String.ofList (Nat.toDigits 16 i.port.toNat)}"
  toLean i := s!"in_eax_imm8 {formatHex8 i.port}"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "IN reads an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [InEaxImm8.mk 0x00, InEaxImm8.mk 0x80, InEaxImm8.mk 0xFF]

/- REF: intel-sdm#vol=2;instr=IN;part=description -/
/-- IN EAX, DX instruction: input doubleword from I/O port specified in DX into EAX. -/
structure InEaxDx where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=IN;part=operation -/
instance : X86_64Instruction InEaxDx where
  encode _ := ByteArray.mk #[0xED]

  step _ s :=
    -- Pure model step: advances RIP by 1 byte
    { s with rip := s.rip + 1 }

  toUops _ := [
    { mnemonic := "IN.portDx32", uopClass := .load, eligiblePorts := [.p2, .p3], latencyCycles := 1, reciprocalThroughput := 0.5 }
  ]
  toNASM _ := "in eax, dx"
  toLean _ := "in_eax_dx"
  canFuzzHardware _ := false
  validationOracle _ := .nasmEncoding "IN reads an I/O port and faults (#GP) under the harness's usermode host process; no privileged execution context is available -- encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and are uncalibrated inline literals; no calibration artifact exists yet (F1 RDTSC harness, docs/tasks/F1-rdtsc-harness.md, status ready/unbuilt) and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates _ rng := ([], rng)
  roundtripCases := [InEaxDx.mk]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IN AL, imm8 helper. -/
def in_al_imm8 (port : UInt8) : AnyX86_64Instruction :=
  ⟨InAlImm8.mk port⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IN AL, DX helper. -/
def in_al_dx : AnyX86_64Instruction :=
  ⟨InAlDx.mk⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IN EAX, imm8 helper. -/
def in_eax_imm8 (port : UInt8) : AnyX86_64Instruction :=
  ⟨InEaxImm8.mk port⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- IN EAX, DX helper. -/
def in_eax_dx : AnyX86_64Instruction :=
  ⟨InEaxDx.mk⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the IN family: `0xE4` (IN AL, imm8), `0xE5` (IN EAX, imm8), `0xEC`
    (IN AL, DX), `0xED` (IN EAX, DX). Errors for any other byte pattern. -/
def inTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  -- NOTE: nested `match`, not `do` — see `addTryDecode`'s comment for why.
  match parseRexAndOpcode bytes offset with
  | .error e => .error e
  | .ok (_, _, _, _, _, opcode, opOffset) =>
    if opcode == 0xE4 then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok port => .ok (in_al_imm8 port, (opOffset + 1) - offset)
    else if opcode == 0xE5 then
      match readUInt8 bytes opOffset with
      | .error e => .error e
      | .ok port => .ok (in_eax_imm8 port, (opOffset + 1) - offset)
    else if opcode == 0xEC then
      .ok (in_al_dx, opOffset - offset)
    else if opcode == 0xED then
      .ok (in_eax_dx, opOffset - offset)
    else
      .error s!"inTryDecode: opcode 0x{String.ofList (Nat.toDigits 16 opcode.toNat)} is not IN"

end Gasm.Targets.X86_64.Instructions
