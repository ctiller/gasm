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

/- REF: intel-sdm#vol=2;instr=XCHG;part=description -/
/-- XCHG r64, r64: Swaps the contents of two 64-bit general-purpose registers without affecting condition flags.

NOTE for future authors (`docs/MEMORY_MODEL.md` §§4–5.1, stage M2-X): this reg-reg form touches no memory and
carries no atomicity semantics — `memAccesses` is honestly `[]`. XCHG with a *memory* operand is
architecturally LOCK'd on x86 (implicitly atomic, with or without the prefix; intel-sdm XCHG
description). Memory forms land with M2-X and declare one `.atomicRmw` event under that model.
The standard-library `ParkedMutex32` Linux/futex baseline specifically requires a naturally aligned
32-bit memory form and practical 32-bit compare-exchange support; this is one preferred implementation
of the representation-independent mutex contract, not a universal mutex layout. 64-bit forms may be
added for independent ISA coverage or proved specialized implementations. Adding either outside
M2-X would create an unannotated atomic. -/
structure XchgR64R64 where
  dst : Reg64
  src : Reg64
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XCHG;part=operation -/
instance : X86_64Instruction XchgR64R64 where
  encode i :=
    let (dstCode, dstExt) := reg64Code i.dst
    let (srcCode, srcExt) := reg64Code i.src
    ByteArray.mk #[makeRex true srcExt false dstExt, 0x87, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.gprs i.dst
    let sVal := s.gprs i.src
    let s' := (s.setGpr64 i.dst sVal).setGpr64 i.src dVal
    { s' with rip := s.rip + 3 }
  toUops _ := [
    { mnemonic := "XCHG.alu1", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "XCHG.alu2", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"xchg {i.dst}, {i.src}"
  toLean i := s!"xchg_r64 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg64 i.dst && hwSafeReg64 i.src
  validationOracle i := if hwSafeReg64 i.dst && hwSafeReg64 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness (see canFuzzHardware/hwSafeReg64/hwSafeReg32's own doc comment); encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; the RDTSC/RDTSCP measurement harness and provisional calibration files exist, but no accepted calibration result is bound to this instance, and intel-sdm (the registered combined architecture SDM) does not publish cycle-latency data -- see docs/RDTSC_HARNESS.md section 8 and docs/X86_ISA_EXPANSION_PREREQUISITES.md P5"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs i.dst i.src rng
  roundtripCases :=
    (allReg64List.map (XchgR64R64.mk · .rax)) ++ (allReg64List.map (XchgR64R64.mk .rax ·)) ++
    (extendedReg64Pairs.map fun p => XchgR64R64.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XCHG;part=description -/
/-- XCHG r32, r32: Swaps the contents of two 32-bit registers, zero-extending both to 64 bits. -/
structure XchgR32R32 where
  dst : Reg32
  src : Reg32
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XCHG;part=operation -/
instance : X86_64Instruction XchgR32R32 where
  encode i :=
    let (dstCode, dstExt) := reg32Code i.dst
    let (srcCode, srcExt) := reg32Code i.src
    let rexPrefix := if dstExt || srcExt then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x87, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr32 i.dst
    let sVal := s.readGpr32 i.src
    let s' := (s.setGpr32 i.dst sVal).setGpr32 i.src dVal
    let len := (if (reg32Code i.dst).2 || (reg32Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "XCHG.alu1", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "XCHG.alu2", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"xchg {i.dst}, {i.src}"
  toLean i := s!"xchg_r32 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg32 i.dst && hwSafeReg32 i.src
  validationOracle i := if hwSafeReg32 i.dst && hwSafeReg32 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg32To64 i.dst) (reg32To64 i.src) rng
  roundtripCases :=
    (allReg32List.map (XchgR32R32.mk · .eax)) ++ (allReg32List.map (XchgR32R32.mk .eax ·)) ++
    (extendedReg32Pairs.map fun p => XchgR32R32.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XCHG;part=description -/
/-- XCHG r16, r16: Swaps the contents of two 16-bit registers, preserving upper 48 bits. -/
structure XchgR16R16 where
  dst : Reg16
  src : Reg16
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XCHG;part=operation -/
instance : X86_64Instruction XchgR16R16 where
  encode i :=
    let (dstCode, dstExt) := reg16Code i.dst
    let (srcCode, srcExt) := reg16Code i.src
    let rexPrefix := if dstExt || srcExt then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk (#[0x66] ++ rexPrefix ++ #[0x87, makeModRM 3 srcCode dstCode])
  step i s :=
    let dVal := s.readGpr16 i.dst
    let sVal := s.readGpr16 i.src
    let s' := (s.setGpr16 i.dst sVal).setGpr16 i.src dVal
    let len := 1 + (if (reg16Code i.dst).2 || (reg16Code i.src).2 then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "XCHG.alu1", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "XCHG.alu2", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"xchg {i.dst}, {i.src}"
  toLean i := s!"xchg_r16 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg16 i.dst && hwSafeReg16 i.src
  validationOracle i := if hwSafeReg16 i.dst && hwSafeReg16 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg16To64 i.dst) (reg16To64 i.src) rng
  roundtripCases :=
    (allReg16List.map (XchgR16R16.mk · .ax)) ++ (allReg16List.map (XchgR16R16.mk .ax ·)) ++
    (extendedReg16Pairs.map fun p => XchgR16R16.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=XCHG;part=description -/
/-- XCHG r8, r8: Swaps the contents of two 8-bit registers, preserving upper 56 bits. -/
structure XchgR8R8 where
  dst : Reg8
  src : Reg8
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=XCHG;part=operation -/
instance : X86_64Instruction XchgR8R8 where
  encode i :=
    let (dstCode, dstExt, dstMandatory) := reg8Code i.dst
    let (srcCode, srcExt, srcMandatory) := reg8Code i.src
    let rexNeeded := dstExt || srcExt || dstMandatory || srcMandatory
    let rexPrefix := if rexNeeded then #[makeRex false srcExt false dstExt] else #[]
    ByteArray.mk rexPrefix ++ ByteArray.mk #[0x86, makeModRM 3 srcCode dstCode]
  step i s :=
    let dVal := s.readGpr8 i.dst
    let sVal := s.readGpr8 i.src
    let s' := (s.setGpr8 i.dst sVal).setGpr8 i.src dVal
    let rexNeeded := (reg8Code i.dst).2.1 || (reg8Code i.src).2.1 || (reg8Code i.dst).2.2 || (reg8Code i.src).2.2
    let len := (if rexNeeded then 1 else 0) + 2
    { s' with rip := s.rip + len }
  toUops _ := [
    { mnemonic := "XCHG.alu1", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 },
    { mnemonic := "XCHG.alu2", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 1, reciprocalThroughput := 0.25 }
  ]
  toNASM i := s!"xchg {i.dst}, {i.src}"
  toLean i := s!"xchg_r8 .{i.dst} .{i.src}"
  canFuzzHardware i := hwSafeReg8 i.dst && hwSafeReg8 i.src
  validationOracle i := if hwSafeReg8 i.dst && hwSafeReg8 i.src then .silicon else .nasmEncoding "RSP/ESP operand unsafe for HardwareHarness; encoding is NASM-cross-checked instead"
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates i rng := generateStandardFuzzStatesFor2Regs (reg8To64 i.dst) (reg8To64 i.src) rng
  roundtripCases :=
    (allReg8List.map (XchgR8R8.mk · .al)) ++ (allReg8List.map (XchgR8R8.mk .al ·)) ++
    (extendedReg8Pairs.map fun p => XchgR8R8.mk p.1 p.2)
  memAccesses _ := []

/- REF: intel-sdm#vol=2;instr=NOP;part=description -/
/-- NOP: One-byte no-operation (0x90, alias of XCHG EAX, EAX / RAX, RAX without REX). Advances RIP by 1. -/
structure NopOp where
  deriving DecidableEq, Repr, Inhabited

/- REF: intel-sdm#vol=2;instr=NOP;part=operation -/
instance : X86_64Instruction NopOp where
  encode _ := ByteArray.mk #[0x90]
  step _ s := { s with rip := s.rip + 1 }
  toUops _ := [{ mnemonic := "NOP", uopClass := .intALU, eligiblePorts := [.p0, .p1, .p5, .p6], latencyCycles := 0, reciprocalThroughput := 0.25 }]
  toNASM _ := "nop"
  toLean _ := "nop_op"
  canFuzzHardware _ := true
  validationOracle _ := .silicon
  costProvenance _ := .modelInternalUnvalidated "toUops coefficients predate Law 14 and remain uncalibrated model values; see docs/RDTSC_HARNESS.md section 8"
  generateFuzzStates _ rng := generateStandardFuzzStatesFor1Reg .rax rng
  roundtripCases := [NopOp.mk]
  memAccesses _ := []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r64, r64 helper. -/
def xchg_r64 (dst src : Reg64) : AnyX86_64Instruction :=
  ⟨XchgR64R64.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r32, r32 helper. -/
def xchg_r32 (dst src : Reg32) : AnyX86_64Instruction :=
  ⟨XchgR32R32.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r16, r16 helper. -/
def xchg_r16 (dst src : Reg16) : AnyX86_64Instruction :=
  ⟨XchgR16R16.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- XCHG r8, r8 helper. -/
def xchg_r8 (dst src : Reg8) : AnyX86_64Instruction :=
  ⟨XchgR8R8.mk dst src⟩

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
/-- NOP helper. -/
def nop_op : AnyX86_64Instruction :=
  ⟨NopOp.mk⟩

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
def xchgDecodeRules : List DecodeRule := [
  { opcode := .one 0x87,
    has0x66 := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xchg_r16: missing ModR/M byte"
      | some m =>
        if m.mod == 3 then
          let dst := codeToReg16 m.rm ctx.rexB
          let src := codeToReg16 m.reg ctx.rexR
          .ok (xchg_r16 dst src, m.pos - ctx.startOffset)
        else .error "xchgTryDecode: unsupported memory form for 16-bit XCHG"
  },
  { opcode := .one 0x90,
    has0x66 := some false,
    builder := fun ctx =>
      if ctx.hasRex then .error "nop: REX prefix unsupported"
      else .ok (nop_op, ctx.opcodePos - ctx.startOffset)
  },
  { opcode := .one 0x86,
    has0x66 := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xchg_r8: missing ModR/M byte"
      | some m =>
        if m.mod == 3 then
          let dst := codeToReg8 m.rm ctx.rexB
          let src := codeToReg8 m.reg ctx.rexR
          let needsRex := ctx.rexR || ctx.rexB || (reg8Code src).2.2 || (reg8Code dst).2.2
          if ctx.hasRex != needsRex then
            .error "xchgTryDecode: noncanonical or legacy high-byte REX identity for 0x86 XCHG"
          else
            .ok (xchg_r8 dst src, m.pos - ctx.startOffset)
        else .error "xchgTryDecode: unsupported memory form for 8-bit XCHG"
  },
  { opcode := .one 0x87,
    has0x66 := some false,
    rexW := some true,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xchg_r64: missing ModR/M byte"
      | some m =>
        if m.mod == 3 then
          let dst := codeToReg64 m.rm ctx.rexB
          let src := codeToReg64 m.reg ctx.rexR
          .ok (xchg_r64 dst src, m.pos - ctx.startOffset)
        else .error "xchgTryDecode: unsupported memory form for 32/64-bit XCHG"
  },
  { opcode := .one 0x87,
    has0x66 := some false,
    rexW := some false,
    builder := fun ctx =>
      match ctx.modrm with
      | none => .error "xchg_r32: missing ModR/M byte"
      | some m =>
        if m.mod == 3 then
          let dst := codeToReg32 m.rm ctx.rexB
          let src := codeToReg32 m.reg ctx.rexR
          .ok (xchg_r32 dst src, m.pos - ctx.startOffset)
        else .error "xchgTryDecode: unsupported memory form for 32/64-bit XCHG"
  }
]

/- REF: docs/TARGETS/X86_64.md#5-stage-b-decoder-modularization -/
/-- Co-located decoder for the XCHG family, evaluating its declarative rules. -/
def xchgTryDecode (bytes : ByteArray) (offset : Nat) : Except String (AnyX86_64Instruction × Nat) :=
  tryDecodeWithRules xchgDecodeRules bytes offset

end Gasm.Targets.X86_64.Instructions
