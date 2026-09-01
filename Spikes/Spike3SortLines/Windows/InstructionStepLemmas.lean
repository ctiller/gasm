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
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.And
import Gasm.Targets.X86_64.Instructions.Cmp
import Gasm.Targets.X86_64.Instructions.Jcc
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret

/-!
# Per-instruction `step` unfolding lemmas for Spike 3's empty-stdin trace

Mirrors `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean` (PA15) Part 1: one `rfl`-provable
equation per instruction shape used, restating `X86_64Instruction.step` as an explicit
`{ s with ... }` record so `rip`/`faulted`/`memory`/`gprs` facts about the *next* state can be
derived by `rw`-ing with the lemma and then substituting known field values of the *previous*
(possibly opaque, `generalize`-d) state -- never by asking `rfl`/`decide` to reduce straight
through an unexpanded `X86_64Instruction.step (smart_constructor ...) s` application, which does
not expose `s.rip` etc. syntactically to a plain `rw`. Restated here rather than imported from
PA15's file, per that file's own stated convention (a spike stays self-contained rather than
depending on an unrelated spike's pathfinder module). `CallRel32`/`CallRipRel`'s lemmas are new
(PA15's routine never called a subroutine or an intercepted import mid-body); the rest are
present, in the same shape, in PA15/PA1 precedent.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_sub_rsp (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (sub_rsp imm) s =
      { (s.setGpr64 .rsp (s.rsp - signExtend8To64 imm)).setFlagsSub64 s.rsp (signExtend8To64 imm) with
        rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_r32 (dst : Reg32) (imm : UInt32) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_r32 dst imm) s =
      { s.setGpr32 dst imm with rip := s.rip + (if (reg32Code dst).2 then 6 else 5) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_r64 dst src) s =
      { s.setGpr64 dst (s.gprs src) with rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_xor_r32 (dst src : Reg32) (s : X86_64MachineState) :
    X86_64Instruction.step (xor_r32 dst src) s =
      { (s.setGpr32 dst
            ((s.gprs (reg32To64 dst)).toUInt32 ^^^ (s.gprs (reg32To64 src)).toUInt32)).setFlagsLogic
          32 (((s.gprs (reg32To64 dst)).toUInt32 ^^^ (s.gprs (reg32To64 src)).toUInt32).toUInt64) with
        rip := s.rip + (if (reg32Code dst).2 || (reg32Code src).2 then 3 else 2) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_mem64_disp_imm (basePtr : Reg64) (disp : UInt8) (imm : UInt32) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_mem64_disp_imm basePtr disp imm) s =
      { s.write64 (s.gprs basePtr + signExtend8To64 disp) (signExtendUInt32To64 imm) with
        rip := s.rip +
          (7 + (if (reg64Code basePtr).1 == 4 then 1 else 0) +
            (if disp != 0 || (reg64Code basePtr).1 == 5 then 1 else 0)) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_mem64_disp (basePtr : Reg64) (disp : UInt8) (srcReg : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_mem64_disp basePtr disp srcReg) s =
      { s.write64 (s.gprs basePtr + signExtend8To64 disp) (s.gprs srcReg) with
        rip := s.rip +
          (3 + (if (reg64Code basePtr).1 == 4 then 1 else 0) +
            (if disp != 0 || (reg64Code basePtr).1 == 5 then 1 else 0)) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_reg64_mem64_disp (dstReg basePtr : Reg64) (disp : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_reg64_mem64_disp dstReg basePtr disp) s =
      { s.setGpr64 dstReg (s.read64 (s.gprs basePtr + signExtend8To64 disp)) with
        rip := s.rip +
          (3 + (if (reg64Code basePtr).1 == 4 then 1 else 0) +
            (if disp != 0 || (reg64Code basePtr).1 == 5 then 1 else 0)) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
-- MH1 (docs/MEMORY_HOOK.md): the raw `memory : Address -> Byte` field is sealed behind
-- X86_64Memory; `s.memory a` no longer type-checks. `step_mov_r32_rsp`/`step_mov_rsp64` are
-- restated against the width-indexed hook API the corresponding `step` definitions
-- (`Gasm/Targets/X86_64/Instructions/Mov.lean`'s `MovReg32Mem32Disp`/`MovRspDispImm64`) were
-- themselves migrated onto, so both remain `rfl` (MovRspDispImm64's single `write64` call of the
-- pre-sign-extended value is byte-identical to the old 8-byte inline ladder this theorem used to
-- assert -- see that instance's own comment).
theorem step_mov_r32_rsp (dstReg : Reg32) (disp : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_r32_rsp dstReg disp) s =
      { s.setGpr32 dstReg (s.read32 (s.rsp + signExtend8To64 disp)).toUInt32 with
        rip := s.rip +
          (movReg32Mem32DispEncodedLength ⟨dstReg, .rsp, disp⟩).toUInt64 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_mov_rsp64 (disp : UInt8) (imm : UInt32) (s : X86_64MachineState) :
    X86_64Instruction.step (mov_rsp64 disp imm) s =
      { s.write64 (s.rsp + signExtend8To64 disp) (signExtendUInt32To64 imm) with
        rip := s.rip + (if disp == 0 then 8 else 9) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_lea_rsp (dst : Reg64) (disp : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (lea_rsp dst disp) s =
      { s.setGpr64 dst (s.rsp + signExtend8To64 disp) with
        rip := s.rip + (if disp == 0 then 4 else 5) } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_add_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (add_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst + signExtend8To64 imm)).setFlagsAdd64 (s.gprs dst)
          (signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_add_r64_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (add_r64 dst src) s =
      { (s.setGpr64 dst (s.gprs dst + s.gprs src)).setFlagsAdd64 (s.gprs dst) (s.gprs src) with
        rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_and_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (and_r64_imm8 dst imm) s =
      { (s.setGpr64 dst (s.gprs dst &&& signExtend8To64 imm)).setFlagsLogic64
          (s.gprs dst &&& signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_cmp_r64_imm8 (dst : Reg64) (imm : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm8 dst imm) s =
      { s.setFlagsCmp64 (s.gprs dst) (signExtend8To64 imm) with rip := s.rip + 4 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_cmp_r64 (dst src : Reg64) (s : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64 dst src) s =
      { s.setFlagsCmp64 (s.gprs dst) (s.gprs src) with rip := s.rip + 3 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_jne_rel8 (disp : UInt8) (s : X86_64MachineState) :
    X86_64Instruction.step (jne_rel8 disp) s =
      { s with rip := if !s.zf then s.rip + 2 + signExtend8To64 disp else s.rip + 2 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_je_rel32 (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (je_rel32 disp) s =
      { s with rip := if s.zf then s.rip + 6 + signExtend32To64 disp else s.rip + 6 } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
theorem step_ret (s : X86_64MachineState) :
    X86_64Instruction.step ret_op s =
      { s.setGpr64 .rsp (s.rsp + 8) with rip := s.read64 s.rsp } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `CallRel32`'s step: a *direct*, same-program subroutine call (`smol_malloc`/`smol_free`, both
    inlined into `spike3Instructions` -- `Spikes/Spike3SortLines/Windows/Program.lean:519-526`).
    Kept generic in `disp` (a `rfl` fact, not needing its concrete numeral): the caller determines
    `disp` from a `instructionAtRip ... = some (call_rel32 disp)` fetch fact whose witness Lean's
    elaborator resolves by unification, so the linker's exact displacement is never hand-computed
    or written out. -/
theorem step_call_rel32 (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (call_rel32 disp) s =
      { (s.push64 (s.rip + 5)) with rip := s.rip + 5 + signExtend32To64 disp } := rfl

/- REF: docs/PATHFINDER_CRC32.md -/
/-- `CallRipRel`'s step: an *indirect* call through `[rip+disp]`, used for every Win32 import
    (`call_import`, lowered by `Assembler.assembleProgram` to `call_rip`,
    `Gasm/Targets/X86_64/Assembler.lean:375-379`). The pushed return address is the real
    `s.rip + 6`; the landing `rip` is whatever 8 bytes sit at the resolved IAT slot (a
    self-referential address by construction, per `Win32API.lean`'s `loadMemory`/`findIatIndex`)
    -- kept as `s.read64 (...)`, not hand-evaluated, since that fact is what
    `interceptCall`/`findIatIndex` itself needs to recognize the slot. -/
theorem step_call_rip (disp : Int32) (s : X86_64MachineState) :
    X86_64Instruction.step (call_rip disp) s =
      { (s.push64 (s.rip + 6)) with rip := s.read64 (s.rip + 6 + signExtend32To64 disp) } := rfl

end Spikes.Spike3SortLines.Windows
