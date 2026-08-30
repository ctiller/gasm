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

import Spikes.Spike3SortLines.NativeExecutionRefinement
import Spikes.Spike3SortLines.Linux.LinkCertificate

/-!
The first successful native allocation in the Linux artifact.

This module proves the emitted path, including every unsigned guard, all four
header writes, and the hardware `ret`.  The public certificate deliberately
hides the intermediate register states; consumers receive only the persistent
allocator result, payload pointer, return state/event continuation, and fuel.
-/

namespace Spikes.Spike3SortLines.Linux

open Gasm.Core Gasm.Effects Gasm.Core.Platform
open Gasm.Targets.Linux Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.ProductionPrefix
open Stdlib.SmolAlloc Spikes.Spike3SortLines

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

def linuxConcreteMallocEntryRip : UInt64 := 4199732
def linuxFirstMallocReturnRip : UInt64 := 4198523

private def c01 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (sub_rsp 120)
    (nativePreparationEntry .linux spike3ConcreteExecutionContext environment)
private def c02 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .eax 9) (c01 environment)
private def c03 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .edi .edi) (c02 environment)
private def c04 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .esi 65536) (c03 environment)
private def c05 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .edx 3) (c04 environment)
private def c06 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .r10d 0x22) (c05 environment)
private def c07 (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF) (c06 environment)
private def linuxBeforeMmap (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .r9d .r9d) (c07 environment)

private def linuxMmapBoundary (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step syscall_op (linuxBeforeMmap environment)

private def linuxAfterMmap (environment : Environment) : X86_64MachineState :=
  (spike3LinuxMmapHook (Event := AnyEvent) spike3ConcreteExecutionContext.arenaGrant
    (linuxMmapBoundary environment)).1

private def linuxAfterErrnoCmp (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001) (linuxAfterMmap environment)
private def linuxAfterErrnoBranch (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (jae_rel32 1265) (linuxAfterErrnoCmp environment)
private def linuxAfterArenaEndMove (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64 .r15 .rax) (linuxAfterErrnoBranch environment)
private def linuxAfterArenaEndAdd (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (add_r64_imm32 .r15 65536) (linuxAfterArenaEndMove environment)
private def linuxAfterArenaCarryBranch (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (jb_rel32 1249) (linuxAfterArenaEndAdd environment)
private def linuxAfterBumpInstall (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r64 .r11 .rax) (linuxAfterArenaCarryBranch environment)
private def linuxAfterFreeListInstall (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (xor_r32 .r10d .r10d) (linuxAfterBumpInstall environment)
private def linuxAfterLineCountInit (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem64_disp_imm .rsp 0x30 0)
    (linuxAfterFreeListInstall environment)
private def linuxAfterHeadInit (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem64_disp_imm .rsp 0x38 0) (linuxAfterLineCountInit environment)
private def linuxAfterLineLengthInit (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem64_disp_imm .rsp 0x60 0) (linuxAfterHeadInit environment)
private def linuxAfterLineCapacityInit (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_mem64_disp_imm .rsp 0x68 256)
    (linuxAfterLineLengthInit environment)
private def linuxBeforeFirstMallocCall (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (mov_r32 .ecx 512) (linuxAfterLineCapacityInit environment)

private theorem linuxBeforeMmapRip (environment : Environment) :
    (linuxBeforeMmap environment).rip = 4198440 := by rfl
private theorem linuxBeforeMmapRax (environment : Environment) :
    (linuxBeforeMmap environment).gprs .rax = SYS_mmap := by rfl
private theorem linuxBeforeMmapRsi (environment : Environment) :
    (linuxBeforeMmap environment).gprs .rsi = 65536 := by rfl
private theorem linuxMmapBoundaryRip (environment : Environment) :
    (linuxMmapBoundary environment).rip = linuxSyscallEntry := by rfl
private theorem linuxMmapBoundaryRax (environment : Environment) :
    (linuxMmapBoundary environment).gprs .rax = SYS_mmap := by rfl
private theorem linuxMmapBoundaryRsi (environment : Environment) :
    (linuxMmapBoundary environment).gprs .rsi = 65536 := by rfl
private theorem linuxAfterMmapEq (environment : Environment) :
    linuxAfterMmap environment =
      { (linuxMmapBoundary environment).setGpr64 .rax spike3ConcreteLinuxArena.base with
        rip := 4198442 } := by
  unfold linuxAfterMmap spike3LinuxMmapHook spike3LinuxArena
  rw [linuxMmapBoundaryRsi]
  rfl
private theorem linuxAfterMmapRip (environment : Environment) :
    (linuxAfterMmap environment).rip = 4198442 := by rw [linuxAfterMmapEq]
private theorem linuxAfterMmapRax (environment : Environment) :
    (linuxAfterMmap environment).gprs .rax = spike3ConcreteLinuxArena.base := by
  rw [linuxAfterMmapEq]
  rfl
private theorem linuxAfterMmapSafe (environment : Environment) :
    (linuxAfterMmap environment).fault = none := by
  rw [linuxAfterMmapEq]
  rfl

private theorem cmpImm32StepCf (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) :
    (((X86_64Instruction.step (cmp_r64_imm32 dst value) state).cf = true) : Prop) =
      (state.gprs dst < signExtendUInt32To64 value) := by
  change (((({ state with stdinBuffer := ByteArray.empty, incomingRequests := [] }).setFlagsCmp64
    (state.gprs dst) (signExtendUInt32To64 value)).cf = true) : Prop) = _
  exact X86_64MachineState.setFlagsCmp64_cf _ _ _

private theorem addImm32StepCf (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) :
    (((X86_64Instruction.step (add_r64_imm32 dst value) state).cf = true) : Prop) =
      (state.gprs dst + signExtendUInt32To64 value < state.gprs dst) := by
  change (((({ state with stdinBuffer := ByteArray.empty, incomingRequests := [] }.setGpr64 dst
    (state.gprs dst + signExtendUInt32To64 value)).setFlagsAdd64
      (state.gprs dst) (signExtendUInt32To64 value)).cf = true) : Prop) = _
  exact X86_64MachineState.setFlagsAdd64_cf _ _ _

private theorem cmpImm32StepFault (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (cmp_r64_imm32 dst value) state).fault = state.fault := by
  cases dst <;> rfl
private theorem addImm32StepFault (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (add_r64_imm32 dst value) state).fault = state.fault := by
  cases dst <;> rfl
private theorem addImm32StepGpr (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (add_r64_imm32 dst value) state).gprs dst =
      state.gprs dst + signExtendUInt32To64 value := by
  cases dst <;> rfl
private theorem movStepGpr (dst src : Reg64) (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_r64 dst src) state).gprs dst = state.gprs src := by
  cases dst <;> cases src <;> rfl
private theorem movStepGprOther (dst src : Reg64) (state : X86_64MachineState)
    (register : Reg64) (different : register ≠ dst) :
    (X86_64Instruction.step (mov_r64 dst src) state).gprs register = state.gprs register := by
  change (state.setGpr64 dst (state.gprs src)).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr64, different]
private theorem cmpImm32StepGpr (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) (register : Reg64) :
    (X86_64Instruction.step (cmp_r64_imm32 dst value) state).gprs register =
      state.gprs register := by
  cases dst <;> cases register <;> rfl
private theorem conditionalStepGpr {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind) (state : X86_64MachineState)
    (register : Reg64) :
    (X86_64Instruction.step instruction state).gprs register = state.gprs register := by
  cases encoding <;> rfl

private theorem linuxAfterErrnoCmpSafe (environment : Environment) :
    (linuxAfterErrnoCmp environment).fault = none := by
  rw [linuxAfterErrnoCmp, cmpImm32StepFault, linuxAfterMmapSafe]
private theorem linuxAfterErrnoCmpRip (environment : Environment) :
    (linuxAfterErrnoCmp environment).rip = 4198449 := by
  rw [linuxAfterErrnoCmp,
    (cmp_r64_imm32_sequential .rax 0xFFFFF001).step_rip_eq_of_safe _
      (linuxAfterErrnoCmpSafe environment), linuxAfterMmapRip]
  rfl
private theorem linuxErrnoBranchNotChosen (environment : Environment) :
    ¬ X86BranchCondition.aboveOrEqual.holds (linuxAfterErrnoCmp environment) := by
  simp only [X86BranchCondition.holds]
  have carry : (linuxAfterErrnoCmp environment).cf = true := by
    change (X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001)
      (linuxAfterMmap environment)).cf = true
    rw [cmpImm32StepCf, linuxAfterMmapRax]
    decide
  simp [carry]
private theorem linuxAfterErrnoBranchSafe (environment : Environment) :
    (linuxAfterErrnoBranch environment).fault = none := by
  rw [linuxAfterErrnoBranch, (ConditionalJumpEncoding.jae32 1265).step_fault_eq,
    linuxAfterErrnoCmpSafe]
private theorem linuxAfterErrnoBranchRip (environment : Environment) :
    (linuxAfterErrnoBranch environment).rip = 4198455 := by
  rw [linuxAfterErrnoBranch,
    (ConditionalJumpEncoding.jae32 1265).step_rip_eq_fallthrough _
      (linuxErrnoBranchNotChosen environment), linuxAfterErrnoCmpRip]
  rfl
private theorem linuxAfterArenaEndMoveSafe (environment : Environment) :
    (linuxAfterArenaEndMove environment).fault = none := by
  rw [linuxAfterArenaEndMove, (ControlFlowFree.mov .r15 .rax).step_fault_eq,
    linuxAfterErrnoBranchSafe]
private theorem linuxAfterArenaEndMoveRip (environment : Environment) :
    (linuxAfterArenaEndMove environment).rip = 4198458 := by
  rw [linuxAfterArenaEndMove, (ControlFlowFree.mov .r15 .rax).step_rip_eq,
    linuxAfterErrnoBranchRip]
  rfl
private theorem linuxAfterArenaEndMoveR15 (environment : Environment) :
    (linuxAfterArenaEndMove environment).gprs .r15 = spike3ConcreteLinuxArena.base := by
  rw [linuxAfterArenaEndMove, movStepGpr]
  rw [linuxAfterErrnoBranch, conditionalStepGpr (ConditionalJumpEncoding.jae32 1265)]
  rw [linuxAfterErrnoCmp, cmpImm32StepGpr]
  exact linuxAfterMmapRax environment
private theorem linuxAfterArenaEndAddSafe (environment : Environment) :
    (linuxAfterArenaEndAdd environment).fault = none := by
  rw [linuxAfterArenaEndAdd, addImm32StepFault, linuxAfterArenaEndMoveSafe]
private theorem linuxAfterArenaEndAddRip (environment : Environment) :
    (linuxAfterArenaEndAdd environment).rip = 4198465 := by
  rw [linuxAfterArenaEndAdd,
    (show SequentialInstruction (add_r64_imm32 .r15 65536) from
      { encoding := .addImm32 .r15 65536
        safeFallthrough := by intro state _; rfl }).step_rip_eq_of_safe _
      (linuxAfterArenaEndAddSafe environment),
    linuxAfterArenaEndMoveRip]
  rfl
private theorem linuxAfterArenaEndAddR15 (environment : Environment) :
    (linuxAfterArenaEndAdd environment).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  rw [linuxAfterArenaEndAdd, addImm32StepGpr, linuxAfterArenaEndMoveR15]
  rfl
private theorem linuxArenaCarryNotChosen (environment : Environment) :
    ¬ X86BranchCondition.below.holds (linuxAfterArenaEndAdd environment) := by
  simp only [X86BranchCondition.holds, linuxAfterArenaEndAdd]
  rw [addImm32StepCf, linuxAfterArenaEndMoveR15]
  decide
private theorem linuxAfterArenaCarryBranchSafe (environment : Environment) :
    (linuxAfterArenaCarryBranch environment).fault = none := by
  rw [linuxAfterArenaCarryBranch, (ConditionalJumpEncoding.jb32 1249).step_fault_eq,
    linuxAfterArenaEndAddSafe]
private theorem linuxAfterArenaCarryBranchRip (environment : Environment) :
    (linuxAfterArenaCarryBranch environment).rip = 4198471 := by
  rw [linuxAfterArenaCarryBranch,
    (ConditionalJumpEncoding.jb32 1249).step_rip_eq_fallthrough _
      (linuxArenaCarryNotChosen environment), linuxAfterArenaEndAddRip]
  rfl

/-- Machine entry reached by the first emitted `call smol_malloc`, including its pushed caller
    return address. -/
def linuxFirstMallocEntry (environment : Environment) : X86_64MachineState :=
  X86_64Instruction.step (call_rel32 1209) (linuxBeforeFirstMallocCall environment)

/-- Persistent allocator frame installed by the concrete reservation prologue. -/
def linuxFirstAllocatorBefore (environment : Environment) : SmolAllocatorFrame :=
  { bump := spike3ConcreteLinuxArena.base
    freeHead := 0
    memory := (linuxFirstMallocEntry environment).memory }

private def a01 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_r64 .r8 .rcx) initial
private def a02 (initial : X86_64MachineState) :=
  X86_64Instruction.step (add_r64_imm8 .r8 7) (a01 initial)
private def a03 (initial : X86_64MachineState) :=
  X86_64Instruction.step (jb_rel32 113) (a02 initial)
private def a04 (initial : X86_64MachineState) :=
  X86_64Instruction.step (and_r64_imm8 .r8 0xF8) (a03 initial)
private def a05 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_r64 .r9 .r8) (a04 initial)
private def a06 (initial : X86_64MachineState) :=
  X86_64Instruction.step (add_r64_imm8 .r9 32) (a05 initial)
private def a07 (initial : X86_64MachineState) :=
  X86_64Instruction.step (jb_rel32 96) (a06 initial)
private def a08 (initial : X86_64MachineState) :=
  X86_64Instruction.step (cmp_r64_imm8 .r10 0) (a07 initial)
private def a09 (initial : X86_64MachineState) :=
  X86_64Instruction.step (jne_rel8 0x36) (a08 initial)
private def a10 (initial : X86_64MachineState) :=
  X86_64Instruction.step (cmp_r64 .r11 .r15) (a09 initial)
private def a11 (initial : X86_64MachineState) :=
  X86_64Instruction.step (ja_rel8 0x55) (a10 initial)
private def a12 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_r64 .rax .r15) (a11 initial)
private def a13 (initial : X86_64MachineState) :=
  X86_64Instruction.step (sub_r64 .rax .r11) (a12 initial)
private def a14 (initial : X86_64MachineState) :=
  X86_64Instruction.step (cmp_r64 .rax .r9) (a13 initial)
private def a15 (initial : X86_64MachineState) :=
  X86_64Instruction.step (jb_rel8 0x4A) (a14 initial)
private def a16 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_r64 .rax .r11) (a15 initial)
private def a17 (initial : X86_64MachineState) :=
  X86_64Instruction.step (add_r64 .r11 .r9) (a16 initial)
private def a18 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_mem64_disp .rax 0x00 .r8) (a17 initial)
private def a19 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_mem64_disp_imm .rax 0x08 0) (a18 initial)
private def a20 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_mem64_disp_imm .rax 0x10 8) (a19 initial)
private def a21 (initial : X86_64MachineState) :=
  X86_64Instruction.step (mov_mem64_disp_imm .rax 0x18 0) (a20 initial)
private def a22 (initial : X86_64MachineState) :=
  X86_64Instruction.step (add_r64_imm8 .rax 32) (a21 initial)
private def a23 (initial : X86_64MachineState) :=
  X86_64Instruction.step ret_op (a22 initial)

private def linuxConcreteMallocInstructions : List X86_64Instr :=
  assembleProgram linuxConcreteMallocEntryRip smolMallocSymbolicProgram

private def linuxLinkedFirstCallerIndex : List (UInt64 × X86_64Instr) := [
  (4198400, sub_rsp 120),
  (4198404, mov_r32 .eax 9),
  (4198409, xor_r32 .edi .edi),
  (4198411, mov_r32 .esi 65536),
  (4198416, mov_r32 .edx 3),
  (4198421, mov_r32 .r10d 0x22),
  (4198427, mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF),
  (4198437, xor_r32 .r9d .r9d),
  (4198440, syscall_op),
  (4198442, cmp_r64_imm32 .rax 0xFFFFF001),
  (4198449, jae_rel32 1265),
  (4198455, mov_r64 .r15 .rax),
  (4198458, add_r64_imm32 .r15 65536),
  (4198465, jb_rel32 1249),
  (4198471, mov_r64 .r11 .rax),
  (4198474, xor_r32 .r10d .r10d),
  (4198477, mov_mem64_disp_imm .rsp 0x30 0),
  (4198486, mov_mem64_disp_imm .rsp 0x38 0),
  (4198495, mov_mem64_disp_imm .rsp 0x60 0),
  (4198504, mov_mem64_disp_imm .rsp 0x68 256),
  (4198513, mov_r32 .ecx 512),
  (4198518, call_rel32 1209)
]

private theorem linuxConcreteIndexIdentity (environment : Environment) :
    nativePreparationIndex .linux spike3ConcreteExecutionContext environment =
      spike3NoGrantResourceArtifactIndex := by
  rfl

private theorem linuxLinkedFirstCallerIndexExact :
    spike3NoGrantResourceArtifactIndex.take 22 = linuxLinkedFirstCallerIndex := by
  rfl

private theorem callerIndexedLookup (environment : Environment)
    (entry : UInt64 × X86_64Instr) (member : entry ∈ linuxLinkedFirstCallerIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) entry.1 =
        some entry.2 := by
  rw [linuxConcreteIndexIdentity environment]
  apply spike3NoGrantResourceArtifactLayout.resolves
  apply List.mem_of_mem_take
  rw [linuxLinkedFirstCallerIndexExact]
  exact member

private def linuxLinkedMallocIndex : List (UInt64 × X86_64Instr) := [
  (4199732, mov_r64 .r8 .rcx),
  (4199735, add_r64_imm8 .r8 7),
  (4199739, jb_rel32 113),
  (4199745, and_r64_imm8 .r8 0xF8),
  (4199749, mov_r64 .r9 .r8),
  (4199752, add_r64_imm8 .r9 32),
  (4199756, jb_rel32 96),
  (4199762, cmp_r64_imm8 .r10 0),
  (4199766, jne_rel8 0x36),
  (4199768, cmp_r64 .r11 .r15),
  (4199771, ja_rel8 0x55),
  (4199773, mov_r64 .rax .r15),
  (4199776, sub_r64 .rax .r11),
  (4199779, cmp_r64 .rax .r9),
  (4199782, jb_rel8 0x4A),
  (4199784, mov_r64 .rax .r11),
  (4199787, add_r64 .r11 .r9),
  (4199790, mov_mem64_disp .rax 0 .r8),
  (4199793, mov_mem64_disp_imm .rax 0x08 0),
  (4199801, mov_mem64_disp_imm .rax 0x10 8),
  (4199809, mov_mem64_disp_imm .rax 0x18 0),
  (4199817, add_r64_imm8 .rax 32),
  (4199821, ret_op),
  (4199822, mov_r64 .rax .r10),
  (4199825, mov_reg64_mem64_disp .rdx .rax 0),
  (4199828, cmp_r64 .rdx .r8),
  (4199831, jb_rel8 0xBF),
  (4199833, mov_reg64_mem64_disp .r10 .rax 0x18),
  (4199837, mov_mem64_disp_imm .rax 0x08 0),
  (4199845, mov_mem64_disp_imm .rax 0x18 0),
  (4199853, add_r64_imm8 .rax 32),
  (4199857, ret_op),
  (4199858, xor_r32 .eax .eax),
  (4199860, ret_op)
]

private theorem linuxLinkedMallocIndexExact :
    (spike3NoGrantResourceArtifactIndex.drop 302).take 34 = linuxLinkedMallocIndex := by
  rfl

private theorem mallocIndexedLookup (environment : Environment)
    (entry : UInt64 × X86_64Instr) (member : entry ∈ linuxLinkedMallocIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) entry.1 =
        some entry.2 := by
  rw [linuxConcreteIndexIdentity environment]
  apply spike3NoGrantResourceArtifactLayout.resolves
  rw [spike3_no_grant_resource_index_decomposition]
  apply List.mem_append_right
  apply List.mem_of_mem_take
  rw [linuxLinkedMallocIndexExact]
  exact member

private theorem normalSelected {state : X86_64MachineState}
    (normal : state.rip ≠ linuxSyscallEntry) :
    nativePreparationSelected .linux state.rip state = true := by
  simp [nativePreparationSelected, normal]

private theorem normalSilent {state : X86_64MachineState}
    (normal : state.rip ≠ linuxSyscallEntry) :
    nativePreparationHostIntercept .linux spike3ConcreteExecutionContext state.rip state = none := by
  unfold nativePreparationHostIntercept spike3LinuxCallIntercept
  rw [if_neg]
  · simp [linuxCallIntercept, linuxSyscallIntercept, normal]
  · intro h
    simp at h
    exact normal h.1

private theorem ordinaryOne {environment : Environment} {events : List AnyEvent}
    {state : X86_64MachineState} {instruction : X86_64Instr}
    (encoding : SequentialInstruction instruction)
    (lookup : instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1 state events
      (X86_64Instruction.step instruction state) events [] := by
  apply nativePreparation_ordinaryBlock encoding lookup
  · exact normalSelected normal
  · exact normalSilent normal
  · exact safe

private theorem conditionalFallthroughOne {environment : Environment} {events : List AnyEvent}
    {state : X86_64MachineState} {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind)
    (notChosen : ¬ kind.holds state)
    (lookup : instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1 state events
      (X86_64Instruction.step instruction state) events [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  exact .conditionalFallthrough encoding notChosen lookup (normalSelected normal)
    (normalSilent normal) safe (.nil _ _)

private theorem internalCallOne {environment : Environment} {events : List AnyEvent}
    {state : X86_64MachineState} {instruction : X86_64Instr}
    (encoding : HostInterceptEncoding instruction)
    (lookup : instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1 state events
      (X86_64Instruction.step instruction state) events [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  exact .internalCall encoding lookup (normalSelected normal) (normalSilent normal) safe (.nil _ _)

private theorem nearReturnOne {environment : Environment} {events : List AnyEvent}
    {state : X86_64MachineState} {instruction : X86_64Instr}
    (encoding : ReturnEncoding instruction)
    (lookup : instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1 state events
      (X86_64Instruction.step instruction state) events [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  exact .nearReturn encoding lookup (normalSelected normal) (normalSilent normal) safe (.nil _ _)

private theorem seqAddImm8 (dst : Reg64) (value : UInt8) :
    SequentialInstruction (add_r64_imm8 dst value) where
  encoding := .addImm8 dst value
  safeFallthrough := by intro state _; cases dst <;> rfl

private theorem seqAddImm32 (dst : Reg64) (value : UInt32) :
    SequentialInstruction (add_r64_imm32 dst value) where
  encoding := .addImm32 dst value
  safeFallthrough := by intro state _; cases dst <;> rfl

private theorem seqAndImm8 (dst : Reg64) (value : UInt8) :
    SequentialInstruction (and_r64_imm8 dst value) where
  encoding := .bitAndImm8 dst value
  safeFallthrough := by intro state _; cases dst <;> rfl

private theorem seqCmp (left right : Reg64) : SequentialInstruction (cmp_r64 left right) where
  encoding := .compare left right
  safeFallthrough := by intro state _; cases left <;> cases right <;> rfl

private theorem seqCmpImm8 (dst : Reg64) (value : UInt8) :
    SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
  safeFallthrough := by intro state _; cases dst <;> rfl

private theorem seqXor32 (dst src : Reg32) : SequentialInstruction (xor_r32 dst src) where
  encoding := .xor32 dst src
  safeFallthrough := by intro state _; cases dst <;> cases src <;> rfl

private theorem seqStoreRaxR8 : SequentialInstruction (mov_mem64_disp .rax 0 .r8) where
  encoding := .movMem64Disp .rax 0 .r8
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRax08 : SequentialInstruction (mov_mem64_disp_imm .rax 0x08 0) where
  encoding := .movMem64DispImm .rax 0x08 0
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRax10 : SequentialInstruction (mov_mem64_disp_imm .rax 0x10 8) where
  encoding := .movMem64DispImm .rax 0x10 8
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRax18 : SequentialInstruction (mov_mem64_disp_imm .rax 0x18 0) where
  encoding := .movMem64DispImm .rax 0x18 0
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRsp30 : SequentialInstruction (mov_mem64_disp_imm .rsp 0x30 0) where
  encoding := .movMem64DispImm .rsp 0x30 0
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRsp38 : SequentialInstruction (mov_mem64_disp_imm .rsp 0x38 0) where
  encoding := .movMem64DispImm .rsp 0x38 0
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRsp60 : SequentialInstruction (mov_mem64_disp_imm .rsp 0x60 0) where
  encoding := .movMem64DispImm .rsp 0x60 0
  safeFallthrough := by intro state _; rfl

private theorem seqStoreImmRsp68 : SequentialInstruction (mov_mem64_disp_imm .rsp 0x68 256) where
  encoding := .movMem64DispImm .rsp 0x68 256
  safeFallthrough := by intro state _; rfl

private theorem storeImmStepFault (base : Reg64) (disp : UInt8) (value : UInt32)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_mem64_disp_imm base disp value) state).fault = state.fault := by
  cases base <;> rfl
private theorem storeImmStepGpr (base : Reg64) (disp : UInt8) (value : UInt32)
    (state : X86_64MachineState) (register : Reg64) :
    (X86_64Instruction.step (mov_mem64_disp_imm base disp value) state).gprs register =
      state.gprs register := by
  cases base <;> cases register <;> rfl
private theorem mov32StepFault (dst : Reg32) (value : UInt32) (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_r32 dst value) state).fault = state.fault := by
  cases dst <;> rfl
private theorem mov32StepGprDst (dst : Reg32) (value : UInt32) (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_r32 dst value) state).gprs (reg32To64 dst) = value.toUInt64 := by
  cases dst <;> rfl
private theorem mov32StepGprOther (dst : Reg32) (value : UInt32)
    (state : X86_64MachineState) (register : Reg64)
    (different : register ≠ reg32To64 dst) :
    (X86_64Instruction.step (mov_r32 dst value) state).gprs register = state.gprs register := by
  change (state.setGpr32 dst value).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr32, different]
private theorem xor32StepGprDst (dst src : Reg32) (state : X86_64MachineState) :
    (X86_64Instruction.step (xor_r32 dst src) state).gprs (reg32To64 dst) =
      (state.gprs (reg32To64 dst)).toUInt32.toUInt64 ^^^
        (state.gprs (reg32To64 src)).toUInt32.toUInt64 := by
  cases dst <;> cases src <;> rfl
private theorem xor32StepFault (dst src : Reg32) (state : X86_64MachineState) :
    (X86_64Instruction.step (xor_r32 dst src) state).fault = state.fault := by
  cases dst <;> cases src <;> rfl
private theorem xor32StepGprOther (dst src : Reg32) (state : X86_64MachineState)
    (register : Reg64) (different : register ≠ reg32To64 dst) :
    (X86_64Instruction.step (xor_r32 dst src) state).gprs register = state.gprs register := by
  change (state.setGpr32 dst _).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr32, different]
private theorem xorEdiSelfStepRdiZero (state : X86_64MachineState) :
    (X86_64Instruction.step (xor_r32 .edi .edi) state).gprs .rdi = 0 := by
  change (X86_64Instruction.step (xor_r32 .edi .edi) state).gprs
    (reg32To64 .edi) = 0
  exact xor_r32_self_step_gpr .edi state
private theorem callRel32StepFault (disp : Int32) (state : X86_64MachineState) :
    (X86_64Instruction.step (call_rel32 disp) state).fault = state.fault := by rfl
private theorem callRel32StepGpr (disp : Int32) (state : X86_64MachineState)
    (register : Reg64) (notRsp : register ≠ .rsp) :
    (X86_64Instruction.step (call_rel32 disp) state).gprs register = state.gprs register := by
  change (state.setGpr64 .rsp (state.rsp - 8)).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr64, notRsp]

private theorem addImm32StepGprOther (dst : Reg64) (value : UInt32)
    (state : X86_64MachineState) (register : Reg64) (different : register ≠ dst) :
    (X86_64Instruction.step (add_r64_imm32 dst value) state).gprs register =
      state.gprs register := by
  change (state.setGpr64 dst _).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr64, different]

private theorem linuxAfterArenaCarryBranchR15 (environment : Environment) :
    (linuxAfterArenaCarryBranch environment).gprs .r15 =
      spike3ConcreteLinuxArena.endExclusive := by
  rw [linuxAfterArenaCarryBranch,
    conditionalStepGpr (ConditionalJumpEncoding.jb32 1249)]
  exact linuxAfterArenaEndAddR15 environment
private theorem linuxAfterArenaCarryBranchRax (environment : Environment) :
    (linuxAfterArenaCarryBranch environment).gprs .rax = spike3ConcreteLinuxArena.base := by
  rw [linuxAfterArenaCarryBranch,
    conditionalStepGpr (ConditionalJumpEncoding.jb32 1249)]
  rw [linuxAfterArenaEndAdd, addImm32StepGprOther .r15 65536 _ .rax (by decide)]
  rw [linuxAfterArenaEndMove, movStepGprOther .r15 .rax _ .rax (by decide)]
  rw [linuxAfterErrnoBranch, conditionalStepGpr (ConditionalJumpEncoding.jae32 1265)]
  rw [linuxAfterErrnoCmp, cmpImm32StepGpr]
  exact linuxAfterMmapRax environment
private theorem linuxAfterBumpInstallSafe (environment : Environment) :
    (linuxAfterBumpInstall environment).fault = none := by
  rw [linuxAfterBumpInstall, (ControlFlowFree.mov .r11 .rax).step_fault_eq,
    linuxAfterArenaCarryBranchSafe]
private theorem linuxAfterBumpInstallRip (environment : Environment) :
    (linuxAfterBumpInstall environment).rip = 4198474 := by
  rw [linuxAfterBumpInstall, (ControlFlowFree.mov .r11 .rax).step_rip_eq,
    linuxAfterArenaCarryBranchRip]
  rfl
private theorem linuxAfterBumpInstallR11 (environment : Environment) :
    (linuxAfterBumpInstall environment).gprs .r11 = spike3ConcreteLinuxArena.base := by
  rw [linuxAfterBumpInstall, movStepGpr]
  exact linuxAfterArenaCarryBranchRax environment
private theorem linuxAfterFreeListInstallSafe (environment : Environment) :
    (linuxAfterFreeListInstall environment).fault = none := by
  rw [linuxAfterFreeListInstall, xor32StepFault, linuxAfterBumpInstallSafe]
private theorem linuxAfterFreeListInstallRip (environment : Environment) :
    (linuxAfterFreeListInstall environment).rip = 4198477 := by
  rw [linuxAfterFreeListInstall, (seqXor32 .r10d .r10d).step_rip_eq_of_safe _
    (linuxAfterFreeListInstallSafe environment), linuxAfterBumpInstallRip]
  rfl
private theorem linuxAfterFreeListInstallR10 (environment : Environment) :
    (linuxAfterFreeListInstall environment).gprs .r10 = 0 := by
  rw [linuxAfterFreeListInstall]
  generalize linuxAfterBumpInstall environment = state
  have zero :
      (X86_64Instruction.step (xor_r32 .r10d .r10d)
        state).gprs .r10 = 0 :=
    xor_r32_self_step_gpr .r10d state
  exact zero
private theorem linuxAfterFreeListInstallR11 (environment : Environment) :
    (linuxAfterFreeListInstall environment).gprs .r11 = spike3ConcreteLinuxArena.base := by
  rw [linuxAfterFreeListInstall,
    xor32StepGprOther .r10d .r10d _ .r11 (by decide)]
  exact linuxAfterBumpInstallR11 environment

private theorem linuxAfterLineCountInitSafe (environment : Environment) :
    (linuxAfterLineCountInit environment).fault = none := by
  rw [linuxAfterLineCountInit, storeImmStepFault, linuxAfterFreeListInstallSafe]
private theorem linuxAfterHeadInitSafe (environment : Environment) :
    (linuxAfterHeadInit environment).fault = none := by
  rw [linuxAfterHeadInit, storeImmStepFault, linuxAfterLineCountInitSafe]
private theorem linuxAfterLineLengthInitSafe (environment : Environment) :
    (linuxAfterLineLengthInit environment).fault = none := by
  rw [linuxAfterLineLengthInit, storeImmStepFault, linuxAfterHeadInitSafe]
private theorem linuxCallerStoresSafe (environment : Environment) :
    (linuxAfterLineCapacityInit environment).fault = none := by
  rw [linuxAfterLineCapacityInit, storeImmStepFault, linuxAfterLineLengthInitSafe]
private theorem linuxAfterLineCountInitRip (environment : Environment) :
    (linuxAfterLineCountInit environment).rip = 4198486 := by
  rw [linuxAfterLineCountInit,
    seqStoreImmRsp30.step_rip_eq_of_safe _ (by
      exact linuxAfterLineCountInitSafe environment), linuxAfterFreeListInstallRip]
  rfl
private theorem linuxAfterHeadInitRip (environment : Environment) :
    (linuxAfterHeadInit environment).rip = 4198495 := by
  rw [linuxAfterHeadInit,
    seqStoreImmRsp38.step_rip_eq_of_safe _ (by
      exact linuxAfterHeadInitSafe environment),
    linuxAfterLineCountInitRip]
  rfl
private theorem linuxAfterLineLengthInitRip (environment : Environment) :
    (linuxAfterLineLengthInit environment).rip = 4198504 := by
  rw [linuxAfterLineLengthInit,
    seqStoreImmRsp60.step_rip_eq_of_safe _ (by
      exact linuxAfterLineLengthInitSafe environment), linuxAfterHeadInitRip]
  rfl
private theorem linuxAfterLineCapacityInitRip (environment : Environment) :
    (linuxAfterLineCapacityInit environment).rip = 4198513 := by
  rw [linuxAfterLineCapacityInit,
    seqStoreImmRsp68.step_rip_eq_of_safe _ (linuxCallerStoresSafe environment),
    linuxAfterLineLengthInitRip]
  rfl
private theorem linuxBeforeFirstMallocCallSafe (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).fault = none := by
  rw [linuxBeforeFirstMallocCall, mov32StepFault, linuxCallerStoresSafe]
private theorem linuxBeforeFirstMallocCallRip (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).rip = 4198518 := by
  rw [linuxBeforeFirstMallocCall,
    (mov_r32_sequential .ecx 512).step_rip_eq_of_safe _
      (linuxBeforeFirstMallocCallSafe environment), linuxAfterLineCapacityInitRip]
  rfl
private theorem linuxBeforeFirstMallocCallRcx (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).gprs .rcx = 512 := by
  rw [linuxBeforeFirstMallocCall]
  change (512 : UInt32).toUInt64 = 512
  rfl
private theorem linuxBeforeFirstMallocCallR10 (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).gprs .r10 = 0 := by
  rw [linuxBeforeFirstMallocCall]
  rw [mov32StepGprOther .ecx 512 _ .r10 (by decide)]
  rw [linuxAfterLineCapacityInit, storeImmStepGpr, linuxAfterLineLengthInit,
    storeImmStepGpr, linuxAfterHeadInit, storeImmStepGpr, linuxAfterLineCountInit,
    storeImmStepGpr]
  exact linuxAfterFreeListInstallR10 environment
private theorem linuxBeforeFirstMallocCallR11 (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).gprs .r11 = spike3ConcreteLinuxArena.base := by
  rw [linuxBeforeFirstMallocCall]
  rw [mov32StepGprOther .ecx 512 _ .r11 (by decide)]
  rw [linuxAfterLineCapacityInit, storeImmStepGpr, linuxAfterLineLengthInit,
    storeImmStepGpr, linuxAfterHeadInit, storeImmStepGpr, linuxAfterLineCountInit,
    storeImmStepGpr]
  exact linuxAfterFreeListInstallR11 environment
private theorem linuxBeforeFirstMallocCallR15 (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).gprs .r15 =
      spike3ConcreteLinuxArena.endExclusive := by
  rw [linuxBeforeFirstMallocCall]
  rw [mov32StepGprOther .ecx 512 _ .r15 (by decide)]
  rw [linuxAfterLineCapacityInit, storeImmStepGpr, linuxAfterLineLengthInit,
    storeImmStepGpr, linuxAfterHeadInit, storeImmStepGpr, linuxAfterLineCountInit,
    storeImmStepGpr]
  rw [linuxAfterFreeListInstall,
    xor32StepGprOther .r10d .r10d _ .r15 (by decide)]
  rw [linuxAfterBumpInstall, movStepGprOther .r11 .rax _ .r15 (by decide)]
  exact linuxAfterArenaCarryBranchR15 environment

private theorem linuxNativeEntryRsp (environment : Environment) :
    (nativePreparationEntry .linux spike3ConcreteExecutionContext environment).rsp =
      0x7FFFFFFF0000 := by
  rfl

private theorem linuxBeforeMmapRsp (environment : Environment) :
    (linuxBeforeMmap environment).rsp = 0x7FFFFFFEFF88 := by
  change (nativePreparationEntry .linux spike3ConcreteExecutionContext environment).rsp -
    signExtend8To64 120 = _
  rw [linuxNativeEntryRsp]
  rfl

private theorem linuxAfterMmapRsp (environment : Environment) :
    (linuxAfterMmap environment).rsp = 0x7FFFFFFEFF88 := by
  rw [linuxAfterMmapEq]
  change (linuxMmapBoundary environment).gprs .rsp = _
  change (linuxBeforeMmap environment).gprs .rsp = _
  exact linuxBeforeMmapRsp environment

private theorem linuxAfterErrnoCmpRsp (environment : Environment) :
    (linuxAfterErrnoCmp environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterErrnoCmp environment).gprs .rsp = _
  rw [linuxAfterErrnoCmp, cmpImm32StepGpr]
  change (linuxAfterMmap environment).rsp = _
  exact linuxAfterMmapRsp environment

private theorem linuxAfterErrnoBranchRsp (environment : Environment) :
    (linuxAfterErrnoBranch environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterErrnoBranch environment).gprs .rsp = _
  rw [linuxAfterErrnoBranch,
    conditionalStepGpr (ConditionalJumpEncoding.jae32 1265)]
  change (linuxAfterErrnoCmp environment).rsp = _
  exact linuxAfterErrnoCmpRsp environment

private theorem linuxAfterArenaEndMoveRsp (environment : Environment) :
    (linuxAfterArenaEndMove environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterArenaEndMove environment).gprs .rsp = _
  rw [linuxAfterArenaEndMove,
    movStepGprOther .r15 .rax _ .rsp (by decide)]
  change (linuxAfterErrnoBranch environment).rsp = _
  exact linuxAfterErrnoBranchRsp environment

private theorem linuxAfterArenaEndAddRsp (environment : Environment) :
    (linuxAfterArenaEndAdd environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterArenaEndAdd environment).gprs .rsp = _
  rw [linuxAfterArenaEndAdd,
    addImm32StepGprOther .r15 65536 _ .rsp (by decide)]
  change (linuxAfterArenaEndMove environment).rsp = _
  exact linuxAfterArenaEndMoveRsp environment

private theorem linuxAfterArenaCarryBranchRsp (environment : Environment) :
    (linuxAfterArenaCarryBranch environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterArenaCarryBranch environment).gprs .rsp = _
  rw [linuxAfterArenaCarryBranch,
    conditionalStepGpr (ConditionalJumpEncoding.jb32 1249)]
  change (linuxAfterArenaEndAdd environment).rsp = _
  exact linuxAfterArenaEndAddRsp environment

private theorem linuxAfterBumpInstallRsp (environment : Environment) :
    (linuxAfterBumpInstall environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterBumpInstall environment).gprs .rsp = _
  rw [linuxAfterBumpInstall,
    movStepGprOther .r11 .rax _ .rsp (by decide)]
  change (linuxAfterArenaCarryBranch environment).rsp = _
  exact linuxAfterArenaCarryBranchRsp environment

private theorem linuxAfterFreeListInstallRsp (environment : Environment) :
    (linuxAfterFreeListInstall environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterFreeListInstall environment).gprs .rsp = _
  rw [linuxAfterFreeListInstall,
    xor32StepGprOther .r10d .r10d _ .rsp (by decide)]
  change (linuxAfterBumpInstall environment).rsp = _
  exact linuxAfterBumpInstallRsp environment

private theorem linuxAfterLineCountInitRsp (environment : Environment) :
    (linuxAfterLineCountInit environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterLineCountInit environment).gprs .rsp = _
  rw [linuxAfterLineCountInit, storeImmStepGpr]
  change (linuxAfterFreeListInstall environment).rsp = _
  exact linuxAfterFreeListInstallRsp environment

private theorem linuxAfterHeadInitRsp (environment : Environment) :
    (linuxAfterHeadInit environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterHeadInit environment).gprs .rsp = _
  rw [linuxAfterHeadInit, storeImmStepGpr]
  change (linuxAfterLineCountInit environment).rsp = _
  exact linuxAfterLineCountInitRsp environment

private theorem linuxAfterLineLengthInitRsp (environment : Environment) :
    (linuxAfterLineLengthInit environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterLineLengthInit environment).gprs .rsp = _
  rw [linuxAfterLineLengthInit, storeImmStepGpr]
  change (linuxAfterHeadInit environment).rsp = _
  exact linuxAfterHeadInitRsp environment

private theorem linuxAfterLineCapacityInitRsp (environment : Environment) :
    (linuxAfterLineCapacityInit environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxAfterLineCapacityInit environment).gprs .rsp = _
  rw [linuxAfterLineCapacityInit, storeImmStepGpr]
  change (linuxAfterLineLengthInit environment).rsp = _
  exact linuxAfterLineLengthInitRsp environment

private theorem linuxBeforeFirstMallocCallRsp (environment : Environment) :
    (linuxBeforeFirstMallocCall environment).rsp = 0x7FFFFFFEFF88 := by
  change (linuxBeforeFirstMallocCall environment).gprs .rsp = _
  rw [linuxBeforeFirstMallocCall,
    mov32StepGprOther .ecx 512 _ .rsp (by decide)]
  change (linuxAfterLineCapacityInit environment).rsp = _
  exact linuxAfterLineCapacityInitRsp environment

private theorem linuxFirstMallocEntrySafe (environment : Environment) :
    (linuxFirstMallocEntry environment).fault = none := by
  rw [linuxFirstMallocEntry, callRel32StepFault, linuxBeforeFirstMallocCallSafe]

private theorem linuxFirstMallocEntryRip (environment : Environment) :
    (linuxFirstMallocEntry environment).rip = linuxConcreteMallocEntryRip := by
  change (linuxBeforeFirstMallocCall environment).rip + 5 + signExtend32To64 1209 = _
  rw [linuxBeforeFirstMallocCallRip]
  rfl

private theorem linuxFirstMallocEntryRsp (environment : Environment) :
    (linuxFirstMallocEntry environment).rsp = 0x7FFFFFFEFF80 := by
  rw [linuxFirstMallocEntry, call_rel32_step_rsp, linuxBeforeFirstMallocCallRsp]
  rfl

private theorem linuxFirstMallocEntryRcx (environment : Environment) :
    (linuxFirstMallocEntry environment).gprs .rcx = 512 := by
  rw [linuxFirstMallocEntry,
    callRel32StepGpr 1209 _ .rcx (by decide), linuxBeforeFirstMallocCallRcx]

private theorem linuxFirstMallocEntryR10 (environment : Environment) :
    (linuxFirstMallocEntry environment).gprs .r10 = 0 := by
  rw [linuxFirstMallocEntry,
    callRel32StepGpr 1209 _ .r10 (by decide), linuxBeforeFirstMallocCallR10]

private theorem linuxFirstMallocEntryR11 (environment : Environment) :
    (linuxFirstMallocEntry environment).gprs .r11 = spike3ConcreteLinuxArena.base := by
  rw [linuxFirstMallocEntry,
    callRel32StepGpr 1209 _ .r11 (by decide), linuxBeforeFirstMallocCallR11]

private theorem linuxFirstMallocEntryR15 (environment : Environment) :
    (linuxFirstMallocEntry environment).gprs .r15 =
      spike3ConcreteLinuxArena.endExclusive := by
  rw [linuxFirstMallocEntry,
    callRel32StepGpr 1209 _ .r15 (by decide), linuxBeforeFirstMallocCallR15]

private theorem linuxFirstMallocCallerSlot (environment : Environment) :
    (linuxFirstMallocEntry environment).read64 (linuxFirstMallocEntry environment).rsp =
      linuxFirstMallocReturnRip := by
  rw [linuxFirstMallocEntry, call_rel32_step_return_slot, linuxBeforeFirstMallocCallRip]
  rfl

private structure FreshEntryConditions (initial : X86_64MachineState) : Prop where
  rip : initial.rip = 4199732
  request : initial.gprs .rcx = 512
  freeHead : initial.gprs .r10 = 0
  bump : initial.gprs .r11 = spike3ConcreteLinuxArena.base
  arenaEnd : initial.gprs .r15 = spike3ConcreteLinuxArena.endExclusive
  stackAddress : initial.rsp = 0x7FFFFFFEFF80
  returnSlot : initial.read64 initial.rsp = linuxFirstMallocReturnRip
  safe : initial.fault = none

private theorem ordinarySafe {instruction : X86_64Instr}
    (ordinary : ControlFlowFree instruction) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step instruction state).fault = none := by
  rw [ordinary.step_fault_eq, safe]

private theorem addImm8Safe (dst : Reg64) (value : UInt8) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step (add_r64_imm8 dst value) state).fault = none := by
  cases dst <;> exact safe

private theorem addImm32Safe (dst : Reg64) (value : UInt32) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step (add_r64_imm32 dst value) state).fault = none := by
  cases dst <;> exact safe

private theorem andImm8Safe (dst : Reg64) (value : UInt8) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step (and_r64_imm8 dst value) state).fault = none := by
  cases dst <;> exact safe

private theorem cmpSafe (left right : Reg64) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step (cmp_r64 left right) state).fault = none := by
  cases left <;> cases right <;> exact safe

private theorem cmpImm8Safe (dst : Reg64) (value : UInt8) (state : X86_64MachineState)
    (safe : state.fault = none) :
    (X86_64Instruction.step (cmp_r64_imm8 dst value) state).fault = none := by
  cases dst <;> exact safe

private theorem storeRaxR8Safe (state : X86_64MachineState) (safe : state.fault = none) :
    (X86_64Instruction.step (mov_mem64_disp .rax 0 .r8) state).fault = none := by
  exact safe

private theorem storeImmRaxSafe (disp : UInt8) (value : UInt32)
    (state : X86_64MachineState) (safe : state.fault = none) :
    (X86_64Instruction.step (mov_mem64_disp_imm .rax disp value) state).fault = none := by
  exact safe

private theorem a01Safe (initial) (h : FreshEntryConditions initial) : (a01 initial).fault = none :=
  ordinarySafe (.mov .r8 .rcx) initial h.safe
private theorem a02Safe (initial) (h : FreshEntryConditions initial) : (a02 initial).fault = none :=
  addImm8Safe .r8 7 (a01 initial) (a01Safe initial h)
private theorem a03Safe (initial) (h : FreshEntryConditions initial) : (a03 initial).fault = none := by
  rw [a03, (ConditionalJumpEncoding.jb32 113).step_fault_eq, a02Safe initial h]
private theorem a04Safe (initial) (h : FreshEntryConditions initial) : (a04 initial).fault = none :=
  andImm8Safe .r8 0xF8 (a03 initial) (a03Safe initial h)
private theorem a05Safe (initial) (h : FreshEntryConditions initial) : (a05 initial).fault = none :=
  ordinarySafe (.mov .r9 .r8) (a04 initial) (a04Safe initial h)
private theorem a06Safe (initial) (h : FreshEntryConditions initial) : (a06 initial).fault = none :=
  addImm8Safe .r9 32 (a05 initial) (a05Safe initial h)
private theorem a07Safe (initial) (h : FreshEntryConditions initial) : (a07 initial).fault = none := by
  rw [a07, (ConditionalJumpEncoding.jb32 96).step_fault_eq, a06Safe initial h]
private theorem a08Safe (initial) (h : FreshEntryConditions initial) : (a08 initial).fault = none :=
  cmpImm8Safe .r10 0 (a07 initial) (a07Safe initial h)
private theorem a09Safe (initial) (h : FreshEntryConditions initial) : (a09 initial).fault = none := by
  rw [a09, (ConditionalJumpEncoding.jne8 0x36).step_fault_eq, a08Safe initial h]
private theorem a10Safe (initial) (h : FreshEntryConditions initial) : (a10 initial).fault = none :=
  cmpSafe .r11 .r15 (a09 initial) (a09Safe initial h)
private theorem a11Safe (initial) (h : FreshEntryConditions initial) : (a11 initial).fault = none := by
  rw [a11, (ConditionalJumpEncoding.ja8 0x55).step_fault_eq, a10Safe initial h]
private theorem a12Safe (initial) (h : FreshEntryConditions initial) : (a12 initial).fault = none :=
  ordinarySafe (.mov .rax .r15) (a11 initial) (a11Safe initial h)
private theorem a13Safe (initial) (h : FreshEntryConditions initial) : (a13 initial).fault = none :=
  ordinarySafe (.sub .rax .r11) (a12 initial) (a12Safe initial h)
private theorem a14Safe (initial) (h : FreshEntryConditions initial) : (a14 initial).fault = none :=
  cmpSafe .rax .r9 (a13 initial) (a13Safe initial h)
private theorem a15Safe (initial) (h : FreshEntryConditions initial) : (a15 initial).fault = none := by
  rw [a15, (ConditionalJumpEncoding.jb8 0x4A).step_fault_eq, a14Safe initial h]
private theorem a16Safe (initial) (h : FreshEntryConditions initial) : (a16 initial).fault = none :=
  ordinarySafe (.mov .rax .r11) (a15 initial) (a15Safe initial h)
private theorem a17Safe (initial) (h : FreshEntryConditions initial) : (a17 initial).fault = none :=
  ordinarySafe (.add .r11 .r9) (a16 initial) (a16Safe initial h)
private theorem a18Safe (initial) (h : FreshEntryConditions initial) : (a18 initial).fault = none :=
  storeRaxR8Safe (a17 initial) (a17Safe initial h)
private theorem a19Safe (initial) (h : FreshEntryConditions initial) : (a19 initial).fault = none :=
  storeImmRaxSafe 0x08 0 (a18 initial) (a18Safe initial h)
private theorem a20Safe (initial) (h : FreshEntryConditions initial) : (a20 initial).fault = none :=
  storeImmRaxSafe 0x10 8 (a19 initial) (a19Safe initial h)
private theorem a21Safe (initial) (h : FreshEntryConditions initial) : (a21 initial).fault = none :=
  storeImmRaxSafe 0x18 0 (a20 initial) (a20Safe initial h)
private theorem a22Safe (initial) (h : FreshEntryConditions initial) : (a22 initial).fault = none :=
  addImm8Safe .rax 32 (a21 initial) (a21Safe initial h)
private theorem a23Safe (initial) (h : FreshEntryConditions initial) : (a23 initial).fault = none := by
  change (a22 initial).fault = none
  exact a22Safe initial h

private theorem a01R8 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a01 initial).gprs .r8 = 512 := by
  change initial.gprs .rcx = 512
  exact h.request

private theorem a02R8 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a02 initial).gprs .r8 = 519 := by
  change (a01 initial).gprs .r8 + 7 = 519
  rw [a01R8 initial h]
  decide

private theorem a03R8 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a03 initial).gprs .r8 = 519 := by
  change (a02 initial).gprs .r8 = 519
  exact a02R8 initial h

private theorem a04R8 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a04 initial).gprs .r8 = 512 := by
  change (a03 initial).gprs .r8 &&& signExtend8To64 0xF8 = 512
  rw [a03R8 initial h]
  rfl

private theorem a05R9 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a05 initial).gprs .r9 = 512 := by
  change (a04 initial).gprs .r8 = 512
  exact a04R8 initial h

private theorem a07R10 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a07 initial).gprs .r10 = 0 := by
  change initial.gprs .r10 = 0
  exact h.freeHead

private theorem a09R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a09 initial).gprs .r11 = spike3ConcreteLinuxArena.base := by
  change initial.gprs .r11 = spike3ConcreteLinuxArena.base
  exact h.bump

private theorem a09R15 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a09 initial).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  change initial.gprs .r15 = spike3ConcreteLinuxArena.endExclusive
  exact h.arenaEnd

private theorem a06R9 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a06 initial).gprs .r9 = 544 := by
  change (a05 initial).gprs .r9 + 32 = 544
  rw [a05R9 initial h]
  decide

private theorem a12Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a12 initial).gprs .rax = spike3ConcreteLinuxArena.endExclusive := by
  change (a09 initial).gprs .r15 = spike3ConcreteLinuxArena.endExclusive
  exact a09R15 initial h

private theorem a12R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a12 initial).gprs .r11 = spike3ConcreteLinuxArena.base := by
  change (a09 initial).gprs .r11 = spike3ConcreteLinuxArena.base
  exact a09R11 initial h

private theorem a13Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a13 initial).gprs .rax = 65536 := by
  change (a12 initial).gprs .rax - (a12 initial).gprs .r11 = 65536
  rw [a12Rax initial h, a12R11 initial h]
  rfl

private theorem a13R9 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a13 initial).gprs .r9 = 544 := by
  change (a06 initial).gprs .r9 = 544
  exact a06R9 initial h

private theorem cmpImm8ZeroSetsZf (state : X86_64MachineState)
    (zero : state.gprs .r10 = 0) :
    (X86_64Instruction.step (cmp_r64_imm8 .r10 0) state).zf = true := by
  change (({ state with stdinBuffer := ByteArray.empty, incomingRequests := [] }.setFlagsCmp64
    (state.gprs .r10) 0).zf = true)
  exact X86_64MachineState.setFlagsCmp64_zf_of_eq _ _ _ zero

private theorem guard03 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a02 initial) := by
  simp only [X86BranchCondition.holds, a02]
  rw [add_r64_imm8_step_cf, a01R8 initial h]
  decide

private theorem guard07 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a06 initial) := by
  simp only [X86BranchCondition.holds, a06]
  rw [add_r64_imm8_step_cf, a05R9 initial h]
  decide

private theorem guard09 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    ¬ X86BranchCondition.notEqual.holds (a08 initial) := by
  simp only [X86BranchCondition.holds, a08]
  rw [cmpImm8ZeroSetsZf (a07 initial) (a07R10 initial h)]
  simp

private theorem guard11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    ¬ X86BranchCondition.above.holds (a10 initial) := by
  have carry : (a10 initial).cf = true := by
    change (X86_64Instruction.step (cmp_r64 .r11 .r15) (a09 initial)).cf = true
    rw [cmp_r64_step_cf, a09R11 initial h, a09R15 initial h]
    decide
  simp [X86BranchCondition.holds, carry]

private theorem guard15 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a14 initial) := by
  simp only [X86BranchCondition.holds, a14]
  rw [cmp_r64_step_cf, a13Rax initial h, a13R9 initial h]
  decide

private theorem a01Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a01 initial).rip = 4199735 := by
  rw [a01, (ControlFlowFree.mov .r8 .rcx).step_rip_eq, h.rip]
  rfl
private theorem a02Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a02 initial).rip = 4199739 := by
  rw [a02, (seqAddImm8 .r8 7).step_rip_eq_of_safe _ (a02Safe initial h), a01Rip initial h]
  rfl
private theorem a03Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a03 initial).rip = 4199745 := by
  rw [a03, (ConditionalJumpEncoding.jb32 113).step_rip_eq_fallthrough _ (guard03 initial h),
    a02Rip initial h]
  rfl
private theorem a04Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a04 initial).rip = 4199749 := by
  rw [a04, (seqAndImm8 .r8 0xF8).step_rip_eq_of_safe _ (a04Safe initial h), a03Rip initial h]
  rfl
private theorem a05Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a05 initial).rip = 4199752 := by
  rw [a05, (ControlFlowFree.mov .r9 .r8).step_rip_eq, a04Rip initial h]
  rfl
private theorem a06Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a06 initial).rip = 4199756 := by
  rw [a06, (seqAddImm8 .r9 32).step_rip_eq_of_safe _ (a06Safe initial h), a05Rip initial h]
  rfl
private theorem a07Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a07 initial).rip = 4199762 := by
  rw [a07, (ConditionalJumpEncoding.jb32 96).step_rip_eq_fallthrough _ (guard07 initial h),
    a06Rip initial h]
  rfl
private theorem a08Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a08 initial).rip = 4199766 := by
  rw [a08, (seqCmpImm8 .r10 0).step_rip_eq_of_safe _ (a08Safe initial h), a07Rip initial h]
  rfl
private theorem a09Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a09 initial).rip = 4199768 := by
  rw [a09, (ConditionalJumpEncoding.jne8 0x36).step_rip_eq_fallthrough _ (guard09 initial h),
    a08Rip initial h]
  rfl
private theorem a10Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a10 initial).rip = 4199771 := by
  rw [a10, (seqCmp .r11 .r15).step_rip_eq_of_safe _ (a10Safe initial h), a09Rip initial h]
  rfl
private theorem a11Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a11 initial).rip = 4199773 := by
  rw [a11, (ConditionalJumpEncoding.ja8 0x55).step_rip_eq_fallthrough _ (guard11 initial h),
    a10Rip initial h]
  rfl
private theorem a12Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a12 initial).rip = 4199776 := by
  rw [a12, (ControlFlowFree.mov .rax .r15).step_rip_eq, a11Rip initial h]
  rfl
private theorem a13Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a13 initial).rip = 4199779 := by
  rw [a13, (ControlFlowFree.sub .rax .r11).step_rip_eq, a12Rip initial h]
  rfl
private theorem a14Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a14 initial).rip = 4199782 := by
  rw [a14, (seqCmp .rax .r9).step_rip_eq_of_safe _ (a14Safe initial h), a13Rip initial h]
  rfl
private theorem a15Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a15 initial).rip = 4199784 := by
  rw [a15, (ConditionalJumpEncoding.jb8 0x4A).step_rip_eq_fallthrough _ (guard15 initial h),
    a14Rip initial h]
  rfl
private theorem a16Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a16 initial).rip = 4199787 := by
  rw [a16, (ControlFlowFree.mov .rax .r11).step_rip_eq, a15Rip initial h]
  rfl
private theorem a17Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a17 initial).rip = 4199790 := by
  rw [a17, (ControlFlowFree.add .r11 .r9).step_rip_eq, a16Rip initial h]
  rfl
private theorem a18Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a18 initial).rip = 4199793 := by
  rw [a18, seqStoreRaxR8.step_rip_eq_of_safe _ (a18Safe initial h), a17Rip initial h]
  rfl
private theorem a19Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a19 initial).rip = 4199801 := by
  rw [a19, seqStoreImmRax08.step_rip_eq_of_safe _ (a19Safe initial h), a18Rip initial h]
  rfl
private theorem a20Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a20 initial).rip = 4199809 := by
  rw [a20, seqStoreImmRax10.step_rip_eq_of_safe _ (a20Safe initial h), a19Rip initial h]
  rfl
private theorem a21Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a21 initial).rip = 4199817 := by
  rw [a21, seqStoreImmRax18.step_rip_eq_of_safe _ (a21Safe initial h), a20Rip initial h]
  rfl
private theorem a22Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a22 initial).rip = 4199821 := by
  rw [a22, (seqAddImm8 .rax 32).step_rip_eq_of_safe _ (a22Safe initial h), a21Rip initial h]
  rfl

private theorem a16Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a16 initial).gprs .rax = spike3ConcreteLinuxArena.base := by
  change (a09 initial).gprs .r11 = spike3ConcreteLinuxArena.base
  exact a09R11 initial h

private theorem a16R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a16 initial).gprs .r11 = spike3ConcreteLinuxArena.base := by
  change (a09 initial).gprs .r11 = spike3ConcreteLinuxArena.base
  exact a09R11 initial h

private theorem a16R9 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a16 initial).gprs .r9 = 544 := by
  change (a06 initial).gprs .r9 = 544
  exact a06R9 initial h

private theorem a17Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a17 initial).gprs .rax = spike3ConcreteLinuxArena.base := by
  change (a16 initial).gprs .rax = spike3ConcreteLinuxArena.base
  exact a16Rax initial h

private theorem a17R8 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a17 initial).gprs .r8 = 512 := by
  change (a04 initial).gprs .r8 = 512
  exact a04R8 initial h

private theorem a17R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a17 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  change (a16 initial).gprs .r11 + (a16 initial).gprs .r9 = _
  rw [a16R11 initial h, a16R9 initial h]

private theorem a17R10 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a17 initial).gprs .r10 = 0 := by
  change (a07 initial).gprs .r10 = 0
  exact a07R10 initial h

private theorem a17Memory (initial : X86_64MachineState) :
    (a17 initial).memory = initial.memory := by
  rfl

private theorem a17Rsp (initial : X86_64MachineState) :
    (a17 initial).rsp = initial.rsp := by
  rfl

private theorem a18Memory (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a18 initial).memory =
      X86_64Mem.write .w64 spike3ConcreteLinuxArena.base 512 initial.memory := by
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0)
    ((a17 initial).gprs .r8) (a17 initial).memory = _
  rw [a17Rax initial h, a17R8 initial h, a17Memory]
  rfl

private theorem a19Memory (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a19 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 8) 0
      (X86_64Mem.write .w64 spike3ConcreteLinuxArena.base 512 initial.memory) := by
  change X86_64Mem.write .w64 ((a18 initial).gprs .rax + signExtend8To64 0x08)
    (signExtendUInt32To64 0) (a18 initial).memory = _
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x08)
    (signExtendUInt32To64 0) (a18 initial).memory = _
  rw [a17Rax initial h, a18Memory initial h]
  rfl

private theorem a20Memory (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a20 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 16) 8
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 8) 0
        (X86_64Mem.write .w64 spike3ConcreteLinuxArena.base 512 initial.memory)) := by
  change X86_64Mem.write .w64 ((a19 initial).gprs .rax + signExtend8To64 0x10)
    (signExtendUInt32To64 8) (a19 initial).memory = _
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x10)
    (signExtendUInt32To64 8) (a19 initial).memory = _
  rw [a17Rax initial h, a19Memory initial h]
  rfl

private theorem a21Memory (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a21 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 24) 0
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 16) 8
        (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 8) 0
          (X86_64Mem.write .w64 spike3ConcreteLinuxArena.base 512 initial.memory))) := by
  change X86_64Mem.write .w64 ((a20 initial).gprs .rax + signExtend8To64 0x18)
    (signExtendUInt32To64 0) (a20 initial).memory = _
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x18)
    (signExtendUInt32To64 0) (a20 initial).memory = _
  rw [a17Rax initial h, a20Memory initial h]
  rfl

private theorem a22Memory (initial : X86_64MachineState) (_h : FreshEntryConditions initial) :
    (a22 initial).memory = (a21 initial).memory := by
  rfl

private theorem a22Rsp (initial : X86_64MachineState) :
    (a22 initial).rsp = initial.rsp := by
  rfl

private theorem readStack_writeArena0 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 spike3ConcreteLinuxArena.base value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem readStack_writeArena8 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 8) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem readStack_writeArena16 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 16) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem readStack_writeArena24 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 24) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem a22ReturnSlot (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a22 initial).read64 (a22 initial).rsp = linuxFirstMallocReturnRip := by
  rw [a22Rsp, h.stackAddress]
  change X86_64Mem.read .w64 0x7FFFFFFEFF80 (a22 initial).memory = _
  rw [a22Memory initial h, a21Memory initial h, readStack_writeArena24,
    readStack_writeArena16, readStack_writeArena8, readStack_writeArena0]
  have slot := h.returnSlot
  rw [h.stackAddress] at slot
  exact slot

private theorem a23Rip (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).rip = linuxFirstMallocReturnRip := by
  change (a22 initial).read64 (a22 initial).rsp = linuxFirstMallocReturnRip
  exact a22ReturnSlot initial h

private theorem mallocLookupAt (environment : Environment) (state : X86_64MachineState)
    (entry : UInt64 × X86_64Instr) (ripExact : state.rip = entry.1)
    (member : entry ∈ linuxLinkedMallocIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some entry.2 := by
  rw [ripExact]
  exact mallocIndexedLookup environment entry member

private theorem normalAt (address : UInt64) (state : X86_64MachineState)
    (ripExact : state.rip = address) (different : address ≠ linuxSyscallEntry) :
    state.rip ≠ linuxSyscallEntry := by
  rw [ripExact]
  exact different

private theorem callerLookupAt (environment : Environment) (state : X86_64MachineState)
    (entry : UInt64 × X86_64Instr) (ripExact : state.rip = entry.1)
    (member : entry ∈ linuxLinkedFirstCallerIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some entry.2 := by
  rw [ripExact]
  exact callerIndexedLookup environment entry member

private theorem linuxMmapSelected (environment : Environment) :
    nativePreparationSelected .linux (linuxMmapBoundary environment).rip
      (linuxMmapBoundary environment) = true := by
  simp [nativePreparationSelected, linuxMmapBoundaryRip, linuxMmapBoundaryRax, SYS_mmap]

private theorem linuxMmapHookEventNone (state : X86_64MachineState) :
    (spike3LinuxMmapHook (Event := AnyEvent) spike3ConcreteExecutionContext.arenaGrant state).2 =
      none := by
  unfold spike3LinuxMmapHook spike3LinuxArena
  by_cases admitted : spike3ConcreteExecutionContext.arenaGrant.admits
      (state.gprs .rsi) = true
  · simp only [admitted, ↓reduceIte]
    cases NativeArenaCapability.ofReservation 0x70000000 (state.gprs .rsi) <;> rfl
  · simp [admitted]

private theorem linuxMmapIntercepted (environment : Environment) :
    nativePreparationHostIntercept .linux spike3ConcreteExecutionContext
      (linuxMmapBoundary environment).rip (linuxMmapBoundary environment) =
        some (linuxAfterMmap environment, none) := by
  unfold nativePreparationHostIntercept
  simp [spike3LinuxCallIntercept, linuxMmapBoundaryRip, linuxMmapBoundaryRax, SYS_mmap,
    linuxAfterMmap]
  generalize hookExact :
    spike3LinuxMmapHook (Event := AnyEvent) spike3ConcreteExecutionContext.arenaGrant
      (linuxMmapBoundary environment) = outcome
  rcases outcome with ⟨hooked, event⟩
  have eventNone : event = none := by
    calc
      event = (spike3LinuxMmapHook (Event := AnyEvent)
        spike3ConcreteExecutionContext.arenaGrant (linuxMmapBoundary environment)).2 :=
          (congrArg Prod.snd hookExact).symm
      _ = none := linuxMmapHookEventNone (linuxMmapBoundary environment)
  subst event
  rfl

private theorem linuxFirstMallocCallerSelectedPath (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 22
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstMallocEntry environment) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 22
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (X86_64Instruction.step (call_rel32 1209)
        (linuxBeforeFirstMallocCall environment)) [] []
  have p01 := ordinaryOne (environment := environment) (events := [])
    (sub_rsp_sequential 120)
    (callerLookupAt environment
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment)
      (4198400, sub_rsp 120) (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198404 (c01 environment) (by rfl) (by decide)) (by rfl)
  have p02 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .eax 9)
    (callerLookupAt environment (c01 environment) (4198404, mov_r32 .eax 9)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198409 (c02 environment) (by rfl) (by decide)) (by rfl)
  have p03 := ordinaryOne (environment := environment) (events := [])
    (seqXor32 .edi .edi)
    (callerLookupAt environment (c02 environment) (4198409, xor_r32 .edi .edi)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198411 (c03 environment) (by rfl) (by decide)) (by rfl)
  have p04 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .esi 65536)
    (callerLookupAt environment (c03 environment) (4198411, mov_r32 .esi 65536)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198416 (c04 environment) (by rfl) (by decide)) (by rfl)
  have p05 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .edx 3)
    (callerLookupAt environment (c04 environment) (4198416, mov_r32 .edx 3)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198421 (c05 environment) (by rfl) (by decide)) (by rfl)
  have p06 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .r10d 0x22)
    (callerLookupAt environment (c05 environment) (4198421, mov_r32 .r10d 0x22)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198427 (c06 environment) (by rfl) (by decide)) (by rfl)
  have p07 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.loadImm .r8 0xFFFFFFFFFFFFFFFF).sequential
    (callerLookupAt environment (c06 environment)
      (4198427, mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198437 (c07 environment) (by rfl) (by decide)) (by rfl)
  have p08 := ordinaryOne (environment := environment) (events := [])
    (seqXor32 .r9d .r9d)
    (callerLookupAt environment (c07 environment) (4198437, xor_r32 .r9d .r9d)
      (by rfl) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198440 (linuxBeforeMmap environment) (linuxBeforeMmapRip environment)
      (by decide)) (by rfl)
  have p09 := nativePreparation_hostBlock (environment := environment)
    (state := linuxBeforeMmap environment) (next := linuxAfterMmap environment)
    (events := []) HostInterceptEncoding.syscall
    (callerLookupAt environment (linuxBeforeMmap environment) (4198440, syscall_op)
      (linuxBeforeMmapRip environment) (by simp [linuxLinkedFirstCallerIndex]))
    (linuxMmapSelected environment) (linuxMmapIntercepted environment)
    (linuxAfterMmapSafe environment)
  have p10 := ordinaryOne (environment := environment) (events := [])
    (cmp_r64_imm32_sequential .rax 0xFFFFF001)
    (callerLookupAt environment (linuxAfterMmap environment)
      (4198442, cmp_r64_imm32 .rax 0xFFFFF001) (linuxAfterMmapRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198449 (linuxAfterErrnoCmp environment) (linuxAfterErrnoCmpRip environment)
      (by decide)) (linuxAfterErrnoCmpSafe environment)
  have p11 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jae32 1265) (linuxErrnoBranchNotChosen environment)
    (callerLookupAt environment (linuxAfterErrnoCmp environment) (4198449, jae_rel32 1265)
      (linuxAfterErrnoCmpRip environment) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198455 (linuxAfterErrnoBranch environment)
      (linuxAfterErrnoBranchRip environment) (by decide)) (linuxAfterErrnoBranchSafe environment)
  have p12 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r15 .rax).sequential
    (callerLookupAt environment (linuxAfterErrnoBranch environment)
      (4198455, mov_r64 .r15 .rax) (linuxAfterErrnoBranchRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198458 (linuxAfterArenaEndMove environment) (linuxAfterArenaEndMoveRip environment)
      (by decide)) (linuxAfterArenaEndMoveSafe environment)
  have p13 := ordinaryOne (environment := environment) (events := [])
    (seqAddImm32 .r15 65536)
    (callerLookupAt environment (linuxAfterArenaEndMove environment)
      (4198458, add_r64_imm32 .r15 65536) (linuxAfterArenaEndMoveRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198465 (linuxAfterArenaEndAdd environment) (linuxAfterArenaEndAddRip environment)
      (by decide)) (linuxAfterArenaEndAddSafe environment)
  have p14 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb32 1249) (linuxArenaCarryNotChosen environment)
    (callerLookupAt environment (linuxAfterArenaEndAdd environment) (4198465, jb_rel32 1249)
      (linuxAfterArenaEndAddRip environment) (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198471 (linuxAfterArenaCarryBranch environment)
      (linuxAfterArenaCarryBranchRip environment) (by decide))
    (linuxAfterArenaCarryBranchSafe environment)
  have p15 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r11 .rax).sequential
    (callerLookupAt environment (linuxAfterArenaCarryBranch environment)
      (4198471, mov_r64 .r11 .rax) (linuxAfterArenaCarryBranchRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198474 (linuxAfterBumpInstall environment) (linuxAfterBumpInstallRip environment)
      (by decide)) (linuxAfterBumpInstallSafe environment)
  have p16 := ordinaryOne (environment := environment) (events := [])
    (seqXor32 .r10d .r10d)
    (callerLookupAt environment (linuxAfterBumpInstall environment)
      (4198474, xor_r32 .r10d .r10d) (linuxAfterBumpInstallRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198477 (linuxAfterFreeListInstall environment)
      (linuxAfterFreeListInstallRip environment) (by decide))
    (linuxAfterFreeListInstallSafe environment)
  have p17 := ordinaryOne (environment := environment) (events := []) seqStoreImmRsp30
    (callerLookupAt environment (linuxAfterFreeListInstall environment)
      (4198477, mov_mem64_disp_imm .rsp 0x30 0) (linuxAfterFreeListInstallRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198486 (linuxAfterLineCountInit environment) (linuxAfterLineCountInitRip environment)
      (by decide)) (linuxAfterLineCountInitSafe environment)
  have p18 := ordinaryOne (environment := environment) (events := []) seqStoreImmRsp38
    (callerLookupAt environment (linuxAfterLineCountInit environment)
      (4198486, mov_mem64_disp_imm .rsp 0x38 0) (linuxAfterLineCountInitRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198495 (linuxAfterHeadInit environment) (linuxAfterHeadInitRip environment)
      (by decide)) (linuxAfterHeadInitSafe environment)
  have p19 := ordinaryOne (environment := environment) (events := []) seqStoreImmRsp60
    (callerLookupAt environment (linuxAfterHeadInit environment)
      (4198495, mov_mem64_disp_imm .rsp 0x60 0) (linuxAfterHeadInitRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198504 (linuxAfterLineLengthInit environment)
      (linuxAfterLineLengthInitRip environment) (by decide))
    (linuxAfterLineLengthInitSafe environment)
  have p20 := ordinaryOne (environment := environment) (events := []) seqStoreImmRsp68
    (callerLookupAt environment (linuxAfterLineLengthInit environment)
      (4198504, mov_mem64_disp_imm .rsp 0x68 256) (linuxAfterLineLengthInitRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198513 (linuxAfterLineCapacityInit environment)
      (linuxAfterLineCapacityInitRip environment) (by decide)) (linuxCallerStoresSafe environment)
  have p21 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .ecx 512)
    (callerLookupAt environment (linuxAfterLineCapacityInit environment)
      (4198513, mov_r32 .ecx 512) (linuxAfterLineCapacityInitRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt 4198518 (linuxBeforeFirstMallocCall environment)
      (linuxBeforeFirstMallocCallRip environment) (by decide))
    (linuxBeforeFirstMallocCallSafe environment)
  have p22 := internalCallOne (environment := environment) (events := [])
    (HostInterceptEncoding.callRel32 1209)
    (callerLookupAt environment (linuxBeforeFirstMallocCall environment)
      (4198518, call_rel32 1209) (linuxBeforeFirstMallocCallRip environment)
      (by simp [linuxLinkedFirstCallerIndex]))
    (normalAt linuxConcreteMallocEntryRip (linuxFirstMallocEntry environment)
      (linuxFirstMallocEntryRip environment) (by decide)) (linuxFirstMallocEntrySafe environment)
  have q02 := SelectedPrefix.append p01 p02
  have q03 := SelectedPrefix.append q02 p03
  have q04 := SelectedPrefix.append q03 p04
  have q05 := SelectedPrefix.append q04 p05
  have q06 := SelectedPrefix.append q05 p06
  have q07 := SelectedPrefix.append q06 p07
  have q08 := SelectedPrefix.append q07 p08
  have q09 := SelectedPrefix.append q08 p09
  have q10 := SelectedPrefix.append q09 p10
  have q11 := SelectedPrefix.append q10 p11
  have q12 := SelectedPrefix.append q11 p12
  have q13 := SelectedPrefix.append q12 p13
  have q14 := SelectedPrefix.append q13 p14
  have q15 := SelectedPrefix.append q14 p15
  have q16 := SelectedPrefix.append q15 p16
  have q17 := SelectedPrefix.append q16 p17
  have q18 := SelectedPrefix.append q17 p18
  have q19 := SelectedPrefix.append q18 p19
  have q20 := SelectedPrefix.append q19 p20
  have q21 := SelectedPrefix.append q20 p21
  have q22 := SelectedPrefix.append q21 p22
  simpa using q22

private theorem linuxFirstAllocatorSelectedPath (environment : Environment)
    (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 23
      initial [] (a23 initial) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 23
      initial [] (X86_64Instruction.step ret_op (a22 initial)) [] []
  have p01 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r8 .rcx).sequential
    (mallocLookupAt environment initial (4199732, mov_r64 .r8 .rcx) h.rip
      (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199735 (a01 initial) (a01Rip initial h) (by decide))
    (a01Safe initial h)
  have p02 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .r8 7)
    (mallocLookupAt environment (a01 initial) (4199735, add_r64_imm8 .r8 7)
      (a01Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199739 (a02 initial) (a02Rip initial h) (by decide))
    (a02Safe initial h)
  have p03 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb32 113)
    (guard03 initial h)
    (mallocLookupAt environment (a02 initial) (4199739, jb_rel32 113)
      (a02Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199745 (a03 initial) (a03Rip initial h) (by decide))
    (a03Safe initial h)
  have p04 := ordinaryOne (environment := environment) (events := []) (seqAndImm8 .r8 0xF8)
    (mallocLookupAt environment (a03 initial) (4199745, and_r64_imm8 .r8 0xF8)
      (a03Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199749 (a04 initial) (a04Rip initial h) (by decide))
    (a04Safe initial h)
  have p05 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r9 .r8).sequential
    (mallocLookupAt environment (a04 initial) (4199749, mov_r64 .r9 .r8)
      (a04Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199752 (a05 initial) (a05Rip initial h) (by decide))
    (a05Safe initial h)
  have p06 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .r9 32)
    (mallocLookupAt environment (a05 initial) (4199752, add_r64_imm8 .r9 32)
      (a05Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199756 (a06 initial) (a06Rip initial h) (by decide))
    (a06Safe initial h)
  have p07 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb32 96)
    (guard07 initial h)
    (mallocLookupAt environment (a06 initial) (4199756, jb_rel32 96)
      (a06Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199762 (a07 initial) (a07Rip initial h) (by decide))
    (a07Safe initial h)
  have p08 := ordinaryOne (environment := environment) (events := []) (seqCmpImm8 .r10 0)
    (mallocLookupAt environment (a07 initial) (4199762, cmp_r64_imm8 .r10 0)
      (a07Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199766 (a08 initial) (a08Rip initial h) (by decide))
    (a08Safe initial h)
  have p09 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jne8 0x36)
    (guard09 initial h)
    (mallocLookupAt environment (a08 initial) (4199766, jne_rel8 0x36)
      (a08Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199768 (a09 initial) (a09Rip initial h) (by decide))
    (a09Safe initial h)
  have p10 := ordinaryOne (environment := environment) (events := []) (seqCmp .r11 .r15)
    (mallocLookupAt environment (a09 initial) (4199768, cmp_r64 .r11 .r15)
      (a09Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199771 (a10 initial) (a10Rip initial h) (by decide))
    (a10Safe initial h)
  have p11 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.ja8 0x55)
    (guard11 initial h)
    (mallocLookupAt environment (a10 initial) (4199771, ja_rel8 0x55)
      (a10Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199773 (a11 initial) (a11Rip initial h) (by decide))
    (a11Safe initial h)
  have p12 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .rax .r15).sequential
    (mallocLookupAt environment (a11 initial) (4199773, mov_r64 .rax .r15)
      (a11Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199776 (a12 initial) (a12Rip initial h) (by decide))
    (a12Safe initial h)
  have p13 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.sub .rax .r11).sequential
    (mallocLookupAt environment (a12 initial) (4199776, sub_r64 .rax .r11)
      (a12Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199779 (a13 initial) (a13Rip initial h) (by decide))
    (a13Safe initial h)
  have p14 := ordinaryOne (environment := environment) (events := []) (seqCmp .rax .r9)
    (mallocLookupAt environment (a13 initial) (4199779, cmp_r64 .rax .r9)
      (a13Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199782 (a14 initial) (a14Rip initial h) (by decide))
    (a14Safe initial h)
  have p15 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb8 0x4A)
    (guard15 initial h)
    (mallocLookupAt environment (a14 initial) (4199782, jb_rel8 0x4A)
      (a14Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199784 (a15 initial) (a15Rip initial h) (by decide))
    (a15Safe initial h)
  have p16 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .rax .r11).sequential
    (mallocLookupAt environment (a15 initial) (4199784, mov_r64 .rax .r11)
      (a15Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199787 (a16 initial) (a16Rip initial h) (by decide))
    (a16Safe initial h)
  have p17 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.add .r11 .r9).sequential
    (mallocLookupAt environment (a16 initial) (4199787, add_r64 .r11 .r9)
      (a16Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199790 (a17 initial) (a17Rip initial h) (by decide))
    (a17Safe initial h)
  have p18 := ordinaryOne (environment := environment) (events := []) seqStoreRaxR8
    (mallocLookupAt environment (a17 initial) (4199790, mov_mem64_disp .rax 0 .r8)
      (a17Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199793 (a18 initial) (a18Rip initial h) (by decide))
    (a18Safe initial h)
  have p19 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax08
    (mallocLookupAt environment (a18 initial) (4199793, mov_mem64_disp_imm .rax 0x08 0)
      (a18Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199801 (a19 initial) (a19Rip initial h) (by decide))
    (a19Safe initial h)
  have p20 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax10
    (mallocLookupAt environment (a19 initial) (4199801, mov_mem64_disp_imm .rax 0x10 8)
      (a19Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199809 (a20 initial) (a20Rip initial h) (by decide))
    (a20Safe initial h)
  have p21 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax18
    (mallocLookupAt environment (a20 initial) (4199809, mov_mem64_disp_imm .rax 0x18 0)
      (a20Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199817 (a21 initial) (a21Rip initial h) (by decide))
    (a21Safe initial h)
  have p22 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .rax 32)
    (mallocLookupAt environment (a21 initial) (4199817, add_r64_imm8 .rax 32)
      (a21Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199821 (a22 initial) (a22Rip initial h) (by decide))
    (a22Safe initial h)
  have p23 := nearReturnOne (environment := environment) (events := []) ReturnEncoding.near
    (mallocLookupAt environment (a22 initial) (4199821, ret_op)
      (a22Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt linuxFirstMallocReturnRip (a23 initial) (a23Rip initial h) (by decide))
    (a23Safe initial h)
  have q02 := SelectedPrefix.append p01 p02
  have q03 := SelectedPrefix.append q02 p03
  have q04 := SelectedPrefix.append q03 p04
  have q05 := SelectedPrefix.append q04 p05
  have q06 := SelectedPrefix.append q05 p06
  have q07 := SelectedPrefix.append q06 p07
  have q08 := SelectedPrefix.append q07 p08
  have q09 := SelectedPrefix.append q08 p09
  have q10 := SelectedPrefix.append q09 p10
  have q11 := SelectedPrefix.append q10 p11
  have q12 := SelectedPrefix.append q11 p12
  have q13 := SelectedPrefix.append q12 p13
  have q14 := SelectedPrefix.append q13 p14
  have q15 := SelectedPrefix.append q14 p15
  have q16 := SelectedPrefix.append q15 p16
  have q17 := SelectedPrefix.append q16 p17
  have q18 := SelectedPrefix.append q17 p18
  have q19 := SelectedPrefix.append q18 p19
  have q20 := SelectedPrefix.append q19 p20
  have q21 := SelectedPrefix.append q20 p21
  have q22 := SelectedPrefix.append q21 p22
  have q23 := SelectedPrefix.append q22 p23
  simpa using q23

private theorem linuxFirstFreshEntry (environment : Environment) :
    FreshEntryConditions (linuxFirstMallocEntry environment) where
  rip := by simpa [linuxConcreteMallocEntryRip] using linuxFirstMallocEntryRip environment
  request := linuxFirstMallocEntryRcx environment
  freeHead := linuxFirstMallocEntryR10 environment
  bump := linuxFirstMallocEntryR11 environment
  arenaEnd := linuxFirstMallocEntryR15 environment
  stackAddress := linuxFirstMallocEntryRsp environment
  returnSlot := linuxFirstMallocCallerSlot environment
  safe := linuxFirstMallocEntrySafe environment

private theorem a21Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a21 initial).gprs .rax = spike3ConcreteLinuxArena.base := by
  change (a17 initial).gprs .rax = spike3ConcreteLinuxArena.base
  exact a17Rax initial h

private theorem a22Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a22 initial).gprs .rax = spike3ConcreteLinuxArena.base + 32 := by
  change (a21 initial).gprs .rax + signExtend8To64 32 = _
  rw [a21Rax initial h]
  rw [show signExtend8To64 32 = 32 by decide]

private theorem a22R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a22 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  change (a17 initial).gprs .r11 = _
  exact a17R11 initial h

private theorem a22R10 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a22 initial).gprs .r10 = 0 := by
  change (a17 initial).gprs .r10 = 0
  exact a17R10 initial h

private theorem a23Rax (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).gprs .rax = spike3ConcreteLinuxArena.base + 32 := by
  rw [a23, ret_op_step_gpr_other _ .rax (by decide)]
  exact a22Rax initial h

private theorem a23R11 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  rw [a23, ret_op_step_gpr_other _ .r11 (by decide)]
  exact a22R11 initial h

private theorem a23R10 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).gprs .r10 = 0 := by
  rw [a23, ret_op_step_gpr_other _ .r10 (by decide)]
  exact a22R10 initial h

private theorem a23Memory (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).memory = (a21 initial).memory := by
  rw [a23, ret_op_step_memory, a22Memory initial h]

private theorem a23StackRestored (environment : Environment) :
    (a23 (linuxFirstMallocEntry environment)).rsp =
      (linuxBeforeFirstMallocCall environment).rsp := by
  rw [a23, ret_op_step_rsp, a22Rsp,
    linuxFirstMallocEntryRsp, linuxBeforeFirstMallocCallRsp]
  rfl

private theorem a23SizeHeader (initial : X86_64MachineState)
    (h : FreshEntryConditions initial) :
    X86_64Mem.read .w64 spike3ConcreteLinuxArena.base (a23 initial).memory = 512 := by
  rw [a23Memory initial h, a21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]
  simpa using le_bytes_reassemble (512 : UInt64)

private theorem a23FreeHeader (initial : X86_64MachineState)
    (h : FreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 8) (a23 initial).memory = 0 := by
  rw [a23Memory initial h, a21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem a23AlignmentHeader (initial : X86_64MachineState)
    (h : FreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 16) (a23 initial).memory = 8 := by
  rw [a23Memory initial h, a21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]
  simpa using le_bytes_reassemble (8 : UInt64)

private theorem a23NextFreeHeader (initial : X86_64MachineState)
    (h : FreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 24) (a23 initial).memory = 0 := by
  rw [a23Memory initial h, a21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write,
    X86_64Mem.readByte]

private theorem linuxFirstAllocatorInitialFrame (environment : Environment) :
    NativeAllocatorInitialFrame spike3ConcreteLinuxArena
      (linuxFirstAllocatorBefore environment) where
  bumpAtArenaBase := rfl
  freeListEmpty := rfl

private theorem linuxFirstAllocatorBeforeProjectsEntry (environment : Environment) :
    (linuxFirstAllocatorBefore environment).bump =
        (linuxFirstMallocEntry environment).gprs .r11 ∧
      (linuxFirstAllocatorBefore environment).freeHead =
        (linuxFirstMallocEntry environment).gprs .r10 := by
  constructor
  · rw [linuxFirstAllocatorBefore, linuxFirstMallocEntryR11]
  · rw [linuxFirstAllocatorBefore, linuxFirstMallocEntryR10]

private theorem linuxFirstFreshDecision (environment : Environment) :
    ∃ logicalAfter,
      smolFreshAllocation 512 spike3ConcreteLinuxArena
        (linuxFirstAllocatorBefore environment) = some logicalAfter ∧
      logicalAfter.bump = spike3ConcreteLinuxArena.base + 544 ∧
      logicalAfter.freeHead = 0 := by
  let logicalAfter : SmolAllocatorFrame :=
    { bump := spike3ConcreteLinuxArena.base + 544
      freeHead := 0
      memory := (linuxFirstAllocatorBefore environment).memory }
  refine ⟨logicalAfter, ?_, rfl, rfl⟩
  unfold smolFreshAllocation
  rw [if_neg (by decide)]
  rw [show (512 + 7 : UInt64) &&& 0xFFFFFFFFFFFFFFF8 = 512 by decide]
  rw [if_neg (by decide)]
  simp [NativeArenaCapability.allocateFresh, linuxFirstAllocatorBefore,
    spike3ConcreteLinuxArena, logicalAfter]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Projection-limited canonical result of the exact selected fresh-allocation block.
    Intermediate registers and guard states do not escape this type. -/
structure LinuxFirstFreshMallocCertificate (environment : Environment) where
  finalFrame : SmolAllocatorFrame
  resultPointer : UInt64
  returnState : X86_64MachineState
  returnEvents : List AnyEvent
  fuel : Nat

/-- The canonical successful first-allocation value exposes the persistent frame, payload pointer,
    return continuation, events, and fuel. -/
def linuxFirstFreshMallocCertificate (environment : Environment) :
    LinuxFirstFreshMallocCertificate environment :=
  let initial := linuxFirstMallocEntry environment
  { finalFrame :=
      { bump := spike3ConcreteLinuxArena.base + 544
        freeHead := 0
        memory := (a23 initial).memory }
    resultPointer := spike3ConcreteLinuxArena.base + 32
    returnState := a23 initial
    returnEvents := []
    fuel := 23 }

/-- Private evidence behind the projection-limited result record.  Keeping this type private prevents every
    alignment/capacity join and transient allocator register from becoming public API. -/
private structure LinuxFirstFreshMallocEvidence (environment : Environment)
    (certificate : LinuxFirstFreshMallocCertificate environment) : Prop where
  initialFrame : NativeAllocatorInitialFrame spike3ConcreteLinuxArena
    (linuxFirstAllocatorBefore environment)
  freshDecision : ∃ logicalAfter,
    smolFreshAllocation 512 spike3ConcreteLinuxArena (linuxFirstAllocatorBefore environment) =
      some logicalAfter ∧
    logicalAfter.bump = certificate.finalFrame.bump ∧
      logicalAfter.freeHead = certificate.finalFrame.freeHead
  callerReturnSlot : (linuxFirstMallocEntry environment).read64
    (linuxFirstMallocEntry environment).rsp = linuxFirstMallocReturnRip
  selectedPath : NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
    certificate.fuel (linuxFirstMallocEntry environment) [] certificate.returnState
    certificate.returnEvents []
  resultProjected : certificate.returnState.gprs .rax = certificate.resultPointer
  bumpProjected : certificate.returnState.gprs .r11 = certificate.finalFrame.bump
  freeListProjected : certificate.returnState.gprs .r10 = certificate.finalFrame.freeHead
  memoryProjected : certificate.returnState.memory = certificate.finalFrame.memory
  returnedToCaller : certificate.returnState.rip = linuxFirstMallocReturnRip
  stackRestored : certificate.returnState.rsp = (linuxBeforeFirstMallocCall environment).rsp
  eventsPreserved : certificate.returnEvents = []
  sizeHeader : X86_64Mem.read .w64 spike3ConcreteLinuxArena.base
    certificate.finalFrame.memory = 512
  freeHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 8)
    certificate.finalFrame.memory = 0
  alignmentHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 16)
    certificate.finalFrame.memory = 8
  nextFreeHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 24)
    certificate.finalFrame.memory = 0

private theorem linuxFirstFreshMallocEvidence (environment : Environment) :
    LinuxFirstFreshMallocEvidence environment (linuxFirstFreshMallocCertificate environment) := by
  let initial := linuxFirstMallocEntry environment
  let conditions := linuxFirstFreshEntry environment
  refine {
    initialFrame := linuxFirstAllocatorInitialFrame environment
    freshDecision := by
      rcases linuxFirstFreshDecision environment with ⟨logicalAfter, decision, bump, free⟩
      exact ⟨logicalAfter, decision, by simpa [linuxFirstFreshMallocCertificate] using bump,
        by simpa [linuxFirstFreshMallocCertificate] using free⟩
    callerReturnSlot := linuxFirstMallocCallerSlot environment
    selectedPath := by
      simpa [linuxFirstFreshMallocCertificate, initial] using
        linuxFirstAllocatorSelectedPath environment initial conditions
    resultProjected := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23Rax initial conditions
    bumpProjected := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23R11 initial conditions
    freeListProjected := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23R10 initial conditions
    memoryProjected := by simp [linuxFirstFreshMallocCertificate]
    returnedToCaller := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23Rip initial conditions
    stackRestored := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23StackRestored environment
    eventsPreserved := rfl
    sizeHeader := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23SizeHeader initial conditions
    freeHeader := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23FreeHeader initial conditions
    alignmentHeader := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23AlignmentHeader initial conditions
    nextFreeHeader := by
      simpa [linuxFirstFreshMallocCertificate, initial] using a23NextFreeHeader initial conditions }

/-- Exact selected allocator block carried by the projection-limited result record. -/
theorem linuxFirstFreshMallocCertificate_selectedPath (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
      (linuxFirstFreshMallocCertificate environment).fuel
      (linuxFirstMallocEntry environment) []
      (linuxFirstFreshMallocCertificate environment).returnState
      (linuxFirstFreshMallocCertificate environment).returnEvents [] :=
  (linuxFirstFreshMallocEvidence environment).selectedPath

/-- Persistent/result projection of the canonical allocator result. -/
theorem linuxFirstFreshMallocCertificate_projection (environment : Environment) :
    let certificate := linuxFirstFreshMallocCertificate environment
    certificate.returnState.gprs .rax = certificate.resultPointer ∧
      certificate.returnState.gprs .r11 = certificate.finalFrame.bump ∧
      certificate.returnState.gprs .r10 = certificate.finalFrame.freeHead ∧
      certificate.returnState.memory = certificate.finalFrame.memory ∧
      certificate.returnState.rip = linuxFirstMallocReturnRip ∧
      certificate.returnState.rsp = (linuxBeforeFirstMallocCall environment).rsp ∧
      certificate.returnEvents = [] := by
  let evidence := linuxFirstFreshMallocEvidence environment
  exact ⟨evidence.resultProjected, evidence.bumpProjected, evidence.freeListProjected,
    evidence.memoryProjected, evidence.returnedToCaller, evidence.stackRestored,
    evidence.eventsPreserved⟩

/-- Exact caller return slot accepted by the allocator block. -/
theorem linuxFirstFreshMallocCertificate_exactCallerReturnSlot (environment : Environment) :
    (linuxFirstMallocEntry environment).read64 (linuxFirstMallocEntry environment).rsp =
      linuxFirstMallocReturnRip :=
  (linuxFirstFreshMallocEvidence environment).callerReturnSlot

/-- The four emitted allocator stores are observable only as their persistent final headers. -/
theorem linuxFirstFreshMallocCertificate_headers (environment : Environment) :
    let certificate := linuxFirstFreshMallocCertificate environment
    X86_64Mem.read .w64 spike3ConcreteLinuxArena.base certificate.finalFrame.memory = 512 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 8)
        certificate.finalFrame.memory = 0 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 16)
        certificate.finalFrame.memory = 8 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 24)
        certificate.finalFrame.memory = 0 := by
  let evidence := linuxFirstFreshMallocEvidence environment
  exact ⟨evidence.sizeHeader, evidence.freeHeader, evidence.alignmentHeader,
    evidence.nextFreeHeader⟩

/-- The logical and physical fresh paths agree on persistent bump/free-list control state. -/
theorem linuxFirstFreshMallocCertificate_freshDecision (environment : Environment) :
    ∃ logicalAfter,
      smolFreshAllocation 512 spike3ConcreteLinuxArena
        (linuxFirstAllocatorBefore environment) = some logicalAfter ∧
      logicalAfter.bump = (linuxFirstFreshMallocCertificate environment).finalFrame.bump ∧
      logicalAfter.freeHead =
        (linuxFirstFreshMallocCertificate environment).finalFrame.freeHead :=
  (linuxFirstFreshMallocEvidence environment).freshDecision

/-- The first concrete Linux prologue, admitted `mmap`, allocator call, successful fresh block,
    and hardware return form one exact 45-step spine in the selected linked artifact. -/
theorem linuxFirstMallocCallReturnSpine (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 45
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstFreshMallocCertificate environment).returnState
      (linuxFirstFreshMallocCertificate environment).returnEvents [] := by
  let initial := linuxFirstMallocEntry environment
  let conditions := linuxFirstFreshEntry environment
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 45
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (a23 initial) [] []
  have caller := linuxFirstMallocCallerSelectedPath environment
  have allocator := linuxFirstAllocatorSelectedPath environment initial conditions
  have spine := SelectedPrefix.append caller allocator
  simpa using spine

/-! ## Second fresh allocation and the first read boundary -/

def linuxSecondMallocReturnRip : UInt64 := 4198548

private def linuxCallerThroughReadIndex : List (UInt64 × X86_64Instr) := [
    (4198523, cmp_r64_imm8 .rax 0),
    (4198527, je_rel32 1187),
    (4198533, mov_mem64_disp .rsp 0x50 .rax),
    (4198538, mov_r32 .ecx 256),
    (4198543, call_rel32 1184),
    (4198548, cmp_r64_imm8 .rax 0),
    (4198552, je_rel32 1162),
    (4198558, mov_mem64_disp .rsp 0x58 .rax),
    (4198563, xor_r32 .edi .edi),
    (4198565, mov_reg64_mem64_disp .rsi .rsp 0x50),
    (4198570, mov_r32 .edx 512),
    (4198575, mov_r32 .eax 0),
    (4198580, mov_mem64_disp .rsp 0x40 .r11),
    (4198585, mov_mem64_disp .rsp 0x48 .r10),
    (4198590, syscall_op),
    (4198592, mov_reg64_mem64_disp .r11 .rsp 0x40),
    (4198597, mov_reg64_mem64_disp .r10 .rsp 0x48),
    (4198602, mov_mem64_disp .rsp 0x28 .rax),
    (4198607, cmp_r64_imm8 .rax 0),
    (4198611, jle_rel32 420)
  ]

set_option maxHeartbeats 1000000 in
private theorem linuxCallerThroughReadIndexExact :
    (spike3NoGrantResourceArtifactIndex.drop 22).take 20 = linuxCallerThroughReadIndex := by
  rfl

private theorem callerThroughReadIndexedLookup (environment : Environment)
    (entry : UInt64 × X86_64Instr) (member : entry ∈ linuxCallerThroughReadIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) entry.1 =
        some entry.2 := by
  rw [linuxConcreteIndexIdentity environment]
  apply spike3NoGrantResourceArtifactLayout.resolves
  apply List.mem_of_mem_drop
  apply List.mem_of_mem_take
  rw [linuxCallerThroughReadIndexExact]
  exact member

private theorem callerThroughReadLookupAt (environment : Environment)
    (state : X86_64MachineState) (entry : UInt64 × X86_64Instr)
    (ripExact : state.rip = entry.1) (member : entry ∈ linuxCallerThroughReadIndex) :
    instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some entry.2 := by
  rw [ripExact]
  exact callerThroughReadIndexedLookup environment entry member

private def secondCaller00 (environment : Environment) : X86_64MachineState :=
  (linuxFirstFreshMallocCertificate environment).returnState
private def secondCaller01 (environment : Environment) :=
  X86_64Instruction.step (cmp_r64_imm8 .rax 0) (secondCaller00 environment)
private def secondCaller02 (environment : Environment) :=
  X86_64Instruction.step (je_rel32 1187) (secondCaller01 environment)
private def secondCaller03 (environment : Environment) :=
  X86_64Instruction.step (mov_mem64_disp .rsp 0x50 .rax) (secondCaller02 environment)
private def secondCaller04 (environment : Environment) :=
  X86_64Instruction.step (mov_r32 .ecx 256) (secondCaller03 environment)
def linuxSecondMallocEntry (environment : Environment) :=
  X86_64Instruction.step (call_rel32 1184) (secondCaller04 environment)

private theorem secondCaller00Rip (environment : Environment) :
    (secondCaller00 environment).rip = 4198523 := by
  exact (linuxFirstFreshMallocEvidence environment).returnedToCaller

private theorem secondCaller00Safe (environment : Environment) :
    (secondCaller00 environment).fault = none := by
  exact a23Safe (linuxFirstMallocEntry environment) (linuxFirstFreshEntry environment)

private theorem secondCaller00Rax (environment : Environment) :
    (secondCaller00 environment).gprs .rax = spike3ConcreteLinuxArena.base + 32 := by
  exact (linuxFirstFreshMallocEvidence environment).resultProjected

private theorem secondCaller00R10 (environment : Environment) :
    (secondCaller00 environment).gprs .r10 = 0 := by
  exact (linuxFirstFreshMallocEvidence environment).freeListProjected

private theorem secondCaller00R11 (environment : Environment) :
    (secondCaller00 environment).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  exact (linuxFirstFreshMallocEvidence environment).bumpProjected

private theorem a23R15 (initial : X86_64MachineState) (h : FreshEntryConditions initial) :
    (a23 initial).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  change initial.gprs .r15 = spike3ConcreteLinuxArena.endExclusive
  exact h.arenaEnd

private theorem secondCaller00R15 (environment : Environment) :
    (secondCaller00 environment).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  exact a23R15 (linuxFirstMallocEntry environment) (linuxFirstFreshEntry environment)

private theorem secondCaller00Rsp (environment : Environment) :
    (secondCaller00 environment).rsp = 0x7FFFFFFEFF88 := by
  calc
    (secondCaller00 environment).rsp = (linuxBeforeFirstMallocCall environment).rsp :=
      (linuxFirstFreshMallocEvidence environment).stackRestored
    _ = 0x7FFFFFFEFF88 := linuxBeforeFirstMallocCallRsp environment

private theorem cmpImm8RaxZeroZfOfNe (state : X86_64MachineState)
    (nonzero : state.gprs .rax ≠ 0) :
    (X86_64Instruction.step (cmp_r64_imm8 .rax 0) state).zf = false := by
  change (state.setFlagsCmp64 (state.gprs .rax) 0).zf = false
  apply X86_64MachineState.setFlagsCmp64_zf_of_ne
  exact nonzero

private theorem secondCaller01Zf (environment : Environment) :
    (secondCaller01 environment).zf = false := by
  apply cmpImm8RaxZeroZfOfNe
  rw [secondCaller00Rax]
  decide

private theorem secondCaller01Safe (environment : Environment) :
    (secondCaller01 environment).fault = none :=
  cmpImm8Safe .rax 0 _ (secondCaller00Safe environment)

private theorem secondCaller01Rip (environment : Environment) :
    (secondCaller01 environment).rip = 4198527 := by
  rw [secondCaller01, (seqCmpImm8 .rax 0).step_rip_eq_of_safe _
    (secondCaller01Safe environment), secondCaller00Rip]
  rfl

private theorem firstSuccessBranchNotChosen (environment : Environment) :
    ¬ X86BranchCondition.equal.holds (secondCaller01 environment) := by
  simp [X86BranchCondition.holds, secondCaller01Zf environment]

private theorem secondCaller02Safe (environment : Environment) :
    (secondCaller02 environment).fault = none := by
  rw [secondCaller02, (ConditionalJumpEncoding.je32 1187).step_fault_eq,
    secondCaller01Safe]

private theorem secondCaller02Rip (environment : Environment) :
    (secondCaller02 environment).rip = 4198533 := by
  rw [secondCaller02, (ConditionalJumpEncoding.je32 1187).step_rip_eq_fallthrough _
    (firstSuccessBranchNotChosen environment), secondCaller01Rip]
  rfl

private theorem storeStepFault (base : Reg64) (disp : UInt8) (src : Reg64)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_mem64_disp base disp src) state).fault = state.fault := by
  cases base <;> cases src <;> rfl

private theorem storeStepGpr (base : Reg64) (disp : UInt8) (src : Reg64)
    (state : X86_64MachineState) (register : Reg64) :
    (X86_64Instruction.step (mov_mem64_disp base disp src) state).gprs register =
      state.gprs register := by
  cases base <;> cases src <;> cases register <;> rfl

private theorem storeStepRsp (base : Reg64) (disp : UInt8) (src : Reg64)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_mem64_disp base disp src) state).rsp = state.rsp := by
  cases base <;> cases src <;> rfl

private theorem cmpImm8StepGprAny (dst : Reg64) (value : UInt8)
    (state : X86_64MachineState) (register : Reg64) :
    (X86_64Instruction.step (cmp_r64_imm8 dst value) state).gprs register =
      state.gprs register := by
  cases dst <;> cases register <;> rfl

private theorem cmpImm8StepRsp (dst : Reg64) (value : UInt8)
    (state : X86_64MachineState) :
    (X86_64Instruction.step (cmp_r64_imm8 dst value) state).rsp = state.rsp := by
  cases dst <;> rfl

private theorem conditionalStepRsp {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind) (state : X86_64MachineState) :
    (X86_64Instruction.step instruction state).rsp = state.rsp := by
  exact conditionalStepGpr encoding state .rsp

private theorem mov32EcxStepRsp (value : UInt32) (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_r32 .ecx value) state).rsp = state.rsp := by rfl

private theorem seqStoreRsp50Rax :
    SequentialInstruction (mov_mem64_disp .rsp 0x50 .rax) where
  encoding := .movMem64Disp .rsp 0x50 .rax
  safeFallthrough := by intro state _; rfl

private theorem secondCaller03Safe (environment : Environment) :
    (secondCaller03 environment).fault = none := by
  rw [secondCaller03, storeStepFault, secondCaller02Safe]

private theorem secondCaller03Rip (environment : Environment) :
    (secondCaller03 environment).rip = 4198538 := by
  rw [secondCaller03, seqStoreRsp50Rax.step_rip_eq_of_safe _
    (secondCaller03Safe environment), secondCaller02Rip]
  rfl

private theorem secondCaller03R10 (environment : Environment) :
    (secondCaller03 environment).gprs .r10 = 0 := by
  rw [secondCaller03, storeStepGpr, secondCaller02]
  rw [conditionalStepGpr (ConditionalJumpEncoding.je32 1187), secondCaller01]
  rw [cmpImm8StepGprAny]
  exact secondCaller00R10 environment

private theorem secondCaller03R11 (environment : Environment) :
    (secondCaller03 environment).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  rw [secondCaller03, storeStepGpr, secondCaller02]
  rw [conditionalStepGpr (ConditionalJumpEncoding.je32 1187), secondCaller01]
  rw [cmpImm8StepGprAny]
  exact secondCaller00R11 environment

private theorem secondCaller03R15 (environment : Environment) :
    (secondCaller03 environment).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  rw [secondCaller03, storeStepGpr, secondCaller02]
  rw [conditionalStepGpr (ConditionalJumpEncoding.je32 1187), secondCaller01]
  rw [cmpImm8StepGprAny]
  exact secondCaller00R15 environment

private theorem secondCaller03Rsp (environment : Environment) :
    (secondCaller03 environment).rsp = 0x7FFFFFFEFF88 := by
  rw [secondCaller03, storeStepRsp, secondCaller02,
    conditionalStepRsp (ConditionalJumpEncoding.je32 1187), secondCaller01,
    cmpImm8StepRsp]
  exact secondCaller00Rsp environment

private theorem secondCaller04Safe (environment : Environment) :
    (secondCaller04 environment).fault = none := by
  rw [secondCaller04, mov32StepFault, secondCaller03Safe]

private theorem secondCaller04Rip (environment : Environment) :
    (secondCaller04 environment).rip = 4198543 := by
  rw [secondCaller04, (mov_r32_sequential .ecx 256).step_rip_eq_of_safe _
    (secondCaller04Safe environment), secondCaller03Rip]
  rfl

private theorem secondCaller04Rsp (environment : Environment) :
    (secondCaller04 environment).rsp = 0x7FFFFFFEFF88 := by
  rw [secondCaller04, mov32EcxStepRsp]
  exact secondCaller03Rsp environment

private theorem linuxSecondMallocEntrySafe (environment : Environment) :
    (linuxSecondMallocEntry environment).fault = none := by
  rw [linuxSecondMallocEntry, callRel32StepFault, secondCaller04Safe]

private theorem linuxSecondMallocEntryRip (environment : Environment) :
    (linuxSecondMallocEntry environment).rip = 4199732 := by
  change (secondCaller04 environment).rip + 5 + signExtend32To64 1184 = _
  rw [secondCaller04Rip]
  rfl

private theorem linuxSecondMallocEntryRsp (environment : Environment) :
    (linuxSecondMallocEntry environment).rsp = 0x7FFFFFFEFF80 := by
  rw [linuxSecondMallocEntry, call_rel32_step_rsp]
  rw [secondCaller04Rsp]
  rfl

private theorem linuxSecondMallocEntryRcx (environment : Environment) :
    (linuxSecondMallocEntry environment).gprs .rcx = 256 := by
  rw [linuxSecondMallocEntry, callRel32StepGpr 1184 _ .rcx (by decide), secondCaller04]
  change (256 : UInt32).toUInt64 = 256
  rfl

private theorem linuxSecondMallocEntryR10 (environment : Environment) :
    (linuxSecondMallocEntry environment).gprs .r10 = 0 := by
  rw [linuxSecondMallocEntry, callRel32StepGpr 1184 _ .r10 (by decide), secondCaller04,
    mov32StepGprOther .ecx 256 _ .r10 (by decide)]
  exact secondCaller03R10 environment

private theorem linuxSecondMallocEntryR11 (environment : Environment) :
    (linuxSecondMallocEntry environment).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  rw [linuxSecondMallocEntry, callRel32StepGpr 1184 _ .r11 (by decide), secondCaller04,
    mov32StepGprOther .ecx 256 _ .r11 (by decide)]
  exact secondCaller03R11 environment

private theorem linuxSecondMallocEntryR15 (environment : Environment) :
    (linuxSecondMallocEntry environment).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  rw [linuxSecondMallocEntry, callRel32StepGpr 1184 _ .r15 (by decide), secondCaller04,
    mov32StepGprOther .ecx 256 _ .r15 (by decide)]
  exact secondCaller03R15 environment

private theorem linuxSecondMallocCallerSlot (environment : Environment) :
    (linuxSecondMallocEntry environment).read64 (linuxSecondMallocEntry environment).rsp =
      linuxSecondMallocReturnRip := by
  rw [linuxSecondMallocEntry, call_rel32_step_return_slot, secondCaller04Rip]
  rfl

private structure SecondFreshEntryConditions (initial : X86_64MachineState) : Prop where
  rip : initial.rip = 4199732
  request : initial.gprs .rcx = 256
  freeHead : initial.gprs .r10 = 0
  bump : initial.gprs .r11 = spike3ConcreteLinuxArena.base + 544
  arenaEnd : initial.gprs .r15 = spike3ConcreteLinuxArena.endExclusive
  stackAddress : initial.rsp = 0x7FFFFFFEFF80
  returnSlot : initial.read64 initial.rsp = linuxSecondMallocReturnRip
  safe : initial.fault = none

private theorem linuxSecondFreshEntry (environment : Environment) :
    SecondFreshEntryConditions (linuxSecondMallocEntry environment) where
  rip := linuxSecondMallocEntryRip environment
  request := linuxSecondMallocEntryRcx environment
  freeHead := linuxSecondMallocEntryR10 environment
  bump := linuxSecondMallocEntryR11 environment
  arenaEnd := linuxSecondMallocEntryR15 environment
  stackAddress := linuxSecondMallocEntryRsp environment
  returnSlot := linuxSecondMallocCallerSlot environment
  safe := linuxSecondMallocEntrySafe environment

private theorem sA01Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a01 initial).fault = none := ordinarySafe (.mov .r8 .rcx) initial h.safe
private theorem sA02Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a02 initial).fault = none := addImm8Safe .r8 7 _ (sA01Safe initial h)
private theorem sA03Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a03 initial).fault = none := by
  rw [a03, (ConditionalJumpEncoding.jb32 113).step_fault_eq, sA02Safe initial h]
private theorem sA04Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a04 initial).fault = none := andImm8Safe .r8 0xF8 _ (sA03Safe initial h)
private theorem sA05Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a05 initial).fault = none := ordinarySafe (.mov .r9 .r8) _ (sA04Safe initial h)
private theorem sA06Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a06 initial).fault = none := addImm8Safe .r9 32 _ (sA05Safe initial h)
private theorem sA07Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a07 initial).fault = none := by
  rw [a07, (ConditionalJumpEncoding.jb32 96).step_fault_eq, sA06Safe initial h]
private theorem sA08Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a08 initial).fault = none := cmpImm8Safe .r10 0 _ (sA07Safe initial h)
private theorem sA09Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a09 initial).fault = none := by
  rw [a09, (ConditionalJumpEncoding.jne8 0x36).step_fault_eq, sA08Safe initial h]
private theorem sA10Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a10 initial).fault = none := cmpSafe .r11 .r15 _ (sA09Safe initial h)
private theorem sA11Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a11 initial).fault = none := by
  rw [a11, (ConditionalJumpEncoding.ja8 0x55).step_fault_eq, sA10Safe initial h]
private theorem sA12Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a12 initial).fault = none := ordinarySafe (.mov .rax .r15) _ (sA11Safe initial h)
private theorem sA13Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a13 initial).fault = none := ordinarySafe (.sub .rax .r11) _ (sA12Safe initial h)
private theorem sA14Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a14 initial).fault = none := cmpSafe .rax .r9 _ (sA13Safe initial h)
private theorem sA15Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a15 initial).fault = none := by
  rw [a15, (ConditionalJumpEncoding.jb8 0x4A).step_fault_eq, sA14Safe initial h]
private theorem sA16Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a16 initial).fault = none := ordinarySafe (.mov .rax .r11) _ (sA15Safe initial h)
private theorem sA17Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a17 initial).fault = none := ordinarySafe (.add .r11 .r9) _ (sA16Safe initial h)
private theorem sA18Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a18 initial).fault = none := storeRaxR8Safe _ (sA17Safe initial h)
private theorem sA19Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a19 initial).fault = none := storeImmRaxSafe 0x08 0 _ (sA18Safe initial h)
private theorem sA20Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a20 initial).fault = none := storeImmRaxSafe 0x10 8 _ (sA19Safe initial h)
private theorem sA21Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a21 initial).fault = none := storeImmRaxSafe 0x18 0 _ (sA20Safe initial h)
private theorem sA22Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a22 initial).fault = none := addImm8Safe .rax 32 _ (sA21Safe initial h)
private theorem sA23Safe (initial) (h : SecondFreshEntryConditions initial) :
    (a23 initial).fault = none := by change (a22 initial).fault = none; exact sA22Safe initial h

private theorem sA01R8 (initial) (h : SecondFreshEntryConditions initial) :
    (a01 initial).gprs .r8 = 256 := by change initial.gprs .rcx = 256; exact h.request
private theorem sA02R8 (initial) (h : SecondFreshEntryConditions initial) :
    (a02 initial).gprs .r8 = 263 := by
  change (a01 initial).gprs .r8 + 7 = 263
  rw [sA01R8 initial h]
  decide
private theorem sA04R8 (initial) (h : SecondFreshEntryConditions initial) :
    (a04 initial).gprs .r8 = 256 := by
  change (a02 initial).gprs .r8 &&& signExtend8To64 0xF8 = 256
  rw [sA02R8 initial h]
  rfl
private theorem sA05R9 (initial) (h : SecondFreshEntryConditions initial) :
    (a05 initial).gprs .r9 = 256 := by change (a04 initial).gprs .r8 = 256; exact sA04R8 initial h
private theorem sA06R9 (initial) (h : SecondFreshEntryConditions initial) :
    (a06 initial).gprs .r9 = 288 := by
  change (a05 initial).gprs .r9 + 32 = 288
  rw [sA05R9 initial h]
  decide
private theorem sA07R10 (initial) (h : SecondFreshEntryConditions initial) :
    (a07 initial).gprs .r10 = 0 := by change initial.gprs .r10 = 0; exact h.freeHead
private theorem sA09R11 (initial) (h : SecondFreshEntryConditions initial) :
    (a09 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  change initial.gprs .r11 = _
  exact h.bump
private theorem sA09R15 (initial) (h : SecondFreshEntryConditions initial) :
    (a09 initial).gprs .r15 = spike3ConcreteLinuxArena.endExclusive := by
  change initial.gprs .r15 = _
  exact h.arenaEnd
private theorem sA13Rax (initial) (h : SecondFreshEntryConditions initial) :
    (a13 initial).gprs .rax = 64992 := by
  change (a09 initial).gprs .r15 - (a09 initial).gprs .r11 = 64992
  rw [sA09R15 initial h, sA09R11 initial h]
  rfl
private theorem sA13R9 (initial) (h : SecondFreshEntryConditions initial) :
    (a13 initial).gprs .r9 = 288 := by change (a06 initial).gprs .r9 = 288; exact sA06R9 initial h

private theorem sGuard03 (initial) (h : SecondFreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a02 initial) := by
  simp only [X86BranchCondition.holds, a02]
  rw [add_r64_imm8_step_cf, sA01R8 initial h]
  decide
private theorem sGuard07 (initial) (h : SecondFreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a06 initial) := by
  simp only [X86BranchCondition.holds, a06]
  rw [add_r64_imm8_step_cf, sA05R9 initial h]
  decide
private theorem sGuard09 (initial) (h : SecondFreshEntryConditions initial) :
    ¬ X86BranchCondition.notEqual.holds (a08 initial) := by
  simp only [X86BranchCondition.holds, a08]
  rw [cmpImm8ZeroSetsZf (a07 initial) (sA07R10 initial h)]
  simp
private theorem sGuard11 (initial) (h : SecondFreshEntryConditions initial) :
    ¬ X86BranchCondition.above.holds (a10 initial) := by
  have carry : (a10 initial).cf = true := by
    change (X86_64Instruction.step (cmp_r64 .r11 .r15) (a09 initial)).cf = true
    rw [cmp_r64_step_cf, sA09R11 initial h, sA09R15 initial h]
    decide
  simp [X86BranchCondition.holds, carry]
private theorem sGuard15 (initial) (h : SecondFreshEntryConditions initial) :
    ¬ X86BranchCondition.below.holds (a14 initial) := by
  simp only [X86BranchCondition.holds, a14]
  rw [cmp_r64_step_cf, sA13Rax initial h, sA13R9 initial h]
  decide

private theorem sA01Rip (initial) (h : SecondFreshEntryConditions initial) : (a01 initial).rip = 4199735 := by
  rw [a01, (ControlFlowFree.mov .r8 .rcx).step_rip_eq, h.rip]; rfl
private theorem sA02Rip (initial) (h : SecondFreshEntryConditions initial) : (a02 initial).rip = 4199739 := by
  rw [a02, (seqAddImm8 .r8 7).step_rip_eq_of_safe _ (sA02Safe initial h), sA01Rip initial h]; rfl
private theorem sA03Rip (initial) (h : SecondFreshEntryConditions initial) : (a03 initial).rip = 4199745 := by
  rw [a03, (ConditionalJumpEncoding.jb32 113).step_rip_eq_fallthrough _ (sGuard03 initial h), sA02Rip initial h]; rfl
private theorem sA04Rip (initial) (h : SecondFreshEntryConditions initial) : (a04 initial).rip = 4199749 := by
  rw [a04, (seqAndImm8 .r8 0xF8).step_rip_eq_of_safe _ (sA04Safe initial h), sA03Rip initial h]; rfl
private theorem sA05Rip (initial) (h : SecondFreshEntryConditions initial) : (a05 initial).rip = 4199752 := by
  rw [a05, (ControlFlowFree.mov .r9 .r8).step_rip_eq, sA04Rip initial h]; rfl
private theorem sA06Rip (initial) (h : SecondFreshEntryConditions initial) : (a06 initial).rip = 4199756 := by
  rw [a06, (seqAddImm8 .r9 32).step_rip_eq_of_safe _ (sA06Safe initial h), sA05Rip initial h]; rfl
private theorem sA07Rip (initial) (h : SecondFreshEntryConditions initial) : (a07 initial).rip = 4199762 := by
  rw [a07, (ConditionalJumpEncoding.jb32 96).step_rip_eq_fallthrough _ (sGuard07 initial h), sA06Rip initial h]; rfl
private theorem sA08Rip (initial) (h : SecondFreshEntryConditions initial) : (a08 initial).rip = 4199766 := by
  rw [a08, (seqCmpImm8 .r10 0).step_rip_eq_of_safe _ (sA08Safe initial h), sA07Rip initial h]; rfl
private theorem sA09Rip (initial) (h : SecondFreshEntryConditions initial) : (a09 initial).rip = 4199768 := by
  rw [a09, (ConditionalJumpEncoding.jne8 0x36).step_rip_eq_fallthrough _ (sGuard09 initial h), sA08Rip initial h]; rfl
private theorem sA10Rip (initial) (h : SecondFreshEntryConditions initial) : (a10 initial).rip = 4199771 := by
  rw [a10, (seqCmp .r11 .r15).step_rip_eq_of_safe _ (sA10Safe initial h), sA09Rip initial h]; rfl
private theorem sA11Rip (initial) (h : SecondFreshEntryConditions initial) : (a11 initial).rip = 4199773 := by
  rw [a11, (ConditionalJumpEncoding.ja8 0x55).step_rip_eq_fallthrough _ (sGuard11 initial h), sA10Rip initial h]; rfl
private theorem sA12Rip (initial) (h : SecondFreshEntryConditions initial) : (a12 initial).rip = 4199776 := by
  rw [a12, (ControlFlowFree.mov .rax .r15).step_rip_eq, sA11Rip initial h]; rfl
private theorem sA13Rip (initial) (h : SecondFreshEntryConditions initial) : (a13 initial).rip = 4199779 := by
  rw [a13, (ControlFlowFree.sub .rax .r11).step_rip_eq, sA12Rip initial h]; rfl
private theorem sA14Rip (initial) (h : SecondFreshEntryConditions initial) : (a14 initial).rip = 4199782 := by
  rw [a14, (seqCmp .rax .r9).step_rip_eq_of_safe _ (sA14Safe initial h), sA13Rip initial h]; rfl
private theorem sA15Rip (initial) (h : SecondFreshEntryConditions initial) : (a15 initial).rip = 4199784 := by
  rw [a15, (ConditionalJumpEncoding.jb8 0x4A).step_rip_eq_fallthrough _ (sGuard15 initial h), sA14Rip initial h]; rfl
private theorem sA16Rip (initial) (h : SecondFreshEntryConditions initial) : (a16 initial).rip = 4199787 := by
  rw [a16, (ControlFlowFree.mov .rax .r11).step_rip_eq, sA15Rip initial h]; rfl
private theorem sA17Rip (initial) (h : SecondFreshEntryConditions initial) : (a17 initial).rip = 4199790 := by
  rw [a17, (ControlFlowFree.add .r11 .r9).step_rip_eq, sA16Rip initial h]; rfl
private theorem sA18Rip (initial) (h : SecondFreshEntryConditions initial) : (a18 initial).rip = 4199793 := by
  rw [a18, seqStoreRaxR8.step_rip_eq_of_safe _ (sA18Safe initial h), sA17Rip initial h]; rfl
private theorem sA19Rip (initial) (h : SecondFreshEntryConditions initial) : (a19 initial).rip = 4199801 := by
  rw [a19, seqStoreImmRax08.step_rip_eq_of_safe _ (sA19Safe initial h), sA18Rip initial h]; rfl
private theorem sA20Rip (initial) (h : SecondFreshEntryConditions initial) : (a20 initial).rip = 4199809 := by
  rw [a20, seqStoreImmRax10.step_rip_eq_of_safe _ (sA20Safe initial h), sA19Rip initial h]; rfl
private theorem sA21Rip (initial) (h : SecondFreshEntryConditions initial) : (a21 initial).rip = 4199817 := by
  rw [a21, seqStoreImmRax18.step_rip_eq_of_safe _ (sA21Safe initial h), sA20Rip initial h]; rfl
private theorem sA22Rip (initial) (h : SecondFreshEntryConditions initial) : (a22 initial).rip = 4199821 := by
  rw [a22, (seqAddImm8 .rax 32).step_rip_eq_of_safe _ (sA22Safe initial h), sA21Rip initial h]; rfl

private theorem sA16Rax (initial) (h : SecondFreshEntryConditions initial) :
    (a16 initial).gprs .rax = spike3ConcreteLinuxArena.base + 544 := by
  change (a09 initial).gprs .r11 = _
  exact sA09R11 initial h
private theorem sA16R11 (initial) (h : SecondFreshEntryConditions initial) :
    (a16 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 544 := by
  change (a09 initial).gprs .r11 = _
  exact sA09R11 initial h
private theorem sA16R9 (initial) (h : SecondFreshEntryConditions initial) :
    (a16 initial).gprs .r9 = 288 := by change (a06 initial).gprs .r9 = 288; exact sA06R9 initial h
private theorem sA17Rax (initial) (h : SecondFreshEntryConditions initial) :
    (a17 initial).gprs .rax = spike3ConcreteLinuxArena.base + 544 := by
  change (a16 initial).gprs .rax = _
  exact sA16Rax initial h
private theorem sA17R8 (initial) (h : SecondFreshEntryConditions initial) :
    (a17 initial).gprs .r8 = 256 := by change (a04 initial).gprs .r8 = 256; exact sA04R8 initial h
private theorem sA17R11 (initial) (h : SecondFreshEntryConditions initial) :
    (a17 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 832 := by
  change (a16 initial).gprs .r11 + (a16 initial).gprs .r9 = _
  rw [sA16R11 initial h, sA16R9 initial h]
  simp [spike3ConcreteLinuxArena]
private theorem sA17R10 (initial) (h : SecondFreshEntryConditions initial) :
    (a17 initial).gprs .r10 = 0 := by change (a07 initial).gprs .r10 = 0; exact sA07R10 initial h

private theorem sA18Memory (initial) (h : SecondFreshEntryConditions initial) :
    (a18 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 544) 256 initial.memory := by
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0)
    ((a17 initial).gprs .r8) (a17 initial).memory = _
  rw [sA17Rax initial h, sA17R8 initial h, a17Memory]
  rfl
private theorem sA19Memory (initial) (h : SecondFreshEntryConditions initial) :
    (a19 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 552) 0
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 544) 256 initial.memory) := by
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x08)
    (signExtendUInt32To64 0) (a18 initial).memory = _
  rw [sA17Rax initial h, sA18Memory initial h]
  rfl
private theorem sA20Memory (initial) (h : SecondFreshEntryConditions initial) :
    (a20 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 560) 8
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 552) 0
        (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 544) 256 initial.memory)) := by
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x10)
    (signExtendUInt32To64 8) (a19 initial).memory = _
  rw [sA17Rax initial h, sA19Memory initial h]
  rfl
private theorem sA21Memory (initial) (h : SecondFreshEntryConditions initial) :
    (a21 initial).memory = X86_64Mem.write .w64
      (spike3ConcreteLinuxArena.base + 568) 0
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 560) 8
        (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 552) 0
          (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 544) 256 initial.memory))) := by
  change X86_64Mem.write .w64 ((a17 initial).gprs .rax + signExtend8To64 0x18)
    (signExtendUInt32To64 0) (a20 initial).memory = _
  rw [sA17Rax initial h, sA20Memory initial h]
  rfl
private theorem sA22Memory (initial) : (a22 initial).memory = (a21 initial).memory := by rfl

private theorem readStack_writeSecond0 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 544) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
private theorem readStack_writeSecond8 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 552) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
private theorem readStack_writeSecond16 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 560) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
private theorem readStack_writeSecond24 (value : UInt64) (memory : X86_64Memory) :
    X86_64Mem.read .w64 0x7FFFFFFEFF80
      (X86_64Mem.write .w64 (spike3ConcreteLinuxArena.base + 568) value memory) =
        X86_64Mem.read .w64 0x7FFFFFFEFF80 memory := by
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]

private theorem sA22ReturnSlot (initial) (h : SecondFreshEntryConditions initial) :
    (a22 initial).read64 (a22 initial).rsp = linuxSecondMallocReturnRip := by
  rw [a22Rsp, h.stackAddress]
  change X86_64Mem.read .w64 0x7FFFFFFEFF80 (a22 initial).memory = _
  rw [sA22Memory initial, sA21Memory initial h, readStack_writeSecond24,
    readStack_writeSecond16, readStack_writeSecond8, readStack_writeSecond0]
  have slot := h.returnSlot
  rw [h.stackAddress] at slot
  exact slot
private theorem sA23Rip (initial) (h : SecondFreshEntryConditions initial) :
    (a23 initial).rip = linuxSecondMallocReturnRip := by
  change (a22 initial).read64 (a22 initial).rsp = linuxSecondMallocReturnRip
  exact sA22ReturnSlot initial h
private theorem sA22Rax (initial) (h : SecondFreshEntryConditions initial) :
    (a22 initial).gprs .rax = spike3ConcreteLinuxArena.base + 576 := by
  change (a17 initial).gprs .rax + signExtend8To64 32 = _
  rw [sA17Rax initial h]
  rfl
private theorem sA23Rax (initial) (h : SecondFreshEntryConditions initial) :
    (a23 initial).gprs .rax = spike3ConcreteLinuxArena.base + 576 := by
  rw [a23, ret_op_step_gpr_other _ .rax (by decide)]
  exact sA22Rax initial h
private theorem sA23R11 (initial) (h : SecondFreshEntryConditions initial) :
    (a23 initial).gprs .r11 = spike3ConcreteLinuxArena.base + 832 := by
  rw [a23, ret_op_step_gpr_other _ .r11 (by decide)]
  change (a17 initial).gprs .r11 = _
  exact sA17R11 initial h
private theorem sA23R10 (initial) (h : SecondFreshEntryConditions initial) :
    (a23 initial).gprs .r10 = 0 := by
  rw [a23, ret_op_step_gpr_other _ .r10 (by decide)]
  change (a17 initial).gprs .r10 = 0
  exact sA17R10 initial h
private theorem sA23Memory (initial) (_h : SecondFreshEntryConditions initial) :
    (a23 initial).memory = (a21 initial).memory := by
  rw [a23, ret_op_step_memory, sA22Memory initial]
private theorem sA23StackRestored (environment : Environment) :
    (a23 (linuxSecondMallocEntry environment)).rsp = 0x7FFFFFFEFF88 := by
  rw [a23, ret_op_step_rsp, a22Rsp, linuxSecondMallocEntryRsp]
  rfl

private theorem linuxSecondCallerSelectedPath (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 5
      (secondCaller00 environment) [] (linuxSecondMallocEntry environment) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 5
      (secondCaller00 environment) []
      (X86_64Instruction.step (call_rel32 1184) (secondCaller04 environment)) [] []
  have p01 := ordinaryOne (environment := environment) (events := []) (seqCmpImm8 .rax 0)
    (callerThroughReadLookupAt environment (secondCaller00 environment)
      (4198523, cmp_r64_imm8 .rax 0) (secondCaller00Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198527 (secondCaller01 environment) (secondCaller01Rip environment) (by decide))
    (secondCaller01Safe environment)
  have p02 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.je32 1187) (firstSuccessBranchNotChosen environment)
    (callerThroughReadLookupAt environment (secondCaller01 environment)
      (4198527, je_rel32 1187) (secondCaller01Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198533 (secondCaller02 environment) (secondCaller02Rip environment) (by decide))
    (secondCaller02Safe environment)
  have p03 := ordinaryOne (environment := environment) (events := []) seqStoreRsp50Rax
    (callerThroughReadLookupAt environment (secondCaller02 environment)
      (4198533, mov_mem64_disp .rsp 0x50 .rax) (secondCaller02Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198538 (secondCaller03 environment) (secondCaller03Rip environment) (by decide))
    (secondCaller03Safe environment)
  have p04 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .ecx 256)
    (callerThroughReadLookupAt environment (secondCaller03 environment)
      (4198538, mov_r32 .ecx 256) (secondCaller03Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198543 (secondCaller04 environment) (secondCaller04Rip environment) (by decide))
    (secondCaller04Safe environment)
  have p05 := internalCallOne (environment := environment) (events := [])
    (HostInterceptEncoding.callRel32 1184)
    (callerThroughReadLookupAt environment (secondCaller04 environment)
      (4198543, call_rel32 1184) (secondCaller04Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4199732 (linuxSecondMallocEntry environment)
      (linuxSecondMallocEntryRip environment) (by decide))
    (linuxSecondMallocEntrySafe environment)
  simpa [linuxSecondMallocEntry] using SelectedPrefix.append (SelectedPrefix.append
    (SelectedPrefix.append (SelectedPrefix.append p01 p02) p03) p04) p05

private theorem linuxSecondAllocatorSelectedPath (environment : Environment)
    (initial : X86_64MachineState) (h : SecondFreshEntryConditions initial) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 23
      initial [] (a23 initial) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 23
      initial [] (X86_64Instruction.step ret_op (a22 initial)) [] []
  have p01 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r8 .rcx).sequential
    (mallocLookupAt environment initial (4199732, mov_r64 .r8 .rcx) h.rip
      (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199735 (a01 initial) (sA01Rip initial h) (by decide)) (sA01Safe initial h)
  have p02 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .r8 7)
    (mallocLookupAt environment (a01 initial) (4199735, add_r64_imm8 .r8 7)
      (sA01Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199739 (a02 initial) (sA02Rip initial h) (by decide)) (sA02Safe initial h)
  have p03 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb32 113) (sGuard03 initial h)
    (mallocLookupAt environment (a02 initial) (4199739, jb_rel32 113)
      (sA02Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199745 (a03 initial) (sA03Rip initial h) (by decide)) (sA03Safe initial h)
  have p04 := ordinaryOne (environment := environment) (events := []) (seqAndImm8 .r8 0xF8)
    (mallocLookupAt environment (a03 initial) (4199745, and_r64_imm8 .r8 0xF8)
      (sA03Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199749 (a04 initial) (sA04Rip initial h) (by decide)) (sA04Safe initial h)
  have p05 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .r9 .r8).sequential
    (mallocLookupAt environment (a04 initial) (4199749, mov_r64 .r9 .r8)
      (sA04Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199752 (a05 initial) (sA05Rip initial h) (by decide)) (sA05Safe initial h)
  have p06 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .r9 32)
    (mallocLookupAt environment (a05 initial) (4199752, add_r64_imm8 .r9 32)
      (sA05Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199756 (a06 initial) (sA06Rip initial h) (by decide)) (sA06Safe initial h)
  have p07 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb32 96) (sGuard07 initial h)
    (mallocLookupAt environment (a06 initial) (4199756, jb_rel32 96)
      (sA06Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199762 (a07 initial) (sA07Rip initial h) (by decide)) (sA07Safe initial h)
  have p08 := ordinaryOne (environment := environment) (events := []) (seqCmpImm8 .r10 0)
    (mallocLookupAt environment (a07 initial) (4199762, cmp_r64_imm8 .r10 0)
      (sA07Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199766 (a08 initial) (sA08Rip initial h) (by decide)) (sA08Safe initial h)
  have p09 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jne8 0x36) (sGuard09 initial h)
    (mallocLookupAt environment (a08 initial) (4199766, jne_rel8 0x36)
      (sA08Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199768 (a09 initial) (sA09Rip initial h) (by decide)) (sA09Safe initial h)
  have p10 := ordinaryOne (environment := environment) (events := []) (seqCmp .r11 .r15)
    (mallocLookupAt environment (a09 initial) (4199768, cmp_r64 .r11 .r15)
      (sA09Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199771 (a10 initial) (sA10Rip initial h) (by decide)) (sA10Safe initial h)
  have p11 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.ja8 0x55) (sGuard11 initial h)
    (mallocLookupAt environment (a10 initial) (4199771, ja_rel8 0x55)
      (sA10Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199773 (a11 initial) (sA11Rip initial h) (by decide)) (sA11Safe initial h)
  have p12 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .rax .r15).sequential
    (mallocLookupAt environment (a11 initial) (4199773, mov_r64 .rax .r15)
      (sA11Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199776 (a12 initial) (sA12Rip initial h) (by decide)) (sA12Safe initial h)
  have p13 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.sub .rax .r11).sequential
    (mallocLookupAt environment (a12 initial) (4199776, sub_r64 .rax .r11)
      (sA12Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199779 (a13 initial) (sA13Rip initial h) (by decide)) (sA13Safe initial h)
  have p14 := ordinaryOne (environment := environment) (events := []) (seqCmp .rax .r9)
    (mallocLookupAt environment (a13 initial) (4199779, cmp_r64 .rax .r9)
      (sA13Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199782 (a14 initial) (sA14Rip initial h) (by decide)) (sA14Safe initial h)
  have p15 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.jb8 0x4A) (sGuard15 initial h)
    (mallocLookupAt environment (a14 initial) (4199782, jb_rel8 0x4A)
      (sA14Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199784 (a15 initial) (sA15Rip initial h) (by decide)) (sA15Safe initial h)
  have p16 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.mov .rax .r11).sequential
    (mallocLookupAt environment (a15 initial) (4199784, mov_r64 .rax .r11)
      (sA15Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199787 (a16 initial) (sA16Rip initial h) (by decide)) (sA16Safe initial h)
  have p17 := ordinaryOne (environment := environment) (events := [])
    (ControlFlowFree.add .r11 .r9).sequential
    (mallocLookupAt environment (a16 initial) (4199787, add_r64 .r11 .r9)
      (sA16Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199790 (a17 initial) (sA17Rip initial h) (by decide)) (sA17Safe initial h)
  have p18 := ordinaryOne (environment := environment) (events := []) seqStoreRaxR8
    (mallocLookupAt environment (a17 initial) (4199790, mov_mem64_disp .rax 0 .r8)
      (sA17Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199793 (a18 initial) (sA18Rip initial h) (by decide)) (sA18Safe initial h)
  have p19 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax08
    (mallocLookupAt environment (a18 initial) (4199793, mov_mem64_disp_imm .rax 0x08 0)
      (sA18Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199801 (a19 initial) (sA19Rip initial h) (by decide)) (sA19Safe initial h)
  have p20 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax10
    (mallocLookupAt environment (a19 initial) (4199801, mov_mem64_disp_imm .rax 0x10 8)
      (sA19Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199809 (a20 initial) (sA20Rip initial h) (by decide)) (sA20Safe initial h)
  have p21 := ordinaryOne (environment := environment) (events := []) seqStoreImmRax18
    (mallocLookupAt environment (a20 initial) (4199809, mov_mem64_disp_imm .rax 0x18 0)
      (sA20Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199817 (a21 initial) (sA21Rip initial h) (by decide)) (sA21Safe initial h)
  have p22 := ordinaryOne (environment := environment) (events := []) (seqAddImm8 .rax 32)
    (mallocLookupAt environment (a21 initial) (4199817, add_r64_imm8 .rax 32)
      (sA21Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt 4199821 (a22 initial) (sA22Rip initial h) (by decide)) (sA22Safe initial h)
  have p23 := nearReturnOne (environment := environment) (events := []) ReturnEncoding.near
    (mallocLookupAt environment (a22 initial) (4199821, ret_op)
      (sA22Rip initial h) (by simp [linuxLinkedMallocIndex]))
    (normalAt linuxSecondMallocReturnRip (a23 initial) (sA23Rip initial h) (by decide))
    (sA23Safe initial h)
  have q02 := SelectedPrefix.append p01 p02
  have q03 := SelectedPrefix.append q02 p03
  have q04 := SelectedPrefix.append q03 p04
  have q05 := SelectedPrefix.append q04 p05
  have q06 := SelectedPrefix.append q05 p06
  have q07 := SelectedPrefix.append q06 p07
  have q08 := SelectedPrefix.append q07 p08
  have q09 := SelectedPrefix.append q08 p09
  have q10 := SelectedPrefix.append q09 p10
  have q11 := SelectedPrefix.append q10 p11
  have q12 := SelectedPrefix.append q11 p12
  have q13 := SelectedPrefix.append q12 p13
  have q14 := SelectedPrefix.append q13 p14
  have q15 := SelectedPrefix.append q14 p15
  have q16 := SelectedPrefix.append q15 p16
  have q17 := SelectedPrefix.append q16 p17
  have q18 := SelectedPrefix.append q17 p18
  have q19 := SelectedPrefix.append q18 p19
  have q20 := SelectedPrefix.append q19 p20
  have q21 := SelectedPrefix.append q20 p21
  have q22 := SelectedPrefix.append q21 p22
  simpa [a23] using SelectedPrefix.append q22 p23

private theorem sA23SizeHeader (initial) (h : SecondFreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 544) (a23 initial).memory = 256 := by
  rw [sA23Memory initial h, sA21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
  simpa using le_bytes_reassemble (256 : UInt64)
private theorem sA23FreeHeader (initial) (h : SecondFreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 552) (a23 initial).memory = 0 := by
  rw [sA23Memory initial h, sA21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
private theorem sA23AlignmentHeader (initial) (h : SecondFreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 560) (a23 initial).memory = 8 := by
  rw [sA23Memory initial h, sA21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]
  simpa using le_bytes_reassemble (8 : UInt64)
private theorem sA23NextFreeHeader (initial) (h : SecondFreshEntryConditions initial) :
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 568) (a23 initial).memory = 0 := by
  rw [sA23Memory initial h, sA21Memory initial h]
  simp [spike3ConcreteLinuxArena, X86_64Mem.read, X86_64Mem.write, X86_64Mem.readByte]

def linuxSecondAllocatorBefore (environment : Environment) : SmolAllocatorFrame :=
  { bump := spike3ConcreteLinuxArena.base + 544
    freeHead := 0
    memory := (linuxFirstFreshMallocCertificate environment).finalFrame.memory }

private theorem linuxSecondFreshDecision (environment : Environment) :
    ∃ logicalAfter,
      smolFreshAllocation 256 spike3ConcreteLinuxArena (linuxSecondAllocatorBefore environment) =
        some logicalAfter ∧
      logicalAfter.bump = spike3ConcreteLinuxArena.base + 832 ∧
      logicalAfter.freeHead = 0 := by
  let logicalAfter : SmolAllocatorFrame :=
    { bump := spike3ConcreteLinuxArena.base + 832
      freeHead := 0
      memory := (linuxSecondAllocatorBefore environment).memory }
  refine ⟨logicalAfter, ?_, rfl, rfl⟩
  unfold smolFreshAllocation
  rw [if_neg (by decide)]
  rw [show (256 + 7 : UInt64) &&& 0xFFFFFFFFFFFFFFF8 = 256 by decide]
  rw [if_neg (by decide)]
  simp [NativeArenaCapability.allocateFresh, linuxSecondAllocatorBefore,
    spike3ConcreteLinuxArena, logicalAfter]

/- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model -/
/-- Projection-limited canonical result of the second selected fresh allocation. -/
structure LinuxSecondFreshMallocCertificate (environment : Environment) where
  finalFrame : SmolAllocatorFrame
  resultPointer : UInt64
  returnState : X86_64MachineState
  returnEvents : List AnyEvent
  fuel : Nat

def linuxSecondFreshMallocCertificate (environment : Environment) :
    LinuxSecondFreshMallocCertificate environment :=
  let initial := linuxSecondMallocEntry environment
  { finalFrame :=
      { bump := spike3ConcreteLinuxArena.base + 832
        freeHead := 0
        memory := (a23 initial).memory }
    resultPointer := spike3ConcreteLinuxArena.base + 576
    returnState := a23 initial
    returnEvents := []
    fuel := 23 }

private structure LinuxSecondFreshMallocEvidence (environment : Environment)
    (certificate : LinuxSecondFreshMallocCertificate environment) : Prop where
  freshDecision : ∃ logicalAfter,
    smolFreshAllocation 256 spike3ConcreteLinuxArena (linuxSecondAllocatorBefore environment) =
      some logicalAfter ∧
    logicalAfter.bump = certificate.finalFrame.bump ∧
    logicalAfter.freeHead = certificate.finalFrame.freeHead
  exactCallerReturnSlot : (linuxSecondMallocEntry environment).read64
    (linuxSecondMallocEntry environment).rsp = linuxSecondMallocReturnRip
  selectedPath : NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
    certificate.fuel (linuxSecondMallocEntry environment) [] certificate.returnState
    certificate.returnEvents []
  resultProjected : certificate.returnState.gprs .rax = certificate.resultPointer
  bumpProjected : certificate.returnState.gprs .r11 = certificate.finalFrame.bump
  freeListProjected : certificate.returnState.gprs .r10 = certificate.finalFrame.freeHead
  memoryProjected : certificate.returnState.memory = certificate.finalFrame.memory
  returnedToCaller : certificate.returnState.rip = linuxSecondMallocReturnRip
  stackRestored : certificate.returnState.rsp = 0x7FFFFFFEFF88
  sizeHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 544)
    certificate.finalFrame.memory = 256
  freeHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 552)
    certificate.finalFrame.memory = 0
  alignmentHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 560)
    certificate.finalFrame.memory = 8
  nextFreeHeader : X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 568)
    certificate.finalFrame.memory = 0

private theorem linuxSecondFreshMallocEvidence (environment : Environment) :
    LinuxSecondFreshMallocEvidence environment (linuxSecondFreshMallocCertificate environment) := by
  let initial := linuxSecondMallocEntry environment
  let conditions := linuxSecondFreshEntry environment
  refine {
    freshDecision := by
      rcases linuxSecondFreshDecision environment with ⟨after, decision, bump, free⟩
      exact ⟨after, decision, by simpa [linuxSecondFreshMallocCertificate] using bump,
        by simpa [linuxSecondFreshMallocCertificate] using free⟩
    exactCallerReturnSlot := linuxSecondMallocCallerSlot environment
    selectedPath := by
      simpa [linuxSecondFreshMallocCertificate, initial] using
        linuxSecondAllocatorSelectedPath environment initial conditions
    resultProjected := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23Rax initial conditions
    bumpProjected := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23R11 initial conditions
    freeListProjected := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23R10 initial conditions
    memoryProjected := by simp [linuxSecondFreshMallocCertificate]
    returnedToCaller := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23Rip initial conditions
    stackRestored := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23StackRestored environment
    sizeHeader := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23SizeHeader initial conditions
    freeHeader := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23FreeHeader initial conditions
    alignmentHeader := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23AlignmentHeader initial conditions
    nextFreeHeader := by
      simpa [linuxSecondFreshMallocCertificate, initial] using sA23NextFreeHeader initial conditions }

theorem linuxSecondFreshMallocCertificate_selectedPath (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
      (linuxSecondFreshMallocCertificate environment).fuel
      (linuxSecondMallocEntry environment) []
      (linuxSecondFreshMallocCertificate environment).returnState
      (linuxSecondFreshMallocCertificate environment).returnEvents [] :=
  (linuxSecondFreshMallocEvidence environment).selectedPath

theorem linuxSecondFreshMallocCertificate_projection (environment : Environment) :
    let certificate := linuxSecondFreshMallocCertificate environment
    certificate.returnState.gprs .rax = certificate.resultPointer ∧
      certificate.returnState.gprs .r11 = certificate.finalFrame.bump ∧
      certificate.returnState.gprs .r10 = certificate.finalFrame.freeHead ∧
      certificate.returnState.memory = certificate.finalFrame.memory ∧
      certificate.returnState.rip = linuxSecondMallocReturnRip ∧
      certificate.returnState.rsp = 0x7FFFFFFEFF88 ∧
      certificate.returnEvents = [] := by
  let evidence := linuxSecondFreshMallocEvidence environment
  exact ⟨evidence.resultProjected, evidence.bumpProjected, evidence.freeListProjected,
    evidence.memoryProjected, evidence.returnedToCaller, evidence.stackRestored, rfl⟩

theorem linuxSecondFreshMallocCertificate_exactCallerReturnSlot (environment : Environment) :
    (linuxSecondMallocEntry environment).read64 (linuxSecondMallocEntry environment).rsp =
      linuxSecondMallocReturnRip :=
  (linuxSecondFreshMallocEvidence environment).exactCallerReturnSlot

theorem linuxSecondFreshMallocCertificate_headers (environment : Environment) :
    let certificate := linuxSecondFreshMallocCertificate environment
    X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 544) certificate.finalFrame.memory = 256 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 552) certificate.finalFrame.memory = 0 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 560) certificate.finalFrame.memory = 8 ∧
      X86_64Mem.read .w64 (spike3ConcreteLinuxArena.base + 568) certificate.finalFrame.memory = 0 := by
  let evidence := linuxSecondFreshMallocEvidence environment
  exact ⟨evidence.sizeHeader, evidence.freeHeader, evidence.alignmentHeader,
    evidence.nextFreeHeader⟩

/-- The logical fresh decision and emitted allocator block agree on bump/free-list control state. -/
theorem linuxSecondFreshMallocCertificate_freshControlJoin (environment : Environment) :
    ∃ logicalAfter,
      smolFreshAllocation 256 spike3ConcreteLinuxArena (linuxSecondAllocatorBefore environment) =
        some logicalAfter ∧
      logicalAfter.bump = (linuxSecondFreshMallocCertificate environment).finalFrame.bump ∧
      logicalAfter.freeHead =
        (linuxSecondFreshMallocCertificate environment).finalFrame.freeHead :=
  (linuxSecondFreshMallocEvidence environment).freshDecision

/-- Both concrete allocator call/return blocks form one exact selected 73-step spine. -/
theorem linuxTwoFreshMallocCallReturnSpine (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 73
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxSecondFreshMallocCertificate environment).returnState [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 73
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (a23 (linuxSecondMallocEntry environment)) [] []
  have first := linuxFirstMallocCallReturnSpine environment
  have caller := linuxSecondCallerSelectedPath environment
  have second := linuxSecondFreshMallocCertificate_selectedPath environment
  have toEntry := SelectedPrefix.append first caller
  simpa [linuxSecondFreshMallocCertificate] using SelectedPrefix.append toEntry second

private def readCaller00 (environment : Environment) : X86_64MachineState :=
  (linuxSecondFreshMallocCertificate environment).returnState
private def readCaller01 (environment : Environment) :=
  X86_64Instruction.step (cmp_r64_imm8 .rax 0) (readCaller00 environment)
private def readCaller02 (environment : Environment) :=
  X86_64Instruction.step (je_rel32 1162) (readCaller01 environment)
private def readCaller03 (environment : Environment) :=
  X86_64Instruction.step (mov_mem64_disp .rsp 0x58 .rax) (readCaller02 environment)
private def readCaller04 (environment : Environment) :=
  X86_64Instruction.step (xor_r32 .edi .edi) (readCaller03 environment)
private theorem readCaller04_eq (environment : Environment) :
    readCaller04 environment =
      X86_64Instruction.step (xor_r32 .edi .edi) (readCaller03 environment) := rfl
private def readCaller05 (environment : Environment) :=
  X86_64Instruction.step (mov_reg64_mem64_disp .rsi .rsp 0x50) (readCaller04 environment)
private def readCaller06 (environment : Environment) :=
  X86_64Instruction.step (mov_r32 .edx 512) (readCaller05 environment)
private def readCaller07 (environment : Environment) :=
  X86_64Instruction.step (mov_r32 .eax 0) (readCaller06 environment)
private def readCaller08 (environment : Environment) :=
  X86_64Instruction.step (mov_mem64_disp .rsp 0x40 .r11) (readCaller07 environment)
private def readCaller09 (environment : Environment) :=
  X86_64Instruction.step (mov_mem64_disp .rsp 0x48 .r10) (readCaller08 environment)
def linuxFirstReadBoundary (environment : Environment) :=
  X86_64Instruction.step syscall_op (readCaller09 environment)
private def linuxFirstReadAfterHost (environment : Environment) : X86_64MachineState :=
  (sysReadHook (Event := AnyEvent) (linuxFirstReadBoundary environment)).1
private def readCaller10 (environment : Environment) :=
  X86_64Instruction.step (mov_reg64_mem64_disp .r11 .rsp 0x40)
    (linuxFirstReadAfterHost environment)
private def readCaller11 (environment : Environment) :=
  X86_64Instruction.step (mov_reg64_mem64_disp .r10 .rsp 0x48) (readCaller10 environment)
private def readCaller12 (environment : Environment) :=
  X86_64Instruction.step (mov_mem64_disp .rsp 0x28 .rax) (readCaller11 environment)
private def readCaller13 (environment : Environment) :=
  X86_64Instruction.step (cmp_r64_imm8 .rax 0) (readCaller12 environment)
def linuxFirstReadComparedState (environment : Environment) : X86_64MachineState :=
  readCaller13 environment
private def linuxFirstReadHappyState (environment : Environment) :=
  X86_64Instruction.step (jle_rel32 420) (readCaller13 environment)
private def linuxFirstReadFailureState (environment : Environment) :=
  X86_64Instruction.step (jle_rel32 420) (readCaller13 environment)

private theorem seqStoreRsp58Rax :
    SequentialInstruction (mov_mem64_disp .rsp 0x58 .rax) where
  encoding := .movMem64Disp .rsp 0x58 .rax
  safeFallthrough := by intro state _; rfl
private theorem seqStoreRsp40R11 :
    SequentialInstruction (mov_mem64_disp .rsp 0x40 .r11) where
  encoding := .movMem64Disp .rsp 0x40 .r11
  safeFallthrough := by intro state _; rfl
private theorem seqStoreRsp48R10 :
    SequentialInstruction (mov_mem64_disp .rsp 0x48 .r10) where
  encoding := .movMem64Disp .rsp 0x48 .r10
  safeFallthrough := by intro state _; rfl
private theorem seqStoreRsp28Rax :
    SequentialInstruction (mov_mem64_disp .rsp 0x28 .rax) where
  encoding := .movMem64Disp .rsp 0x28 .rax
  safeFallthrough := by intro state _; rfl
private theorem seqLoadRsp50Rsi :
    SequentialInstruction (mov_reg64_mem64_disp .rsi .rsp 0x50) where
  encoding := .movReg64Mem64Disp .rsi .rsp 0x50
  safeFallthrough := by intro state _; rfl
private theorem seqLoadRsp40R11 :
    SequentialInstruction (mov_reg64_mem64_disp .r11 .rsp 0x40) where
  encoding := .movReg64Mem64Disp .r11 .rsp 0x40
  safeFallthrough := by intro state _; rfl
private theorem seqLoadRsp48R10 :
    SequentialInstruction (mov_reg64_mem64_disp .r10 .rsp 0x48) where
  encoding := .movReg64Mem64Disp .r10 .rsp 0x48
  safeFallthrough := by intro state _; rfl

private theorem loadStepFault (dst base : Reg64) (disp : UInt8) (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_reg64_mem64_disp dst base disp) state).fault = state.fault := by
  cases dst <;> cases base <;> rfl
private theorem loadStepGprOther (dst base : Reg64) (disp : UInt8)
    (state : X86_64MachineState) (register : Reg64) (different : register ≠ dst) :
    (X86_64Instruction.step (mov_reg64_mem64_disp dst base disp) state).gprs register =
      state.gprs register := by
  change (state.setGpr64 dst _).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr64, different]

private theorem readCaller00Rip (environment : Environment) :
    (readCaller00 environment).rip = 4198548 :=
  (linuxSecondFreshMallocEvidence environment).returnedToCaller
private theorem readCaller00Safe (environment : Environment) :
    (readCaller00 environment).fault = none :=
  sA23Safe (linuxSecondMallocEntry environment) (linuxSecondFreshEntry environment)
private theorem readCaller00Rax (environment : Environment) :
    (readCaller00 environment).gprs .rax = spike3ConcreteLinuxArena.base + 576 :=
  (linuxSecondFreshMallocEvidence environment).resultProjected
private theorem readCaller00R10 (environment : Environment) :
    (readCaller00 environment).gprs .r10 = 0 :=
  (linuxSecondFreshMallocEvidence environment).freeListProjected
private theorem readCaller00R11 (environment : Environment) :
    (readCaller00 environment).gprs .r11 = spike3ConcreteLinuxArena.base + 832 :=
  (linuxSecondFreshMallocEvidence environment).bumpProjected
private theorem readCaller00Rsp (environment : Environment) :
    (readCaller00 environment).rsp = 0x7FFFFFFEFF88 :=
  (linuxSecondFreshMallocEvidence environment).stackRestored

private theorem readCaller01Safe (environment : Environment) :
    (readCaller01 environment).fault = none :=
  cmpImm8Safe .rax 0 _ (readCaller00Safe environment)
private theorem readCaller01Zf (environment : Environment) :
    (readCaller01 environment).zf = false := by
  apply cmpImm8RaxZeroZfOfNe
  rw [readCaller00Rax]
  decide
private theorem readCaller01Rip (environment : Environment) :
    (readCaller01 environment).rip = 4198552 := by
  rw [readCaller01, (seqCmpImm8 .rax 0).step_rip_eq_of_safe _ (readCaller01Safe environment),
    readCaller00Rip]
  rfl
private theorem secondSuccessBranchNotChosen (environment : Environment) :
    ¬ X86BranchCondition.equal.holds (readCaller01 environment) := by
  simp [X86BranchCondition.holds, readCaller01Zf environment]
private theorem readCaller02Safe (environment : Environment) :
    (readCaller02 environment).fault = none := by
  rw [readCaller02, (ConditionalJumpEncoding.je32 1162).step_fault_eq, readCaller01Safe]
private theorem readCaller02Rip (environment : Environment) :
    (readCaller02 environment).rip = 4198558 := by
  rw [readCaller02, (ConditionalJumpEncoding.je32 1162).step_rip_eq_fallthrough _
    (secondSuccessBranchNotChosen environment), readCaller01Rip]
  rfl

private theorem readCaller03Safe (environment : Environment) :
    (readCaller03 environment).fault = none := by
  rw [readCaller03, storeStepFault, readCaller02Safe]
private theorem readCaller03Rip (environment : Environment) :
    (readCaller03 environment).rip = 4198563 := by
  rw [readCaller03, seqStoreRsp58Rax.step_rip_eq_of_safe _ (readCaller03Safe environment),
    readCaller02Rip]
  rfl
private theorem readCaller04Safe (environment : Environment) :
    (readCaller04 environment).fault = none := by
  rw [readCaller04, xor32StepFault, readCaller03Safe]
private theorem readCaller04Rip (environment : Environment) :
    (readCaller04 environment).rip = 4198565 := by
  rw [readCaller04, (seqXor32 .edi .edi).step_rip_eq_of_safe _ (readCaller04Safe environment),
    readCaller03Rip]
  rfl
private theorem readCaller04Rdi (environment : Environment) :
    (readCaller04 environment).gprs .rdi = 0 := by
  rw [readCaller04_eq]
  exact xorEdiSelfStepRdiZero (readCaller03 environment)
private theorem readCaller05Safe (environment : Environment) :
    (readCaller05 environment).fault = none := by
  rw [readCaller05, loadStepFault, readCaller04Safe]
private theorem readCaller05Rip (environment : Environment) :
    (readCaller05 environment).rip = 4198570 := by
  rw [readCaller05, seqLoadRsp50Rsi.step_rip_eq_of_safe _ (readCaller05Safe environment),
    readCaller04Rip]
  rfl
private theorem readCaller05Rdi (environment : Environment) :
    (readCaller05 environment).gprs .rdi = 0 := by
  rw [readCaller05, loadStepGprOther .rsi .rsp 0x50 _ .rdi (by decide)]
  exact readCaller04Rdi environment
private theorem readCaller06Safe (environment : Environment) :
    (readCaller06 environment).fault = none := by
  rw [readCaller06, mov32StepFault, readCaller05Safe]
private theorem readCaller06Rip (environment : Environment) :
    (readCaller06 environment).rip = 4198575 := by
  rw [readCaller06, (mov_r32_sequential .edx 512).step_rip_eq_of_safe _
    (readCaller06Safe environment), readCaller05Rip]
  rfl
private theorem readCaller06Rdx (environment : Environment) :
    (readCaller06 environment).gprs .rdx = 512 := by rfl
private theorem readCaller06Rdi (environment : Environment) :
    (readCaller06 environment).gprs .rdi = 0 := by
  rw [readCaller06, mov32StepGprOther .edx 512 _ .rdi (by decide)]
  exact readCaller05Rdi environment
private theorem readCaller07Safe (environment : Environment) :
    (readCaller07 environment).fault = none := by
  rw [readCaller07, mov32StepFault, readCaller06Safe]
private theorem readCaller07Rip (environment : Environment) :
    (readCaller07 environment).rip = 4198580 := by
  rw [readCaller07, (mov_r32_sequential .eax 0).step_rip_eq_of_safe _
    (readCaller07Safe environment), readCaller06Rip]
  rfl
private theorem readCaller07Rax (environment : Environment) :
    (readCaller07 environment).gprs .rax = SYS_read := by rfl
private theorem readCaller07Rdx (environment : Environment) :
    (readCaller07 environment).gprs .rdx = 512 := by
  rw [readCaller07, mov32StepGprOther .eax 0 _ .rdx (by decide)]
  exact readCaller06Rdx environment
private theorem readCaller07Rdi (environment : Environment) :
    (readCaller07 environment).gprs .rdi = 0 := by
  rw [readCaller07, mov32StepGprOther .eax 0 _ .rdi (by decide)]
  exact readCaller06Rdi environment
private theorem readCaller08Safe (environment : Environment) :
    (readCaller08 environment).fault = none := by
  rw [readCaller08, storeStepFault, readCaller07Safe]
private theorem readCaller08Rip (environment : Environment) :
    (readCaller08 environment).rip = 4198585 := by
  rw [readCaller08, seqStoreRsp40R11.step_rip_eq_of_safe _ (readCaller08Safe environment),
    readCaller07Rip]
  rfl
private theorem readCaller09Safe (environment : Environment) :
    (readCaller09 environment).fault = none := by
  rw [readCaller09, storeStepFault, readCaller08Safe]
private theorem readCaller09Rip (environment : Environment) :
    (readCaller09 environment).rip = 4198590 := by
  rw [readCaller09, seqStoreRsp48R10.step_rip_eq_of_safe _ (readCaller09Safe environment),
    readCaller08Rip]
  rfl

private theorem readCaller09Rax (environment : Environment) :
    (readCaller09 environment).gprs .rax = SYS_read := by
  rw [readCaller09, storeStepGpr, readCaller08, storeStepGpr]
  exact readCaller07Rax environment
private theorem readCaller09Rdx (environment : Environment) :
    (readCaller09 environment).gprs .rdx = 512 := by
  rw [readCaller09, storeStepGpr, readCaller08, storeStepGpr]
  exact readCaller07Rdx environment
private theorem readCaller09Rdi (environment : Environment) :
    (readCaller09 environment).gprs .rdi = 0 := by
  rw [readCaller09, storeStepGpr, readCaller08, storeStepGpr]
  exact readCaller07Rdi environment

private theorem syscallStepRip (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).rip = linuxSyscallEntry := by rfl
private theorem syscallStepFault (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).fault = state.fault := by rfl
private theorem syscallStepGprOther (state : X86_64MachineState) (register : Reg64)
    (notRcx : register ≠ .rcx) (notR11 : register ≠ .r11) :
    (X86_64Instruction.step syscall_op state).gprs register = state.gprs register := by
  change ((state.setGpr64 .rcx _).setGpr64 .r11 _).gprs register = state.gprs register
  simp [X86_64MachineState.setGpr64, notRcx, notR11]
private theorem syscallStepRcx (state : X86_64MachineState) :
    (X86_64Instruction.step syscall_op state).gprs .rcx = state.rip + 2 := by rfl

private theorem linuxFirstReadBoundaryRip (environment : Environment) :
    (linuxFirstReadBoundary environment).rip = linuxSyscallEntry := by
  rw [linuxFirstReadBoundary, syscallStepRip]
private theorem linuxFirstReadBoundarySafe (environment : Environment) :
    (linuxFirstReadBoundary environment).fault = none := by
  rw [linuxFirstReadBoundary, syscallStepFault]
  exact readCaller09Safe environment
private theorem linuxFirstReadBoundaryRax (environment : Environment) :
    (linuxFirstReadBoundary environment).gprs .rax = SYS_read := by
  rw [linuxFirstReadBoundary, syscallStepGprOther _ .rax (by decide) (by decide)]
  exact readCaller09Rax environment
private theorem linuxFirstReadBoundaryRdx (environment : Environment) :
    (linuxFirstReadBoundary environment).gprs .rdx = 512 := by
  rw [linuxFirstReadBoundary, syscallStepGprOther _ .rdx (by decide) (by decide)]
  exact readCaller09Rdx environment
private theorem linuxFirstReadBoundaryRdi (environment : Environment) :
    (linuxFirstReadBoundary environment).gprs .rdi = 0 := by
  rw [linuxFirstReadBoundary, syscallStepGprOther _ .rdi (by decide) (by decide)]
  exact readCaller09Rdi environment
private theorem linuxFirstReadBoundaryRcx (environment : Environment) :
    (linuxFirstReadBoundary environment).gprs .rcx = 4198592 := by
  rw [linuxFirstReadBoundary, syscallStepRcx]
  rw [readCaller09Rip]
  rfl

theorem linuxFirstReadBoundary_exact (environment : Environment) :
    NativeReadBoundary .linux 512 (linuxFirstReadBoundary environment) :=
  .linux (linuxFirstReadBoundaryRip environment) (linuxFirstReadBoundaryRax environment)
    (linuxFirstReadBoundaryRdi environment) (linuxFirstReadBoundaryRdx environment)

private theorem linuxFirstReadSelected (environment : Environment) :
    nativePreparationSelected .linux (linuxFirstReadBoundary environment).rip
      (linuxFirstReadBoundary environment) = true := by
  simp [nativePreparationSelected, linuxFirstReadBoundaryRip environment,
    linuxFirstReadBoundaryRax environment, SYS_read]

private theorem linuxFirstReadIntercepted (environment : Environment) :
    nativePreparationHostIntercept .linux spike3ConcreteExecutionContext
      (linuxFirstReadBoundary environment).rip (linuxFirstReadBoundary environment) =
        some (linuxFirstReadAfterHost environment, none) := by
  unfold nativePreparationHostIntercept
  unfold spike3LinuxCallIntercept
  rw [if_neg]
  · simp [linuxCallIntercept, linuxSyscallIntercept, linuxFirstReadBoundaryRip environment,
      linuxFirstReadBoundaryRax environment, SYS_read, linuxFirstReadAfterHost]
    unfold sysReadHook
    rw [if_pos (by simpa using linuxFirstReadBoundaryRdi environment)]
  · simp [linuxFirstReadBoundaryRip environment, linuxFirstReadBoundaryRax environment,
      SYS_read, SYS_mmap]

private theorem sysReadHookSafeOfStdin (state : X86_64MachineState)
    (stdin : state.gprs .rdi = 0) :
    (sysReadHook (Event := AnyEvent) state).1.fault = state.fault := by
  unfold sysReadHook
  rw [if_pos (by simpa using stdin)]
  rfl
private theorem sysReadHookRipOfStdin (state : X86_64MachineState)
    (stdin : state.gprs .rdi = 0) :
    (sysReadHook (Event := AnyEvent) state).1.rip = state.gprs .rcx := by
  unfold sysReadHook
  rw [if_pos (by simpa using stdin)]

private theorem linuxFirstReadAfterHostSafe (environment : Environment) :
    (linuxFirstReadAfterHost environment).fault = none := by
  rw [linuxFirstReadAfterHost,
    sysReadHookSafeOfStdin _ (linuxFirstReadBoundaryRdi environment)]
  exact linuxFirstReadBoundarySafe environment
private theorem linuxFirstReadAfterHostRip (environment : Environment) :
    (linuxFirstReadAfterHost environment).rip = 4198592 := by
  rw [linuxFirstReadAfterHost,
    sysReadHookRipOfStdin _ (linuxFirstReadBoundaryRdi environment)]
  exact linuxFirstReadBoundaryRcx environment

private theorem readCaller10Safe (environment : Environment) :
    (readCaller10 environment).fault = none := by
  rw [readCaller10, loadStepFault, linuxFirstReadAfterHostSafe]
private theorem readCaller10Rip (environment : Environment) :
    (readCaller10 environment).rip = 4198597 := by
  rw [readCaller10, seqLoadRsp40R11.step_rip_eq_of_safe _ (readCaller10Safe environment),
    linuxFirstReadAfterHostRip]
  rfl
private theorem readCaller11Safe (environment : Environment) :
    (readCaller11 environment).fault = none := by
  rw [readCaller11, loadStepFault, readCaller10Safe]
private theorem readCaller11Rip (environment : Environment) :
    (readCaller11 environment).rip = 4198602 := by
  rw [readCaller11, seqLoadRsp48R10.step_rip_eq_of_safe _ (readCaller11Safe environment),
    readCaller10Rip]
  rfl
private theorem readCaller12Safe (environment : Environment) :
    (readCaller12 environment).fault = none := by
  rw [readCaller12, storeStepFault, readCaller11Safe]
private theorem readCaller12Rip (environment : Environment) :
    (readCaller12 environment).rip = 4198607 := by
  rw [readCaller12, seqStoreRsp28Rax.step_rip_eq_of_safe _ (readCaller12Safe environment),
    readCaller11Rip]
  rfl
private theorem readCaller13Safe (environment : Environment) :
    (readCaller13 environment).fault = none := cmpImm8Safe .rax 0 _ (readCaller12Safe environment)
private theorem readCaller13Rip (environment : Environment) :
    (readCaller13 environment).rip = 4198611 := by
  rw [readCaller13, (seqCmpImm8 .rax 0).step_rip_eq_of_safe _ (readCaller13Safe environment),
    readCaller12Rip]
  rfl

private theorem conditionalTakenOne {environment : Environment} {events : List AnyEvent}
    {state : X86_64MachineState} {instruction : X86_64Instr} {kind : X86BranchCondition}
    (encoding : ConditionalJumpEncoding instruction kind) (chosen : kind.holds state)
    (lookup : instructionAtRipIndexed
      (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) state.rip =
        some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1 state events
      (X86_64Instruction.step instruction state) events [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  exact .conditionalTaken encoding chosen lookup (normalSelected normal) (normalSilent normal)
    safe (.nil _ _)

private theorem jle32StepRipTaken (disp : Int32) (state : X86_64MachineState)
    (chosen : X86BranchCondition.lessEqual.holds state) :
    (X86_64Instruction.step (jle_rel32 disp) state).rip =
      state.rip + 6 + signExtend32To64 disp := by
  simp only [X86BranchCondition.holds] at chosen
  change (if state.zf || (state.sf != state.of_) then
    state.rip + 6 + signExtend32To64 disp else state.rip + 6) = _
  rcases chosen with zero | signed
  · rw [zero]
    rfl
  · have signedBool : (state.sf != state.of_) = true := by
      exact signed
    rw [signedBool]
    simp

private theorem linuxFirstReadSharedSelectedPath (environment : Environment) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 14
      (readCaller00 environment) [] (readCaller13 environment) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 14
      (readCaller00 environment) []
      (X86_64Instruction.step (cmp_r64_imm8 .rax 0) (readCaller12 environment)) [] []
  have p01 := ordinaryOne (environment := environment) (events := []) (seqCmpImm8 .rax 0)
    (callerThroughReadLookupAt environment (readCaller00 environment)
      (4198548, cmp_r64_imm8 .rax 0) (readCaller00Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198552 (readCaller01 environment) (readCaller01Rip environment) (by decide))
    (readCaller01Safe environment)
  have p02 := conditionalFallthroughOne (environment := environment) (events := [])
    (ConditionalJumpEncoding.je32 1162) (secondSuccessBranchNotChosen environment)
    (callerThroughReadLookupAt environment (readCaller01 environment)
      (4198552, je_rel32 1162) (readCaller01Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198558 (readCaller02 environment) (readCaller02Rip environment) (by decide))
    (readCaller02Safe environment)
  have p03 := ordinaryOne (environment := environment) (events := []) seqStoreRsp58Rax
    (callerThroughReadLookupAt environment (readCaller02 environment)
      (4198558, mov_mem64_disp .rsp 0x58 .rax) (readCaller02Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198563 (readCaller03 environment) (readCaller03Rip environment) (by decide))
    (readCaller03Safe environment)
  have p04 := ordinaryOne (environment := environment) (events := []) (seqXor32 .edi .edi)
    (callerThroughReadLookupAt environment (readCaller03 environment)
      (4198563, xor_r32 .edi .edi) (readCaller03Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198565 (readCaller04 environment) (readCaller04Rip environment) (by decide))
    (readCaller04Safe environment)
  have p05 := ordinaryOne (environment := environment) (events := []) seqLoadRsp50Rsi
    (callerThroughReadLookupAt environment (readCaller04 environment)
      (4198565, mov_reg64_mem64_disp .rsi .rsp 0x50) (readCaller04Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198570 (readCaller05 environment) (readCaller05Rip environment) (by decide))
    (readCaller05Safe environment)
  have p06 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .edx 512)
    (callerThroughReadLookupAt environment (readCaller05 environment)
      (4198570, mov_r32 .edx 512) (readCaller05Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198575 (readCaller06 environment) (readCaller06Rip environment) (by decide))
    (readCaller06Safe environment)
  have p07 := ordinaryOne (environment := environment) (events := [])
    (mov_r32_sequential .eax 0)
    (callerThroughReadLookupAt environment (readCaller06 environment)
      (4198575, mov_r32 .eax 0) (readCaller06Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198580 (readCaller07 environment) (readCaller07Rip environment) (by decide))
    (readCaller07Safe environment)
  have p08 := ordinaryOne (environment := environment) (events := []) seqStoreRsp40R11
    (callerThroughReadLookupAt environment (readCaller07 environment)
      (4198580, mov_mem64_disp .rsp 0x40 .r11) (readCaller07Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198585 (readCaller08 environment) (readCaller08Rip environment) (by decide))
    (readCaller08Safe environment)
  have p09 := ordinaryOne (environment := environment) (events := []) seqStoreRsp48R10
    (callerThroughReadLookupAt environment (readCaller08 environment)
      (4198585, mov_mem64_disp .rsp 0x48 .r10) (readCaller08Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198590 (readCaller09 environment) (readCaller09Rip environment) (by decide))
    (readCaller09Safe environment)
  have p10 := nativePreparation_hostBlock (environment := environment)
    (state := readCaller09 environment) (next := linuxFirstReadAfterHost environment)
    (events := []) HostInterceptEncoding.syscall
    (callerThroughReadLookupAt environment (readCaller09 environment)
      (4198590, syscall_op) (readCaller09Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (linuxFirstReadSelected environment) (linuxFirstReadIntercepted environment)
    (linuxFirstReadAfterHostSafe environment)
  have p11 := ordinaryOne (environment := environment) (events := []) seqLoadRsp40R11
    (callerThroughReadLookupAt environment (linuxFirstReadAfterHost environment)
      (4198592, mov_reg64_mem64_disp .r11 .rsp 0x40) (linuxFirstReadAfterHostRip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198597 (readCaller10 environment) (readCaller10Rip environment) (by decide))
    (readCaller10Safe environment)
  have p12 := ordinaryOne (environment := environment) (events := []) seqLoadRsp48R10
    (callerThroughReadLookupAt environment (readCaller10 environment)
      (4198597, mov_reg64_mem64_disp .r10 .rsp 0x48) (readCaller10Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198602 (readCaller11 environment) (readCaller11Rip environment) (by decide))
    (readCaller11Safe environment)
  have p13 := ordinaryOne (environment := environment) (events := []) seqStoreRsp28Rax
    (callerThroughReadLookupAt environment (readCaller11 environment)
      (4198602, mov_mem64_disp .rsp 0x28 .rax) (readCaller11Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198607 (readCaller12 environment) (readCaller12Rip environment) (by decide))
    (readCaller12Safe environment)
  have p14 := ordinaryOne (environment := environment) (events := []) (seqCmpImm8 .rax 0)
    (callerThroughReadLookupAt environment (readCaller12 environment)
      (4198607, cmp_r64_imm8 .rax 0) (readCaller12Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198611 (readCaller13 environment) (readCaller13Rip environment) (by decide))
    (readCaller13Safe environment)
  have q02 := SelectedPrefix.append p01 p02
  have q03 := SelectedPrefix.append q02 p03
  have q04 := SelectedPrefix.append q03 p04
  have q05 := SelectedPrefix.append q04 p05
  have q06 := SelectedPrefix.append q05 p06
  have q07 := SelectedPrefix.append q06 p07
  have q08 := SelectedPrefix.append q07 p08
  have q09 := SelectedPrefix.append q08 p09
  have q10 := SelectedPrefix.append q09 p10
  have q11 := SelectedPrefix.append q10 p11
  have q12 := SelectedPrefix.append q11 p12
  have q13 := SelectedPrefix.append q12 p13
  simpa [readCaller13] using SelectedPrefix.append q13 p14

private theorem linuxFirstReadHappyRip (environment : Environment)
    (happy : ¬ X86BranchCondition.lessEqual.holds (readCaller13 environment)) :
    (linuxFirstReadHappyState environment).rip = 4198617 := by
  rw [linuxFirstReadHappyState,
    (ConditionalJumpEncoding.jle32 420).step_rip_eq_fallthrough _ happy,
    readCaller13Rip]
  rfl
private theorem linuxFirstReadFailureRip (environment : Environment)
    (failure : X86BranchCondition.lessEqual.holds (readCaller13 environment)) :
    (linuxFirstReadFailureState environment).rip = 4199037 := by
  rw [linuxFirstReadFailureState, jle32StepRipTaken 420 _ failure, readCaller13Rip]
  rfl
private theorem linuxFirstReadBranchSafe (environment : Environment) :
    (X86_64Instruction.step (jle_rel32 420) (readCaller13 environment)).fault = none := by
  rw [(ConditionalJumpEncoding.jle32 420).step_fault_eq, readCaller13Safe]

private theorem linuxFirstReadHappyBranchSelectedPath (environment : Environment)
    (happy : ¬ X86BranchCondition.lessEqual.holds (readCaller13 environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1
      (readCaller13 environment) [] (linuxFirstReadHappyState environment) [] [] := by
  simpa [linuxFirstReadHappyState] using conditionalFallthroughOne
    (environment := environment) (events := []) (ConditionalJumpEncoding.jle32 420) happy
    (callerThroughReadLookupAt environment (readCaller13 environment)
      (4198611, jle_rel32 420) (readCaller13Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4198617 (linuxFirstReadHappyState environment)
      (linuxFirstReadHappyRip environment happy) (by decide))
    (linuxFirstReadBranchSafe environment)

private theorem linuxFirstReadFailureBranchSelectedPath (environment : Environment)
    (failure : X86BranchCondition.lessEqual.holds (readCaller13 environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 1
      (readCaller13 environment) [] (linuxFirstReadFailureState environment) [] [] := by
  simpa [linuxFirstReadFailureState] using conditionalTakenOne
    (environment := environment) (events := []) (ConditionalJumpEncoding.jle32 420) failure
    (callerThroughReadLookupAt environment (readCaller13 environment)
      (4198611, jle_rel32 420) (readCaller13Rip environment)
      (by simp [linuxCallerThroughReadIndex]))
    (normalAt 4199037 (linuxFirstReadFailureState environment)
      (linuxFirstReadFailureRip environment failure) (by decide))
    (linuxFirstReadBranchSafe environment)

/-- Projection-limited result of one selected first-read continuation. -/
structure LinuxFirstReadBranchCertificate (environment : Environment) where
  finalState : X86_64MachineState
  finalEvents : List AnyEvent
  fuel : Nat

def linuxFirstReadHappyCertificate (environment : Environment) :
    LinuxFirstReadBranchCertificate environment :=
  { finalState := linuxFirstReadHappyState environment
    finalEvents := []
    fuel := 15 }

def linuxFirstReadFailureCertificate (environment : Environment) :
    LinuxFirstReadBranchCertificate environment :=
  { finalState := linuxFirstReadFailureState environment
    finalEvents := []
    fuel := 15 }

/-- The forward state from the actual read dispatcher meets the happy edge's weakest requirement
    exactly when signed `bytesRead > 0`; the linked `jle` then falls through to chunk scanning. -/
theorem linuxFirstReadHappyCertificate_selectedPath (environment : Environment)
    (happy : ¬ X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
      (linuxFirstReadHappyCertificate environment).fuel
      (linuxSecondFreshMallocCertificate environment).returnState []
      (linuxFirstReadHappyCertificate environment).finalState
      (linuxFirstReadHappyCertificate environment).finalEvents [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 15
      (readCaller00 environment) [] (linuxFirstReadHappyState environment) [] []
  have shared := linuxFirstReadSharedSelectedPath environment
  have happyLocal : ¬ X86BranchCondition.lessEqual.holds (readCaller13 environment) := by
    simpa [linuxFirstReadComparedState] using happy
  have branch := linuxFirstReadHappyBranchSelectedPath environment happyLocal
  simpa [linuxFirstReadHappyCertificate, readCaller00] using SelectedPrefix.append shared branch

/-- The read failure/EOF edge carries the exact compared state to `stream_eof` when the linked
    signed `jle` predicate holds. -/
theorem linuxFirstReadFailureCertificate_selectedPath (environment : Environment)
    (failure : X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment
      (linuxFirstReadFailureCertificate environment).fuel
      (linuxSecondFreshMallocCertificate environment).returnState []
      (linuxFirstReadFailureCertificate environment).finalState
      (linuxFirstReadFailureCertificate environment).finalEvents [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 15
      (readCaller00 environment) [] (linuxFirstReadFailureState environment) [] []
  have shared := linuxFirstReadSharedSelectedPath environment
  have failureLocal : X86BranchCondition.lessEqual.holds (readCaller13 environment) := by
    simpa [linuxFirstReadComparedState] using failure
  have branch := linuxFirstReadFailureBranchSelectedPath environment failureLocal
  simpa [linuxFirstReadFailureCertificate, readCaller00] using
    SelectedPrefix.append shared branch

theorem linuxFirstReadHappyCertificate_projection (environment : Environment)
    (happy : ¬ X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    (linuxFirstReadHappyCertificate environment).finalState.rip = 4198617 ∧
      (linuxFirstReadHappyCertificate environment).finalEvents = [] ∧
      (linuxFirstReadHappyCertificate environment).fuel = 15 := by
  have happyLocal : ¬ X86BranchCondition.lessEqual.holds (readCaller13 environment) := by
    simpa [linuxFirstReadComparedState] using happy
  exact ⟨by simpa [linuxFirstReadHappyCertificate] using
    linuxFirstReadHappyRip environment happyLocal, rfl, rfl⟩

theorem linuxFirstReadFailureCertificate_projection (environment : Environment)
    (failure : X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    (linuxFirstReadFailureCertificate environment).finalState.rip = 4199037 ∧
      (linuxFirstReadFailureCertificate environment).finalEvents = [] ∧
      (linuxFirstReadFailureCertificate environment).fuel = 15 := by
  have failureLocal : X86BranchCondition.lessEqual.holds (readCaller13 environment) := by
    simpa [linuxFirstReadComparedState] using failure
  exact ⟨by simpa [linuxFirstReadFailureCertificate] using
    linuxFirstReadFailureRip environment failureLocal, rfl, rfl⟩

/-- Concrete prologue, two successful fresh allocations, real first read hook, and positive-read
    branch form one exact 88-step selected spine. -/
theorem linuxFirstReadHappySpine (environment : Environment)
    (happy : ¬ X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 88
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstReadHappyCertificate environment).finalState [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 88
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstReadHappyState environment) [] []
  have allocations := linuxTwoFreshMallocCallReturnSpine environment
  have read := linuxFirstReadHappyCertificate_selectedPath environment happy
  simpa [linuxFirstReadHappyCertificate] using SelectedPrefix.append allocations read

/-- Concrete prologue, two successful fresh allocations, real first read hook, and EOF/failure
    branch form one exact 88-step selected spine. -/
theorem linuxFirstReadFailureSpine (environment : Environment)
    (failure : X86BranchCondition.lessEqual.holds (linuxFirstReadComparedState environment)) :
    NativePreparationPrefix .linux spike3ConcreteExecutionContext environment 88
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstReadFailureCertificate environment).finalState [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent :=
    spike3LinuxRuntime AnyEvent spike3ConcreteExecutionContext.arenaGrant
  change SelectedPrefix (nativePreparationSelected .linux)
    (nativePreparationIndex .linux spike3ConcreteExecutionContext environment) 88
      (nativePreparationEntry .linux spike3ConcreteExecutionContext environment) []
      (linuxFirstReadFailureState environment) [] []
  have allocations := linuxTwoFreshMallocCallReturnSpine environment
  have read := linuxFirstReadFailureCertificate_selectedPath environment failure
  simpa [linuxFirstReadFailureCertificate] using SelectedPrefix.append allocations read

end Spikes.Spike3SortLines.Linux
