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

import Spikes.Spike3SortLines.NativeRuntime
import Spikes.Spike3SortLines.NativeOutcome
import Spikes.Spike3SortLines.Linux.LinkCertificate
import Gasm.Targets.X86_64.EventfulSegment

namespace Spikes.Spike3SortLines.Linux

open Gasm.Effects Gasm.Core Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.Linux Spikes.Spike3SortLines

set_option maxRecDepth 2000000

/-- The no-grant execution admits exactly its rejected `mmap` and final `exit` call boundaries.
All ordinary instruction addresses are selected without accounting overhead. -/
def noGrantSelected (address : Address) (state : X86_64MachineState) : Bool :=
  if address == linuxSyscallEntry then
    state.gprs .rax == SYS_mmap || state.gprs .rax == SYS_exit
  else true

/-- The real final artifact and arbitrary framed stdin used by the rejection proof. -/
def noGrantInitial (stdin : ByteArray) : X86_64MachineState :=
  (spike3ExecutableWithArena spike3NoGrantReservationBytes).loadWithStdin stdin

private theorem noGrantInitial_rip (stdin : ByteArray) : (noGrantInitial stdin).rip = 4198400 := by rfl

private theorem entry_sub_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198400 = some (sub_rsp 120) := by rfl

private def after0 (stdin : ByteArray) := X86_64Instruction.step (sub_rsp 120) (noGrantInitial stdin)

private theorem after0_rip (stdin : ByteArray) : (after0 stdin).rip = 4198404 := by rfl

private theorem entrySubPrefix (stdin : ByteArray) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 1
      (noGrantInitial stdin) [] (after0 stdin) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  refine .ordinary (sub_rsp_sequential 120) entry_sub_lookup ?_ ?_ ?_ (.nil _ _)
  · change noGrantSelected (after0 stdin).rip (after0 stdin) = true
    have hnormal : (after0 stdin).rip ≠ linuxSyscallEntry := by rw [after0_rip]; decide
    simp [noGrantSelected, hnormal]
  · change spike3LinuxCallIntercept noNativeArenaGrant (after0 stdin).rip (after0 stdin) = none
    have hnormal : (after0 stdin).rip ≠ linuxSyscallEntry := by rw [after0_rip]; decide
    simp [spike3LinuxCallIntercept, linuxCallIntercept, linuxSyscallIntercept, hnormal]
  · rfl

private theorem ordinaryStep {instruction : X86_64Instr} {state : X86_64MachineState}
    (encoding : SequentialInstruction instruction)
    (lookup : instructionAtRipIndexed spike3NoGrantResourceArtifactIndex state.rip = some instruction)
    (normal : (X86_64Instruction.step instruction state).rip ≠ linuxSyscallEntry)
    (safe : (X86_64Instruction.step instruction state).fault = none) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 1
      state [] (X86_64Instruction.step instruction state) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  refine .ordinary encoding lookup ?_ ?_ safe (.nil _ _)
  · simp [noGrantSelected, normal]
  · change spike3LinuxCallIntercept noNativeArenaGrant
      (X86_64Instruction.step instruction state).rip (X86_64Instruction.step instruction state) = none
    unfold spike3LinuxCallIntercept
    rw [if_neg]
    · simp [linuxCallIntercept, linuxSyscallIntercept, normal]
    · intro h
      simp at h
      exact normal h.1

private def after1 (stdin : ByteArray) := X86_64Instruction.step (mov_r32 .eax 9) (after0 stdin)
private def after2 (stdin : ByteArray) := X86_64Instruction.step (xor_r32 .edi .edi) (after1 stdin)
private def after3 (stdin : ByteArray) := X86_64Instruction.step (mov_r32 .esi 65536) (after2 stdin)
private def after4 (stdin : ByteArray) := X86_64Instruction.step (mov_r32 .edx 3) (after3 stdin)
private def after5 (stdin : ByteArray) := X86_64Instruction.step (mov_r32 .r10d 0x22) (after4 stdin)
private def after6 (stdin : ByteArray) :=
  X86_64Instruction.step (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF) (after5 stdin)
private def after7 (stdin : ByteArray) := X86_64Instruction.step (xor_r32 .r9d .r9d) (after6 stdin)
private def after8 (stdin : ByteArray) := X86_64Instruction.step syscall_op (after7 stdin)

private theorem after1_rip (stdin : ByteArray) : (after1 stdin).rip = 4198409 := by rfl
private theorem after2_rip (stdin : ByteArray) : (after2 stdin).rip = 4198411 := by rfl
private theorem after3_rip (stdin : ByteArray) : (after3 stdin).rip = 4198416 := by rfl
private theorem after4_rip (stdin : ByteArray) : (after4 stdin).rip = 4198421 := by rfl
private theorem after5_rip (stdin : ByteArray) : (after5 stdin).rip = 4198427 := by rfl
private theorem after6_rip (stdin : ByteArray) : (after6 stdin).rip = 4198437 := by rfl
private theorem after7_rip (stdin : ByteArray) : (after7 stdin).rip = 4198440 := by rfl
private theorem after8_rip (stdin : ByteArray) : (after8 stdin).rip = linuxSyscallEntry := by rfl
private theorem after8_rax (stdin : ByteArray) : (after8 stdin).gprs .rax = SYS_mmap := by rfl
private theorem after8_rsi (stdin : ByteArray) : (after8 stdin).gprs .rsi = 65536 := by rfl
private theorem after8_rcx (stdin : ByteArray) : (after8 stdin).gprs .rcx = 4198442 := by rfl

private theorem entry_mov_eax_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198404 = some (mov_r32 .eax 9) := by rfl
private theorem entry_xor_edi_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198409 = some (xor_r32 .edi .edi) := by rfl
private theorem entry_mov_esi_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198411 = some (mov_r32 .esi 65536) := by rfl
private theorem entry_mov_edx_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198416 = some (mov_r32 .edx 3) := by rfl
private theorem entry_mov_r10d_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198421 = some (mov_r32 .r10d 0x22) := by rfl
private theorem entry_mov_r8_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198427 =
      some (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF) := by rfl
private theorem entry_xor_r9d_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198437 = some (xor_r32 .r9d .r9d) := by rfl
private theorem entry_syscall_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198440 = some syscall_op := by rfl

private theorem xor_r32_sequential (left right : Reg32) :
    SequentialInstruction (xor_r32 left right) where
  encoding := .xor32 left right
  safeFallthrough := by intro state _; cases left <;> cases right <;> rfl

private theorem entryOrdinaryPrefix (stdin : ByteArray) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 8
      (noGrantInitial stdin) [] (after7 stdin) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  have p0 := entrySubPrefix stdin
  have p1 := ordinaryStep (mov_r32_sequential .eax 9) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after0 stdin).rip = some (mov_r32 .eax 9) by
        rw [after0_rip]; exact entry_mov_eax_lookup)
      (by change (after1 stdin).rip ≠ linuxSyscallEntry; rw [after1_rip]; decide) (by rfl)
  have p2 := ordinaryStep (xor_r32_sequential .edi .edi) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after1 stdin).rip = some (xor_r32 .edi .edi) by
        rw [after1_rip]; exact entry_xor_edi_lookup)
      (by change (after2 stdin).rip ≠ linuxSyscallEntry; rw [after2_rip]; decide) (by rfl)
  have p3 := ordinaryStep (mov_r32_sequential .esi 65536) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after2 stdin).rip = some (mov_r32 .esi 65536) by
        rw [after2_rip]; exact entry_mov_esi_lookup)
      (by change (after3 stdin).rip ≠ linuxSyscallEntry; rw [after3_rip]; decide) (by rfl)
  have p4 := ordinaryStep (mov_r32_sequential .edx 3) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after3 stdin).rip = some (mov_r32 .edx 3) by
        rw [after3_rip]; exact entry_mov_edx_lookup)
      (by change (after4 stdin).rip ≠ linuxSyscallEntry; rw [after4_rip]; decide) (by rfl)
  have p5 := ordinaryStep (mov_r32_sequential .r10d 0x22) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after4 stdin).rip = some (mov_r32 .r10d 0x22) by
        rw [after4_rip]; exact entry_mov_r10d_lookup)
      (by change (after5 stdin).rip ≠ linuxSyscallEntry; rw [after5_rip]; decide) (by rfl)
  have p6 := ordinaryStep ((ControlFlowFree.loadImm .r8 0xFFFFFFFFFFFFFFFF).sequential)
      (show instructionAtRipIndexed spike3NoGrantResourceArtifactIndex (after5 stdin).rip =
        some (mov_r64_imm64 .r8 0xFFFFFFFFFFFFFFFF) by
          rw [after5_rip]; exact entry_mov_r8_lookup)
      (by change (after6 stdin).rip ≠ linuxSyscallEntry; rw [after6_rip]; decide) (by rfl)
  have p7 := ordinaryStep (xor_r32_sequential .r9d .r9d) (show instructionAtRipIndexed
      spike3NoGrantResourceArtifactIndex (after6 stdin).rip = some (xor_r32 .r9d .r9d) by
        rw [after6_rip]; exact entry_xor_r9d_lookup)
      (by change (after7 stdin).rip ≠ linuxSyscallEntry; rw [after7_rip]; decide) (by rfl)
  simpa [after0, after1, after2, after3, after4, after5, after6, after7] using
    ProductionPrefix.SelectedPrefix.append
      (ProductionPrefix.SelectedPrefix.append
        (ProductionPrefix.SelectedPrefix.append
          (ProductionPrefix.SelectedPrefix.append
            (ProductionPrefix.SelectedPrefix.append
              (ProductionPrefix.SelectedPrefix.append
                (ProductionPrefix.SelectedPrefix.append p0 p1) p2) p3) p4) p5) p6) p7

private def afterMmap (stdin : ByteArray) : X86_64MachineState :=
  (spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant (after8 stdin)).1

private theorem noGrantRejects (stdin : ByteArray) :
    noNativeArenaGrant.admits ((after8 stdin).gprs .rsi) = false := by
  simpa only [after8_rsi] using
    (show noNativeArenaGrant.admits 65536 = false by decide)

private theorem afterMmap_eq (stdin : ByteArray) :
    afterMmap stdin =
      { (after8 stdin).setGpr64 .rax linuxEnomem with rip := (after8 stdin).gprs .rcx } := by
  unfold afterMmap spike3LinuxMmapHook spike3LinuxArena
  simp only [after8_rsi]
  have hreject : noNativeArenaGrant.admits 65536 = false := by decide
  simp [hreject]

private theorem afterMmap_rip (stdin : ByteArray) : (afterMmap stdin).rip = 4198442 := by
  rw [afterMmap_eq, after8_rcx]

private theorem afterMmap_rax (stdin : ByteArray) : (afterMmap stdin).gprs .rax = linuxEnomem := by
  rw [afterMmap_eq]
  rfl

private theorem afterMmap_safe (stdin : ByteArray) : (afterMmap stdin).fault = none := by
  rw [afterMmap_eq]
  rfl

private theorem mmapHook_event_none (state : X86_64MachineState) :
    (spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant state).2 = none := by
  unfold spike3LinuxMmapHook spike3LinuxArena
  by_cases h : noNativeArenaGrant.admits (state.gprs .rsi) = true
  · simp only [h, ↓reduceIte]
    cases Stdlib.SmolAlloc.NativeArenaCapability.ofReservation 0x70000000 (state.gprs .rsi) <;> rfl
  · simp [h]

private theorem mmapRejectionPrefix (stdin : ByteArray) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 1
      (after7 stdin) [] (afterMmap stdin) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := noGrantSelected) (indexed := spike3NoGrantResourceArtifactIndex)
    (fuel := 0) (state := after7 stdin) (hooked := afterMmap stdin) (final := afterMmap stdin)
    (eventsRev := []) (finalEventsRev := []) (emitted := []) (instruction := syscall_op)
    (event := (none : Option AnyEvent))
    (HostInterceptEncoding.syscall : HostInterceptEncoding syscall_op) ?_ ?_ ?_ ?_
    (.nil _ _)
  · change instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198440 = some syscall_op
    exact entry_syscall_lookup
  · change noGrantSelected linuxSyscallEntry (after8 stdin) = true
    simp [noGrantSelected, after8_rax]
  · change spike3LinuxCallIntercept noNativeArenaGrant linuxSyscallEntry (after8 stdin) =
      some (afterMmap stdin, none)
    simp [spike3LinuxCallIntercept, after8_rax, SYS_mmap, afterMmap]
    generalize hhook : spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant (after8 stdin) = outcome
    rcases outcome with ⟨hooked, event⟩
    have hevent : event = none := by
      calc
        event = (spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant (after8 stdin)).2 :=
          (congrArg Prod.snd hhook).symm
        _ = none := mmapHook_event_none (after8 stdin)
    subst event
    rfl
  · exact afterMmap_safe stdin

private def afterCmp (stdin : ByteArray) :=
  X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001) (afterMmap stdin)
private def afterBranch (stdin : ByteArray) := X86_64Instruction.step (jae_rel32 1265) (afterCmp stdin)

private theorem stepCmpRax (state : X86_64MachineState) :
    X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001) state =
      { state.setFlagsCmp64 (state.gprs .rax) (signExtendUInt32To64 0xFFFFF001) with rip := state.rip + 7 } := rfl
private theorem stepJae (state : X86_64MachineState) :
    X86_64Instruction.step (jae_rel32 1265) state =
      { state with rip := if !state.cf then state.rip + 6 + signExtend32To64 1265 else state.rip + 6 } := rfl

private theorem stepCmpRax_cf (state : X86_64MachineState) :
    (X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001) state).cf =
      (state.gprs .rax < signExtendUInt32To64 0xFFFFF001) := by
  rw [stepCmpRax]
  exact X86_64MachineState.setFlagsCmp64_cf _ _ _

private theorem afterCmp_cf (stdin : ByteArray) : (afterCmp stdin).cf = false := by
  unfold afterCmp
  generalize hcf : (X86_64Instruction.step (cmp_r64_imm32 .rax 0xFFFFF001)
    (afterMmap stdin)).cf = flag
  cases flag with
  | false => rfl
  | true =>
    exfalso
    rw [stepCmpRax_cf] at hcf
    rw [afterMmap_rax] at hcf
    have hnot : ¬ (linuxEnomem < signExtendUInt32To64 0xFFFFF001) := by decide
    exact hnot hcf
private theorem afterCmp_rip (stdin : ByteArray) : (afterCmp stdin).rip = 4198449 := by
  unfold afterCmp
  rw [stepCmpRax]
  change (afterMmap stdin).rip + 7 = 4198449
  rw [afterMmap_rip]
  decide
set_option maxHeartbeats 1000000 in
private theorem afterBranch_rip (stdin : ByteArray) : (afterBranch stdin).rip = spike3NoGrantResourceFailureBase := by
  unfold afterBranch
  rw [stepJae, afterCmp_cf, afterCmp_rip]
  rfl
private theorem afterBranch_safe (stdin : ByteArray) : (afterBranch stdin).fault = none := by
  change (afterCmp stdin).fault = none
  unfold afterCmp
  rw [stepCmpRax]
  exact afterMmap_safe stdin

private theorem cmpPrefix (stdin : ByteArray) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 1
      (afterMmap stdin) [] (afterCmp stdin) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  apply ordinaryStep (cmp_r64_imm32_sequential .rax 0xFFFFF001)
  · change instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198442 =
      some (cmp_r64_imm32 .rax 0xFFFFF001)
    rfl
  · change (afterCmp stdin).rip ≠ linuxSyscallEntry
    rw [afterCmp_rip]; decide
  · rw [stepCmpRax]
    exact afterMmap_safe stdin

private theorem branchToResourcePrefix (stdin : ByteArray) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 1
      (afterCmp stdin) [] (afterBranch stdin) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  refine .conditionalTaken (.jae32 1265) ?_ ?_ ?_ ?_ ?_ (.nil _ _)
  · change (afterCmp stdin).cf = false
    exact afterCmp_cf stdin
  · change instructionAtRipIndexed spike3NoGrantResourceArtifactIndex 4198449 = some (jae_rel32 1265)
    rfl
  · change noGrantSelected (afterBranch stdin).rip (afterBranch stdin) = true
    have normal : (afterBranch stdin).rip ≠ linuxSyscallEntry := by
      rw [afterBranch_rip, spike3_no_grant_resource_failure_base]; decide
    simp [noGrantSelected, normal]
  · change spike3LinuxCallIntercept noNativeArenaGrant (afterBranch stdin).rip (afterBranch stdin) = none
    have normal : (afterBranch stdin).rip ≠ linuxSyscallEntry := by
      rw [afterBranch_rip, spike3_no_grant_resource_failure_base]; decide
    unfold spike3LinuxCallIntercept
    rw [if_neg]
    · simp [linuxCallIntercept, linuxSyscallIntercept, normal]
    · intro h; simp at h; exact normal h.1
  · exact afterBranch_safe stdin

private def afterExitCode (state : X86_64MachineState) :=
  X86_64Instruction.step (mov_r32 .edi spike3ResourceFailureExitCode) state
private def afterExitNumber (state : X86_64MachineState) :=
  X86_64Instruction.step (mov_r32 .eax 60) (afterExitCode state)
private theorem afterExitCode_rip (state : X86_64MachineState)
    (hrip : state.rip = spike3NoGrantResourceFailureBase) : (afterExitCode state).rip =
      spike3NoGrantResourceFailureBase + 5 := by
  unfold afterExitCode
  change state.rip + 5 = spike3NoGrantResourceFailureBase + 5
  rw [hrip]
private theorem afterExitNumber_rip (state : X86_64MachineState)
    (hrip : state.rip = spike3NoGrantResourceFailureBase) : (afterExitNumber state).rip =
      spike3NoGrantResourceFailureBase + 10 := by
  unfold afterExitNumber afterExitCode
  change state.rip + 5 + 5 = spike3NoGrantResourceFailureBase + 10
  rw [hrip]
  decide
private theorem afterExitNumber_rax (state : X86_64MachineState) : (afterExitNumber state).gprs .rax = 60 := by rfl
private theorem afterExitNumber_rdi (state : X86_64MachineState) :
    (afterExitNumber state).gprs .rdi = spike3ResourceFailureExitCode.toUInt64 := by rfl

private theorem resourceTail (state : X86_64MachineState)
    (hrip : state.rip = spike3NoGrantResourceFailureBase) (safe : state.fault = none) :
    letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
    ProductionPrefix.SelectedPrefix (Event := AnyEvent) noGrantSelected spike3NoGrantResourceArtifactIndex 2
      state [] (afterExitNumber state) [] [] := by
  letI : ExternalCallInterceptor X86_64 AnyEvent := spike3LinuxRuntime AnyEvent noNativeArenaGrant
  have p0 := ordinaryStep (mov_r32_sequential .edi spike3ResourceFailureExitCode)
    (show instructionAtRipIndexed spike3NoGrantResourceArtifactIndex state.rip =
      some (mov_r32 .edi spike3ResourceFailureExitCode) by rw [hrip]; exact spike3_no_grant_resource_failure_exit_code_lookup)
    (by
      change (afterExitCode state).rip ≠ linuxSyscallEntry
      rw [afterExitCode_rip state hrip, spike3_no_grant_resource_failure_base]
      decide)
    (by change state.fault = none; exact safe)
  have p1 := ordinaryStep (mov_r32_sequential .eax 60)
    (show instructionAtRipIndexed spike3NoGrantResourceArtifactIndex (afterExitCode state).rip = some (mov_r32 .eax 60) by
      rw [afterExitCode_rip state hrip]
      exact spike3_no_grant_resource_failure_lookup
        (spike3NoGrantResourceFailureBase + 5, mov_r32 .eax 60) (by
          have hsize : (X86_64Instruction.encode
            (mov_r32 .edi spike3ResourceFailureExitCode)).size = 5 := rfl
          simp [indexInstructions, indexInstructions.loop, spike3ResourceFailureInstructions, hsize]))
    (by
      change (afterExitNumber state).rip ≠ linuxSyscallEntry
      rw [afterExitNumber_rip state hrip, spike3_no_grant_resource_failure_base]
      decide)
    (by change state.fault = none; exact safe)
  simpa [afterExitCode, afterExitNumber] using ProductionPrefix.SelectedPrefix.append p0 p1

end Spikes.Spike3SortLines.Linux
