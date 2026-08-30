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

import Spikes.Spike2Fibonacci.Linux.RowWriteSetupAuthority
import Gasm.Targets.X86_64.MemoryFrame.Jcc

/-!
# Physical preservation across a parametric row

The proofs in this module advance existing projection authorities one local slice at a time.
They do not compare complete memories or complete machine states.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
namespace Row8Parametric

private theorem authority_afterRecurrenceLoadStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64 .r8 .r14) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterRecurrenceAddStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (add_r64 .r8 .r15) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterRecurrenceCurrentStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64 .r14 .r15) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterRecurrenceNextStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64 .r15 .r8) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterRecurrenceCounterStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (add_r64_imm8 .r13 1) state) :=
  authority.transportRead64 _ _ (by intro; rfl)

private theorem authority_afterBackEdgeStep (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (jmp_rel32 4294967027) state) := by
  apply authority.transportRead64 state _
  intro address
  exact X86_64Mem.read_congr' .w64 address _ _ (by
    intro k _
    simp only [X86_64Instruction.step]
    apply Gasm.Targets.X86_64.MemoryFrame.JmpRel32.writesWithin
    simp [Gasm.Targets.X86_64.storeFootprint, X86_64Instruction.memAccesses,
      Gasm.Targets.X86_64.footprintFor])

private theorem rowCode_afterLoadStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (mov_r64 .r8 .r14) state) :=
  authority.transportRead64 _ _ (by intro _ _; rfl)

private theorem rowCode_afterAddStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (add_r64 .r8 .r15) state) :=
  authority.transportRead64 _ _ (by intro _ _; rfl)

private theorem rowCode_afterCurrentStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (mov_r64 .r14 .r15) state) :=
  authority.transportRead64 _ _ (by intro _ _; rfl)

private theorem rowCode_afterNextStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (mov_r64 .r15 .r8) state) :=
  authority.transportRead64 _ _ (by intro _ _; rfl)

private theorem rowCode_afterCounterStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (add_r64_imm8 .r13 1) state) :=
  authority.transportRead64 _ _ (by intro _ _; rfl)

private theorem rowCode_afterBackEdgeStep (state : X86_64MachineState)
    (authority : Spike2RowCodeAuthority state) :
    Spike2RowCodeAuthority (X86_64Instruction.step (jmp_rel32 4294967027) state) := by
  apply authority.transportRead64 state _
  intro address _
  exact X86_64Mem.read_congr' .w64 address _ _ (by
    intro k _
    simp only [X86_64Instruction.step]
    apply Gasm.Targets.X86_64.MemoryFrame.JmpRel32.writesWithin
    simp [Gasm.Targets.X86_64.storeFootprint, X86_64Instruction.memAccesses,
      Gasm.Targets.X86_64.footprintFor])

/-- The five register-only recurrence instructions and linked jump preserve decimal text
authority one named projection cutpoint at a time. -/
theorem decimalAuthority_afterRecurrenceLoad {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSyscall predecessor)) :
    Spike2DecimalTextAuthority (afterRecurrenceLoad predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r64 .r8 .r14) (afterWriteSyscall predecessor))
  exact authority_afterRecurrenceLoadStep _ authority

theorem decimalAuthority_afterRecurrenceAdd {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterRecurrenceLoad predecessor)) :
    Spike2DecimalTextAuthority (afterRecurrenceAdd predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (add_r64 .r8 .r15) (afterRecurrenceLoad predecessor))
  exact authority_afterRecurrenceAddStep _ authority

theorem decimalAuthority_afterRecurrenceCurrent {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterRecurrenceAdd predecessor)) :
    Spike2DecimalTextAuthority (afterRecurrenceCurrent predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r64 .r14 .r15) (afterRecurrenceAdd predecessor))
  exact authority_afterRecurrenceCurrentStep _ authority

theorem decimalAuthority_afterRecurrenceNext {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterRecurrenceCurrent predecessor)) :
    Spike2DecimalTextAuthority (afterRecurrenceNext predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (mov_r64 .r15 .r8) (afterRecurrenceCurrent predecessor))
  exact authority_afterRecurrenceNextStep _ authority

theorem decimalAuthority_beforeBackEdge {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterRecurrenceNext predecessor)) :
    Spike2DecimalTextAuthority (beforeBackEdge predecessor) := by
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (add_r64_imm8 .r13 1) (afterRecurrenceNext predecessor))
  exact authority_afterRecurrenceCounterStep _ authority

theorem decimalAuthority_afterRecurrence {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWriteSyscall predecessor)) :
    Spike2DecimalTextAuthority (afterRecurrence predecessor) := by
  have atLoad := decimalAuthority_afterRecurrenceLoad (predecessor := predecessor) authority
  have atAdd := decimalAuthority_afterRecurrenceAdd (predecessor := predecessor) atLoad
  have atCurrent := decimalAuthority_afterRecurrenceCurrent (predecessor := predecessor) atAdd
  have atNext := decimalAuthority_afterRecurrenceNext (predecessor := predecessor) atCurrent
  have atBack := decimalAuthority_beforeBackEdge (predecessor := predecessor) atNext
  change Spike2DecimalTextAuthority
    (X86_64Instruction.step (jmp_rel32 4294967027) (beforeBackEdge predecessor))
  exact authority_afterBackEdgeStep _ atBack

/-- Named recurrence cutpoints preserve bounded row-code authority through the back-edge. -/
theorem rowCodeAuthority_afterRecurrence {predecessor : X86_64MachineState}
    (authority : Spike2RowCodeAuthority (afterWriteSyscall predecessor)) :
    Spike2RowCodeAuthority (afterRecurrence predecessor) := by
  have atLoad : Spike2RowCodeAuthority (afterRecurrenceLoad predecessor) := by
    change Spike2RowCodeAuthority
      (X86_64Instruction.step (mov_r64 .r8 .r14) (afterWriteSyscall predecessor))
    exact rowCode_afterLoadStep _ authority
  have atAdd : Spike2RowCodeAuthority (afterRecurrenceAdd predecessor) := by
    change Spike2RowCodeAuthority
      (X86_64Instruction.step (add_r64 .r8 .r15) (afterRecurrenceLoad predecessor))
    exact rowCode_afterAddStep _ atLoad
  have atCurrent : Spike2RowCodeAuthority (afterRecurrenceCurrent predecessor) := by
    change Spike2RowCodeAuthority
      (X86_64Instruction.step (mov_r64 .r14 .r15) (afterRecurrenceAdd predecessor))
    exact rowCode_afterCurrentStep _ atAdd
  have atNext : Spike2RowCodeAuthority (afterRecurrenceNext predecessor) := by
    change Spike2RowCodeAuthority
      (X86_64Instruction.step (mov_r64 .r15 .r8) (afterRecurrenceCurrent predecessor))
    exact rowCode_afterNextStep _ atCurrent
  have atBack : Spike2RowCodeAuthority (beforeBackEdge predecessor) := by
    change Spike2RowCodeAuthority
      (X86_64Instruction.step (add_r64_imm8 .r13 1) (afterRecurrenceNext predecessor))
    exact rowCode_afterCounterStep _ atNext
  change Spike2RowCodeAuthority
    (X86_64Instruction.step (jmp_rel32 4294967027) (beforeBackEdge predecessor))
  exact rowCode_afterBackEdgeStep _ atBack

/-- Complete row-code authority preservation from formatter entry to recurrence endpoint. -/
theorem LocalRowNeeds.nextRowCodeAuthority {predecessor : X86_64MachineState}
    (needs : LocalRowNeeds predecessor) :
    Spike2RowCodeAuthority (afterRecurrence predecessor) := by
  have formatted := rowCodeAuthority_afterFormatter needs.formatter needs.formatterAuthority
  have line := rowCodeAuthority_afterLineTerminator formatted needs.tailAuthority
  have afterCall := rowCodeAuthority_afterWriteSyscall (predecessor := predecessor) line
  exact rowCodeAuthority_afterRecurrence (predecessor := predecessor) afterCall

/-- Complete non-decimal tail preservation.  The syscall and recurrence are discharged by a
read64 projection lemma, not by exposing an equality of their memories. -/
theorem decimalAuthority_afterTail {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWrite predecessor))
    (physical : TailAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterRecurrence predecessor) := by
  have line := decimalAuthority_afterLineTerminator authority physical
  have afterCall := decimalAuthority_afterWriteSyscall (predecessor := predecessor) line
  exact decimalAuthority_afterRecurrence (predecessor := predecessor) afterCall

/-- Decimal text authority is preserved across the complete two-pass row formatter and tail. -/
theorem decimalAuthority_afterRow {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (formatterPhysical : FormatterAuthorityFrame predecessor)
    (tailPhysical : TailAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterRecurrence predecessor) :=
  decimalAuthority_afterTail
    (predecessor := predecessor)
    (decimalAuthority_afterFormatter formatter formatterPhysical) tailPhysical

/-- The accepted text-authority field of `LocalRowNeeds` is re-established at the recurrence
back-edge using only the current row's local projection premises. -/
theorem LocalRowNeeds.nextDecimalAuthority {predecessor : X86_64MachineState}
    (needs : LocalRowNeeds predecessor) :
    Spike2DecimalTextAuthority (afterRecurrence predecessor) :=
  decimalAuthority_afterRow needs.formatter needs.formatterAuthority needs.tailAuthority

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux
