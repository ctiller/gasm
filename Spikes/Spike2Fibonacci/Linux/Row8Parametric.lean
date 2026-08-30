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

import Spikes.Spike2Fibonacci.Linux.RowScheme
import Spikes.Spike2Fibonacci.Linux.Row8
import Spikes.Spike2Fibonacci.Linux.DecimalRuntime

/-!
# Row 8 from a symbolic predecessor

Every state in this producer is an instruction-step function of the supplied predecessor.
Consequently a cached prefix ending at that predecessor joins syntactically.  The producer
consumes only live projections plus state-local ordinary-code authority; it assumes neither
whole-memory nor whole-machine-state equality.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule
open Spikes.Spike2Fibonacci

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

namespace Row8Parametric

def body (predecessor : X86_64MachineState) : X86_64MachineState :=
  spike2AfterMainHeader predecessor

def afterF (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (body predecessor)

def afterI (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (afterF predecessor)

def afterB (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (afterI predecessor)

def afterOpen (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp_byte 0x43 0x28) (afterB predecessor)

def afterIndexCmp (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (cmp_r64_imm8 .r13 10) (afterOpen predecessor)

def afterIndexHeader (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jge_rel8 41) (afterIndexCmp predecessor)

def indexHeadCode : List X86_64Instr := [
  mov_r64 .rax .r13,
  add_r64_imm8 .rax 0x30,
  lea_rsp .rdi 0x44,
  mov_mem8 .rdi .rax,
  mov_rsp_byte 0x45 0x29,
  mov_rsp_byte 0x46 0x20,
  mov_rsp_byte 0x47 0x3d,
  mov_rsp_byte 0x48 0x20,
  lea_rsp .rdi 0x49
]

def beforeIndexJoin (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps indexHeadCode (afterIndexHeader predecessor)

def afterIndex (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel8 65) (beforeIndexJoin predecessor)

def valueSetupCode : List X86_64Instr := [
  mov_r64 .rax .r14,
  mov_r64_imm64 .r10 10,
  xor_r32 .ecx .ecx
]

def afterValueSetup (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps valueSetupCode (afterIndex predecessor)

def afterExtractionFirst (predecessor : X86_64MachineState) : X86_64MachineState :=
  extractionFinal 236 (afterValueSetup predecessor)

def afterExtraction (predecessor : X86_64MachineState) : X86_64MachineState :=
  extractionFinal 236 (afterExtractionFirst predecessor)

def afterWriteFirst (predecessor : X86_64MachineState) : X86_64MachineState :=
  writeFinal 243 (afterExtraction predecessor)

def afterWrite (predecessor : X86_64MachineState) : X86_64MachineState :=
  writeFinal 243 (afterWriteFirst predecessor)

def lineTerminatorCode : List X86_64Instr := [
  mov_r64_imm64 .rax 13,
  mov_mem8 .rdi .rax,
  add_r64_imm8 .rdi 1,
  mov_r64_imm64 .rax 10,
  mov_mem8 .rdi .rax,
  add_r64_imm8 .rdi 1
]

def afterLineTerminator (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps lineTerminatorCode (afterWrite predecessor)

def writeSetupCode : List X86_64Instr := [
  mov_r64 .r8 .rdi,
  lea_rsp .rsi 0x40,
  sub_r64 .r8 .rsi,
  mov_r64 .rdx .r8,
  mov_r32 .edi 1,
  mov_r32 .eax 1
]

def beforeWriteSyscall (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps writeSetupCode (afterLineTerminator predecessor)

def writeStep (predecessor : X86_64MachineState) : X86_64MachineState × Option AnyEvent :=
  sysWriteHook (Event := AnyEvent)
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor))

def afterWriteSyscall (predecessor : X86_64MachineState) : X86_64MachineState :=
  (writeStep predecessor).1

def writeEvent (predecessor : X86_64MachineState) : Option AnyEvent :=
  (writeStep predecessor).2

def recurrenceHeadCode : List X86_64Instr := [
  mov_r64 .r8 .r14,
  add_r64 .r8 .r15,
  mov_r64 .r14 .r15,
  mov_r64 .r15 .r8,
  add_r64_imm8 .r13 1
]

def beforeBackEdge (predecessor : X86_64MachineState) : X86_64MachineState :=
  runLocalSteps recurrenceHeadCode (afterWriteSyscall predecessor)

def afterRecurrence (predecessor : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (jmp_rel32 4294967027) (beforeBackEdge predecessor)

/-- Selector/interceptor authority at the six exact successor states of the index header.
Each field is a pair of projections (`rip` and `read64 rip`), not a memory relation. -/
structure OpeningFrame (predecessor : X86_64MachineState) : Prop where
  afterF : Spike2OrdinaryCode (afterF predecessor)
  afterI : Spike2OrdinaryCode (afterI predecessor)
  afterB : Spike2OrdinaryCode (afterB predecessor)
  afterOpen : Spike2OrdinaryCode (afterOpen predecessor)
  afterIndexCmp : Spike2OrdinaryCode (afterIndexCmp predecessor)
  afterIndexHeader : Spike2OrdinaryCode (afterIndexHeader predecessor)

/-- Exact safety/placement projections for Row 8's two extraction and two reverse-write passes.
The frame describes only the four concrete pass entries and their successor code observations;
it contains no memory equality and no equality to a generated checkpoint. -/
structure FormatterFrame (predecessor : X86_64MachineState) : Prop where
  extractionFirstEntry : (afterValueSetup predecessor).rip = spike2ExtractionAddress .clearHigh
  extractionFirstSafety : ExtractionSafety 0 (afterValueSetup predecessor)
  extractionFirstExecution : ExtractionExecutionSafety 236 (afterValueSetup predecessor)
  extractionFirstOrdinary : Spike2ExtractionOrdinary 236 (afterValueSetup predecessor)
  extractionFirstBranch :
    X86BranchCondition.notEqual.holds
        (extractionStates (afterValueSetup predecessor)).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds
        (extractionStates (afterValueSetup predecessor)).2.2.2.2.2
  extractionSecondEntry : (afterExtractionFirst predecessor).rip =
    spike2ExtractionAddress .clearHigh
  extractionSecondSafety : ExtractionSafety 0 (afterExtractionFirst predecessor)
  extractionSecondExecution : ExtractionExecutionSafety 236 (afterExtractionFirst predecessor)
  extractionSecondOrdinary : Spike2ExtractionOrdinary 236 (afterExtractionFirst predecessor)
  extractionSecondBranch :
    X86BranchCondition.notEqual.holds
        (extractionStates (afterExtractionFirst predecessor)).2.2.2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds
        (extractionStates (afterExtractionFirst predecessor)).2.2.2.2.2
  writeFirstEntry : (afterExtraction predecessor).rip = spike2WriteAddress .pop
  writeFirstSafety : WriteSafety predecessor.rsp (predecessor.rsp + 136)
    (afterExtraction predecessor)
  writeFirstExecution : WriteExecutionSafety 243 (afterExtraction predecessor)
  writeFirstOrdinary : Spike2WriteOrdinary 243 (afterExtraction predecessor)
  writeFirstBranch :
    X86BranchCondition.notEqual.holds (writeStates (afterExtraction predecessor)).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates (afterExtraction predecessor)).2.2.2
  writeSecondEntry : (afterWriteFirst predecessor).rip = spike2WriteAddress .pop
  writeSecondSafety : WriteSafety predecessor.rsp (predecessor.rsp + 136)
    (afterWriteFirst predecessor)
  writeSecondExecution : WriteExecutionSafety 243 (afterWriteFirst predecessor)
  writeSecondOrdinary : Spike2WriteOrdinary 243 (afterWriteFirst predecessor)
  writeSecondBranch :
    X86BranchCondition.notEqual.holds (writeStates (afterWriteFirst predecessor)).2.2.2 ∨
      ¬ X86BranchCondition.notEqual.holds (writeStates (afterWriteFirst predecessor)).2.2.2

abbrev SequentialBlockFrame (code : List X86_64Instr) (initial : X86_64MachineState) : Prop :=
  ∀ beforeCode instruction suffix, code = beforeCode ++ instruction :: suffix →
    SelectedSequentialStepEvidence (Event := AnyEvent) selectedNonInputPlatformCall
      spike2Indexed initial beforeCode instruction

/-- Projection evidence for the one-digit index path after the conditional header and the three
formatter-setup instructions. -/
structure OpeningRestFrame (predecessor : X86_64MachineState) : Prop where
  indexHead : SequentialBlockFrame indexHeadCode (afterIndexHeader predecessor)
  indexJoinLookup : instructionAtRipIndexed spike2Indexed (beforeIndexJoin predecessor).rip =
    some (jmp_rel8 65)
  indexJoinOrdinary : Spike2OrdinaryCode (afterIndex predecessor)
  indexJoinSafe : (afterIndex predecessor).fault = none
  valueSetup : SequentialBlockFrame valueSetupCode (afterIndex predecessor)

/-- Narrow authority for the non-decimal tail.  The two straight-line blocks carry one bundled
projection record per reached successor; the syscall and back edge expose only their exact
selector/interceptor and safety facts. -/
structure TailFrame (predecessor : X86_64MachineState) : Prop where
  line : SequentialBlockFrame lineTerminatorCode (afterWrite predecessor)
  writeSetup : SequentialBlockFrame writeSetupCode (afterLineTerminator predecessor)
  syscallLookup : instructionAtRipIndexed spike2Indexed (beforeWriteSyscall predecessor).rip =
    some syscall_op
  syscallSelected : selectedNonInputPlatformCall
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor)).rip
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor)) = true
  syscallIntercept : ExternalCallInterceptor.interceptCall X86_64
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor)).rip
    (X86_64Instruction.step syscall_op (beforeWriteSyscall predecessor)) =
      some (afterWriteSyscall predecessor, writeEvent predecessor)
  afterWriteSyscallSafe : (afterWriteSyscall predecessor).fault = none
  liveR13 : (afterWriteSyscall predecessor).gprs .r13 = predecessor.gprs .r13
  liveR14 : (afterWriteSyscall predecessor).gprs .r14 = predecessor.gprs .r14
  liveR15 : (afterWriteSyscall predecessor).gprs .r15 = predecessor.gprs .r15
  recurrence : SequentialBlockFrame recurrenceHeadCode (afterWriteSyscall predecessor)
  backRip : (beforeBackEdge predecessor).rip = 4198701
  backLookup : instructionAtRipIndexed spike2Indexed (beforeBackEdge predecessor).rip =
    some (jmp_rel32 4294967027)
  backOrdinary : Spike2OrdinaryCode (afterRecurrence predecessor)
  backSafe : (afterRecurrence predecessor).fault = none

private theorem ordinarySelected (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    selectedNonInputPlatformCall state.rip state = true := by
  simp [selectedNonInputPlatformCall, ordinary.notLinuxEntry,
    Gasm.Targets.Windows.selectedNonInputWin32Call,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem ordinarySilent (state : X86_64MachineState)
    (ordinary : Spike2OrdinaryCode state) :
    ExternalCallInterceptor.interceptCall X86_64 (Event := AnyEvent) state.rip state = none := by
  change (if state.rip == linuxSyscallEntry then linuxSyscallIntercept _ _ else
      Gasm.Targets.Windows.win32Intercept _ _) = none
  simp [ordinary.notLinuxEntry, Gasm.Targets.Windows.win32Intercept,
    Gasm.Targets.Windows.findIatIndex, ordinary.notWin32Iat]

private theorem bodyRip {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    (entry : Spike2LinuxRowEntry completed current next predecessor) :
    (body predecessor).rip = 4198447 :=
  spike2_after_main_header_body_rip completed predecessor entry.completed_lt entry.rip entry.counter

private theorem indexHeaderPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState}
    {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (oneDigit : completed + 1 < 10)
    (frame : OpeningFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 6
      (body predecessor) eventsRev (afterIndexHeader predecessor) eventsRev [] := by
  have hbody : (body predecessor).rip = 4198447 := bodyRip entry
  have hf : (afterF predecessor).rip = 4198452 := by
    rw [afterF, show (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
      (body predecessor)).rip = (body predecessor).rip + 5 by rfl, hbody]
    decide
  have hi : (afterI predecessor).rip = 4198457 := by
    rw [afterI, show (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (afterF predecessor)).rip = (afterF predecessor).rip + 5 by rfl, hf]
    decide
  have hb : (afterB predecessor).rip = 4198462 := by
    rw [afterB, show (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (afterI predecessor)).rip = (afterI predecessor).rip + 5 by rfl, hi]
    decide
  have hopen : (afterOpen predecessor).rip = 4198467 := by
    rw [afterOpen, show (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
      (afterB predecessor)).rip = (afterB predecessor).rip + 5 by rfl, hb]
    decide
  have hcmp : (afterIndexCmp predecessor).rip = 4198471 := by
    rw [afterIndexCmp, show (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (afterOpen predecessor)).rip = (afterOpen predecessor).rip + 4 by rfl, hopen]
    decide
  have hcounter : (afterOpen predecessor).gprs .r13 = (completed + 1).toUInt64 := by
    change predecessor.gprs .r13 = (completed + 1).toUInt64
    exact entry.counter
  have hfallthrough : ¬ X86BranchCondition.greaterEqual.holds
      (afterIndexCmp predecessor) := by
    exact spike2_index_one_digit (afterOpen predecessor) (completed + 1) oneDigit hcounter
  refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x40 0x46
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
  · rw [hbody]
    rfl
  · exact ordinarySelected _ frame.afterF
  · exact ordinarySilent _ frame.afterF
  · change predecessor.fault = none
    exact entry.safe
  · refine ProductionPrefix.SelectedPrefix.ordinary ({
      encoding := .movRspByte 0x41 0x69
      safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
    · change instructionAtRipIndexed spike2Indexed (afterF predecessor).rip = _
      rw [hf]
      rfl
    · exact ordinarySelected _ frame.afterI
    · exact ordinarySilent _ frame.afterI
    · change predecessor.fault = none
      exact entry.safe
    · refine ProductionPrefix.SelectedPrefix.ordinary ({
        encoding := .movRspByte 0x42 0x62
        safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
      · change instructionAtRipIndexed spike2Indexed (afterI predecessor).rip = _
        rw [hi]
        rfl
      · exact ordinarySelected _ frame.afterB
      · exact ordinarySilent _ frame.afterB
      · change predecessor.fault = none
        exact entry.safe
      · refine ProductionPrefix.SelectedPrefix.ordinary ({
          encoding := .movRspByte 0x43 0x28
          safeFallthrough := by intro _ _; rfl }) ?_ ?_ ?_ ?_ ?_
        · change instructionAtRipIndexed spike2Indexed (afterB predecessor).rip = _
          rw [hb]
          rfl
        · exact ordinarySelected _ frame.afterOpen
        · exact ordinarySilent _ frame.afterOpen
        · change predecessor.fault = none
          exact entry.safe
        · refine ProductionPrefix.SelectedPrefix.ordinary
            (Spikes.Spike2Fibonacci.Linux.Row8BoundaryData.spike2Row8SequentialCmp .r13 10)
            ?_ ?_ ?_ ?_ ?_
          · change instructionAtRipIndexed spike2Indexed (afterOpen predecessor).rip = _
            rw [hopen]
            rfl
          · exact ordinarySelected _ frame.afterIndexCmp
          · exact ordinarySilent _ frame.afterIndexCmp
          · change predecessor.fault = none
            exact entry.safe
          · refine ProductionPrefix.SelectedPrefix.conditionalFallthrough (.jge8 41)
              hfallthrough ?_ ?_ ?_ ?_ ?_
            · change instructionAtRipIndexed spike2Indexed (afterIndexCmp predecessor).rip = _
              rw [hcmp]
              rfl
            · exact ordinarySelected _ frame.afterIndexHeader
            · exact ordinarySilent _ frame.afterIndexHeader
            · change predecessor.fault = none
              exact entry.safe
            · exact .nil _ _

theorem openingPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (oneDigit : completed + 1 < 10)
    (frame : OpeningFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 8
      predecessor eventsRev (afterIndexHeader predecessor) eventsRev [] := by
  exact (spike2_row_header_from_entry (eventsRev := eventsRev) entry).append
    (indexHeaderPrefix entry oneDigit frame)

/-- One-digit index materialization and decimal value setup from the exact symbolic predecessor. -/
theorem openingRestPrefix {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : OpeningRestFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 13
      (afterIndexHeader predecessor) eventsRev (afterValueSetup predecessor) eventsRev [] := by
  have indexHead := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall indexHeadCode spike2Indexed (afterIndexHeader predecessor)
    frame.indexHead eventsRev
  have join : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (beforeIndexJoin predecessor) eventsRev (afterIndex predecessor) eventsRev [] := by
    refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent) (.rel8 65)
      frame.indexJoinLookup ?_ ?_ frame.indexJoinSafe (.nil _ _)
    · exact ordinarySelected _ frame.indexJoinOrdinary
    · exact ordinarySilent _ frame.indexJoinOrdinary
  have setup := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall valueSetupCode spike2Indexed (afterIndex predecessor)
    frame.valueSetup eventsRev
  simpa [indexHeadCode, beforeIndexJoin, afterIndex, valueSetupCode, afterValueSetup] using
    (indexHead.append join).append setup

/-- The production decimal formatter is now wholly parametric in the exact predecessor.  Its
four schedule-sized pass producers share endpoints by definition and therefore compose without
any state transport. -/
theorem formatterPrefix {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : FormatterFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 24
      (afterValueSetup predecessor) eventsRev (afterWrite predecessor) eventsRev [] := by
  have extractionFirst := spike2ExtractionLinkedLayout_selectedPass
    (afterValueSetup predecessor) frame.extractionFirstEntry frame.extractionFirstSafety
    frame.extractionFirstExecution frame.extractionFirstOrdinary frame.extractionFirstBranch
  have extractionSecond := spike2ExtractionLinkedLayout_selectedPass
    (afterExtractionFirst predecessor) frame.extractionSecondEntry frame.extractionSecondSafety
    frame.extractionSecondExecution frame.extractionSecondOrdinary frame.extractionSecondBranch
  have writeFirst := spike2WriteLinkedLayout_selectedPass
    (afterExtraction predecessor) frame.writeFirstEntry frame.writeFirstSafety
    frame.writeFirstExecution frame.writeFirstOrdinary frame.writeFirstBranch
  have writeSecond := spike2WriteLinkedLayout_selectedPass
    (afterWriteFirst predecessor) frame.writeSecondEntry frame.writeSecondSafety
    frame.writeSecondExecution frame.writeSecondOrdinary frame.writeSecondBranch
  have extraction := extractionFirst.selectedPrefix (eventsRev := eventsRev) |>.append
    (extractionSecond.selectedPrefix (eventsRev := eventsRev))
  have write := writeFirst.selectedPrefix (eventsRev := eventsRev) |>.append
    (writeSecond.selectedPrefix (eventsRev := eventsRev))
  simpa [afterExtractionFirst, afterExtraction, afterWriteFirst, afterWrite] using
    extraction.append write

private theorem syscallPrefix {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : TailFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (beforeWriteSyscall predecessor) eventsRev (afterWriteSyscall predecessor)
      (accumulateEvent eventsRev (writeEvent predecessor))
      (emittedBy (writeEvent predecessor)) := by
  refine ProductionPrefix.SelectedPrefix.hostIntercept (Event := AnyEvent)
    (selected := selectedNonInputPlatformCall) (indexed := spike2Indexed) (.syscall)
    (hooked := afterWriteSyscall predecessor) (event := writeEvent predecessor)
    ?_ ?_ ?_ ?_ ?_
  · exact frame.syscallLookup
  · exact frame.syscallSelected
  · exact frame.syscallIntercept
  · exact frame.afterWriteSyscallSafe
  · exact .nil _ _

/-- Parametric CR/LF, `SYS_write`, recurrence, and linked back-edge producer. -/
theorem tailPrefix {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : TailFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 19
      (afterWrite predecessor) eventsRev (afterRecurrence predecessor)
      (accumulateEvent eventsRev (writeEvent predecessor))
      (emittedBy (writeEvent predecessor)) := by
  have line := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall lineTerminatorCode spike2Indexed (afterWrite predecessor)
    frame.line eventsRev
  have setup := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall writeSetupCode spike2Indexed
    (afterLineTerminator predecessor) frame.writeSetup eventsRev
  have syscall := syscallPrefix (eventsRev := eventsRev) frame
  have recurrence := selectedPrefixOfSequentialEvidence (Event := AnyEvent)
    selectedNonInputPlatformCall recurrenceHeadCode spike2Indexed
    (afterWriteSyscall predecessor) frame.recurrence
    (accumulateEvent eventsRev (writeEvent predecessor))
  have back : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
      (beforeBackEdge predecessor) (accumulateEvent eventsRev (writeEvent predecessor))
      (afterRecurrence predecessor) (accumulateEvent eventsRev (writeEvent predecessor)) [] := by
    refine ProductionPrefix.SelectedPrefix.directBranch (Event := AnyEvent)
      (.rel32 4294967027) frame.backLookup ?_ ?_ frame.backSafe (.nil _ _)
    · exact ordinarySelected _ frame.backOrdinary
    · exact ordinarySilent _ frame.backOrdinary
  have beforeCall := line.append setup
  have afterCall := syscall.append (recurrence.append back)
  simpa [lineTerminatorCode, afterLineTerminator, writeSetupCode, beforeWriteSyscall,
    recurrenceHeadCode, beforeBackEdge, afterRecurrence] using beforeCall.append afterCall

/-- Opaque cache boundaries keep downstream row composition independent of constructor spines. -/
opaque openingProducer {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (oneDigit : completed + 1 < 10)
    (frame : OpeningFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 8
      predecessor eventsRev (afterIndexHeader predecessor) eventsRev [] :=
  openingPrefix entry oneDigit frame

opaque openingRestProducer {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : OpeningRestFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 13
      (afterIndexHeader predecessor) eventsRev (afterValueSetup predecessor) eventsRev [] :=
  openingRestPrefix frame

opaque formatterProducer {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : FormatterFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 24
      (afterValueSetup predecessor) eventsRev (afterWrite predecessor) eventsRev [] :=
  formatterPrefix frame

opaque tailProducer {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (frame : TailFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 19
      (afterWrite predecessor) eventsRev (afterRecurrence predecessor)
      (accumulateEvent eventsRev (writeEvent predecessor))
      (emittedBy (writeEvent predecessor)) :=
  tailPrefix frame

/-- Complete Row 8 producer from the exact symbolic predecessor.  All intermediate states are
functions of `predecessor`, so the five schedule-sized producers append without transport. -/
theorem rowPrefix {completed : Nat} {current next : UInt64}
    {predecessor : X86_64MachineState} {eventsRev : List AnyEvent}
    (entry : Spike2LinuxRowEntry completed current next predecessor)
    (oneDigit : completed + 1 < 10)
    (openingFrame : OpeningFrame predecessor)
    (openingRestFrame : OpeningRestFrame predecessor)
    (formatterFrame : FormatterFrame predecessor)
    (tailFrame : TailFrame predecessor) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 64
      predecessor eventsRev (afterRecurrence predecessor)
      (accumulateEvent eventsRev (writeEvent predecessor))
      (emittedBy (writeEvent predecessor)) := by
  have opening := openingProducer (eventsRev := eventsRev) entry oneDigit openingFrame
  have rest := openingRestProducer (eventsRev := eventsRev) openingRestFrame
  have formatter := formatterProducer (eventsRev := eventsRev) formatterFrame
  have tail := tailProducer (eventsRev := eventsRev) tailFrame
  simpa using ((opening.append rest).append formatter).append tail

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux
