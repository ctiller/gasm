/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister5

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem spike2_writeFile_call_lowMemory (state : X86_64MachineState)
    (low : Spike2RowLowMemory state) (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterWriteFileCall state) := by
  have rspConcrete : state.rsp = 140737488289664 := rsp.trans spike2_after_prologue_rsp_eq
  have pushed := low.write64 (state.rsp - 8) (state.rip + 6)
    (by rw [rspConcrete]; decide) (by rw [rspConcrete]; decide)
  exact pushed.of_memory_eq (spike2_after_writeFile_call_memory state)

structure Spike2WriteHookResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) where
  final : X86_64MachineState
  finalEventsRev : List AnyEvent
  emitted : List AnyEvent
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
    initial eventsRev final finalEventsRev emitted
  registers : Spike2RowRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713523
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none

opaque spike2_write_hook_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (hrip : state.rip = 5368713517) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (writtenPointer : state.gprs .r9 = state.rsp + 40)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (writeFileIat : state.read64 5368721424 = 5368721424) :
    Spike2WriteHookResult state eventsRev := by
  let called := spike2AfterWriteFileCall state
  let final := (writeFileHook (Event := AnyEvent) called).1
  have target := spike2_writeFile_call_target state hrip writeFileIat
  have calledLow := spike2_writeFile_call_lowMemory state low rsp
  have selfref : called.read64 5368721424 = 5368721424 := by
    rw [calledLow 5368721424 (by decide)]
    exact spike2_after_prologue_writeFileIat
  have iatIndex := spike2_writeFile_iat_index called target selfref
  have callSafe := spike2_writeFile_call_safe state safe
  have certificate := spike2_writeFile_selected_prefix state eventsRev hrip target iatIndex callSafe
  have observations := spike2_writeFile_hook_registerFrame state
  have hookLow := spike2_writeFile_lowMemory state low rsp writtenPointer
  have registerFrame : Spike2RowRegisterFrame state final := {
    rsp := observations.2.1
    r13 := observations.2.2.1
    fault := observations.2.2.2 }
  exact {
    final := final
    finalEventsRev := accumulateEvent eventsRev (writeFileHook (Event := AnyEvent) called).2
    emitted := emittedBy (writeFileHook (Event := AnyEvent) called).2
    certificate := certificate
    registers := registerFrame
    lowMemory := hookLow
    rip := by rw [observations.1, hrip]; rfl
    rsp := observations.2.1.trans rsp
    fault := observations.2.2.2.trans safe }

end Spikes.Spike2Fibonacci.Windows
