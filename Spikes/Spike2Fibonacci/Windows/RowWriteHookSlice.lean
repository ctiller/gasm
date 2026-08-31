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
-/import Spikes.Spike2Fibonacci.NativeLoop
import Spikes.Spike2Fibonacci.Windows.RowRecurrenceRegister5

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForRowWriteHookSlice :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.Windows
open Gasm.Targets.X86_64

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem readString_eq_decodeNativeBytes (state : X86_64MachineState)
    (buffer : Address) (bytes : List UInt8)
    (holds : BufHolds state.memory buffer bytes) :
    state.readString buffer bytes.length = decodeNativeBytes bytes := by
  have observed :
      (List.range bytes.length).map
          (fun index => (X86_64Mem.read .w8 (buffer + index.toUInt64) state.memory).toUInt8) =
        bytes := by
    apply List.ext_getElem
    · simp
    · intro index left right
      have byte := BufHolds_getElem state.memory buffer bytes holds index right
      simpa [left, X86_64Mem.read] using byte
  unfold X86_64MachineState.readString decodeNativeBytes
  rw [observed]
  rfl

/-- A separately compiled logical call boundary: the formatter establishes this shape, while
the generic Win32 theorem below consumes it.  Unrelated call paths acquire no obligation. -/
class WriteFileEmissionShape (state : X86_64MachineState) (buffer : Address)
    (bytes : List UInt8) : Prop where
  bufferArgument : state.gprs .rdx = buffer
  lengthArgument : (state.gprs .r8).toNat = bytes.length
  content : BufHolds state.memory buffer bytes

theorem writeFileHook_emits_shape (state : X86_64MachineState) (buffer : Address)
    (bytes : List UInt8) [shape : WriteFileEmissionShape state buffer bytes] :
    emittedBy (writeFileHook (Event := AnyEvent) state).2 =
      [Inject.inject (ConsoleEvent.out (decodeNativeBytes bytes))] := by
  have text := readString_eq_decodeNativeBytes state buffer bytes shape.content
  simp [writeFileHook, shape.bufferArgument, shape.lengthArgument, emittedBy, text]

theorem spike2_writeFile_call_lowMemory (state : X86_64MachineState)
    (low : Spike2RowLowMemory state) (rsp : state.rsp = spike2AfterPrologue.rsp) :
    Spike2RowLowMemory (spike2AfterWriteFileCall state) := by
  have rspConcrete : state.rsp = 140737488289664 := rsp.trans spike2_after_prologue_rsp_eq
  have pushed := low.write64 (state.rsp - 8) (state.rip + 6)
    (by rw [rspConcrete]; decide) (by rw [rspConcrete]; decide)
  exact pushed.of_memory_eq (spike2_after_writeFile_call_memory state)

structure Spike2WriteHookResult (initial : X86_64MachineState)
    (eventsRev : List AnyEvent) (bytes : List UInt8) where
  final : X86_64MachineState
  finalEventsRev : List AnyEvent
  emitted : List AnyEvent
  certificate : ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 1
    initial eventsRev final finalEventsRev emitted
  registers : Spike2RowRegisterFrame initial final
  fibRegisters : Spike2FibRegisterFrame initial final
  lowMemory : Spike2RowLowMemory final
  rip : final.rip = 5368713523
  rsp : final.rsp = spike2AfterPrologue.rsp
  fault : final.fault = none
  emittedExact : emitted = [Inject.inject (ConsoleEvent.out (decodeNativeBytes bytes))]
  eventsExact : finalEventsRev =
    Inject.inject (ConsoleEvent.out (decodeNativeBytes bytes)) :: eventsRev

opaque spike2_write_hook_slice (state : X86_64MachineState) (eventsRev : List AnyEvent)
    (bytes : List UInt8)
    (hrip : state.rip = 5368713517) (rsp : state.rsp = spike2AfterPrologue.rsp)
    (writtenPointer : state.gprs .r9 = state.rsp + 40)
    (safe : state.fault = none) (low : Spike2RowLowMemory state)
    (writeFileIat : state.read64 5368721424 = 5368721424)
    (bufferArgument : state.gprs .rdx = state.rsp + 64)
    (lengthArgument : (state.gprs .r8).toNat = bytes.length)
    (buffer : BufHolds state.memory (state.rsp + 64) bytes)
    (bufferNoWrap : (state.rsp + 64).toNat + bytes.length < 2 ^ 64) :
    Spike2WriteHookResult state eventsRev bytes := by
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
  have calledMemory : called.memory =
      X86_64Mem.write .w64 (state.rsp - 8) (state.rip + 6) state.memory := by rfl
  have calledBuffer : BufHolds called.memory (state.rsp + 64) bytes := by
    rw [calledMemory, BufHolds_write64_before]
    · exact buffer
    · rw [rsp, spike2_after_prologue_rsp_eq]
      decide
    · rw [rsp, spike2_after_prologue_rsp_eq]
      decide
    · exact bufferNoWrap
  let shape : WriteFileEmissionShape called (state.rsp + 64) bytes := {
    bufferArgument := by exact bufferArgument
    lengthArgument := by exact lengthArgument
    content := calledBuffer }
  letI : WriteFileEmissionShape called (state.rsp + 64) bytes := shape
  have emittedExact := writeFileHook_emits_shape called (state.rsp + 64) bytes
  have hookSome : (writeFileHook (Event := AnyEvent) called).2 =
      some (Inject.inject (ConsoleEvent.out (decodeNativeBytes bytes))) := by
    cases hook : (writeFileHook (Event := AnyEvent) called).2 with
    | none => simp [hook, emittedBy] at emittedExact
    | some event =>
      have eventEq : event = Inject.inject (ConsoleEvent.out (decodeNativeBytes bytes)) := by
        simpa [hook, emittedBy] using emittedExact
      exact congrArg some eventEq
  exact {
    final := final
    finalEventsRev := accumulateEvent eventsRev (writeFileHook (Event := AnyEvent) called).2
    emitted := emittedBy (writeFileHook (Event := AnyEvent) called).2
    certificate := certificate
    registers := registerFrame
    fibRegisters := spike2_writeFile_hook_fibRegisterFrame state
    lowMemory := hookLow
    rip := by rw [observations.1, hrip]; rfl
    rsp := observations.2.1.trans rsp
    fault := observations.2.2.2.trans safe
    emittedExact := emittedExact
    eventsExact := by simp [hookSome, accumulateEvent] }

end Spikes.Spike2Fibonacci.Windows
