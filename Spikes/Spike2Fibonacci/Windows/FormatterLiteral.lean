/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.FormatterLocal
import Spikes.Spike2Fibonacci.Windows.ItoaBridge

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Core Gasm.Effects Gasm.Targets Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions Gasm.Targets.X86_64.MacroAssembler

private theorem sequentialMovRspByte40 : SequentialInstruction (mov_rsp_byte 0x40 0x46) where
  encoding := .movRspByte 0x40 0x46
  safeFallthrough := by intro _ _; rfl

private theorem sequentialMovRspByte41 : SequentialInstruction (mov_rsp_byte 0x41 0x69) where
  encoding := .movRspByte 0x41 0x69
  safeFallthrough := by intro _ _; rfl

private theorem sequentialMovRspByte42 : SequentialInstruction (mov_rsp_byte 0x42 0x62) where
  encoding := .movRspByte 0x42 0x62
  safeFallthrough := by intro _ _; rfl

private theorem sequentialMovRspByte43 : SequentialInstruction (mov_rsp_byte 0x43 0x28) where
  encoding := .movRspByte 0x43 0x28
  safeFallthrough := by intro _ _; rfl

/-- State after the four concrete stack stores which materialize `"Fib("`. -/
def spike2AfterFibLiteral (state : X86_64MachineState) : X86_64MachineState :=
  X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
    (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)))

theorem spike2_fib_literal_buffer (state : X86_64MachineState) :
    BufHolds (spike2AfterFibLiteral state).memory (state.rsp + 64)
      [0x46, 0x69, 0x62, 0x28] := by
  let s1 := X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state
  let s2 := X86_64Instruction.step (mov_rsp_byte 0x41 0x69) s1
  let s3 := X86_64Instruction.step (mov_rsp_byte 0x42 0x62) s2
  let s4 := X86_64Instruction.step (mov_rsp_byte 0x43 0x28) s3
  have m1 : s1.memory = X86_64Mem.write .w8 (state.rsp + 64) 0x46 state.memory := rfl
  have m2 : s2.memory = X86_64Mem.write .w8 (state.rsp + 65) 0x69 s1.memory := rfl
  have m3 : s3.memory = X86_64Mem.write .w8 (state.rsp + 66) 0x62 s2.memory := rfl
  have m4 : s4.memory = X86_64Mem.write .w8 (state.rsp + 67) 0x28 s3.memory := rfl
  change BufHolds s4.memory (state.rsp + 64) _
  rw [m4, m3, m2, m1]
  have h6465 : state.rsp + 64 ≠ state.rsp + 65 := by bv_decide
  have h6466 : state.rsp + 64 ≠ state.rsp + 66 := by bv_decide
  have h6467 : state.rsp + 64 ≠ state.rsp + 67 := by bv_decide
  have h6566 : state.rsp + 65 ≠ state.rsp + 66 := by bv_decide
  have h6567 : state.rsp + 65 ≠ state.rsp + 67 := by bv_decide
  have h6667 : state.rsp + 66 ≠ state.rsp + 67 := by bv_decide
  have a65 : state.rsp + 64 + 1 = state.rsp + 65 := by bv_decide
  have a66 : state.rsp + 65 + 1 = state.rsp + 66 := by bv_decide
  have a67 : state.rsp + 66 + 1 = state.rsp + 67 := by bv_decide
  simp only [BufHolds]
  rw [a65, a66, a67]
  simp [X86_64Mem.read, X86_64Mem.write, h6465, h6466, h6467,
    h6566, h6567, h6667]

/-- Exact selected producer for the literal `"Fib("` part of every formatter row. -/
theorem spike2_fib_literal_selected_prefix (state : X86_64MachineState)
    (eventsRev : List AnyEvent) (hrip : state.rip = 5368713277) (hsafe : state.fault = none) :
    ProductionPrefix.SelectedPrefix selectedNonInputPlatformCall spike2Indexed 4 state eventsRev
      (spike2AfterFibLiteral state) eventsRev [] := by
  have h1rip : (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state).rip = 5368713282 := by
    rw [show (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state).rip = state.rip + 5 by rfl, hrip]
    rfl
  have h1safe : (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state).fault = none := by
    change state.fault = none
    exact hsafe
  have h2rip : (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)).rip = 5368713287 := by
    rw [show (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)).rip =
      (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state).rip + 5 by rfl, h1rip]
    rfl
  have h2safe : (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)).fault = none := by
    change state.fault = none
    exact hsafe
  have h3rip : (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state))).rip = 5368713292 := by
    rw [show (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state))).rip =
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)).rip + 5 by rfl, h2rip]
    rfl
  have h3safe : (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state))).fault = none := by
    change state.fault = none
    exact hsafe
  have h4safe : (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
      (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
        (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
          (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)))).fault = none := by
    change state.fault = none
    exact hsafe
  have p1 := spike2_selected_local_prefix (mov_rsp_byte 0x40 0x46)
    sequentialMovRspByte40 state eventsRev (by rw [hrip]; rfl)
    5368713282 h1rip (by decide) (by decide) h1safe
  have p2 := spike2_selected_local_prefix (mov_rsp_byte 0x41 0x69)
    sequentialMovRspByte41 (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)
    eventsRev (by rw [h1rip]; rfl) 5368713287 h2rip (by decide) (by decide) h2safe
  have p3 := spike2_selected_local_prefix (mov_rsp_byte 0x42 0x62)
    sequentialMovRspByte42 (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
      (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state))
    eventsRev (by rw [h2rip]; rfl) 5368713292 h3rip (by decide) (by decide) h3safe
  have p4 := spike2_selected_local_prefix (mov_rsp_byte 0x43 0x28)
    sequentialMovRspByte43 (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
      (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
        (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)))
    eventsRev (by rw [h3rip]; rfl) 5368713297 (by
      rw [show (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state)))).rip =
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state))).rip + 5 by rfl, h3rip]
      rfl) (by decide) (by decide) h4safe
  simpa [spike2AfterFibLiteral] using
    ProductionPrefix.SelectedPrefix.append
      (ProductionPrefix.SelectedPrefix.append (ProductionPrefix.SelectedPrefix.append p1 p2) p3) p4

end Spikes.Spike2Fibonacci.Windows
