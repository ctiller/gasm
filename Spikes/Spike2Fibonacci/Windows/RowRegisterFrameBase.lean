/- Copyright 2026 Craig Tiller -/
import Spikes.Spike2Fibonacci.Windows.RowCallFrame
import Spikes.Spike2Fibonacci.Windows.RowCounterFacts

namespace Spikes.Spike2Fibonacci.Windows

open Gasm.Targets.X86_64

/-- Registers carried unchanged from the driver header to the Win32 call boundary. -/
structure Spike2RowRegisterFrame (initial final : X86_64MachineState) : Prop where
  rsp : final.rsp = initial.rsp
  r13 : final.gprs .r13 = initial.gprs .r13
  fault : final.fault = initial.fault

theorem Spike2RowRegisterFrame.trans {first middle final : X86_64MachineState}
    (left : Spike2RowRegisterFrame first middle)
    (right : Spike2RowRegisterFrame middle final) :
    Spike2RowRegisterFrame first final where
  rsp := right.rsp.trans left.rsp
  r13 := right.r13.trans left.r13
  fault := right.fault.trans left.fault

theorem spike2_main_header_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterMainHeader state) := by
  constructor <;> rfl

theorem spike2_fib_literal_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterFibLiteral state) := by
  constructor <;> rfl

theorem spike2_index_header_registerFrame (state : X86_64MachineState) :
    Spike2RowRegisterFrame state (spike2AfterIndexHeader state) := by
  constructor <;> rfl

end Spikes.Spike2Fibonacci.Windows
