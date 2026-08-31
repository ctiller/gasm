/- Copyright 2026 Craig Tiller -/
import Gasm.Targets.X86_64.DecimalSchedule
import Spikes.Spike2Fibonacci.Windows.FormatterDecimal

namespace Spikes.Spike2Fibonacci.Windows

local instance (priority := 1100) spike2WindowsRuntimeForFormatterTextFrame :
    Gasm.Targets.X86_64.ExternalCallInterceptor
    Gasm.Targets.X86_64.X86_64 Gasm.Effects.AnyEvent := spike2WindowsRuntime

open Gasm.Core Gasm.Targets.X86_64 Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

/-- A decimal extraction pass changes only its pushed stack word.  Thus it preserves an aligned
text word when the text observation lies below the stack write. -/
theorem spike2_extraction_preserves_text_word {backDisp : UInt8}
    {state final : X86_64MachineState} (effect : ExtractionPassEffect backDisp state final)
    (address : UInt64) (noWrap : (state.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (below : address.toNat + 8 ≤ (state.rsp - 8).toNat) :
    final.read64 address = state.read64 address := by
  change X86_64Mem.read .w64 address final.memory = X86_64Mem.read .w64 address state.memory
  rw [effect.memory]
  exact X86_64Mem.read64_write_below .w64 state.memory (state.rsp - 8) address _ noWrap below

/-- A decimal reverse-write pass changes only its output byte.  It therefore preserves a text
word below the current output cursor. -/
theorem spike2_write_preserves_text_word {backDisp : UInt8}
    {state final : X86_64MachineState} (effect : WritePassEffect backDisp state final)
    (address : UInt64) (noWrap : (state.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (below : address.toNat + 8 ≤ (state.gprs .rdi).toNat) :
    final.read64 address = state.read64 address := by
  change X86_64Mem.read .w64 address final.memory = X86_64Mem.read .w64 address state.memory
  rw [effect.memory]
  exact X86_64Mem.read64_write_below .w8 state.memory (state.gprs .rdi) address _ noWrap below

end Spikes.Spike2Fibonacci.Windows
