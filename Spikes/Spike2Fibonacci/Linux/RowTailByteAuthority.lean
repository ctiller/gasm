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

import Spikes.Spike2Fibonacci.Linux.RowFormatterAuthorityPreservation

/-! # Decimal text authority across the CR/LF row suffix -/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
namespace Row8Parametric

private theorem decimalTextBelowRowText {address : Nat}
    (above : spike2RowLinkedTextUpper ≤ address) : 4198635 ≤ address := by
  unfold spike2RowLinkedTextUpper at above
  omega

private theorem decimalAuthority_afterMovRax (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) (value : UInt64) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_r64_imm64 .rax value) state) :=
  authority.transportRead64 state _ (by intro; rfl)

private theorem decimalAuthority_afterAddRdi (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state) (value : UInt8) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (add_r64_imm8 .rdi value) state) :=
  authority.transportRead64 state _ (by intro; rfl)

private theorem decimalAuthority_afterMovMem8 (state : X86_64MachineState)
    (authority : Spike2DecimalTextAuthority state)
    (writeNoWrap : (state.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : 4198635 ≤ (state.gprs .rdi).toNat) :
    Spike2DecimalTextAuthority (X86_64Instruction.step (mov_mem8 .rdi .rax) state) := by
  have written := authority.afterWrite8 state (state.gprs .rdi) (state.gprs .rax).toUInt8
    writeNoWrap above
  exact written.transportRead64 _ _ (by intro; rfl)

/-- The first tail byte write preserves decimal text authority. -/
theorem decimalAuthority_afterCarriageReturn {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWrite predecessor))
    (physical : TailAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterCarriageReturn predecessor) := by
  change Spike2DecimalTextAuthority (X86_64Instruction.step (mov_mem8 .rdi .rax)
    (beforeCarriageReturnStore predecessor))
  have loaded := decimalAuthority_afterMovRax (afterWrite predecessor) authority 13
  exact decimalAuthority_afterMovMem8 _ loaded physical.carriageNoWrap
    (decimalTextBelowRowText physical.carriageAbove)

/-- Both CR/LF writes preserve decimal text authority. -/
theorem decimalAuthority_afterLineTerminator {predecessor : X86_64MachineState}
    (authority : Spike2DecimalTextAuthority (afterWrite predecessor))
    (physical : TailAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterLineTerminator predecessor) := by
  have carriage := decimalAuthority_afterCarriageReturn authority physical
  have beforeFeed : Spike2DecimalTextAuthority (beforeLineFeedStore predecessor) := by
    exact decimalAuthority_afterMovRax _
      (decimalAuthority_afterAddRdi _ carriage 1) 10
  have feed := decimalAuthority_afterMovMem8 _ beforeFeed physical.lineFeedNoWrap
    (decimalTextBelowRowText physical.lineFeedAbove)
  exact decimalAuthority_afterAddRdi _ feed 1

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux
