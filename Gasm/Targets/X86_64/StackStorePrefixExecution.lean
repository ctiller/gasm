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

import Gasm.Targets.X86_64.StackStorePrefixLink
import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge

/-!
# Production execution of the selected stack-store prefix

This module promotes the exact static fetch facts in `StackStorePrefixLink` into a two-step
`ProductionPrefix` certificate.  The certificate follows `runProgramOutcomeLoop` itself: it
fetches the production `sub rsp, 40`, reaches the exact indexed store address, fetches the
production `mov byte [rsp + 32], value`, and reaches `StackStorePrefix.afterStore` without an
interceptor transition or machine fault.

The caller must supply host-interceptor silence and the initial no-fault fact.  The result grants
no logical ownership, mapping or writability, binding/view validity, dynamic binding-use event,
platform admission, or `VerifiedProgram` authority.  Those remain obligations of the canonical
world, target profile, artifact connection, and final production `VerifiedProgram.compose`.
-/

namespace Gasm.Targets.X86_64.StackStorePrefixExecution

open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.X86_64.StackStorePrefix
open Gasm.Targets.X86_64.StackStorePrefixLink

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- The selected byte store is an ordinary fallthrough instruction.  This is only control-flow
classification; its memory authority is deliberately not part of `SequentialInstruction`. -/
theorem store_sequential (value : UInt8) :
    SequentialInstruction (mov_rsp_byte byteOffset value) where
  encoding := .movRspByte byteOffset value
  safeFallthrough := by
    intro state _
    rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Exact two-step certificate for the selected prefix in the production indexed runner. -/
theorem productionPrefix {Event : Type} [interceptor : ExternalCallInterceptor X86_64 Event]
    (state : X86_64MachineState) (eventsRev : List Event) (value : UInt8)
    (textNoWrap : state.rip.toNat + 9 ≤ 2 ^ 64)
    (initialSafe : state.fault = none)
    (allocateSilent : interceptor.interceptCall
      (afterAllocate state).rip (afterAllocate state) = none)
    (storeSilent : interceptor.interceptCall
      (afterStore value state).rip (afterStore value state) = none) :
    ProductionPrefix (indexed state.rip value) 2 state eventsRev
      (afterStore value state) eventsRev [] := by
  apply ProductionPrefix.ordinary (sub_rsp_sequential frameSize)
    (lookup_allocate state.rip value) allocateSilent
  · change (afterAllocate state).fault = none
    change state.fault = none
    exact initialSafe
  apply ProductionPrefix.ordinary (store_sequential value)
    (lookup_store_after_allocate state value textNoWrap) storeSilent
  · change (afterStore value state).fault = none
    rw [afterStore_fault]
    exact initialSafe
  exact ProductionPrefix.nil _ _

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Consuming the certified prefix's two units of fuel in the actual production loop reaches the
exact post-store state and leaves the reverse event accumulator unchanged. -/
theorem runProgramOutcomeLoop_prefix {Event : Type}
    [interceptor : ExternalCallInterceptor X86_64 Event]
    (state : X86_64MachineState) (eventsRev : List Event) (value : UInt8)
    (textNoWrap : state.rip.toNat + 9 ≤ 2 ^ 64)
    (initialSafe : state.fault = none)
    (allocateSilent : interceptor.interceptCall
      (afterAllocate state).rip (afterAllocate state) = none)
    (storeSilent : interceptor.interceptCall
      (afterStore value state).rip (afterStore value state) = none)
    (continuationFuel : Nat) :
    runProgramOutcomeLoop (indexed state.rip value) (2 + continuationFuel) state eventsRev =
      runProgramOutcomeLoop (indexed state.rip value) continuationFuel
        (afterStore value state) eventsRev := by
  exact (productionPrefix state eventsRev value textNoWrap initialSafe allocateSilent storeSilent).run
    continuationFuel

end Gasm.Targets.X86_64.StackStorePrefixExecution
