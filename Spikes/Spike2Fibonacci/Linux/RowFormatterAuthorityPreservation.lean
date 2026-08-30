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

import Spikes.Spike2Fibonacci.Linux.RowLoopInvariant

/-!
# Decimal text authority across the parametric row formatter

These proofs reuse the selected-pass preservation API and expose only the four physical write
bounds needed by the two extraction and two reverse-write passes.
-/

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.DecimalSegments
open Gasm.Targets.X86_64.DecimalSchedule

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 5000000
namespace Row8Parametric

private theorem decimalTextBelowRowText {address : Nat}
    (above : spike2RowLinkedTextUpper ≤ address) : 4198635 ≤ address := by
  unfold spike2RowLinkedTextUpper at above
  omega

private theorem Spike2RowCodeAuthority.afterExtractionPass {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8} {stackLower : UInt64}
    {initial : X86_64MachineState}
    (authority : Spike2RowCodeAuthority initial)
    (pass : SelectedExtractionPass (Event := Event) selected indexed backDisp stackLower initial)
    (writeNoWrap : (initial.rsp - 8).toNat + 8 ≤ 2 ^ 64)
    (above : spike2RowLinkedTextUpper ≤ (initial.rsp - 8).toNat) :
    Spike2RowCodeAuthority (extractionFinal backDisp initial) := by
  constructor
  intro address observed
  rw [spike2_extraction_pass_preserves_text_read64 pass address writeNoWrap]
  · exact authority.ordinary address observed
  · have within := spike2RowObservedRips_bounded observed
    unfold spike2RowLinkedTextUpper at within above
    omega

private theorem Spike2RowCodeAuthority.afterWritePass {Event : Type}
    [ExternalCallInterceptor X86_64 Event]
    {selected : Gasm.Core.Address → X86_64MachineState → Bool}
    {indexed : List (UInt64 × X86_64Instr)} {backDisp : UInt8}
    {stackUpper outputLimit : UInt64} {initial : X86_64MachineState}
    (authority : Spike2RowCodeAuthority initial)
    (pass : SelectedWritePass (Event := Event) selected indexed backDisp stackUpper outputLimit initial)
    (writeNoWrap : (initial.gprs .rdi).toNat + 1 ≤ 2 ^ 64)
    (above : spike2RowLinkedTextUpper ≤ (initial.gprs .rdi).toNat) :
    Spike2RowCodeAuthority (writeFinal backDisp initial) := by
  constructor
  intro address observed
  rw [spike2_write_pass_preserves_text_read64 pass address writeNoWrap]
  · exact authority.ordinary address observed
  · have within := spike2RowObservedRips_bounded observed
    unfold spike2RowLinkedTextUpper at within above
    omega

/-- The accepted `Spike2DecimalTextAuthority` advances across the first extraction pass. -/
theorem decimalAuthority_afterExtractionFirst {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterExtractionFirst predecessor) := by
  have pass := spike2ExtractionLinkedLayout_selectedPass
    (afterValueSetup predecessor) formatter.extractionFirstEntry
    formatter.extractionFirstSafety formatter.extractionFirstExecution
    formatter.extractionFirstOrdinary formatter.extractionFirstBranch
  exact physical.entry.afterExtraction pass physical.extractionFirstNoWrap
    (decimalTextBelowRowText physical.extractionFirstAbove)

/-- Decimal text authority advances across the second extraction pass. -/
theorem decimalAuthority_afterExtraction {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterExtraction predecessor) := by
  have first := decimalAuthority_afterExtractionFirst formatter physical
  have pass := spike2ExtractionLinkedLayout_selectedPass
    (afterExtractionFirst predecessor) formatter.extractionSecondEntry
    formatter.extractionSecondSafety formatter.extractionSecondExecution
    formatter.extractionSecondOrdinary formatter.extractionSecondBranch
  exact first.afterExtraction pass physical.extractionSecondNoWrap
    (decimalTextBelowRowText physical.extractionSecondAbove)

/-- Decimal text authority advances across the first reverse-write pass. -/
theorem decimalAuthority_afterWriteFirst {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterWriteFirst predecessor) := by
  have extracted := decimalAuthority_afterExtraction formatter physical
  have pass := spike2WriteLinkedLayout_selectedPass
    (afterExtraction predecessor) formatter.writeFirstEntry formatter.writeFirstSafety
    formatter.writeFirstExecution formatter.writeFirstOrdinary formatter.writeFirstBranch
  exact extracted.afterWrite pass physical.writeFirstNoWrap
    (decimalTextBelowRowText physical.writeFirstAbove)

/-- Complete two-pass formatter preservation theorem. -/
theorem decimalAuthority_afterFormatter {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2DecimalTextAuthority (afterWrite predecessor) := by
  have first := decimalAuthority_afterWriteFirst formatter physical
  have pass := spike2WriteLinkedLayout_selectedPass
    (afterWriteFirst predecessor) formatter.writeSecondEntry formatter.writeSecondSafety
    formatter.writeSecondExecution formatter.writeSecondOrdinary formatter.writeSecondBranch
  exact first.afterWrite pass physical.writeSecondNoWrap
    (decimalTextBelowRowText physical.writeSecondAbove)

theorem rowCodeAuthority_afterExtractionFirst {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2RowCodeAuthority (afterExtractionFirst predecessor) := by
  have pass := spike2ExtractionLinkedLayout_selectedPass
    (afterValueSetup predecessor) formatter.extractionFirstEntry
    formatter.extractionFirstSafety formatter.extractionFirstExecution
    formatter.extractionFirstOrdinary formatter.extractionFirstBranch
  exact physical.rowCodeEntry.afterExtractionPass pass physical.extractionFirstNoWrap
    physical.extractionFirstAbove

theorem rowCodeAuthority_afterExtraction {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2RowCodeAuthority (afterExtraction predecessor) := by
  have first := rowCodeAuthority_afterExtractionFirst formatter physical
  have pass := spike2ExtractionLinkedLayout_selectedPass
    (afterExtractionFirst predecessor) formatter.extractionSecondEntry
    formatter.extractionSecondSafety formatter.extractionSecondExecution
    formatter.extractionSecondOrdinary formatter.extractionSecondBranch
  exact first.afterExtractionPass pass physical.extractionSecondNoWrap
    physical.extractionSecondAbove

theorem rowCodeAuthority_afterWriteFirst {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2RowCodeAuthority (afterWriteFirst predecessor) := by
  have extracted := rowCodeAuthority_afterExtraction formatter physical
  have pass := spike2WriteLinkedLayout_selectedPass
    (afterExtraction predecessor) formatter.writeFirstEntry formatter.writeFirstSafety
    formatter.writeFirstExecution formatter.writeFirstOrdinary formatter.writeFirstBranch
  exact extracted.afterWritePass pass physical.writeFirstNoWrap physical.writeFirstAbove

/-- The same four selected passes preserve the bounded linked row-code observations. -/
theorem rowCodeAuthority_afterFormatter {predecessor : X86_64MachineState}
    (formatter : FormatterFrame predecessor)
    (physical : FormatterAuthorityFrame predecessor) :
    Spike2RowCodeAuthority (afterWrite predecessor) := by
  have first := rowCodeAuthority_afterWriteFirst formatter physical
  have pass := spike2WriteLinkedLayout_selectedPass
    (afterWriteFirst predecessor) formatter.writeSecondEntry formatter.writeSecondSafety
    formatter.writeSecondExecution formatter.writeSecondOrdinary formatter.writeSecondBranch
  exact first.afterWritePass pass physical.writeSecondNoWrap physical.writeSecondAbove

end Row8Parametric

end Spikes.Spike2Fibonacci.Linux
