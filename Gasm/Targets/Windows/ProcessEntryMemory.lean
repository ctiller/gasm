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

import Gasm.MemoryModel.AddressRange
import Gasm.Targets.Windows.Win32API

/-!
Selected Windows-x64 process-entry memory profile.

The ordinary x86 machine state intentionally contains total byte memory and therefore cannot
establish virtual mapping, page protection, provenance, or lifetime. This module adds a distinct
target-owned loader result. It issues a fresh invocation identity, records one address-domain
generation, and carries explicit reserved, guard, and committed-writable stack extents. A checked
consumer may derive a mapped-writable subrange only from that loader result.

The concrete virtual extents below are part of this modeled Windows loader/TCB profile. The cited
Windows sources justify the reserve/commit/guard and x64 stack discipline, not these chosen virtual
addresses. No theorem derives the grant from `X86_64Mem` or from an observed numeric `rsp` alone.
-/

namespace Gasm.Targets.Windows.ProcessEntryMemory

open Gasm.Core
open Gasm.MemoryModel
open Gasm.MemoryModel.AddressRange
open Gasm.Targets.X86_64
open Gasm.Targets.Windows

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Generative process-entry invocation identity. -/
structure InvocationId where
  serial : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Generation of the virtual-to-backing address domain selected for one invocation. -/
structure AddressDomainGeneration where
  invocation : InvocationId
  serial : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Governed finite namespace of already-issued invocations. -/
structure InvocationWorld where
  issued : List InvocationId
  unique : issued.Nodup
  nextSerial : Nat
  issuedBeforeNext : ∀ invocation ∈ issued, invocation.serial < nextSerial

namespace InvocationWorld

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def empty : InvocationWorld where
  issued := []
  unique := List.nodup_nil
  nextSerial := 0
  issuedBeforeNext := by simp

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def fresh (world : InvocationWorld) : InvocationId :=
  ⟨world.nextSerial⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem fresh_not_issued (world : InvocationWorld) : world.fresh ∉ world.issued := by
  intro member
  have before := world.issuedBeforeNext world.fresh member
  exact Nat.lt_irrefl world.nextSerial before

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def issue (world : InvocationWorld) : InvocationWorld where
  issued := world.fresh :: world.issued
  unique := List.nodup_cons.mpr ⟨world.fresh_not_issued, world.unique⟩
  nextSerial := world.nextSerial + 1
  issuedBeforeNext := by
    intro invocation member
    simp only [List.mem_cons] at member
    rcases member with equal | prior
    · subst invocation
      simp [fresh]
    · exact Nat.lt_succ_of_lt (world.issuedBeforeNext invocation prior)

end InvocationWorld

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Exact target-governed issuance of one fresh invocation. -/
structure InvocationIssuance (before after : InvocationWorld) (issued : InvocationId) : Prop where
  issuedFresh : issued = before.fresh
  exactAfter : after = before.issue

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem invocation_issuance (before : InvocationWorld) :
    InvocationIssuance before before.issue before.fresh := by
  exact ⟨rfl, rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
/-- Consecutive target invocations cannot share an identity. -/
theorem consecutive_invocations_ne (world : InvocationWorld) :
    world.issue.fresh ≠ world.fresh := by
  intro equal
  have serialEqual := congrArg InvocationId.serial equal
  change world.nextSerial + 1 = world.nextSerial at serialEqual
  omega

/- REF: windows-thread-stack-size -/
inductive PageState where
  | reserved
  | guard
  | committedWritable
  deriving DecidableEq, Repr

/- REF: windows-thread-stack-size -/
inductive StackLifetime where
  | active
  | retired
  deriving DecidableEq, Repr

/- REF: windows-thread-stack-size -/
/- REF: windows-x64-stack-usage -/
/-- One invocation-scoped stack mapping selected by the Windows loader profile. -/
structure StackMapping (invocation : InvocationId)
    (domain : AddressDomainGeneration) where
  reservedRange : AddressRange
  guardRange : AddressRange
  committedRange : AddressRange
  guardState : PageState
  committedState : PageState
  lifetime : StackLifetime
  reservedWellFormed : reservedRange.WellFormed
  guardWellFormed : guardRange.WellFormed
  committedWellFormed : committedRange.WellFormed
  guardWithinReserve : reservedRange.Contains guardRange
  committedWithinReserve : reservedRange.Contains committedRange
  guardImmediatelyBelow : guardRange.endExclusive = committedRange.start.toNat

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackReservedRange : AddressRange := ⟨0x7FFFFFFE0000, 0x11000⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackGuardRange : AddressRange := ⟨0x7FFFFFFEE000, 0x1000⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackCommittedRange : AddressRange := ⟨0x7FFFFFFEF000, 0x2000⟩

/- REF: windows-thread-stack-size -/
/- REF: windows-x64-stack-usage -/
def activeStackMapping (invocation : InvocationId) (domain : AddressDomainGeneration) :
    StackMapping invocation domain where
  reservedRange := stackReservedRange
  guardRange := stackGuardRange
  committedRange := stackCommittedRange
  guardState := .guard
  committedState := .committedWritable
  lifetime := .active
  reservedWellFormed := ⟨by decide, by decide⟩
  guardWellFormed := ⟨by decide, by decide⟩
  committedWellFormed := ⟨by decide, by decide⟩
  guardWithinReserve := by
    change 0x7FFFFFFE0000 ≤ 0x7FFFFFFEE000 ∧
      0x7FFFFFFEE000 + 0x1000 ≤ 0x7FFFFFFE0000 + 0x11000
    omega
  committedWithinReserve := by
    change 0x7FFFFFFE0000 ≤ 0x7FFFFFFEF000 ∧
      0x7FFFFFFEF000 + 0x2000 ≤ 0x7FFFFFFE0000 + 0x11000
    omega
  guardImmediatelyBelow := by decide

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Target-owned result of loading one PE image at one freshly issued process-entry invocation. -/
structure ProcessEntryLoad (executable : WindowsExecutable) (before : InvocationWorld) where
  private mk ::
  afterInvocations : InvocationWorld
  invocation : InvocationId
  issuance : InvocationIssuance before afterInvocations invocation
  addressDomain : AddressDomainGeneration
  domainScoped : addressDomain.invocation = invocation
  machine : X86_64MachineState
  exactMachine : machine = executable.load
  initialRip : machine.rip = executable.imageBase + executable.entryRva.toUInt64
  initialRsp : machine.rsp = 0x7FFFFFFF0008
  stack : StackMapping invocation addressDomain
  stackExact : stack = activeStackMapping invocation addressDomain

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/- REF: windows-thread-stack-size -/
/- REF: windows-x64-calling-convention -/
/-- The selected Windows loader transition. Programs consume its result; they do not synthesize
    mapping evidence from their own machine-state bytes. -/
def WindowsExecutable.loadProcessEntry (executable : WindowsExecutable)
    (before : InvocationWorld) : ProcessEntryLoad executable before where
  afterInvocations := before.issue
  invocation := before.fresh
  issuance := invocation_issuance before
  addressDomain := ⟨before.fresh, before.nextSerial⟩
  domainScoped := rfl
  machine := executable.load
  exactMachine := rfl
  initialRip := rfl
  initialRsp := rfl
  stack := activeStackMapping before.fresh ⟨before.fresh, before.nextSerial⟩
  stackExact := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Namespace-local spelling used by profile consumers. -/
def loadProcessEntry (executable : WindowsExecutable) (before : InvocationWorld) :
    ProcessEntryLoad executable before :=
  WindowsExecutable.loadProcessEntry executable before

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- The selected address-domain translation. It is identity for this modeled process, but only the
    committed mapping below grants permission to use it. -/
def StackMapping.translate {invocation domain}
    (_mapping : StackMapping invocation domain) (address : Address) : Address := address

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Exact mapped+writable range evidence derived from one target-owned process-entry load. -/
structure MappedWritable {executable : WindowsExecutable} {before : InvocationWorld}
    (loaded : ProcessEntryLoad executable before) (range : AddressRange) : Prop where
  private mk ::
  rangeWellFormed : range.WellFormed
  withinCommitted : loaded.stack.committedRange.Contains range
  writableProtection : loaded.stack.committedState = .committedWritable
  activeLifetime : loaded.stack.lifetime = .active
  backingTranslation : ∀ address, range.ContainsAddress address →
    loaded.stack.translate address = address

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem mappedWritable {executable : WindowsExecutable} {before : InvocationWorld}
    (loaded : ProcessEntryLoad executable before) (range : AddressRange)
    (wellFormed : range.WellFormed)
    (contained : loaded.stack.committedRange.Contains range) :
    MappedWritable loaded range where
  rangeWellFormed := wellFormed
  withinCommitted := contained
  writableProtection := by
    rw [loaded.stackExact]
    rfl
  activeLifetime := by
    rw [loaded.stackExact]
    rfl
  backingTranslation := by intro _ _; rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Target-owned root-lifetime transition after a selected process termination. The concrete
    consumer must separately connect its actual terminal event to this cause. -/
structure RootTeardown {executable : WindowsExecutable} {before : InvocationWorld}
    (loaded : ProcessEntryLoad executable before) (exitCode : UInt32)
    (afterLifetime : StackLifetime) : Prop where
  private mk ::
  priorLifetime : loaded.stack.lifetime = .active
  retired : afterLifetime = .retired

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
theorem rootTeardownAfterExitProcess {executable : WindowsExecutable}
    {before : InvocationWorld} (loaded : ProcessEntryLoad executable before) (exitCode : UInt32) :
    RootTeardown loaded exitCode .retired where
  priorLifetime := by
    rw [loaded.stackExact]
    rfl
  retired := rfl

end Gasm.Targets.Windows.ProcessEntryMemory
