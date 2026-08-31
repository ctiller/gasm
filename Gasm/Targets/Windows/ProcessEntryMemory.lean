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
import Gasm.Targets.X86_64.Instructions

/-!
Operational Windows-x64 process-entry memory profile.

The authority-bearing state is a host page table indexed by a profile namespace and generation.
Loading threads that state through explicit reserve, guard, and commit transitions. Writable
evidence is indexed by the exact active host state and is derived from page-table membership;
retirement produces a distinct host state in which the committed entry has retired lifetime.

The final program consumer is parameterized by its incoming host state. Reusing the same incoming
state deterministically replays the same identity and therefore cannot establish disjoint
composition; sequential composition must consume `ProcessEntryLoad.afterHost`, while independent
composition requires distinct namespaces (or a separately proved injective renaming).
-/

namespace Gasm.Targets.Windows.ProcessEntryMemory

open Gasm.Core
open Gasm.MemoryModel
open Gasm.MemoryModel.AddressRange
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
structure HostNamespace where
  key : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
structure InvocationId where
  hostNamespace : HostNamespace
  generation : Nat
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
structure AddressDomainGeneration where
  invocation : InvocationId
  generation : Nat
  deriving DecidableEq, Repr

/- REF: windows-thread-stack-size -/
inductive PageState where
  | reserved
  | guard
  | committedWritable
  deriving DecidableEq, Repr

/- REF: windows-thread-stack-size -/
inductive MappingLifetime where
  | active
  | retired
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
structure PageMapping where
  private mk ::
  invocation : InvocationId
  domain : AddressDomainGeneration
  range : AddressRange
  state : PageState
  lifetime : MappingLifetime
  deriving DecidableEq, Repr

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Profile-owned operational host state. Programs receive this state; they do not reconstruct it
    from x86 memory or reset it per invocation. -/
structure WindowsHostState where
  private mk ::
  hostNamespace : HostNamespace
  nextGeneration : Nat
  pageTable : List PageMapping
  liveInvocations : List InvocationId
  deriving Repr

namespace WindowsHostState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Root state supplied once by the selected host profile. Production programs consume an incoming
    state parameter and never call this constructor as part of entry. -/
def root (hostNamespace : HostNamespace) : WindowsHostState :=
  ⟨hostNamespace, 0, [], []⟩

def nextInvocation (host : WindowsHostState) : InvocationId :=
  ⟨host.hostNamespace, host.nextGeneration⟩

def nextDomain (host : WindowsHostState) : AddressDomainGeneration :=
  ⟨host.nextInvocation, host.nextGeneration⟩

def issue (host : WindowsHostState) : WindowsHostState :=
  { host with
    nextGeneration := host.nextGeneration + 1
    liveInvocations := host.nextInvocation :: host.liveInvocations }

def mapPage (host : WindowsHostState) (mapping : PageMapping) : WindowsHostState :=
  { host with pageTable := mapping :: host.pageTable }

def retireInvocation (host : WindowsHostState) (invocation : InvocationId) : WindowsHostState :=
  { host with
    pageTable := host.pageTable.map fun mapping =>
      if mapping.invocation = invocation then { mapping with lifetime := .retired } else mapping
    liveInvocations := host.liveInvocations.filter (· ≠ invocation) }

end WindowsHostState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackReservedRange : AddressRange := ⟨0x7FFFFFFE0000, 0x11000⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackGuardRange : AddressRange := ⟨0x7FFFFFFEE000, 0x1000⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def stackCommittedRange : AddressRange := ⟨0x7FFFFFFEF000, 0x2000⟩

private def stackMapping (host : WindowsHostState) (range : AddressRange)
    (state : PageState) : PageMapping :=
  ⟨host.nextInvocation, host.nextDomain, range, state, .active⟩

/- REF: windows-thread-stack-size -/
def reserveStack (host : WindowsHostState) : WindowsHostState :=
  host.mapPage (stackMapping host stackReservedRange .reserved)

/- REF: windows-thread-stack-size -/
def guardStack (host : WindowsHostState) : WindowsHostState :=
  host.mapPage (stackMapping host stackGuardRange .guard)

/- REF: windows-thread-stack-size -/
def commitStack (host : WindowsHostState) : WindowsHostState :=
  host.mapPage (stackMapping host stackCommittedRange .committedWritable)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- Data result of one operational loader transition. No protection, lifetime, or containment
    proposition is stored here; those are derived by lookup in `afterHost`. -/
structure ProcessEntryLoad (executable : WindowsExecutable) (before : WindowsHostState) where
  private mk ::
  afterHost : WindowsHostState
  invocation : InvocationId
  addressDomain : AddressDomainGeneration
  machine : X86_64MachineState

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def loadProcessEntry (executable : WindowsExecutable) (before : WindowsHostState) :
    ProcessEntryLoad executable before :=
  let reserved := reserveStack before
  let guarded := guardStack reserved
  let committed := commitStack guarded
  { afterHost := committed.issue
    invocation := before.nextInvocation
    addressDomain := before.nextDomain
    machine := executable.load }

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem load_invocation {executable : WindowsExecutable} (before : WindowsHostState) :
    (loadProcessEntry executable before).invocation = before.nextInvocation := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem load_machine {executable : WindowsExecutable} (before : WindowsHostState) :
    (loadProcessEntry executable before).machine = executable.load := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem load_initial_rsp {executable : WindowsExecutable} (before : WindowsHostState) :
    (loadProcessEntry executable before).machine.rsp = 0x7FFFFFFF0008 := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem load_initial_rip {executable : WindowsExecutable} (before : WindowsHostState) :
    (loadProcessEntry executable before).machine.rip =
      executable.imageBase + executable.entryRva.toUInt64 := rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def committedEntry (loaded : ProcessEntryLoad executable before) : PageMapping :=
  ⟨loaded.invocation, loaded.addressDomain, stackCommittedRange, .committedWritable, .active⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem committedEntry_mem (before : WindowsHostState) (executable : WindowsExecutable) :
    committedEntry (loadProcessEntry executable before) ∈
      (loadProcessEntry executable before).afterHost.pageTable := by
  simp [loadProcessEntry, commitStack, guardStack, reserveStack, WindowsHostState.mapPage,
    WindowsHostState.issue, committedEntry, stackMapping, WindowsHostState.nextInvocation,
    WindowsHostState.nextDomain]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
def AddressDomainGeneration.translate (_domain : AddressDomainGeneration)
    (address : Address) : Address := address

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
/-- A use-at-occurrence grant indexed by the exact current host state. -/
structure MappedWritable {executable : WindowsExecutable} {before : WindowsHostState}
    (loaded : ProcessEntryLoad executable before) (current : WindowsHostState)
    (range : AddressRange) : Prop where
  private mk ::
  currentIsLoaded : current = loaded.afterHost
  committedPresent : committedEntry loaded ∈ current.pageTable
  rangeWellFormed : range.WellFormed
  withinCommitted : stackCommittedRange.Contains range
  backingTranslation : ∀ address, range.ContainsAddress address →
    loaded.addressDomain.translate address = address

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#windows-process-entry-grant-prerequisite -/
theorem mappedWritable (before : WindowsHostState) (executable : WindowsExecutable)
    (range : AddressRange) (wellFormed : range.WellFormed)
    (contained : stackCommittedRange.Contains range) :
    MappedWritable (loadProcessEntry executable before)
      (loadProcessEntry executable before).afterHost range where
  currentIsLoaded := rfl
  committedPresent := committedEntry_mem before executable
  rangeWellFormed := wellFormed
  withinCommitted := contained
  backingTranslation := by intro _ _; rfl

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Operational root-exit transition. Authority is destroyed with the root mapping; it is not
    described as a return to a nonexistent recipient. -/
structure RootTeardown {executable : WindowsExecutable} {before : WindowsHostState}
    (loaded : ProcessEntryLoad executable before) (exitCode : UInt32) where
  private mk ::
  afterHost : WindowsHostState
  exactTransition : afterHost = loaded.afterHost.retireInvocation loaded.invocation

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
def rootTeardownAfterExitProcess (loaded : ProcessEntryLoad executable before)
    (exitCode : UInt32) : RootTeardown loaded exitCode :=
  ⟨loaded.afterHost.retireInvocation loaded.invocation, rfl⟩

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
theorem committedEntry_not_active_after_teardown
    (loaded : ProcessEntryLoad executable before) (exitCode : UInt32) :
    committedEntry loaded ∉ (rootTeardownAfterExitProcess loaded exitCode).afterHost.pageTable := by
  simp only [rootTeardownAfterExitProcess, WindowsHostState.retireInvocation,
    List.mem_map, not_exists, not_and]
  intro mapping member
  by_cases same : mapping.invocation = loaded.invocation
  · simp [same, committedEntry]
  · simp only [same, ↓reduceIte]
    intro equal
    exact same (congrArg PageMapping.invocation equal)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
theorem sequential_invocations_ne (before : WindowsHostState) (executable : WindowsExecutable) :
    (loadProcessEntry executable (loadProcessEntry executable before).afterHost).invocation ≠
      (loadProcessEntry executable before).invocation := by
  simp [loadProcessEntry, WindowsHostState.issue, WindowsHostState.nextInvocation,
    commitStack, guardStack, reserveStack, WindowsHostState.mapPage]

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#required-negative-controls -/
theorem namespace_separates_invocations {left right : WindowsHostState}
    (different : left.hostNamespace ≠ right.hostNamespace) (executable : WindowsExecutable) :
    (loadProcessEntry executable left).invocation ≠
      (loadProcessEntry executable right).invocation := by
  intro equal
  exact different (congrArg InvocationId.hostNamespace equal)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Complete target-owned binding-event vocabulary for this profile. Ordinary CPU steps record
    their actual RIP interval and evaluated descriptor list but preserve the host page table.
    Rebind, invalidate, and retirement are distinct operational transitions. -/
inductive BindingEvent where
  | loaded (invocation : InvocationId) (domain : AddressDomainGeneration)
  | cpuStep (invocation : InvocationId) (beforeRip afterRip : UInt64)
      (accesses : List MemAccessSpec)
  | rebound (invocation : InvocationId) (domain : AddressDomainGeneration)
  | invalidated (invocation : InvocationId)
  | retired (invocation : InvocationId)

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
structure ProcessExecution (loaded : ProcessEntryLoad executable before) where
  private mk ::
  host : WindowsHostState
  machine : X86_64MachineState
  binding : Option AddressDomainGeneration
  events : List BindingEvent

namespace ProcessExecution

def begin (loaded : ProcessEntryLoad executable before) : ProcessExecution loaded :=
  ⟨loaded.afterHost, loaded.machine, some loaded.addressDomain,
    [.loaded loaded.invocation loaded.addressDomain]⟩

def cpuStep (execution : ProcessExecution loaded) (instruction : AnyX86_64Instruction) :
    ProcessExecution loaded :=
  let next := X86_64Instruction.step instruction execution.machine
  { host := execution.host
    machine := next
    binding := execution.binding
    events := execution.events ++ [.cpuStep loaded.invocation execution.machine.rip next.rip
      (X86_64Instruction.memAccesses instruction)] }

def rebind (execution : ProcessExecution loaded) (domain : AddressDomainGeneration) :
    ProcessExecution loaded :=
  { execution with
    binding := some domain
    events := execution.events ++ [.rebound loaded.invocation domain] }

def invalidate (execution : ProcessExecution loaded) : ProcessExecution loaded :=
  { execution with
    binding := none
    events := execution.events ++ [.invalidated loaded.invocation] }

def retire (execution : ProcessExecution loaded) (exitCode : UInt32) : ProcessExecution loaded :=
  let teardown := rootTeardownAfterExitProcess loaded exitCode
  { host := teardown.afterHost
    machine := execution.machine
    binding := none
    events := execution.events ++ [.retired loaded.invocation] }

end ProcessExecution

/- REF: docs/M1_X86_CHECKED_AUTHORING_PROOF_BRIEF.md#completion-gate -/
/-- Exhaustive projection of all target binding-changing events. `cpuStep` cannot disappear as a
    rebind because this pattern match is closed over the target event vocabulary. -/
def bindingChanges : List BindingEvent → List BindingEvent
  | [] => []
  | .loaded _ _ :: rest => bindingChanges rest
  | .cpuStep _ _ _ _ :: rest => bindingChanges rest
  | event@(.rebound _ _) :: rest => event :: bindingChanges rest
  | event@(.invalidated _) :: rest => event :: bindingChanges rest
  | event@(.retired _) :: rest => event :: bindingChanges rest

@[simp] theorem bindingChanges_append_cpuStep (events : List BindingEvent)
    (invocation : InvocationId) (beforeRip afterRip : UInt64)
    (accesses : List MemAccessSpec) :
    bindingChanges (events ++ [.cpuStep invocation beforeRip afterRip accesses]) =
      bindingChanges events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [bindingChanges, ih]

@[simp] theorem bindingChanges_append_invalidated (events : List BindingEvent)
    (invocation : InvocationId) :
    bindingChanges (events ++ [.invalidated invocation]) =
      bindingChanges events ++ [.invalidated invocation] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [bindingChanges, ih]

@[simp] theorem bindingChanges_append_rebound (events : List BindingEvent)
    (invocation : InvocationId) (domain : AddressDomainGeneration) :
    bindingChanges (events ++ [.rebound invocation domain]) =
      bindingChanges events ++ [.rebound invocation domain] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [bindingChanges, ih]

@[simp] theorem bindingChanges_begin (loaded : ProcessEntryLoad executable before) :
    bindingChanges (ProcessExecution.begin loaded).events = [] := rfl

@[simp] theorem bindingChanges_cpuStep (execution : ProcessExecution loaded)
    (instruction : AnyX86_64Instruction) :
    bindingChanges (execution.cpuStep instruction).events = bindingChanges execution.events := by
  simp [ProcessExecution.cpuStep]

end Gasm.Targets.Windows.ProcessEntryMemory
