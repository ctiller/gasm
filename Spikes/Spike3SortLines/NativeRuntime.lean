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

import Gasm.Effects.Console
import Gasm.Effects.Inject
import Gasm.Effects.Network
import Gasm.Effects.Process
import Gasm.Core.Verification
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.Windows.Win32API
import Spikes.Spike3SortLines.Platform
import Stdlib.SmolAlloc.Program

/-! The ordinary Linux and Win32 host interceptors remain total simulation helpers for their
general consumers.  Spike 3 selects these grant-indexed runtimes explicitly, so only a consumer
claiming this finite resource capability receives a fallible virtual-memory provider. -/

namespace Spikes.Spike3SortLines

open Gasm.Core
open Gasm.Core.Platform
open Gasm.Core.Verification
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Linux
open Gasm.Targets.Windows
open Stdlib.SmolAlloc

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A caller-provided finite native backing-arena grant.  It has no default: a native execution
    must select either an insufficient grant (for its explicit resource outcome) or a grant known
    to cover the requested mapping. -/
structure Spike3NativeArenaGrant where
  bytes : UInt32
  deriving Repr, DecidableEq

/-- The emitted artifact asks for the grant's bounded amount, with a 64 KiB minimum so even an
    empty/insufficient grant follows the ordinary reservation-and-failure path rather than issuing
    an invalid zero-length OS request. -/
def Spike3NativeArenaGrant.requestedBytes (grant : Spike3NativeArenaGrant) : UInt32 :=
  if grant.bytes < 65536 then 65536 else grant.bytes

/-- Exact admission check for a native virtual-memory reservation.  Zero-sized grants never
    satisfy a nonzero request, and requests cannot exceed the caller's capability. -/
def Spike3NativeArenaGrant.admits (grant : Spike3NativeArenaGrant) (requested : UInt64) : Bool :=
  requested != 0 && requested <= grant.bytes.toUInt64

theorem Spike3NativeArenaGrant.admits_of_le (grant : Spike3NativeArenaGrant)
    {requested : UInt64} (hrequested : requested != 0) (hcapacity : requested <= grant.bytes.toUInt64) :
    grant.admits requested = true := by
  simp [Spike3NativeArenaGrant.admits, hrequested, hcapacity]

/-- Linux syscall results in this unsigned interval encode `-errno` rather than a pointer. -/
def linuxRawErrnoFloor : UInt64 := 0xFFFFFFFFFFFFF001

/-- The explicit `ENOMEM` result used when the caller did not grant the requested arena. -/
def linuxEnomem : UInt64 := 0xFFFFFFFFFFFFFFF4

def isLinuxRawErrno (result : UInt64) : Bool :=
  linuxRawErrnoFloor ≤ result

theorem linuxEnomem_is_raw_errno : isLinuxRawErrno linuxEnomem = true := by
  rfl

/-- Concrete capability whose base and exclusive end are exactly the values installed in the
    Linux program's `rax`/`r15` initialization sequence. -/
def spike3LinuxArena (grant : Spike3NativeArenaGrant) (requested : UInt64) :
    Option NativeArenaCapability :=
  if grant.admits requested then NativeArenaCapability.ofReservation 0x70000000 requested else none

/-- Concrete capability whose base and exclusive end are exactly the values installed in the
    Win32 program's `rax`/`r15` initialization sequence. -/
def spike3WindowsArena (grant : Spike3NativeArenaGrant) (requested : UInt64) :
    Option NativeArenaCapability :=
  if grant.admits requested then NativeArenaCapability.ofReservation 0x20000000 requested else none

/- REF: docs/TARGETS/LINUX.md#22-memory-mapping-mmap-state-model -/
/-- Spike 3's grant-aware `mmap` realization.  Failure is Linux's actual raw `-ENOMEM` encoding,
    not a null pointer; the lowered entry sequence rejects the complete `[-4095, -1]` range
    before it installs an arena base or writes allocator state. -/
def spike3LinuxMmapHook {Event : Type} (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) : X86_64MachineState × Option Event :=
  let requested := state.gprs .rsi
  match spike3LinuxArena grant requested with
  | some arena =>
      ({ (state.setGpr64 .rax arena.base) with rip := state.gprs .rcx }, none)
  | none =>
      ({ (state.setGpr64 .rax linuxEnomem) with rip := state.gprs .rcx }, none)

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's grant-aware `VirtualAlloc` realization.  It pops the import call's return address
    on both success and failure, so the zero result is observed by the caller rather than being a
    stuck IAT state. -/
def spike3VirtualAllocHook {Event : Type} (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) : X86_64MachineState × Option Event :=
  let requested := state.gprs .rdx
  match spike3WindowsArena grant requested with
  | some arena =>
      (popReturnAddress state |>.setGpr64 .rax arena.base, none)
  | none =>
      (popReturnAddress state |>.setGpr64 .rax 0, none)

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's process exit is terminal for both success and resource exhaustion.  The general
    Win32 trace helper retains a nonterminal legacy event state; this selected runtime instead
    records the real process boundary so no execution can fall through after `ExitProcess`. -/
def spike3ExitProcessHook {Event : Type} [Inject ProcessEvent Event]
    (state : X86_64MachineState) : X86_64MachineState × Option Event :=
  let code := (state.gprs .rcx).toUInt32
  ({ state with rip := 0, fault := some .halted }, some (Inject.inject (ProcessEvent.exit code)))

/- REF: docs/TARGETS/LINUX.md#23-semantic-syscall-interception -/
/-- Linux runtime dispatch for a consumer that explicitly selected a Spike 3 finite arena grant. -/
def spike3LinuxCallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    [Inject NetEvent Event] (grant : Spike3NativeArenaGrant) (address : Address)
    (state : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  if address == linuxSyscallEntry && state.gprs .rax == SYS_mmap then
    some (spike3LinuxMmapHook grant state)
  else
    linuxCallIntercept address state

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Win32 runtime dispatch for a consumer that explicitly selected a Spike 3 finite arena grant. -/
def spike3WindowsCallIntercept {Event : Type} [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    [Inject NetEvent Event] (grant : Spike3NativeArenaGrant) (address : Address)
    (state : X86_64MachineState) : Option (X86_64MachineState × Option Event) :=
  match findIatIndex state address with
  | some 3 => some (spike3ExitProcessHook state)
  | some 4 => some (spike3VirtualAllocHook grant state)
  | _ => win32CallIntercept address state

/-- The explicit Linux runtime context selected by the native arena capability. -/
def spike3LinuxRuntime (Event : Type) [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    [Inject NetEvent Event] (grant : Spike3NativeArenaGrant) : ExternalCallInterceptor X86_64 Event where
  interceptCall := spike3LinuxCallIntercept grant

/-- The explicit Win32 runtime context selected by the native arena capability. -/
def spike3WindowsRuntime (Event : Type) [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    [Inject NetEvent Event] (grant : Spike3NativeArenaGrant) : ExternalCallInterceptor X86_64 Event where
  interceptCall := spike3WindowsCallIntercept grant

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The local Linux resource capability.  It has no providers because its effect is to select the
    grant-indexed syscall runtime, not to claim a fictitious import.  Consumers that do not select
    this composition continue using the ordinary Linux runtime and carry no arena premise. -/
def spike3LinuxArenaCapability (Event : Type) : Capability (LinuxX86_64 Event) where
  Context := Spike3NativeArenaGrant
  providers := []
  establishes := fun _ _ _ _ => True

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Capability composition realizing a Linux Spike 3 finite grant as the operational runtime
    above.  This ties the evidence carried at entry directly to the fallible `mmap` transition. -/
def spike3LinuxArenaCapabilities (Event : Type) [Inject ConsoleEvent Event] [Inject ProcessEvent Event]
    [Inject NetEvent Event] : CapabilityComposition (LinuxX86_64 Event) where
  root := spike3LinuxArenaCapability Event
  realize := fun _ grant => spike3LinuxRuntime Event grant
  realizeSupports := by simp [spike3LinuxArenaCapability]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The local Win32 resource capability row.  It is deliberately separate from the target's
    imported-service row: callers compose it with their selected Win32 providers, while this row
    contributes only the finite arena context consumed by `spike3WindowsRuntime`. -/
def spike3WindowsArenaCapability (Event : Type) : Capability (WindowsX86_64 Event) where
  Context := Spike3NativeArenaGrant
  providers := []
  establishes := fun _ _ _ _ => True

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- The grant-indexed Win32 runtime supports every provider in the standard table.  The only
    altered cases are `ExitProcess` (made terminal) and `VirtualAlloc` (made fallible); both still
    resolve their exact target-owned provider slots. -/
theorem spike3WindowsRuntimeSupports (Event : Type) [Inject ConsoleEvent Event]
    [Inject ProcessEvent Event] [Inject NetEvent Event] (grant : Spike3NativeArenaGrant) :
    ∀ artifact provider, provider ∈ standardWindowsProviders →
      Platform.providerLinked (P := WindowsX86_64 Event) artifact provider →
      Platform.runtimeSupports (P := WindowsX86_64 Event)
        (spike3WindowsRuntime Event grant) artifact provider := by
  intro artifact provider hprovider hlinked
  rcases hlinked with ⟨_, hlinkedSlot⟩
  let layout := computeSectionLayout artifact.executable.textBytes.size
    artifact.executable.rdataBytes.size 512
  let slots := artifact.executable.iatFunctionSlots layout.idataRva
  change (match slots[provider.importIndex]? with
    | some address => ∀ state, Gasm.Targets.Windows.findIatIndex state address =
        some provider.iatIndex →
        ((spike3WindowsRuntime Event grant).interceptCall address state).isSome
    | none => False)
  change (match slots[provider.importIndex]? with
    | some address => _
    | none => False) at hlinkedSlot
  generalize hslot : slots[provider.importIndex]? = resolved at hlinkedSlot ⊢
  cases resolved with
  | none => exact hlinkedSlot.elim
  | some address =>
      intro state hfind
      simp only [standardWindowsProviders, List.mem_cons, List.not_mem_nil, or_false] at hprovider
      rcases hprovider with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        change (spike3WindowsCallIntercept grant address state).isSome
        simp [spike3WindowsCallIntercept, win32CallIntercept, win32Intercept, windowsProvider, hfind]

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Full Win32 capability composition for Spike 3: target-owned imported service providers plus
    the caller-provided finite arena grant.  The grant is operational because realization selects
    `spike3WindowsRuntime` from its second context component. -/
def spike3WindowsArenaCapabilities (Event : Type) [Inject ConsoleEvent Event]
    [Inject ProcessEvent Event] [Inject NetEvent Event] :
    CapabilityComposition (WindowsX86_64 Event) where
  root := Capability.compose (windowsHostCapability Event standardWindowsProviders)
    (spike3WindowsArenaCapability Event)
  realize := fun _ context => spike3WindowsRuntime Event context.2
  realizeSupports := by
    intro context artifact provider hmember hlinked
    simp only [Capability.compose] at hmember
    exact spike3WindowsRuntimeSupports Event context.2 artifact provider hmember hlinked

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A failed Linux reservation returns raw `-ENOMEM` and resumes at the syscall continuation. -/
theorem spike3LinuxMmapHook_rejects_insufficient (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rsi) = false) :
    (spike3LinuxMmapHook (Event := AnyEvent) grant state).1.gprs .rax = linuxEnomem := by
  simp [spike3LinuxMmapHook, spike3LinuxArena, h, X86_64MachineState.setGpr64]

theorem spike3LinuxMmapHook_rejection_is_raw_errno (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rsi) = false) :
    isLinuxRawErrno ((spike3LinuxMmapHook (Event := AnyEvent) grant state).1.gprs .rax) = true := by
  rw [spike3LinuxMmapHook_rejects_insufficient grant state h]
  exact linuxEnomem_is_raw_errno

/-- Refusing a reservation changes only the syscall result and continuation; in particular it
    cannot manufacture an allocator header or mutate client memory before the emitted program
    takes its resource-exhaustion branch. -/
theorem spike3LinuxMmapHook_rejection_preserves_memory (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rsi) = false) :
    (spike3LinuxMmapHook (Event := AnyEvent) grant state).1.memory = state.memory := by
  simp [spike3LinuxMmapHook, spike3LinuxArena, h, X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A sufficient Linux grant recovers the ordinary successful reservation result on a fresh
    invocation.  The theorem is intentionally about a new state: failed runs do not mutate a
    hidden global allocator budget. -/
theorem spike3LinuxMmapHook_recovers_with_sufficient_grant (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (hrequested : state.gprs .rsi = 65536)
    (h : grant.admits (state.gprs .rsi) = true) :
    (spike3LinuxMmapHook (Event := AnyEvent) grant state).1.gprs .rax = 0x70000000 := by
  have h65536 : grant.admits 65536 = true := by simpa [hrequested] using h
  simp [spike3LinuxMmapHook, spike3LinuxArena, hrequested, h65536, NativeArenaCapability.ofReservation,
    X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A failed Win32 reservation returns null after the normal call/return transition. -/
theorem spike3VirtualAllocHook_rejects_insufficient (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rdx) = false) :
    (spike3VirtualAllocHook (Event := AnyEvent) grant state).1.gprs .rax = 0 := by
  simp [spike3VirtualAllocHook, spike3WindowsArena, h, popReturnAddress,
    X86_64MachineState.setGpr64]

theorem spike3VirtualAllocHook_rejection_preserves_memory (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rdx) = false) :
    (spike3VirtualAllocHook (Event := AnyEvent) grant state).1.memory = state.memory := by
  simp [spike3VirtualAllocHook, spike3WindowsArena, h, popReturnAddress,
    X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A sufficient Win32 grant recovers the ordinary successful reservation result on a fresh
    invocation. -/
theorem spike3VirtualAllocHook_recovers_with_sufficient_grant (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (hrequested : state.gprs .rdx = 65536)
    (h : grant.admits (state.gprs .rdx) = true) :
    (spike3VirtualAllocHook (Event := AnyEvent) grant state).1.gprs .rax = 0x20000000 := by
  have h65536 : grant.admits 65536 = true := by simpa [hrequested] using h
  simp [spike3VirtualAllocHook, spike3WindowsArena, hrequested, h65536, NativeArenaCapability.ofReservation, popReturnAddress,
    X86_64MachineState.setGpr64]

end Spikes.Spike3SortLines
