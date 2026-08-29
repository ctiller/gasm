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
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.Windows.Win32API
import Spikes.Spike3SortLines.Platform

/-! The ordinary Linux and Win32 host interceptors remain total simulation helpers for their
general consumers.  Spike 3 selects these grant-indexed runtimes explicitly, so only a consumer
claiming this finite resource capability receives a fallible virtual-memory provider. -/

namespace Spikes.Spike3SortLines

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Linux
open Gasm.Targets.Windows

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A caller-provided finite native backing-arena grant.  It has no default: a native execution
    must select either an insufficient grant (for its explicit resource outcome) or a grant known
    to cover the requested mapping. -/
structure Spike3NativeArenaGrant where
  bytes : UInt64
  deriving Repr, DecidableEq

/-- Exact admission check for a native virtual-memory reservation.  Zero-sized grants never
    satisfy a nonzero request, and requests cannot exceed the caller's capability. -/
def Spike3NativeArenaGrant.admits (grant : Spike3NativeArenaGrant) (requested : UInt64) : Bool :=
  requested != 0 && requested <= grant.bytes

theorem Spike3NativeArenaGrant.admits_of_le (grant : Spike3NativeArenaGrant)
    {requested : UInt64} (hrequested : requested != 0) (hcapacity : requested <= grant.bytes) :
    grant.admits requested = true := by
  simp [Spike3NativeArenaGrant.admits, hrequested, hcapacity]

/- REF: docs/TARGETS/LINUX.md#22-memory-mapping-mmap-state-model -/
/-- Spike 3's grant-aware `mmap` realization.  Failure is a normal zero result with the syscall
    continuation restored, exactly the convention checked by the native program before it uses
    the arena pointer. -/
def spike3LinuxMmapHook {Event : Type} (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) : X86_64MachineState × Option Event :=
  let requested := state.gprs .rsi
  if grant.admits requested then
    sysMmapHook state
  else
    ({ (state.setGpr64 .rax 0) with rip := state.gprs .rcx }, none)

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Spike 3's grant-aware `VirtualAlloc` realization.  It pops the import call's return address
    on both success and failure, so the zero result is observed by the caller rather than being a
    stuck IAT state. -/
def spike3VirtualAllocHook {Event : Type} (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) : X86_64MachineState × Option Event :=
  let requested := state.gprs .rdx
  if grant.admits requested then
    virtualAllocHook state
  else
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

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A failed Linux reservation returns null and resumes at the syscall continuation. -/
theorem spike3LinuxMmapHook_rejects_insufficient (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rsi) = false) :
    (spike3LinuxMmapHook (Event := AnyEvent) grant state).1.gprs .rax = 0 := by
  simp [spike3LinuxMmapHook, h, X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A sufficient Linux grant recovers the ordinary successful reservation result on a fresh
    invocation.  The theorem is intentionally about a new state: failed runs do not mutate a
    hidden global allocator budget. -/
theorem spike3LinuxMmapHook_recovers_with_sufficient_grant (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rsi) = true) :
    (spike3LinuxMmapHook (Event := AnyEvent) grant state).1.gprs .rax = 0x70000000 := by
  simp [spike3LinuxMmapHook, h, sysMmapHook, X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A failed Win32 reservation returns null after the normal call/return transition. -/
theorem spike3VirtualAllocHook_rejects_insufficient (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rdx) = false) :
    (spike3VirtualAllocHook (Event := AnyEvent) grant state).1.gprs .rax = 0 := by
  simp [spike3VirtualAllocHook, h, popReturnAddress, X86_64MachineState.setGpr64]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- A sufficient Win32 grant recovers the ordinary successful reservation result on a fresh
    invocation. -/
theorem spike3VirtualAllocHook_recovers_with_sufficient_grant (grant : Spike3NativeArenaGrant)
    (state : X86_64MachineState) (h : grant.admits (state.gprs .rdx) = true) :
    (spike3VirtualAllocHook (Event := AnyEvent) grant state).1.gprs .rax = 0x20000000 := by
  simp [spike3VirtualAllocHook, h, virtualAllocHook, popReturnAddress,
    X86_64MachineState.setGpr64]

end Spikes.Spike3SortLines
