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

import Gasm.Effects.Inject
import Gasm.Effects.Process
import Gasm.Targets.X86_64.Semantics
import Spikes.Spike3SortLines.Linux.Program
import Spikes.Spike3SortLines.NativeRuntime
import Spikes.Spike3SortLines.Windows.Program

namespace Spikes.Spike3SortLines

open Gasm.Effects
open Gasm.Targets.X86_64

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Runs the actual lowered Linux Spike 3 artifact under a caller-selected finite native grant.
    Fuel is explicit so the termination claim cannot silently depend on the historic 50,000-step
    trace helper. -/
def runSpike3LinuxWithGrant (grant : Spike3NativeArenaGrant) (stdin : ByteArray) (fuel : Nat) :
    NativeRunOutcome AnyEvent :=
  let initial := Linux.spike3Executable.loadWithStdin stdin
  letI := spike3LinuxRuntime AnyEvent grant
  runProgramOutcomeWithLoops initial.rip Linux.spike3Instructions fuel initial

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Runs the actual lowered Win32 Spike 3 artifact under a caller-selected finite native grant. -/
def runSpike3WindowsWithGrant (grant : Spike3NativeArenaGrant) (stdin : ByteArray) (fuel : Nat) :
    NativeRunOutcome AnyEvent :=
  let initial := Windows.spike3Executable.loadWithStdin stdin
  letI := spike3WindowsRuntime AnyEvent grant
  runProgramOutcomeWithLoops initial.rip Windows.spike3Instructions fuel initial

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
/-- Whether a finite native run emitted Spike 3's dedicated resource-exhaustion process result. -/
def emittedSpike3ResourceFailure (outcome : NativeRunOutcome AnyEvent) : Bool :=
  (outcome.events).contains (AnyEvent.of (ProcessEvent.exit spike3ResourceFailureExitCode))

/-- The intentionally insufficient capability used to exercise the genuine native failure path. -/
def noNativeArenaGrant : Spike3NativeArenaGrant := ⟨0⟩

/-- The smallest grant that covers the native artifact's one 64 KiB reservation request. -/
def spike3NativeReservationGrant : Spike3NativeArenaGrant := ⟨65536⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The Linux resource boundary is exact and input-independent: a rejected reservation carries
    raw `-ENOMEM`, does not change memory, and transfers only to the syscall continuation.  The
    emitted Linux entry code compares against the complete raw-errno range before any allocator
    write; its end-to-end literal executions live in `NativeRegression.lean`, not as proof claims. -/
theorem linux_rejected_reservation_is_exact (_stdin : ByteArray) (state : X86_64MachineState)
    (h : noNativeArenaGrant.admits (state.gprs .rsi) = false) :
    (spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant state).1.gprs .rax = linuxEnomem ∧
      isLinuxRawErrno ((spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant state).1.gprs .rax) = true ∧
      (spike3LinuxMmapHook (Event := AnyEvent) noNativeArenaGrant state).1.memory = state.memory := by
  exact ⟨spike3LinuxMmapHook_rejects_insufficient _ _ h,
    spike3LinuxMmapHook_rejection_is_raw_errno _ _ h,
    spike3LinuxMmapHook_rejection_preserves_memory _ _ h⟩

/-- The selected Linux `sys_exit` runtime produces the exact halted resource outcome and leaves
    memory intact after the raw-errno branch has selected `resource_exhausted`. -/
theorem linux_resource_exit_is_exact (state : X86_64MachineState)
    (hcode : (state.gprs .rdi).toUInt32 = spike3ResourceFailureExitCode) :
    (Gasm.Targets.Linux.sysExitHook (Event := AnyEvent) state).1.fault = some .halted ∧
      (Gasm.Targets.Linux.sysExitHook (Event := AnyEvent) state).1.memory = state.memory ∧
      (Gasm.Targets.Linux.sysExitHook (Event := AnyEvent) state).2 =
        some (Inject.inject (ProcessEvent.exit spike3ResourceFailureExitCode)) := by
  simp [Gasm.Targets.Linux.sysExitHook, hcode]

/-- The selected Win32 `ExitProcess` runtime produces the exact halted resource outcome and does
    not alter memory.  This is separate from the Linux raw-errno convention. -/
theorem windows_resource_exit_is_exact (state : X86_64MachineState)
    (hcode : (state.gprs .rcx).toUInt32 = spike3ResourceFailureExitCode) :
    (spike3ExitProcessHook (Event := AnyEvent) state).1.fault = some .halted ∧
      (spike3ExitProcessHook (Event := AnyEvent) state).1.memory = state.memory ∧
      (spike3ExitProcessHook (Event := AnyEvent) state).2 =
        some (Inject.inject (ProcessEvent.exit spike3ResourceFailureExitCode)) := by
  simp [spike3ExitProcessHook, hcode]

/-- A rejected Win32 reservation is null, preserves memory, and the emitted `je
    resource_exhausted` branch supplies the terminal process outcome above. -/
theorem windows_rejected_reservation_is_exact (_stdin : ByteArray) (state : X86_64MachineState)
    (h : noNativeArenaGrant.admits (state.gprs .rdx) = false) :
    (spike3VirtualAllocHook (Event := AnyEvent) noNativeArenaGrant state).1.gprs .rax = 0 ∧
      (spike3VirtualAllocHook (Event := AnyEvent) noNativeArenaGrant state).1.memory = state.memory := by
  exact ⟨spike3VirtualAllocHook_rejects_insufficient _ _ h,
    spike3VirtualAllocHook_rejection_preserves_memory _ _ h⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Retrying with the same input is a fresh grant-indexed invocation.  No state from a failed
    attempt appears in this statement: with a sufficient grant the real Linux reservation
    transition reaches its concrete arena base. -/
theorem fresh_same_input_retry_has_linux_reservation (stdin : ByteArray)
    (state : X86_64MachineState) (hstdin : state.stdinBuffer = stdin)
    (hrequested : state.gprs .rsi = 65536) :
    (spike3LinuxMmapHook (Event := AnyEvent) spike3NativeReservationGrant state).1.gprs .rax =
      0x70000000 ∧
    (spike3LinuxMmapHook (Event := AnyEvent) spike3NativeReservationGrant state).1.stdinBuffer = stdin := by
  have h : Spike3NativeArenaGrant.admits spike3NativeReservationGrant 65536 = true :=
    Spike3NativeArenaGrant.admits_of_le _ (by rfl) (UInt64.le_refl _)
  exact ⟨spike3LinuxMmapHook_recovers_with_sufficient_grant _ _ hrequested (by simpa [hrequested] using h),
    by simp [spike3LinuxMmapHook, spike3LinuxArena, hrequested, h,
      Stdlib.SmolAlloc.NativeArenaCapability.ofReservation,
      X86_64MachineState.setGpr64,
      hstdin]⟩

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The same fresh-input recovery property holds for the Win32 reservation boundary. -/
theorem fresh_same_input_retry_has_windows_reservation (stdin : ByteArray)
    (state : X86_64MachineState) (hstdin : state.stdinBuffer = stdin)
    (hrequested : state.gprs .rdx = 65536) :
    (spike3VirtualAllocHook (Event := AnyEvent) spike3NativeReservationGrant state).1.gprs .rax =
      0x20000000 ∧
    (spike3VirtualAllocHook (Event := AnyEvent) spike3NativeReservationGrant state).1.stdinBuffer = stdin := by
  have h : Spike3NativeArenaGrant.admits spike3NativeReservationGrant 65536 = true :=
    Spike3NativeArenaGrant.admits_of_le _ (by rfl) (UInt64.le_refl _)
  exact ⟨spike3VirtualAllocHook_recovers_with_sufficient_grant _ _ hrequested (by simpa [hrequested] using h),
    by simp [spike3VirtualAllocHook, spike3WindowsArena, hrequested, h,
      Stdlib.SmolAlloc.NativeArenaCapability.ofReservation, Gasm.Targets.Windows.popReturnAddress,
      X86_64MachineState.setGpr64,
      hstdin]⟩

end Spikes.Spike3SortLines
