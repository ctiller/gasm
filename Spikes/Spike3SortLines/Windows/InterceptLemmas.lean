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

import Lean
import Gasm.Core.Types
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Network
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.Instructions.Syscall
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Dispatcher

/-!
# `interceptCall = none` for ordinary (non-IAT-slot) code addresses, independent of state

`Gasm/Targets/Windows/Win32API.lean`'s `findIatIndex` recognizes an address as an IAT import slot
purely structurally: `s.read64 addr == addr` (the slot's stored bytes happen to equal its own
address -- how the loader lays out `.idata`) *and* `addr % 8 == 0`. For any address that is not
8-byte aligned, the second conjunct alone already forces `findIatIndex s addr = none` -- but
proving this via plain kernel reduction (`rfl`/`decide`) on an *opaque* machine state `s` (the
state produced after `generalize`-ing away a chain of prior steps, per the PA15/PA1 discipline)
gets stuck: `s.read64 addr != addr || addr % 8 != 0` is a `Bool` expression, and `Bool.or`'s
definition pattern-matches on its *first* argument, so the kernel must still reduce
`s.read64 addr != addr` to a literal `true`/`false` before it can even look at the (already-known)
second disjunct -- which is impossible once `s` is opaque, even though the disjunction's value
doesn't actually depend on it. This file supplies the four-line propositional detour (rewrite by
the known disjunct, then `Bool.or_true`) that sidesteps this, generically over *any* state `s` --
reusable at every one of a trace proof's many "ordinary instruction, not an intercepted call"
steps without ever touching what `s.memory` actually contains.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Gasm.Targets.Linux

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- A non-8-byte-aligned address is never mistaken for an IAT import slot, regardless of the
    machine state's memory contents (`findIatIndex`'s `addr % 8 == 0` conjunct alone rules it
    out). Proved propositionally (rewrite + `Bool.or_true`), not by kernel-reducing
    `s.read64 addr` -- the point being that this holds for an *opaque* `s`. -/
theorem findIatIndex_none_of_not_aligned {s : X86_64MachineState} {addr : Address}
    (halign : (addr % 8 != 0) = true) :
    findIatIndex s addr = none := by
  unfold findIatIndex
  rw [show (s.read64 addr != addr || addr % 8 != 0) = true from by
    rw [halign, Bool.or_true]]
  simp

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Lifts `findIatIndex_none_of_not_aligned` through `win32Intercept`'s dispatch: every one of its
    branches is guarded by `findIatIndex s addr`, and `none` always falls to its final wildcard
    `none` case. -/
theorem win32Intercept_none_of_not_aligned {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    {s : X86_64MachineState} {addr : Address} (halign : (addr % 8 != 0) = true) :
    win32Intercept (Event := Event) addr s = none := by
  unfold win32Intercept
  rw [findIatIndex_none_of_not_aligned halign]

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Lifts further through the platform `Dispatcher`'s combined interceptor: a non-8-byte-aligned
    address is (a) never the fixed Linux syscall sentinel `linuxSyscallEntry = 0x80000000` (which
    *is* 8-byte aligned) and (b) not an IAT slot by
    `win32Intercept_none_of_not_aligned`, so the combined `interceptCall` is `none`. This is the
    fact actually needed at every "ordinary instruction" step of a `runProgramTraceWithLoops`
    unfolding: it holds for *any* state `s`, so it is safe to use even after `s` has been
    `generalize`-d into an opaque local constant. -/
theorem interceptCall_none_of_not_aligned {Event : Type}
    [Inject ConsoleEvent Event] [Inject ProcessEvent Event] [Inject NetEvent Event]
    {s : X86_64MachineState} {addr : Address} (halign : (addr % 8 != 0) = true) :
    (ExternalCallInterceptor.interceptCall (Event := Event) (Arch := X86_64) addr s) = none := by
  show (if addr == linuxSyscallEntry then linuxSyscallIntercept addr s else win32Intercept addr s) = none
  have hne : (addr == linuxSyscallEntry) = false := by
    cases hc : (addr == linuxSyscallEntry) with
    | false => rfl
    | true =>
      exfalso
      rw [beq_iff_eq] at hc
      subst hc
      simp only [linuxSyscallEntry] at halign
      simp at halign
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  exact win32Intercept_none_of_not_aligned halign

end Spikes.Spike3SortLines.Windows
