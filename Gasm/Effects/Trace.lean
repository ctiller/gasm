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
import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.FileSystem
import Gasm.Effects.Process
import Gasm.Effects.Clock
import Gasm.Effects.Network

namespace Gasm.Effects

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Execution state for the pure trace monad containing emitted events and simulated stdin stream. -/
structure TraceState (Event : Type) where
  events           : List Event := []
  stdinLines       : List String := []
  incomingRequests : List String := []

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Pure trace monad parameterized over an arbitrary strongly-typed event universe. -/
def TraceM (Event : Type) (α : Type) := TraceState Event → Option α × TraceState Event

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
instance : Monad (TraceM Event) where
  pure a := fun s => (some a, s)
  bind m f := fun s =>
    match m s with
    | (some a, s') => f a s'
    | (none, s')   => (none, s')

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Emits a domain event into the active event trace via coproduct injection. -/
def emitEvent {SubEvent Event : Type} [Inject SubEvent Event] (e : SubEvent) : TraceM Event Unit :=
  fun s => (some (), { s with events := s.events ++ [Inject.inject e] })

/- REF: docs/SYSTEM_EFFECTS.md#21-monadconsole-standard-io -/
instance [Inject ConsoleEvent Event] : MonadConsole (TraceM Event) where
  printStr s := emitEvent (ConsoleEvent.out s)
  printLine s := emitEvent (ConsoleEvent.out (s ++ "\r\n"))
  readLine := fun s =>
    match s.stdinLines with
    | [] => (some none, s)
    | l :: rest => (some (some l), { s with stdinLines := rest })

/- REF: docs/SYSTEM_EFFECTS.md#23-monadprocess-lifecycle-environment -/
instance [Inject ProcessEvent Event] : MonadProcess (TraceM Event) where
  exitProcess code := fun s =>
    (none, { s with events := s.events ++ [Inject.inject (ProcessEvent.exit code)] })
  getEnvVar _ := fun s => (some none, s)

/- REF: docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates -/
instance [Inject FileSystemEvent Event] : MonadFileSystem (TraceM Event) where
  openFile _ _ := fun s => (some (Except.ok ⟨1⟩), s)
  readFile _ _ := fun s => (some (Except.ok ByteArray.empty), s)
  writeFile h b := do
    emitEvent (FileSystemEvent.write h b.size)
    return Except.ok b.size
  closeFile h := do
    emitEvent (FileSystemEvent.close h)
    return Except.ok ()

/- REF: docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications -/
instance [Inject ClockEvent Event] : MonadClock (TraceM Event) where
  getMonotonicTimeNs := do
    emitEvent ClockEvent.queryTime
    return 0

/- REF: docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications -/
instance [Inject NetEvent Event] : MonadNetwork (TraceM Event) where
  listen port := do
    emitEvent (NetEvent.listen port)
    return some 100
  accept _sock := fun s =>
    match s.incomingRequests with
    | [] => (some none, s)
    | _ =>
      let s' := { s with events := s.events ++ [Inject.inject (NetEvent.accept "127.0.0.1")] }
      (some (some 101), s')
  -- Short-read contract fix (`docs/READ_BINDER_CONTRACT.md`): the spec-side model must respect `maxLen` (the syscall's
  -- declared cap) the same way the machine-side hooks now do (`Win32API.lean`'s `recvHook`,
  -- `Syscall.lean`'s `sysReadHook`, `WASI/ABI.lean`'s `sock_recv`) -- otherwise a `∀ env`
  -- equivalence proof could never hold once a machine-side hook's short-read behaviour is
  -- genuinely exercised, since the two sides would disagree on what a capped `recv` returns.
  -- Built on the same `Gasm.Effects.splitBytes` primitive for parity.
  recv _sock maxLen := fun s =>
    match s.incomingRequests with
    | [] => (some none, s)
    | req :: rest =>
      let (delivered, remaining) := splitBytes req.toUTF8.toList maxLen
      let deliveredArr := ByteArray.mk delivered.toArray
      let incomingRequests' :=
        match String.fromUTF8? (ByteArray.mk remaining.toArray) with
        | some r => if remaining.isEmpty then rest else r :: rest
        | none => rest
      let deliveredStr := (String.fromUTF8? deliveredArr).getD req
      let s' := { s with
        events := s.events ++ [Inject.inject (NetEvent.recv deliveredStr)],
        incomingRequests := incomingRequests'
      }
      (some (some deliveredStr), s')
  send _sock data := do
    emitEvent (NetEvent.send data)
    return true
  close sock := do
    emitEvent (NetEvent.close sock)
    return ()

/- REF: docs/SYSTEM_EFFECTS.md#5-formal-simulation-proof-bridge -/
/-- Extracts the full observable strongly-typed effect trace from a TraceM model execution. -/
def runModelTrace {Event α : Type} (m : TraceM Event α) (stdinLines : List String := []) (incomingRequests : List String := []) : List Event :=
  (m { events := [], stdinLines := stdinLines, incomingRequests := incomingRequests }).2.events

end Gasm.Effects
