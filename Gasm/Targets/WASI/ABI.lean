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
import Gasm.Effects.Trace
import Gasm.Effects.Console
import Gasm.Effects.Process
import Gasm.Effects.Network
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Semantics
import Gasm.Targets.Wasm.Linker

namespace Gasm.Targets.WASI

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.Wasm

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Standard WASI Snapshot Preview 1 import module namespace. -/
def wasiModuleName : String := "wasi_snapshot_preview1"

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Function type signature for WASI fd_read: (fd: i32, iovs: i32, iovs_len: i32, nread: i32) -> errno: i32. -/
def fdReadType : FuncType :=
  { params := [.i32, .i32, .i32, .i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#21-fdwrite -/
/-- Function type signature for WASI fd_write: (fd: i32, iovs: i32, iovs_len: i32, nwritten: i32) -> errno: i32. -/
def fdWriteType : FuncType :=
  { params := [.i32, .i32, .i32, .i32], results := [.i32] }

/- REF: docs/TARGETS/WASI.md#22-procexit -/
/-- Function type signature for WASI proc_exit: (rval: i32) -> void. -/
def procExitType : FuncType :=
  { params := [.i32], results := [] }

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- Serializes a single __wasi_ciovec_t (buffer pointer + buffer length) into 8 little-endian bytes. -/
def encodeCiovec (bufPtr : UInt32) (bufLen : UInt32) : ByteArray :=
  let b0 := (bufPtr &&& 0xFF).toUInt8
  let b1 := ((bufPtr >>> 8) &&& 0xFF).toUInt8
  let b2 := ((bufPtr >>> 16) &&& 0xFF).toUInt8
  let b3 := ((bufPtr >>> 24) &&& 0xFF).toUInt8
  let l0 := (bufLen &&& 0xFF).toUInt8
  let l1 := ((bufLen >>> 8) &&& 0xFF).toUInt8
  let l2 := ((bufLen >>> 16) &&& 0xFF).toUInt8
  let l3 := ((bufLen >>> 24) &&& 0xFF).toUInt8
  ByteArray.mk #[b0, b1, b2, b3, l0, l1, l2, l3]

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Builds a standard WASI Preview 1 module with fd_write (index 0), proc_exit (index 1), exported _start and memory. -/
def buildWasiModule (startFn : WasmFunction) (extraFuncs : List WasmFunction := []) (dataSegments : List WasmDataSegment := []) : WasmModule :=
  let imports : List Import := [
    { module := wasiModuleName, name := "fd_write", desc := .func 0 },
    { module := wasiModuleName, name := "proc_exit", desc := .func 1 }
  ]
  let startExported := { startFn with exportName := some "_start" }
  let functions := [startExported] ++ extraFuncs
  let exports : List Export := [
    { name := "memory", desc := .mem 0 }
  ]
  { imports := imports, functions := functions, memoryPages := some 1, dataSegments := dataSegments, exports := exports }

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Initializes linear memory with all active data segments. -/
def initWasmMemory (segments : List WasmDataSegment) : ByteArray := Id.run do
  let mut mem := ByteArray.mk (Array.mk (List.replicate 65536 (0 : UInt8)))
  for seg in segments do
    for i in [0:seg.data.size] do
      mem := mem.set! (seg.offset.toNat + i) (seg.data.get! i)
  return mem

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Pure operational host call dispatcher for WASI syscalls. -/
def wasiHostCall (imports : List String) (idx : Nat) (s : WasmMachineState) : WasmMachineState × ControlSignal := Id.run do
  let fnName := imports[idx]?
  match fnName with
  | some "fd_read" =>
    -- WASI fd_read(fd, iovs_ptr, iovs_len, nread_ptr)
    let (nread_ptr, s1) := popI32 s
    let (iovs_len, s2) := popI32 s1
    let (iovs_ptr, s3) := popI32 s2
    let (_fd, s4) := popI32 s3
    let mut totalRead : UInt32 := 0
    let mut curMem := s4.memory
    let mut curPos := s4.stdinPos
    for i in [0:iovs_len.toNat] do
      let entryAddr := iovs_ptr.toNat + i * 8
      let bufPtr := readMem32 curMem entryAddr
      let bufLen := readMem32 curMem (entryAddr + 4)
      let available := if curPos < s4.stdin.size then s4.stdin.size - curPos else 0
      let toRead := min bufLen.toNat available
      for bIdx in [0:toRead] do
        let byteVal := s4.stdin.get! (curPos + bIdx)
        curMem := curMem.set! (bufPtr.toNat + bIdx) byteVal
      curPos := curPos + toRead
      totalRead := totalRead + toRead.toUInt32
    let newMem := writeMem32 curMem nread_ptr.toNat totalRead
    return (pushVal (.i32 0) { s4 with memory := newMem, stdinPos := curPos }, .next)

  | some "fd_write" =>
    -- WASI fd_write(fd, iovs_ptr, iovs_len, nwritten_ptr)
    let (nwritten_ptr, s1) := popI32 s
    let (iovs_len, s2) := popI32 s1
    let (iovs_ptr, s3) := popI32 s2
    let (_fd, s4) := popI32 s3
    let mut totalWritten : UInt32 := 0
    let mut newEvents := s4.events
    for i in [0:iovs_len.toNat] do
      let entryAddr := iovs_ptr.toNat + i * 8
      let bufPtr := readMem32 s4.memory entryAddr
      let bufLen := readMem32 s4.memory (entryAddr + 4)
      let bytes := s4.memory.extract bufPtr.toNat (bufPtr.toNat + bufLen.toNat)
      let str := match String.fromUTF8? bytes with
        | some s => s
        | none => String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat))
      newEvents := newEvents ++ [Inject.inject (ConsoleEvent.out str)]
      totalWritten := totalWritten + bufLen
    let newMem := writeMem32 s4.memory nwritten_ptr.toNat totalWritten
    return (pushVal (.i32 0) { s4 with memory := newMem, events := newEvents }, .next)

  | some "proc_exit" =>
    -- WASI proc_exit(rval)
    let (rval, s1) := popI32 s
    let newEvents := s1.events ++ [Inject.inject (ProcessEvent.exit rval)]
    return ({ s1 with exitCode := some rval, events := newEvents }, .ret)

  | some "sock_listen" =>
    let (port, s1) := popI32 s
    let newEvents := s1.events ++ [Inject.inject (NetEvent.listen port.toUInt16)]
    return (pushVal (.i32 100) { s1 with events := newEvents }, .next)

  | some "sock_accept" =>
    let (_sock, s1) := popI32 s
    match s1.incomingRequests with
    | [] =>
      return (s1, .ret)
    | _ =>
      let newEvents := s1.events ++ [Inject.inject (NetEvent.accept "127.0.0.1")]
      return (pushVal (.i32 101) { s1 with events := newEvents }, .next)

  | some "sock_recv" =>
    -- N2 fix (MODEL_DEBT.md §C1): this hook already capped the write at `max_len` (the
    -- syscall's declared cap), but silently DROPPED the undelivered remainder rather than
    -- queuing it for a following call -- a genuine short read requires the remainder to
    -- survive, not vanish. Rebuilt on `Gasm.Effects.splitBytes` for parity with the
    -- Windows/Linux recv hooks (`Win32API.lean`'s `recvHook`, `Syscall.lean`'s `sysReadHook`).
    let (max_len, s1) := popI32 s
    let (buf_ptr, s2) := popI32 s1
    let (_sock, s3) := popI32 s2
    match s3.incomingRequests with
    | [] =>
      return (pushVal (.i32 0) s3, .next)
    | req :: rest =>
      let (delivered, remaining) := splitBytes req.toUTF8.toList max_len.toNat
      let count := delivered.length
      let deliveredArr := ByteArray.mk delivered.toArray
      let mut curMem := s3.memory
      for i in [0:count] do
        curMem := curMem.set! (buf_ptr.toNat + i) (deliveredArr.get! i)
      let incomingRequests' :=
        match String.fromUTF8? (ByteArray.mk remaining.toArray) with
        | some r => if remaining.isEmpty then rest else r :: rest
        | none => rest
      let deliveredStr := (String.fromUTF8? deliveredArr).getD req
      let newEvents := s3.events ++ [Inject.inject (NetEvent.recv deliveredStr)]
      return (pushVal (.i32 count.toUInt32) { s3 with memory := curMem, incomingRequests := incomingRequests', events := newEvents }, .next)

  | some "sock_send" =>
    let (len, s1) := popI32 s
    let (buf_ptr, s2) := popI32 s1
    let (_sock, s3) := popI32 s2
    let bytes := s3.memory.extract buf_ptr.toNat (buf_ptr.toNat + len.toNat)
    let str := String.fromUTF8! bytes
    let newEvents := s3.events ++ [Inject.inject (NetEvent.send str)]
    return (pushVal (.i32 len) { s3 with events := newEvents }, .next)

  | some "sock_close" =>
    let (sock, s1) := popI32 s
    let newEvents := s1.events ++ [Inject.inject (NetEvent.close sock.toNat)]
    return (pushVal (.i32 0) { s1 with events := newEvents }, .next)

  | _ =>
    return (s, .next)

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Runs a full instruction sequence under the WASI system model and returns the FULL,
    fuel-honest `WasmRunResult`: `.ok (finalState, _)` if a genuine stopping point was reached
    within `fuel`, `.error partialState` if fuel ran out first. This is the one whole-program
    entry point in this codebase that does NOT collapse fuel exhaustion away (contrast
    `runWasiTrace` below, kept for source-compatibility with every existing trace-equality
    theorem) -- every load-bearing `traceEquivalence` proof in `Spikes/*/Wasm/Equivalence.lean`
    is paired with a `#guard !(runWasiTraceState ...).isError` check proving its own program never
    hits the `.error` arm, closing exactly the soundness gap TCB.md's "Fuel exhaustion
    indistinguishable from clean termination" finding diagnoses for the sibling
    `Gasm/Targets/X86_64/Semantics.lean`'s `runProgramTraceWithLoops` (see `WasmRunResult`'s own
    docstring in `Gasm/Targets/Wasm/Semantics.lean`). -/
def runWasiTraceState (instrs : List WasmInstr) (segments : List WasmDataSegment) (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"]) (incomingRequests : List String := []) (fuel : Nat := defaultWasmFuel) : WasmRunResult :=
  let initMem := initWasmMemory segments
  let s : WasmMachineState := { memory := initMem, stdin := stdin, incomingRequests := incomingRequests }
  evalInstrs fuel instrs s (wasiHostCall imports)

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Runs a full instruction sequence under the WASI system model and returns the observable event
    trace alone -- the historical return shape every existing `Spikes/*/Wasm/Equivalence.lean`
    trace-equality theorem is written against, preserved unchanged (same signature, same
    behaviour for any run within `fuel`) so none of them need editing. Extracts `.events` from
    whichever machine state `runWasiTraceState` returns, completed or fuel-exhausted alike --
    ONLY sound because every real program this codebase ships is separately proven
    (`runWasiTraceState`'s own docstring) never to exhaust the default fuel; a caller that cannot
    rely on that proof (e.g. a hypothetical future program known to run long enough to matter)
    must use `runWasiTraceState` directly instead of this convenience wrapper. -/
def runWasiTrace (instrs : List WasmInstr) (segments : List WasmDataSegment) (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"]) (incomingRequests : List String := []) : List AnyEvent :=
  match runWasiTraceState instrs segments stdin imports incomingRequests with
  | .ok (finalState, _) => finalState.events
  | .error partialState => partialState.events

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Typeclass defining how an abstract environment `Env` is loaded into initial WASI state. -/
class WasiEnvironmentLoader (Env : Type) where
  loadWasiEnvironment : Env → ByteArray × List String

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Default loader for standalone WASI programs with closed/empty environment. -/
instance : WasiEnvironmentLoader Unit where
  loadWasiEnvironment _ := (ByteArray.empty, [])

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Loader for WASI CLI filter programs taking dynamic standard input. -/
instance : WasiEnvironmentLoader ByteArray where
  loadWasiEnvironment stdin := (stdin, [])

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Loader for WASI server modules handling incoming network request queues. -/
instance : WasiEnvironmentLoader (List String) where
  loadWasiEnvironment reqs := (ByteArray.empty, reqs)

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-Class Universally Parametric Verified WebAssembly Program Contract.
    A WebAssembly binary or WAT artifact CANNOT be emitted without supplying:
    1. The WasmModule and its instructions/data segments.
    2. The high-level parametric specification function (`spec`).
    3. THE MATHEMATICAL UNIVERSAL EQUIVALENCE PROOF TERM (`traceEquivalence`)
       proving that for ALL possible external environments `env : Env`, the WASI execution trace
       matches the high-level specification trace. -/
structure VerifiedWasmProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [BEq Event] [Inject Event AnyEvent] [WasiEnvironmentLoader Env] where
  name             : String
  module           : WasmModule
  typeSignatures   : List FuncType
  instructions     : List WasmInstr
  dataSegments     : List WasmDataSegment
  imports          : List String := ["fd_write", "proc_exit"]
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    let (stdin, reqs) := WasiEnvironmentLoader.loadWasiEnvironment env
    (runWasiTrace instructions dataSegments stdin imports reqs == (spec env).map Inject.inject) = true

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-Class Verified WebAssembly Program Contract for dynamic stdin stream filters. -/
abbrev VerifiedWasmStdinProgram (Event : Type := AnyEvent) [BEq Event] [Inject Event AnyEvent] :=
  VerifiedWasmProgram ByteArray Event

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Type-Enforced Code Emission for WebAssembly binaries. Fails closed (TCB T7 / TC20) if
    `p.module`'s functions don't all resolve against `p.typeSignatures`. -/
def emitVerifiedWasmBinary {Env : Type} {Event : Type}
    [BEq Event] [Inject Event AnyEvent] [WasiEnvironmentLoader Env]
    (p : VerifiedWasmProgram Env Event) : Except String ByteArray :=
  emitWasmBinary p.module p.typeSignatures

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Type-Enforced Code Emission for WebAssembly WAT text format. -/
def emitVerifiedWasmText {Env : Type} {Event : Type}
    [BEq Event] [Inject Event AnyEvent] [WasiEnvironmentLoader Env]
    (p : VerifiedWasmProgram Env Event) : String :=
  emitWasmText p.module p.typeSignatures

end Gasm.Targets.WASI
