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
import Gasm.Core.Platform
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
/-- Builds a WASI Preview 1 module whose entry point reads the external byte stream.
    The import order is part of the artifact ABI: `fd_read` is index 0, `fd_write`
    index 1, and `proc_exit` index 2.  Keep this separate from `buildWasiModule` so
    existing output-only modules retain their established import indices. -/
def buildWasiStdinModule (startFn : WasmFunction) (extraFuncs : List WasmFunction := [])
    (dataSegments : List WasmDataSegment := []) : WasmModule :=
  let imports : List Import := [
    { module := wasiModuleName, name := "fd_read", desc := .func 0 },
    { module := wasiModuleName, name := "fd_write", desc := .func 1 },
    { module := wasiModuleName, name := "proc_exit", desc := .func 2 }
  ]
  let startExported := { startFn with exportName := some "_start" }
  let functions := [startExported] ++ extraFuncs
  let exports : List Export := [
    { name := "memory", desc := .mem 0 }
  ]
  { imports := imports, functions := functions, memoryPages := some 1,
    dataSegments := dataSegments, exports := exports }

/- REF: docs/TARGETS/WASI.md#1-wasi-snapshot-preview-1-architecture -/
/-- Initializes linear memory with all active data segments, returning the sealed `WasmMemory`
    cell (`MemoryCell.lean`). The data-segment install loop below builds an ordinary, freely
    mutable local `ByteArray` and wraps it via `WasmMem.ofBytes` only once at the end -- exactly
    the pattern `docs/MEMORY_HOOK.md`'s x86-64 seal establishes for loaders (`X86_64Mem.initRegion`):
    computing a fresh image with unrestricted operations is legitimate bulk construction, and the
    seal's job is to prevent touching an *already-installed* cell's bytes from outside this module,
    not to restrict how a brand-new one gets built. -/
def initWasmMemory (segments : List WasmDataSegment) : WasmMemory := Id.run do
  let mut mem := ByteArray.mk (Array.mk (List.replicate 65536 (0 : UInt8)))
  for seg in segments do
    for i in [0:seg.data.size] do
      mem := mem.set! (seg.offset.toNat + i) (seg.data.get! i)
  return WasmMem.ofBytes mem

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Pure operational host call dispatcher for WASI syscalls. -/
def wasiHostCall (imports : List String) (idx : Nat) (s : WasmMachineState) : WasmMachineState × ControlSignal := Id.run do
  let fnName := imports[idx]?
  match fnName with
  | some "fd_read" =>
    -- WASI fd_read(fd, iovs_ptr, iovs_len, nread_ptr)
    -- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- every memory touch below now goes
    -- through the sealed `WasmMem` accessors (`MemoryCell.lean`); an out-of-bounds iovec entry or
    -- destination buffer traps the call (leaving `s4`, the pre-call state, unmutated) instead of
    -- the previous raw `ByteArray.set!`/unchecked `readMem32` bypass of `evalInstr`'s trap check.
    let (nread_ptr, s1) := popI32 s
    let (iovs_len, s2) := popI32 s1
    let (iovs_ptr, s3) := popI32 s2
    let (_fd, s4) := popI32 s3
    let mut totalRead : UInt32 := 0
    let mut curMem := s4.memory
    let mut curPos := s4.stdinPos
    let mut trapped := false
    for i in [0:iovs_len.toNat] do
      if trapped then
        pure ()
      else
        let entryAddr := iovs_ptr.toNat + i * 8
        match WasmMem.read32 curMem entryAddr, WasmMem.read32 curMem (entryAddr + 4) with
        | some bufPtr, some bufLen =>
          let available := if curPos < s4.stdin.size then s4.stdin.size - curPos else 0
          let toRead := min bufLen.toNat available
          let delivered := s4.stdin.extract curPos (curPos + toRead)
          match WasmMem.writeBytes curMem bufPtr.toNat delivered with
          | some m' =>
            curMem := m'
            curPos := curPos + toRead
            totalRead := totalRead + toRead.toUInt32
          | none => trapped := true
        | _, _ => trapped := true
    if trapped then
      return ({ s4 with trapped := true }, .next)
    match WasmMem.write32 curMem nread_ptr.toNat totalRead with
    | some newMem => return (pushVal (.i32 0) { s4 with memory := newMem, stdinPos := curPos }, .next)
    | none => return ({ s4 with trapped := true }, .next)

  | some "fd_write" =>
    -- WASI fd_write(fd, iovs_ptr, iovs_len, nwritten_ptr)
    -- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- see `fd_read`'s note above; the same
    -- checked-accessor discipline applies to the source-buffer reads here.
    let (nwritten_ptr, s1) := popI32 s
    let (iovs_len, s2) := popI32 s1
    let (iovs_ptr, s3) := popI32 s2
    let (_fd, s4) := popI32 s3
    let mut totalWritten : UInt32 := 0
    let mut newEvents := s4.events
    let mut trapped := false
    for i in [0:iovs_len.toNat] do
      if trapped then
        pure ()
      else
        let entryAddr := iovs_ptr.toNat + i * 8
        match WasmMem.read32 s4.memory entryAddr, WasmMem.read32 s4.memory (entryAddr + 4) with
        | some bufPtr, some bufLen =>
          match WasmMem.readBytes s4.memory bufPtr.toNat bufLen.toNat with
          | some bytes =>
            let str := match String.fromUTF8? bytes with
              | some s => s
              | none => String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat))
            newEvents := newEvents ++ [Inject.inject (ConsoleEvent.out str)]
            totalWritten := totalWritten + bufLen
          | none => trapped := true
        | _, _ => trapped := true
    if trapped then
      return ({ s4 with trapped := true }, .next)
    match WasmMem.write32 s4.memory nwritten_ptr.toNat totalWritten with
    | some newMem => return (pushVal (.i32 0) { s4 with memory := newMem, events := newEvents }, .next)
    | none => return ({ s4 with trapped := true }, .next)

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
    -- Short-read contract fix (`docs/READ_BINDER_CONTRACT.md`): this hook already capped the write at `max_len` (the
    -- syscall's declared cap), but silently DROPPED the undelivered remainder rather than
    -- queuing it for a following call -- a genuine short read requires the remainder to
    -- survive, not vanish. Rebuilt on `Gasm.Effects.splitBytes` for parity with the
    -- Windows/Linux recv hooks (`Win32API.lean`'s `recvHook`, `Syscall.lean`'s `sysReadHook`).
    -- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- the destination write is now one
    -- atomic `WasmMem.writeBytes` call instead of a raw per-byte `ByteArray.set!` loop; an
    -- out-of-bounds `buf_ptr` traps rather than writing past the end of linear memory unchecked.
    let (max_len, s1) := popI32 s
    let (buf_ptr, s2) := popI32 s1
    let (_sock, s3) := popI32 s2
    match s3.incomingRequests with
    | [] =>
      return (pushVal (.i32 0) s3, .next)
    | req :: rest =>
      -- F1: shared delivery step -- see `Win32API.lean`'s `recvHook` and
      -- `Gasm.Effects.recvDeliver_lossless`.
      let (delivered, incomingRequests') := recvDeliver req max_len.toNat rest
      let count := delivered.size
      match WasmMem.writeBytes s3.memory buf_ptr.toNat delivered with
      | none => return ({ s3 with trapped := true }, .next)
      | some curMem =>
        let newEvents := s3.events ++ [Inject.inject (NetEvent.recv (bytesToPayload delivered))]
        return (pushVal (.i32 count.toUInt32) { s3 with memory := curMem, incomingRequests := incomingRequests', events := newEvents }, .next)

  | some "sock_send" =>
    -- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -- checked read instead of a raw
    -- `ByteArray.extract` on `s3.memory` (which silently clips rather than trapping an
    -- out-of-declared-range request).
    let (len, s1) := popI32 s
    let (buf_ptr, s2) := popI32 s1
    let (_sock, s3) := popI32 s2
    match WasmMem.readBytes s3.memory buf_ptr.toNat len.toNat with
    | none => return ({ s3 with trapped := true }, .next)
    | some bytes =>
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
    hits the `.error` arm, closing exactly the fuel-exhaustion soundness gap
    `docs/MEMORY_HOOK.md` §12.5 diagnoses for the sibling
    `Gasm/Targets/X86_64/Semantics.lean`'s `runProgramTraceWithLoops` (see `WasmRunResult`'s own
    docstring in `Gasm/Targets/Wasm/Semantics.lean`). -/
def runWasiTraceState (instrs : List WasmInstr) (segments : List WasmDataSegment) (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"]) (incomingRequests : List ByteArray := []) (fuel : Nat := defaultWasmFuel) : WasmRunResult :=
  let initMem := initWasmMemory segments
  let s : WasmMachineState := { memory := initMem, stdin := stdin, incomingRequests := incomingRequests }
  evalInstrs fuel instrs s (wasiHostCall imports)

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- The externally visible result of a WASI execution under finite platform capabilities.

    A clean fall-through, a `proc_exit`, a Wasm trap, interpreter fuel exhaustion, and refusal of
    the memory-page capability are distinct outcomes.  In particular, a caller cannot project a
    successful trace from either resource-exhaustion branch. -/
inductive WasiRunOutcome where
  | completed (state : WasmMachineState) (signal : ControlSignal) : WasiRunOutcome
  | exited (state : WasmMachineState) (code : UInt32) : WasiRunOutcome
  | trapped (state : WasmMachineState) : WasiRunOutcome
  | fuelExhausted (partialState : WasmMachineState) : WasiRunOutcome
  | memoryExhausted (state : WasmMachineState) (requestedPages availablePages : Nat) : WasiRunOutcome

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Finite execution resources supplied by the WASI platform capability.  Input remains an
    arbitrary `ByteArray`; a budget limits execution resources, not the input domain. -/
structure WasiResourceBudget where
  fuel : Nat
  memoryPages : Nat

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Accounting carried by a recoverable allocation scope.  `liveBytes` is charged against the
    capability now; `peakLiveBytes` and `cumulativeAllocatedBytes` remain after scope close for
    auditing, admission control, and parent-scope composition. -/
structure WasiAllocationAccount where
  byteBudget : Nat
  liveBytes : Nat := 0
  peakLiveBytes : Nat := 0
  cumulativeAllocatedBytes : Nat := 0
  deriving Repr, DecidableEq, BEq

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- A lexical allocation scope.  `entry` is retained so closing a child reliably reclaims every
    byte allocated in that child, while cumulative and peak accounting compose into its parent.
    Opening another scope from `current` nests naturally. -/
structure WasiAllocationScope where
  entry : WasiAllocationAccount
  current : WasiAllocationAccount
  deriving Repr, DecidableEq, BEq

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Starts a root allocation scope under a finite byte capability. -/
def WasiAllocationScope.root (byteBudget : Nat) : WasiAllocationScope :=
  let account := { byteBudget := byteBudget }
  { entry := account, current := account }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Opens a nested scope from the current accounting state. -/
def WasiAllocationScope.openChild (scope : WasiAllocationScope) : WasiAllocationScope :=
  { entry := scope.current, current := scope.current }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Data result of a scope-local allocation attempt.  Exhaustion is returned to the request scope
    as data; it does not terminate the process or erase the account needed for recovery. -/
inductive WasiAllocationResult where
  | allocated (scope : WasiAllocationScope) : WasiAllocationResult
  | exhausted (scope : WasiAllocationScope) : WasiAllocationResult
  deriving Repr, DecidableEq, BEq

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Attempts to charge `bytes` to the current scope.  Failed attempts leave all accounting
    unchanged, making retry, fallback, and request-level error responses well-defined. -/
def WasiAllocationScope.allocate (scope : WasiAllocationScope) (bytes : Nat) : WasiAllocationResult :=
  let nextLive := scope.current.liveBytes + bytes
  if nextLive > scope.current.byteBudget then
    .exhausted scope
  else
    let next : WasiAllocationAccount := {
      scope.current with
      liveBytes := nextLive
      peakLiveBytes := Nat.max scope.current.peakLiveBytes nextLive
      cumulativeAllocatedBytes := scope.current.cumulativeAllocatedBytes + bytes
    }
    .allocated { scope with current := next }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Closes a scope and reclaims its live allocations.  Cumulative allocation and peak live usage
    are deliberately retained in the returned parent account, so nested scopes compose without
    losing resource-accounting evidence. -/
def WasiAllocationScope.close (scope : WasiAllocationScope) : WasiAllocationAccount :=
  { scope.entry with
    peakLiveBytes := Nat.max scope.entry.peakLiveBytes scope.current.peakLiveBytes
    cumulativeAllocatedBytes := scope.current.cumulativeAllocatedBytes }

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Request failure closes the same scope as ordinary success: live allocations are reclaimed
    before a caller decides whether to return a request error or escalate to process termination. -/
def WasiAllocationScope.closeOnFailure (scope : WasiAllocationScope) : WasiAllocationAccount :=
  scope.close

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Closing, including failure close, restores the parent's live-byte charge exactly. -/
theorem WasiAllocationScope.close_reclaims_live (scope : WasiAllocationScope) :
    scope.close.liveBytes = scope.entry.liveBytes := rfl

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Allocation exhaustion is recoverable data and leaves the scope unchanged. -/
theorem WasiAllocationScope.exhausted_unchanged (scope : WasiAllocationScope) (bytes : Nat)
    (h : scope.current.byteBudget < scope.current.liveBytes + bytes) :
    scope.allocate bytes = .exhausted scope := by
  simp [WasiAllocationScope.allocate, Nat.not_le_of_lt h]

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Classifies the interpreter result without collapsing fuel exhaustion into a trace. -/
def WasiRunOutcome.ofResult : WasmRunResult → WasiRunOutcome
  | .error partialState => .fuelExhausted partialState
  | .ok (state, signal) =>
    match state.resourceFailure with
    | some (.memoryPages requested available) => .memoryExhausted state requested available
    | none =>
      if state.trapped then .trapped state
      else match state.exitCode with
        | some code => .exited state code
        | none => .completed state signal

abbrev WasiHostRuntime :=
  List String → Nat → WasmMachineState → WasmMachineState × ControlSignal

/-- Runs a WASI artifact under an explicit finite platform resource capability
    and the exact composed host/library runtime selected by its capabilities. -/
def runWasiOutcomeWithHost (host : WasiHostRuntime)
    (instrs : List WasmInstr) (segments : List WasmDataSegment)
    (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"])
    (incomingRequests : List ByteArray := []) (budget : WasiResourceBudget :=
      { fuel := defaultWasmFuel, memoryPages := 65536 }) : WasiRunOutcome :=
  let initialMemory := initWasmMemory segments
  let initialPages := (WasmMem.size initialMemory + 65535) / 65536
  let availablePages := Nat.min budget.memoryPages 65536
  let state : WasmMachineState := {
    memory := initialMemory
    memMax := some availablePages.toUInt32
    stdin := stdin
    incomingRequests := incomingRequests
  }
  if initialPages > availablePages then
    .memoryExhausted state initialPages availablePages
  else
    WasiRunOutcome.ofResult (evalInstrs budget.fuel instrs state (host imports))

/-- Stock WASI execution is the base host-runtime realization. -/
def runWasiOutcome (instrs : List WasmInstr) (segments : List WasmDataSegment)
    (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"])
    (incomingRequests : List ByteArray := []) (budget : WasiResourceBudget :=
      { fuel := defaultWasmFuel, memoryPages := 65536 }) : WasiRunOutcome :=
  runWasiOutcomeWithHost wasiHostCall instrs segments stdin imports incomingRequests budget

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- The observable events of a non-resource WASI outcome.  Resource exhaustion deliberately has
    no event projection, preventing a partial trace from being treated as a successful result. -/
def WasiRunOutcome.events? : WasiRunOutcome → Option (List AnyEvent)
  | .completed state _ => some state.events
  | .exited state _ => some state.events
  | .trapped state => some state.events
  | .fuelExhausted _ => none
  | .memoryExhausted _ _ _ => none

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Observable contract result for a WASI request.  Resource failures are first-class values so a
    service can recover at request scope; a process-level policy may choose to escalate one, but
    the platform does not do so implicitly. -/
inductive WasiObservable (Event : Type) where
  | completed (events : List Event) : WasiObservable Event
  | exited (code : UInt32) (events : List Event) : WasiObservable Event
  | trapped (events : List Event) : WasiObservable Event
  | fuelExhausted : WasiObservable Event
  | memoryExhausted (requestedPages availablePages : Nat) : WasiObservable Event
  deriving BEq

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Maps the event payload without changing completion or resource semantics. -/
def WasiObservable.mapEvents (f : Event → Event') : WasiObservable Event → WasiObservable Event'
  | .completed events => .completed (events.map f)
  | .exited code events => .exited code (events.map f)
  | .trapped events => .trapped (events.map f)
  | .fuelExhausted => .fuelExhausted
  | .memoryExhausted requested available => .memoryExhausted requested available

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Erases machine-internal state only after preserving every externally meaningful outcome. -/
def WasiRunOutcome.observable : WasiRunOutcome → WasiObservable AnyEvent
  | .completed state _ => .completed state.events
  | .exited state code => .exited code state.events
  | .trapped state => .trapped state.events
  | .fuelExhausted _ => .fuelExhausted
  | .memoryExhausted _ requested available => .memoryExhausted requested available

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
def runWasiTrace (instrs : List WasmInstr) (segments : List WasmDataSegment) (stdin : ByteArray := ByteArray.empty) (imports : List String := ["fd_write", "proc_exit"]) (incomingRequests : List ByteArray := []) : List AnyEvent :=
  match runWasiTraceState instrs segments stdin imports incomingRequests with
  | .ok (finalState, _) => finalState.events
  | .error partialState => partialState.events

open Gasm.Core.Platform

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Complete WASI artifact tied to the instructions, resources, and import ABI
    whose behavior is proved by the sole `VerifiedProgram`. -/
structure WasiArtifact where
  module : WasmModule
  typeSignatures : List FuncType
  instructions : List WasmInstr
  dataSegments : List WasmDataSegment
  imports : List String := ["fd_write", "proc_exit"]
  resources : WasiResourceBudget

inductive WasiPlatform

def wasiPublicEntries (artifact : WasiArtifact) : List Export :=
  let importedFunctions := artifact.module.imports.filter (fun imported =>
    match imported.desc with | .func _ => true | _ => false) |>.length
  let generated := artifact.module.functions.zipIdx.filterMap (fun (fn, index) =>
    fn.exportName.map fun name => { name, desc := .func (importedFunctions + index) })
  generated ++ artifact.module.exports

def wasiCallableEntries (artifact : WasiArtifact) : List Export :=
  (wasiPublicEntries artifact).filter fun entry =>
    entry.name != "_start" && match entry.desc with | .func _ => true | .mem _ => false

def wasiBoundarySpec : BoundaryContextSpec Unit Unit :=
  { Args := Unit
    Binding := Unit
    Result := Unit
    Outcome := Unit
    ObligationFragment := Unit
    requiredObligations := fun _ _ => ()
    emittedObligations := fun _ _ _ _ => ()
    requires := fun _ _ _ => True
    transitions := fun _ _ _ _ before after => before = after }

def wasiBoundarySemantics : TargetBoundarySemantics WasiPlatform where
  Implementation := Nat
  Artifact := WasiArtifact
  Signature := FuncType
  EntryKind := Unit
  ExitKind := ControlSignal
  PhysicalState := WasmMachineState
  Execution := List WasmInstr
  PublicEntry := Export
  LookupKey := String
  artifactImplements := fun artifact implementation =>
    implementation < artifact.module.functions.length
  publicEntries := wasiPublicEntries
  callableEntries := wasiCallableEntries
  lookupKey := fun entry => entry.name
  resolvesEntry := fun artifact entry implementation signature _ =>
    ∃ fn,
      artifact.module.functions[implementation]? = some fn ∧
      entry.name = fn.exportName.getD "" ∧
      signature = { params := fn.params, results := fn.results }
  jointlyAdmissible := fun _ entries => entries = []
  runs := fun _ _ _ _ _ _ _ _ => False
  admissible := fun _ _ _ _ _ _ _ _ => False

instance : Platform WasiPlatform where
  Artifact := WasiArtifact
  State := Environment
  Observation := WasiObservable AnyEvent
  RuntimeContext := WasiHostRuntime
  Import := String
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := WasiPlatform
  boundarySpec := wasiBoundarySpec
  boundarySemantics := wasiBoundarySemantics
  imports := fun artifact => artifact.imports
  boundaryArtifact := id
  artifactConnected := fun artifact =>
    artifact.module.functions.head?.map (fun fn => fn.body) = some artifact.instructions ∧
    artifact.module.dataSegments = artifact.dataSegments ∧
    artifact.module.imports.map (fun imported => imported.name) = artifact.imports
  load := fun _ environment => environment
  run := fun runtime artifact environment =>
    (runWasiOutcomeWithHost runtime artifact.instructions artifact.dataSegments environment.stdin
      artifact.imports environment.incomingRequests artifact.resources).observable
  admissible := fun _ artifact _ => ∃ bytes, emitWasmBinary artifact.module artifact.typeSignatures = .ok bytes
  emit := fun artifact => emitWasmBinary artifact.module artifact.typeSignatures

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
def wasiHostCapability : Capability WasiPlatform where
  Context := Unit
  provides := fun _ => True
  implementationConnected := fun artifact => Platform.artifactConnected artifact
  establishes := fun _ _ _ _ => True

def wasiHostCapabilities : CapabilityComposition WasiPlatform where
  root := wasiHostCapability
  realize := fun _ => wasiHostCall

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- WAT rendering remains gated by the same sole proof authority as binary emission. -/
def renderVerifiedWasmText (program : VerifiedProgram WasiPlatform wasiHostCapabilities) : String :=
  emitWasmText program.artifact.module program.artifact.typeSignatures

end Gasm.Targets.WASI
