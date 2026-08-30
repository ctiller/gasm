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
  let b0 := bufPtr.toUInt8
  let b1 := (bufPtr >>> 8).toUInt8
  let b2 := (bufPtr >>> 16).toUInt8
  let b3 := (bufPtr >>> 24).toUInt8
  let l0 := bufLen.toUInt8
  let l1 := (bufLen >>> 8).toUInt8
  let l2 := (bufLen >>> 16).toUInt8
  let l3 := (bufLen >>> 24).toUInt8
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
/-- Installs one active data segment into an already allocated memory image.  The three slices are
    the bytes before the segment, the in-bounds part of its payload, and the untouched suffix.
    Keeping installation in this compositional form exposes the loader's read-after-install laws;
    it is extensionally the same clipped overwrite as the former per-byte `set!` loop, without
    forcing proof reduction to replay one step per byte of a generated payload. -/
def installWasmDataSegment (memory : ByteArray) (segment : WasmDataSegment) : ByteArray :=
  let offset := segment.offset.toNat
  let written := segment.data.extract 0 (memory.size - offset)
  memory.extract 0 offset ++ written ++
    memory.extract (offset + written.size) memory.size

/-- Bulk data installation preserves the declared linear-memory extent. -/
@[simp] theorem installWasmDataSegment_size (memory : ByteArray) (segment : WasmDataSegment) :
    (installWasmDataSegment memory segment).size = memory.size := by
  simp only [installWasmDataSegment, ByteArray.size_append, ByteArray.size_extract]
  omega

/-- Reading the complete in-bounds payload immediately after its loader boundary returns that
    payload exactly; callers do not replay the install loop. -/
theorem readBytes_installWasmDataSegment_self (memory : ByteArray) (segment : WasmDataSegment)
    (hoffset : segment.offset.toNat ≤ memory.size)
    (hfits : segment.offset.toNat + segment.data.size ≤ memory.size) :
    WasmMem.readBytes (WasmMem.ofBytes (installWasmDataSegment memory segment))
      segment.offset.toNat segment.data.size = some segment.data := by
  unfold WasmMem.readBytes
  change (if segment.offset.toNat + segment.data.size ≤
      (installWasmDataSegment memory segment).size then
    some ((installWasmDataSegment memory segment).extract segment.offset.toNat
      (segment.offset.toNat + segment.data.size)) else none) = some segment.data
  rw [installWasmDataSegment_size]
  rw [if_pos hfits]
  simp only [Option.some.injEq]
  simp only [installWasmDataSegment]
  have hcapacity : segment.data.size ≤ memory.size - segment.offset.toNat := by omega
  rw [show segment.data.extract 0 (memory.size - segment.offset.toNat) = segment.data by
    rw [← Nat.max_eq_left hcapacity]
    exact ByteArray.extract_zero_max_size]
  rw [ByteArray.extract_append]
  have hprefix : (memory.extract 0 segment.offset.toNat).extract segment.offset.toNat
      (segment.offset.toNat + segment.data.size) = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]
    simp [ByteArray.size_extract, hoffset]
  rw [ByteArray.extract_append]
  rw [hprefix, ByteArray.empty_append]
  simp [ByteArray.size_extract, hoffset]

/-- A later segment cannot change a proved prefix. -/
theorem readBytes_installWasmDataSegment_prefix (memory : ByteArray)
    (segment : WasmDataSegment) (len : Nat)
    (hlen : len ≤ segment.offset.toNat) (hoffset : segment.offset.toNat ≤ memory.size) :
    WasmMem.readBytes (WasmMem.ofBytes (installWasmDataSegment memory segment)) 0 len =
      WasmMem.readBytes (WasmMem.ofBytes memory) 0 len := by
  unfold WasmMem.readBytes
  simp only [WasmMem.ofBytes, Nat.zero_add]
  change (if len ≤ (installWasmDataSegment memory segment).size then
      some ((installWasmDataSegment memory segment).extract 0 len) else none) =
    (if len ≤ memory.size then some (memory.extract 0 len) else none)
  rw [installWasmDataSegment_size]
  have hbound : len ≤ memory.size := Nat.le_trans hlen hoffset
  rw [if_pos hbound, if_pos hbound]
  simp only [Option.some.injEq, installWasmDataSegment]
  rw [ByteArray.extract_append, ByteArray.extract_append]
  have hprefixSize : (memory.extract 0 segment.offset.toNat).size = segment.offset.toNat := by
    simp [ByteArray.size_extract, hoffset]
  have hafter : len ≤ segment.offset.toNat +
      min (memory.size - segment.offset.toNat) segment.data.size := by omega
  simp [hprefixSize, hlen, hafter, ByteArray.extract_extract]

/-- One zero-filled Wasm page owned by the loader. -/
def initialWasmPage : ByteArray := ByteArray.mk (Array.replicate 65536 (0 : UInt8))

@[simp] theorem initialWasmPage_size : initialWasmPage.size = 65536 := by
  simp [initialWasmPage, ByteArray.size]

/-- Initializes linear memory with all active data segments, returning the sealed `WasmMemory`
    cell (`MemoryCell.lean`).  Segment installation is a fold over typed bulk-overwrite boundaries,
    so loader refinements can reason about an arbitrary payload symbolically rather than replaying
    a 64-KiB zero-fill and every payload byte. -/
def initWasmMemory (segments : List WasmDataSegment) : WasmMemory :=
  WasmMem.ofBytes (segments.foldl installWasmDataSegment initialWasmPage)

/-- The one-page WASI loader always constructs exactly one page; segment writes cannot silently
    grow memory beyond the module's declared page. -/
@[simp] theorem initWasmMemory_size (segments : List WasmDataSegment) :
    WasmMem.size (initWasmMemory segments) = 65536 := by
  simp only [initWasmMemory, WasmMem.size, WasmMem.ofBytes]
  have hfold : ∀ (memory : ByteArray) (rest : List WasmDataSegment),
      (rest.foldl installWasmDataSegment memory).size = memory.size := by
    intro memory rest
    induction rest generalizing memory with
    | nil => rfl
    | cons segment rest ih =>
        simp only [List.foldl_cons]
        rw [ih, installWasmDataSegment_size]
  rw [hfold, initialWasmPage_size]

/-- UTF-8 decoding an existing string's byte representation recovers that string.  WASI output
    contracts use this owner-level inverse law so callers never replay byte-by-byte validation of
    generated static payloads. -/
@[simp] theorem fromUTF8?_toUTF8 (text : String) :
    String.fromUTF8? text.toUTF8 = some text := by
  rcases text with ⟨bytes, hvalid⟩
  change (if h : bytes.IsValidUTF8 then some (String.fromUTF8 bytes h) else none) =
    some ⟨bytes, hvalid⟩
  split
  · rfl
  · contradiction

@[simp] theorem fromUTF8?_toByteArray (text : String) :
    String.fromUTF8? text.toByteArray = some text := by
  simpa only [String.toUTF8_eq_toByteArray] using fromUTF8?_toUTF8 text

/- REF: docs/TARGETS/WASI.md#31-wasiciovect-structure -/
/-- Reads one complete WASI ciovec as a typed ABI boundary instead of making each host operation
    separately prove two correlated 32-bit loads. -/
def readCiovec (memory : WasmMemory) (address : Nat) : Option (UInt32 × UInt32) :=
  match WasmMem.readBytes memory address 8 with
  | none => none
  | some bytes =>
      let ptr := UInt32.ofBitVec
        (((bytes.get! 3).toBitVec ++ (bytes.get! 2).toBitVec) ++
          (bytes.get! 1).toBitVec ++ (bytes.get! 0).toBitVec)
      let len := UInt32.ofBitVec
        (((bytes.get! 7).toBitVec ++ (bytes.get! 6).toBitVec) ++
          (bytes.get! 5).toBitVec ++ (bytes.get! 4).toBitVec)
      some (ptr, len)

/-- `encodeCiovec` and the host's typed reader are exact inverses. -/
theorem readCiovec_encode (memory : WasmMemory) (address : Nat) (ptr len : UInt32)
    (hread : WasmMem.readBytes memory address 8 = some (encodeCiovec ptr len)) :
    readCiovec memory address = some (ptr, len) := by
  simp [readCiovec, hread, encodeCiovec, ByteArray.get!]
  constructor <;>
    apply UInt32.toBitVec_inj.1 <;>
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb] <;>
    rw [BitVec.setWidth_eq_extractLsb' (by omega)] <;>
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)] <;>
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)] <;>
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)] <;>
    simp

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Raw operational host-call dispatcher.  The public dispatcher below applies the target-owned
    external-input boundary around calls that do not consume either input channel. -/
private def wasiHostCallRaw (imports : List String) (idx : Nat)
    (s : WasmMachineState) : WasmMachineState × ControlSignal := Id.run do
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
        match readCiovec s4.memory entryAddr with
        | some (bufPtr, bufLen) =>
          match WasmMem.readBytes s4.memory bufPtr.toNat bufLen.toNat with
          | some bytes =>
            let str := match String.fromUTF8? bytes with
              | some s => s
              | none => String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat))
            newEvents := newEvents ++ [Inject.inject (ConsoleEvent.out str)]
            totalWritten := totalWritten + bufLen
          | none => trapped := true
        | none => trapped := true
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

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Whether an import is allowed to inspect or consume the two external byte channels. -/
def wasiImportUsesExternalInputs : Option String → Bool
  | some "fd_read" | some "sock_accept" | some "sock_recv" => true
  | _ => false

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Pure operational host call dispatcher for WASI syscalls.  Calls which are not input providers
    execute against an input-erased view and have the caller's channels restored afterward.  This
    makes the architectural effect boundary explicit without imposing a whole-interpreter proof on
    each final artifact. -/
def wasiHostCall (imports : List String) (idx : Nat)
    (s : WasmMachineState) : WasmMachineState × ControlSignal :=
  if wasiImportUsesExternalInputs imports[idx]? then
    wasiHostCallRaw imports idx s
  else
    let result := wasiHostCallRaw imports idx
      (s.withExternalInputs ByteArray.empty [])
    (result.1.withExternalInputs s.stdin s.incomingRequests, result.2)

/- REF: docs/TARGETS/WASI.md#21-fdwrite -/
/-- Typed single-iovec `fd_write` boundary contract.  The host layer owns the stack convention and
    memory effects; artifact proofs supply only the three loader read facts and the checked
    `nwritten` write returned by the memory owner. -/
theorem wasiHostCall_fd_write_single
    (memory writtenMemory : WasmMemory) (memMax : Option UInt32) (text : String) (len : UInt32)
    (hciovec : readCiovec memory 0 = some (16, len))
    (hsize : len.toNat = text.toUTF8.size)
    (hpayload : WasmMem.readBytes memory 16 len.toNat = some text.toUTF8)
    (hwritten : WasmMem.write32 memory 8 len = some writtenMemory) :
    wasiHostCall ["fd_write", "proc_exit"] 0
        { stack := [.i32 8, .i32 1, .i32 0, .i32 1], memory := memory, memMax := memMax } =
      ({ stack := [.i32 0], memory := writtenMemory, memMax := memMax,
          events := [Inject.inject (ConsoleEvent.out text)] }, .next) := by
  have hpayload' : WasmMem.readBytes memory 16 text.toUTF8.size = some text.toUTF8 := by
    simpa [hsize] using hpayload
  have hpayload'' : WasmMem.readBytes memory 16 text.utf8ByteSize = some text.toUTF8 := by
    simpa [String.toUTF8_eq_toByteArray, String.size_toByteArray] using hpayload'
  simp [wasiHostCall, wasiHostCallRaw, popI32, hciovec, hpayload'', hwritten,
    hsize, pushVal, WasmMachineState.withExternalInputs]

/- REF: docs/TARGETS/WASI.md#20-fdread -/
/-- Typed single-iovec `fd_read` contract.  This is the exact operational
    progress fact used by streaming WASI consumers: while bytes remain, the
    host copies at most the declared iovec length and advances the concrete
    input cursor by exactly that copied prefix.  The caller retains the iovec
    and checked-memory premises; no unbounded or fabricated read result is
    introduced by the ABI layer. -/
theorem wasiHostCall_fd_read_single
    (state : WasmMachineState) (nreadPtr : UInt32) (pos : Nat)
    (memoryAfterRead memoryAfter : WasmMemory)
    (hpos : pos < state.stdin.size)
    (hbuf : WasmMem.read32 state.memory 0 = some 0x100)
    (hlen : WasmMem.read32 state.memory 4 = some 512)
    (hwrite : WasmMem.writeBytes state.memory 0x100
      (state.stdin.extract pos (pos + Nat.min 512 (state.stdin.size - pos))) = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead nreadPtr.toNat
      (Nat.min 512 (state.stdin.size - pos)).toUInt32 = some memoryAfter) :
    wasiHostCall ["fd_read", "fd_write", "proc_exit"] 0
      { state with stack := [.i32 nreadPtr, .i32 1, .i32 0, .i32 0], stdinPos := pos } =
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos + Nat.min 512 (state.stdin.size - pos), stack := [] }), .next) := by
  simp [wasiHostCall, wasiImportUsesExternalInputs, wasiHostCallRaw, popI32, hbuf, hlen, hpos, hwrite, hnread,
    pushVal]

/- REF: docs/TARGETS/WASI.md#22-procexit -/
/-- Typed clean `proc_exit(0)` boundary contract. -/
@[simp] theorem wasiHostCall_proc_exit_zero (state : WasmMachineState) :
    wasiHostCall ["fd_write", "proc_exit"] 1 { state with stack := [.i32 0] } =
      ({ stack := [], locals := state.locals, memory := state.memory, memMax := state.memMax,
          resourceFailure := state.resourceFailure, stdin := state.stdin, stdinPos := state.stdinPos,
          incomingRequests := state.incomingRequests, trapped := state.trapped,
          exitCode := some 0, events := state.events ++ [Inject.inject (ProcessEvent.exit 0)],
          fuelExhausted := state.fuelExhausted }, .ret) := by
  simp [wasiHostCall, wasiHostCallRaw, popI32, WasmMachineState.withExternalInputs]

/- REF: docs/TARGETS/WASI.md#21-fdwrite -/
/- REF: docs/TARGETS/WASI.md#22-procexit -/
/-- Reusable symbolic contract for the conventional single-iovec write followed by clean exit.
    The artifact supplies only its `fd_write` realization; the WASI owner composes the instruction
    sequence and `proc_exit` contract without inspecting the artifact's memory representation. -/
theorem evalWasiWriteThenExit
    (memory writtenMemory : WasmMemory) (memMax : Option UInt32) (text : String)
    (hwrite :
      wasiHostCall ["fd_write", "proc_exit"] 0
          { stack := [.i32 8, .i32 1, .i32 0, .i32 1], memory := memory, memMax := memMax } =
        ({ stack := [.i32 0], memory := writtenMemory, memMax := memMax,
            events := [Inject.inject (ConsoleEvent.out text)] }, .next)) :
    evalInstrs 100
        [.i32_const 1, .i32_const 0, .i32_const 1, .i32_const 8,
         .call 0, .drop, .i32_const 0, .call 1]
        { memory := memory, memMax := memMax }
        (wasiHostCall ["fd_write", "proc_exit"]) =
      .ok ({ memory := writtenMemory, memMax := memMax, exitCode := some 0,
              events := [Inject.inject (ConsoleEvent.out text),
                Inject.inject (ProcessEvent.exit 0)] }, .ret) := by
  have hproc :
      wasiHostCall ["fd_write", "proc_exit"] 1
          { stack := [.i32 0], memory := writtenMemory, memMax := memMax,
            events := [Inject.inject (ConsoleEvent.out text)] } =
        ({ stack := [], memory := writtenMemory, memMax := memMax, exitCode := some 0,
            events := [Inject.inject (ConsoleEvent.out text),
              Inject.inject (ProcessEvent.exit 0)] }, .ret) := by
    simpa using wasiHostCall_proc_exit_zero
      ({ memory := writtenMemory, memMax := memMax,
         events := [Inject.inject (ConsoleEvent.out text)] } : WasmMachineState)
  simp [evalInstrs, evalInstrMatch, pushVal, hwrite, hproc]

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Every import not designated as an input provider satisfies the external-input frame law. -/
theorem wasiHostCall_external_input_frame_of_not_uses
    (imports : List String) (idx : Nat)
    (huses : wasiImportUsesExternalInputs imports[idx]? = false) :
    ∀ state stdin requests,
      wasiHostCall imports idx (state.withExternalInputs stdin requests) =
        let result := wasiHostCall imports idx state
        (result.1.withExternalInputs stdin requests, result.2) := by
  intro state stdin requests
  simp [wasiHostCall, huses, WasmMachineState.withExternalInputs]

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The stock output-only WASI runtime is independent of both external byte channels. -/
theorem wasiHostCall_output_only_external_input_frame :
    WasmHostPreservesExternalInputFrame (wasiHostCall ["fd_write", "proc_exit"]) := by
  intro index state stdin requests
  apply wasiHostCall_external_input_frame_of_not_uses
  cases index with
  | zero => rfl
  | succ index => cases index <;> rfl

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

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Concrete runtime provision selected at one program entry.  Fuel is deliberately not an
    artifact constant: an artifact is reusable, while the finite work required by a particular
    finite environment is not.  The capability composition selects this record from its entry
    context, so a whole-program proof can require a per-input sufficient fuel grant without
    making the input domain finite or silently treating fuel as infinite.  Linear memory remains
    finite and is still passed to the evaluator as a fallible capability. -/
structure WasiRuntime where
  host : WasiHostRuntime
  resources : WasiResourceBudget

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
  deriving BEq, DecidableEq

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

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Replacing only external byte channels cannot change the classified WASI observation. -/
theorem WasiRunOutcome.ofResult_observable_withExternalInputs
    (result : WasmRunResult) (stdin : ByteArray) (requests : List ByteArray) :
    (WasiRunOutcome.ofResult
      (result.withExternalInputs stdin requests)).observable =
        (WasiRunOutcome.ofResult result).observable := by
  cases result with
  | error state => rfl
  | ok result =>
      rcases result with ⟨state, signal⟩
      cases hresource : state.resourceFailure with
      | some failure =>
          cases failure
          simp [WasmRunResult.withExternalInputs, WasiRunOutcome.ofResult,
            WasiRunOutcome.observable, WasmMachineState.withExternalInputs, hresource]
      | none =>
          cases htrapped : state.trapped with
          | false =>
              cases hexit : state.exitCode <;>
                simp [WasmRunResult.withExternalInputs, WasiRunOutcome.ofResult,
                  WasiRunOutcome.observable, WasmMachineState.withExternalInputs,
                  hresource, htrapped, hexit]
          | true =>
              simp [WasmRunResult.withExternalInputs, WasiRunOutcome.ofResult,
                WasiRunOutcome.observable, WasmMachineState.withExternalInputs,
                hresource, htrapped]

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- A runtime which frames the selected imports produces the same observable result for every
    external byte stream.  This is the artifact-independent transport theorem used by output-only
    final programs; their sole closed certificate is proved at the empty environment. -/
theorem runWasiOutcomeWithHost_observable_external_input_frame
    (host : WasiHostRuntime) (instrs : List WasmInstr) (segments : List WasmDataSegment)
    (imports : List String) (budget : WasiResourceBudget)
    (hhost : WasmHostPreservesExternalInputFrame (host imports))
    (stdin : ByteArray) (requests : List ByteArray) :
    (runWasiOutcomeWithHost host instrs segments stdin imports requests budget).observable =
      (runWasiOutcomeWithHost host instrs segments ByteArray.empty imports [] budget).observable := by
  unfold runWasiOutcomeWithHost
  dsimp only
  split
  · rfl
  · let base : WasmMachineState := {
      memory := initWasmMemory segments
      memMax := some (Nat.min budget.memoryPages 65536).toUInt32
    }
    change (WasiRunOutcome.ofResult
      (evalInstrs budget.fuel instrs
        (base.withExternalInputs stdin requests) (host imports))).observable = _
    rw [evalInstrs_external_input_frame (host imports) hhost]
    exact WasiRunOutcome.ofResult_observable_withExternalInputs _ _ _

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Stock output-only WASI execution has one observation for the entire `Environment` input
    domain. -/
theorem runWasiOutcome_output_only_observable_external_input_frame
    (instrs : List WasmInstr) (segments : List WasmDataSegment)
    (budget : WasiResourceBudget) (stdin : ByteArray) (requests : List ByteArray) :
    (runWasiOutcome instrs segments stdin ["fd_write", "proc_exit"] requests budget).observable =
      (runWasiOutcome instrs segments ByteArray.empty ["fd_write", "proc_exit"] [] budget).observable :=
  runWasiOutcomeWithHost_observable_external_input_frame wasiHostCall instrs segments
    ["fd_write", "proc_exit"] budget wasiHostCall_output_only_external_input_frame stdin requests

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
/-- Complete WASI artifact tied to instructions and import ABI. `defaultResources` is an artifact
    profile for tools and fixed-runtime callers; `Platform.run` deliberately consumes the concrete
    `WasiRuntime.resources` selected at entry instead. A universal verified program must therefore
    establish any input-dependent fuel provision through its capability context. -/
structure WasiArtifact where
  module : WasmModule
  typeSignatures : List FuncType
  instructions : List WasmInstr
  dataSegments : List WasmDataSegment
  imports : List String := ["fd_write", "proc_exit"]
  defaultResources : WasiResourceBudget

/-- One exact host-import slot.  Carrying the complete import vector prevents
    an index proof for one module from being reused against another module's
    differently ordered imports. -/
inductive WasiProviderProtocol where
  | preview1
  | library (key : ProviderProtocolKey)
deriving DecidableEq, BEq

structure WasiProvider where
  protocol : WasiProviderProtocol
  imports : List String
  importIndex : Nat

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
  { Args := fun _ => Unit
    Binding := fun _ => Unit
    Result := fun _ => Unit
    Outcome := fun _ => Unit
    ObligationFragment := fun _ => Unit
    requiredObligations := fun _ _ _ => ()
    emittedObligations := fun _ _ _ _ _ => ()
    requires := fun _ _ _ _ => True
    transitions := fun _ _ _ _ _ before after => before = after }

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
  RuntimeContext := WasiRuntime
  Import := String
  Provider := WasiProvider
  BoundaryWorld := Unit
  BoundaryKey := Unit
  BoundaryTarget := WasiPlatform
  boundarySpec := wasiBoundarySpec
  boundarySemantics := wasiBoundarySemantics
  imports := fun artifact => artifact.imports
  providerProvides := fun provider imported =>
    provider.imports[provider.importIndex]? = some imported
  providerLinked := fun artifact provider => provider.imports = artifact.imports
  runtimeSupports := fun runtime _ provider =>
    match provider.protocol with
    | .preview1 => ∀ state,
        runtime.host provider.imports provider.importIndex state =
          wasiHostCall provider.imports provider.importIndex state
    | .library _ => ∀ state,
        (runtime.host provider.imports provider.importIndex state).1.trapped = state.trapped
  boundaryArtifact := id
  artifactConnected := fun artifact =>
    artifact.module.functions.head?.map (fun fn => fn.body) = some artifact.instructions ∧
    artifact.module.dataSegments = artifact.dataSegments ∧
    artifact.module.imports.map (fun imported => imported.name) = artifact.imports
  load := fun _ environment => environment
  run := fun runtime artifact environment =>
    (runWasiOutcomeWithHost runtime.host artifact.instructions artifact.dataSegments environment.stdin
      artifact.imports environment.incomingRequests runtime.resources).observable
  admissible := fun _ artifact _ => ∃ bytes, emitWasmBinary artifact.module artifact.typeSignatures = .ok bytes
  emit := fun artifact => emitWasmBinary artifact.module artifact.typeSignatures

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
def wasiHostCapability : Capability WasiPlatform where
  Context := WasiResourceBudget
  providers :=
    [{ protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 0 },
     { protocol := .preview1, imports := ["fd_write", "proc_exit"], importIndex := 1 }]
  establishes := fun _ _ _ _ => True

private def realizeWasiHost (_artifact : WasiArtifact) (resources : WasiResourceBudget) :
    WasiRuntime :=
  { host := wasiHostCall, resources }

def wasiHostCapabilities : CapabilityComposition WasiPlatform where
  root := wasiHostCapability
  realize := realizeWasiHost
  realizeSupports := by
    intro context artifact provider hprovider hlinked
    simp only [wasiHostCapability, List.mem_cons, List.not_mem_nil, or_false] at hprovider
    rcases hprovider with rfl | rfl <;> intro state <;> rfl

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- WAT rendering remains gated by the same sole proof authority as binary emission, while allowing
    any capability composition proved for the WASI platform. -/
def renderVerifiedWasmText {capabilities : CapabilityComposition WasiPlatform}
    (program : VerifiedProgram WasiPlatform capabilities) : String :=
  emitWasmText program.artifact.module program.artifact.typeSignatures

end Gasm.Targets.WASI
