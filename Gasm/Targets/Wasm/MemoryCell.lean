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

namespace Gasm.Targets.Wasm

/- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -/
/- REF: wasm-exec-runtime#memory-instances -/
/-- Sealed WebAssembly linear-memory cell. `mk`/`raw` are `private` to this module
    (module-scoped in Lean 4): outside this file no term can construct a `WasmMemory` from an
    arbitrary `ByteArray`, nor project one back out. `WasmMem.read8/32/64`/`write8/32/64` below --
    defined in this same file, the only place the seal permits touching `raw` -- are consequently
    the only functions in the whole tree that can observe or change WebAssembly linear-memory
    bytes; `evalLeafInstr`'s memory cases (`Semantics.lean`) and `wasiHostCall`'s syscall
    implementations (`Gasm/Targets/WASI/ABI.lean`) are both structurally forced through them.

    This is the Wasm-side counterpart of `Gasm/Targets/X86_64/MemoryCell.lean`'s
    `X86_64Memory` seal (Law 13 preference-tier 1: the bypass is unrepresentable, not linted), but
    it exists for a different reason. x86-64's flat address space has no runtime bounds check at
    all, so the seal's job is to force every access through a *single, auditable, capability-
    checkable* chokepoint (Law 11's assemble-time obligation attaches to that chokepoint's
    descriptor). WebAssembly's specification already mandates a runtime bounds check on every
    memory access (`wasm-exec-instructions#memory-instructions`'s trap reduction rule, landed for
    the instruction path by B7) -- so here the seal's job is narrower and purely structural: make
    it impossible to *reintroduce* an access path that skips that check, the way
    `Gasm/Targets/WASI/ABI.lean`'s `wasiHostCall` did before this change (it called the old
    unchecked `readMem32`/`writeMem32` helpers directly, and `fd_read`/`sock_recv` additionally
    called `ByteArray.set!` on `s.memory` raw -- bypassing `evalInstr`'s trap check entirely; see
    `docs/tasks/B7-wasm-oob-trap-and-limits.md`'s closing note and `docs/MEMORY_HOOK.md`'s
    cross-target section for the full asymmetry argument). -/
structure WasmMemory where
  private mk ::
  private raw : ByteArray

namespace WasmMem

/- REF: wasm-exec-runtime#memory-instances -/
/-- Current size of linear memory, in bytes. -/
def size (m : WasmMemory) : Nat := m.raw.size

/- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -/
/-- The empty memory (0 bytes) -- the sealed replacement for the raw `ByteArray.empty` literal
    every pre-seal `WasmMachineState` default/test-literal used. -/
def empty : WasmMemory := ⟨ByteArray.empty⟩

/- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -/
/-- Loader/test-harness bulk-install entry point: wraps an arbitrary, already-computed
    `ByteArray` (an instantiated module's initial linear memory, a differential-fuzzer test
    fixture) as sealed `WasmMemory` in one step. This is the Wasm counterpart of
    `X86_64Mem.initRegion` -- installing a computed memory image is a legitimate bulk operation,
    and naming it keeps callers inside the chokepoint instead of allowlisted around it. The bytes
    themselves may be built with ordinary total `ByteArray` operations (`.set!`, `++`, ...)
    *before* this call, exactly as `X86_64Mem.initRegion`'s callers compute an arbitrary
    `Address → Byte` function before wrapping it -- what the seal forbids is touching the bytes of
    an *already-installed* `WasmMemory` outside this module, not the construction of a fresh image. -/
def ofBytes (b : ByteArray) : WasmMemory := ⟨b⟩

/- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -/
/-- All-zero memory of the given byte length -- the sealed replacement for the raw
    `ByteArray.mk (Array.mk (List.replicate n 0))` literal scattered across the differential
    fuzzer's test fixtures before sealing made constructing that literal outside this file
    impossible. -/
def zero (byteLen : Nat) : WasmMemory :=
  ofBytes (ByteArray.mk (Array.mk (List.replicate byteLen (0 : UInt8))))

/- REF: docs/MEMORY_HOOK.md#12-cross-target-note-wasm -/
/-- Extracts the raw bytes -- a total, read-only OBSERVATION api (serializing a model state's
    memory into a data segment for the host-oracle differential harness, `HostOracle.lean`'s
    `buildTestWasmModuleForResults`), not a mutation path. Mirrors `X86_64Mem.read`'s role: the
    seal restricts who can construct/mutate a `WasmMemory` and does not need to restrict pure
    observation of one, exactly as `docs/MEMORY_HOOK.md` §3.2 notes for the x86-64 seal
    ("Spec/proof-side observation ... uses the read API and is unaffected"). -/
def toBytes (m : WasmMemory) : ByteArray := m.raw

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Unconditional bulk append -- the ONLY way `memory.grow`'s new pages can be installed. The
    caller (`evalLeafInstr`'s `.memory_grow` case) is responsible for the `Limits.max`/hard-ceiling
    admission decision (B8) BEFORE calling this; `grow` itself performs no bounds decision, exactly
    mirroring how `write8/32/64` below make the OOB decision themselves but `evalLeafInstr` decides
    *whether* to grow at all. -/
def grow (m : WasmMemory) (padding : ByteArray) : WasmMemory := ⟨m.raw ++ padding⟩

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Checked single-byte read: `none` means `addr` is out of bounds -- the caller (an instruction's
    `step` or a WASI host call) traps rather than fabricating a value. Per the WebAssembly
    specification's reduction rule for `t.load`, an out-of-bounds read must trap, not silently
    return a default. -/
def read8 (m : WasmMemory) (addr : Nat) : Option UInt8 :=
  if addr < m.raw.size then some (m.raw.get! addr) else none

/- REF: wasm-exec-runtime#memory-instances -/
/-- Checked little-endian 32-bit read, atomic over its 4-byte range: `none` unless every one of
    `[addr, addr+4)` is in bounds -- a straddling access (in-bounds start, out-of-bounds end) traps
    exactly as a fully out-of-bounds one does, matching the spec's single inequality over the whole
    access width rather than a per-byte check. -/
def read32 (m : WasmMemory) (addr : Nat) : Option UInt32 :=
  if addr + 4 <= m.raw.size then
    some (
      (m.raw.get! addr).toUInt32 |||
      ((m.raw.get! (addr + 1)).toUInt32 <<< 8) |||
      ((m.raw.get! (addr + 2)).toUInt32 <<< 16) |||
      ((m.raw.get! (addr + 3)).toUInt32 <<< 24))
  else none

/- REF: wasm-exec-runtime#memory-instances -/
/-- Checked little-endian 64-bit read, atomic over its 8-byte range (see `read32`'s docstring for
    the straddling-access rationale). -/
def read64 (m : WasmMemory) (addr : Nat) : Option UInt64 :=
  if addr + 8 <= m.raw.size then
    some (
      (m.raw.get! addr).toUInt64 |||
      ((m.raw.get! (addr + 1)).toUInt64 <<< 8) |||
      ((m.raw.get! (addr + 2)).toUInt64 <<< 16) |||
      ((m.raw.get! (addr + 3)).toUInt64 <<< 24) |||
      ((m.raw.get! (addr + 4)).toUInt64 <<< 32) |||
      ((m.raw.get! (addr + 5)).toUInt64 <<< 40) |||
      ((m.raw.get! (addr + 6)).toUInt64 <<< 48) |||
      ((m.raw.get! (addr + 7)).toUInt64 <<< 56))
  else none

/- REF: wasm-exec-instructions#memory-instructions -/
/-- Checked single-byte write: `none` means `addr` is out of bounds, and -- critically -- `m` is
    NOT touched at all in that case (`Option`, not a total no-op): the caller must observe the
    failure and trap rather than silently discarding it, which is exactly what made the pre-B7
    `writeMem8`/pre-seal `wasiHostCall` bypass possible (a total no-op function is
    indistinguishable, at the call site, from "nothing needed writing"). -/
def write8 (m : WasmMemory) (addr : Nat) (v : UInt8) : Option WasmMemory :=
  if addr < m.raw.size then some ⟨m.raw.set! addr v⟩ else none

/- REF: wasm-exec-runtime#memory-instances -/
/-- Checked little-endian 32-bit write, atomic over its 4-byte range: either all four bytes are
    written or none are (never a partial write left behind by a straddling access). -/
def write32 (m : WasmMemory) (addr : Nat) (v : UInt32) : Option WasmMemory :=
  if addr + 4 <= m.raw.size then
    let b0 := (v &&& 0xFF).toUInt8
    let b1 := ((v >>> 8) &&& 0xFF).toUInt8
    let b2 := ((v >>> 16) &&& 0xFF).toUInt8
    let b3 := ((v >>> 24) &&& 0xFF).toUInt8
    let r0 := m.raw.set! addr b0
    let r1 := r0.set! (addr + 1) b1
    let r2 := r1.set! (addr + 2) b2
    let r3 := r2.set! (addr + 3) b3
    some ⟨r3⟩
  else none

/- REF: wasm-exec-runtime#memory-instances -/
/-- Checked little-endian 64-bit write, atomic over its 8-byte range (see `write32`'s docstring). -/
def write64 (m : WasmMemory) (addr : Nat) (v : UInt64) : Option WasmMemory :=
  if addr + 8 <= m.raw.size then
    let b0 := (v &&& 0xFF).toUInt8
    let b1 := ((v >>> 8) &&& 0xFF).toUInt8
    let b2 := ((v >>> 16) &&& 0xFF).toUInt8
    let b3 := ((v >>> 24) &&& 0xFF).toUInt8
    let b4 := ((v >>> 32) &&& 0xFF).toUInt8
    let b5 := ((v >>> 40) &&& 0xFF).toUInt8
    let b6 := ((v >>> 48) &&& 0xFF).toUInt8
    let b7 := ((v >>> 56) &&& 0xFF).toUInt8
    let r0 := m.raw.set! addr b0
    let r1 := r0.set! (addr + 1) b1
    let r2 := r1.set! (addr + 2) b2
    let r3 := r2.set! (addr + 3) b3
    let r4 := r3.set! (addr + 4) b4
    let r5 := r4.set! (addr + 5) b5
    let r6 := r5.set! (addr + 6) b6
    let r7 := r6.set! (addr + 7) b7
    some ⟨r7⟩
  else none

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Checked bulk read of `len` bytes starting at `addr`, atomic over the whole range -- the
    chokepoint `wasiHostCall`'s `fd_write`/`sock_send` route their buffer reads through instead of
    calling `ByteArray.extract` on `s.memory` directly (which silently clips to whatever the array
    actually holds rather than treating an out-of-declared-range request as the guest-memory-safety
    violation it is). -/
def readBytes (m : WasmMemory) (addr len : Nat) : Option ByteArray :=
  if addr + len <= m.raw.size then some (m.raw.extract addr (addr + len)) else none

/- REF: docs/TARGETS/WASI.md#2-syscall-signatures -/
/-- Checked bulk write of `bytes` starting at `addr`, atomic over the whole range -- the
    chokepoint `wasiHostCall`'s `fd_read`/`sock_recv` route their buffer writes through instead of
    looping raw `ByteArray.set!` calls directly on `s.memory` (which is exactly the bypass this
    module's docstring names: unchecked, and structurally capable of writing past the end of the
    array with no observable failure at all). -/
def writeBytes (m : WasmMemory) (addr : Nat) (bytes : ByteArray) : Option WasmMemory :=
  if addr + bytes.size <= m.raw.size then
    some ⟨(List.range bytes.size).foldl (fun acc i => acc.set! (addr + i) (bytes.get! i)) m.raw⟩
  else none

end WasmMem

end Gasm.Targets.Wasm
