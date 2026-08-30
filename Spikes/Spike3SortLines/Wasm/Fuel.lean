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

import Gasm.Targets.WASI.ABI

namespace Spikes.Spike3SortLines.Wasm

open Gasm.Targets.Wasm
open Gasm.Targets.WASI

/-! Direct fuel/progress facts for the production Spike 3 Wasm body.

These lemmas deliberately describe the real interpreter and the fixed WASI
imports used by `spike3WasmInstructions`.  They are not a second evaluator or
a generic Wasm cost framework: each subsequent loop lemma will consume the
exact state relation produced here.
-/

/-- One production `fd_read` with Spike 3's statically installed single
    512-byte iovec consumes exactly the available prefix, advances `stdinPos`
    by that amount, and writes the corresponding `nread`.  The memory facts
    are retained explicitly because the full loop invariant must prove that
    the program does not overwrite its input iovec. -/
theorem spike3_fdRead_single_iovec
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
  exact wasiHostCall_fd_read_single state nreadPtr pos memoryAfterRead memoryAfter
    hpos hbuf hlen hwrite hnread

end Spikes.Spike3SortLines.Wasm
