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

import Stdlib.SmolAlloc.Wasm
import Gasm.Targets.Wasm.Semantics

namespace Stdlib.SmolAlloc

open Gasm.Targets.Wasm

/-- Executes the exact alignment guard emitted by the fallible allocator.  The continuation
    pushes a marker, making the accepted and rejected branches observable without introducing an
    allocator-memory access of its own. -/
def evalWasmAlignmentNoWrapGuard (size aligned : UInt32) (memory : WasmMemory) : WasmRunResult :=
  evalInstrs 20 (emitWasmAlignmentNoWrapGuard 0 1 [.i32_const 0x7F])
    { locals := [.i32 size, .i32 aligned], memory := memory }
    (fun _ state => (state, .next))

/-- Exact evaluator boundary: the maximum representable aligned request reaches its continuation. -/
theorem evalWasmAlignmentNoWrapGuard_maximum_accepts (memory : WasmMemory) :
    evalWasmAlignmentNoWrapGuard 0xFFFFFFF8 0xFFFFFFF8 memory =
      .ok ({ stack := [.i32 0x7F], locals := [.i32 0xFFFFFFF8, .i32 0xFFFFFFF8], memory := memory }, .next) := by
  rfl

/-- Exact evaluator boundary: the first alignment-overflow request skips its continuation. -/
theorem evalWasmAlignmentNoWrapGuard_first_overflow_rejects (memory : WasmMemory) :
    evalWasmAlignmentNoWrapGuard 0xFFFFFFF9 0 memory =
      .ok ({ locals := [.i32 0xFFFFFFF9, .i32 0], memory := memory }, .next) := by
  rfl

/-- The rejecting evaluator branch preserves a nonempty free-list cell exactly: the exact emitted
    guard has no memory instruction before deciding to skip the allocator continuation. -/
theorem evalWasmAlignmentNoWrapGuard_overflow_preserves_nonempty_freelist
    (memory : WasmMemory) (head : UInt32)
    (hhead : WasmMem.read32 memory wasmFreeListHeadAddr.toNat = some head) :
    (evalWasmAlignmentNoWrapGuard 0xFFFFFFF9 0 memory).map (fun result => result.1.memory) =
      .ok memory ∧
    WasmMem.read32 memory wasmFreeListHeadAddr.toNat = some head := by
  constructor
  · rfl
  · exact hhead

/-- The exact emitted initialization from a stale nonzero header scratch local. -/
def evalWasmFallibleMallocStaleHeaderInitialization (memory : WasmMemory) : WasmRunResult :=
  let locals := (List.replicate 28 (.i32 0)).set 25 (.i32 0x100)
  evalInstrs 12 (emitSmolMallocWasmFallibleInitialization 23 24 25)
    { stack := [.i32 0xFFFFFFF9], locals := locals, memory := memory }
    (fun _ state => (state, .next))

/-- Before the alignment guard, the exact emitted initialization overwrites stale success
    scratch and performs no memory operation or trap. -/
theorem evalWasmFallibleMallocStaleHeaderInitialization_clears_and_frames_memory
    (memory : WasmMemory) :
    (evalWasmFallibleMallocStaleHeaderInitialization memory).map
      (fun result => (result.1.locals[25]?, result.1.memory, result.1.trapped)) =
      .ok (some (WasmVal.i32 0), memory, false) := by
  rfl

/-- The exact shared fallible-allocator epilogue turns its initialized zero header scratch into
    the ordinary null result without trapping or changing memory. -/
def evalWasmFallibleMallocZeroHeaderEpilogue (memory : WasmMemory) : WasmRunResult :=
  evalInstrs 8 (emitSmolMallocWasmFallibleEpilogue 25)
    { locals := List.replicate 28 (.i32 0), memory := memory }
    (fun _ state => (state, .next))

theorem evalWasmFallibleMallocZeroHeaderEpilogue_returns_null (memory : WasmMemory) :
    (evalWasmFallibleMallocZeroHeaderEpilogue memory).map
      (fun result => (result.1.stack, result.1.memory, result.1.trapped)) =
      .ok ([.i32 0], memory, false) := by
  rfl

end Stdlib.SmolAlloc
