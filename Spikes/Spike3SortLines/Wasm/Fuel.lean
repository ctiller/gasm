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

/-- One ordinary production instruction consumes the two interpreter entries
    (`evalInstrs` and `evalInstrMatch`) and leaves all continuation fuel
    available to the exact remaining instruction list.  This local helper is
    intentionally kept here rather than becoming a second evaluator or a
    global cost model. -/
theorem spike3_evalInstrs_step
    (fuel : Nat) (instruction : WasmInstr) (rest : List WasmInstr)
    (before after : WasmMachineState)
    (hbefore : before.trapped = false) (hexit : before.exitCode = none)
    (hstep : evalInstrMatch (fuel + 1) instruction before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) = .ok (after, .next)) :
    evalInstrs (fuel + 2) (instruction :: rest) before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) =
      evalInstrs (fuel + 1) rest after
        (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  simp only [evalInstrs, hbefore, hexit, Option.isSome_none, Bool.or_self,
    Bool.false_eq_true, if_false, hstep]

/-- Exact production-loop re-entry.  A body which returns `br 0` is the one
    Wasm signal that re-enters that same loop, and it consumes precisely the
    outer `evalLoop` entry before continuing from the post-body state. -/
theorem spike3_evalLoop_reenter
    (fuel : Nat) (body : List WasmInstr) (before after : WasmMachineState)
    (hbody : evalInstrs fuel body before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) = .ok (after, .br 0)) :
    evalLoop (fuel + 1) body before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) =
    evalLoop fuel body after
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) := by
  rw [show fuel + 1 = Nat.succ fuel by rfl]
  simp [evalLoop, hbody]

/-- A branch that targets the enclosing block exits the current production
    loop.  This is the EOF/finished-work shape used by every bounded Spike 3
    loop; the parent block receives the decremented branch signal. -/
theorem spike3_evalLoop_exit
    (fuel depth : Nat) (body : List WasmInstr) (before after : WasmMachineState)
    (hbody : evalInstrs fuel body before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) = .ok (after, .br (depth + 1))) :
    evalLoop (fuel + 1) body before
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) = .ok (after, .br depth) := by
  rw [show fuel + 1 = Nat.succ fuel by rfl]
  simp [evalLoop, hbody]

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

/-- The `call 0` instruction used at the head of every Spike 3 ingestion
    iteration consumes a fixed two-unit interpreter prefix and hands the exact
    host-read post-state to the rest of that *same production loop body*. -/
theorem spike3_step_fdRead
    (fuel : Nat) (rest : List WasmInstr) (state : WasmMachineState)
    (nreadPtr : UInt32) (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hbefore : state.trapped = false) (hexit : state.exitCode = none)
    (hpos : pos < state.stdin.size)
    (hbuf : WasmMem.read32 state.memory 0 = some 0x100)
    (hlen : WasmMem.read32 state.memory 4 = some 512)
    (hwrite : WasmMem.writeBytes state.memory 0x100
      (state.stdin.extract pos (pos + Nat.min 512 (state.stdin.size - pos))) = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead nreadPtr.toNat
      (Nat.min 512 (state.stdin.size - pos)).toUInt32 = some memoryAfter) :
    evalInstrs (fuel + 2) (.call 0 :: rest)
      { state with stack := [.i32 nreadPtr, .i32 1, .i32 0, .i32 0], stdinPos := pos }
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) =
    evalInstrs (fuel + 1) rest
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos + Nat.min 512 (state.stdin.size - pos), stack := [] }))
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) := by
  apply spike3_evalInstrs_step
  · simpa using hbefore
  · simpa using hexit
  · simpa [evalInstrMatch, evalLeafInstr] using
      (spike3_fdRead_single_iovec state nreadPtr pos memoryAfterRead memoryAfter
        hpos hbuf hlen hwrite hnread)

/-- The positive-read branch strictly decreases the remaining-input variant
    used by the outer ingestion loop. -/
theorem spike3_fdRead_remaining_decreases (stdinSize pos : Nat)
    (hpos : pos < stdinSize) :
    stdinSize - (pos + Nat.min 512 (stdinSize - pos)) < stdinSize - pos := by
  have hremaining : 0 < stdinSize - pos := Nat.sub_pos_iff_lt.mpr hpos
  have hchunk : 0 < Nat.min 512 (stdinSize - pos) := by
    by_cases h : 512 ≤ stdinSize - pos
    · simpa only [Nat.min_eq_left h] using (show 0 < (512 : Nat) by omega)
    · simpa only [Nat.min_eq_right (Nat.le_of_not_ge h)] using hremaining
  rw [← Nat.sub_sub]
  exact Nat.sub_lt hremaining hchunk

/-- At EOF the fixed read path writes a zero count and preserves the concrete
    cursor.  The enclosing Wasm loop immediately takes its existing `br_if`
    exit on that count. -/
theorem spike3_fdRead_single_iovec_eof
    (state : WasmMachineState) (nreadPtr : UInt32) (pos : Nat)
    (memoryAfterRead memoryAfter : WasmMemory)
    (heof : state.stdin.size ≤ pos)
    (hbuf : WasmMem.read32 state.memory 0 = some 0x100)
    (hlen : WasmMem.read32 state.memory 4 = some 512)
    (hwrite : WasmMem.writeBytes state.memory 0x100 ByteArray.empty = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead nreadPtr.toNat 0 = some memoryAfter) :
    wasiHostCall ["fd_read", "fd_write", "proc_exit"] 0
      { state with stack := [.i32 nreadPtr, .i32 1, .i32 0, .i32 0], stdinPos := pos } =
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos, stack := [] }), .next) :=
  wasiHostCall_fd_read_single_eof state nreadPtr pos memoryAfterRead memoryAfter
    heof hbuf hlen hwrite hnread

end Spikes.Spike3SortLines.Wasm
