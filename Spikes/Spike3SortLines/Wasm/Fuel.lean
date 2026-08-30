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
import Spikes.Spike3SortLines.Wasm.Program

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

/-- The concrete loader starts the production program with its fixed stdin
    iovec installed at address zero.  Later static segments are outside this
    eight-byte prefix, so their loader steps preserve it. -/
theorem spike3InitialMemory_input_iovec_bytes :
    WasmMem.readBytes (initWasmMemory spike3DataSegments) 0 8 =
      some (encodeCiovec 0x100 512) := by
  simp only [initWasmMemory, spike3DataSegments, List.foldl_cons, List.foldl_nil]
  rw [readBytes_installWasmDataSegment_prefix _ _ 8 (by decide) (by simp)]
  rw [readBytes_installWasmDataSegment_prefix _ _ 8 (by decide) (by simp)]
  have hciovecSize : (encodeCiovec 0x100 512).size = 8 := by rfl
  exact readBytes_installWasmDataSegment_self initialWasmPage
    { offset := 0x00, data := encodeCiovec 0x100 512 } (by simp) (by
      change 0 + (encodeCiovec 0x100 512).size ≤ initialWasmPage.size
      rw [hciovecSize, initialWasmPage_size]
      decide)

/-- Typed view of the loader fact: the initial production state exposes the
    fixed 512-byte stdin iovec, rather than an arbitrary host-selected read
    buffer. -/
theorem spike3InitialMemory_input_iovec :
    readCiovec (initWasmMemory spike3DataSegments) 0 = some (0x100, 512) :=
  readCiovec_encode _ _ _ _ spike3InitialMemory_input_iovec_bytes

/-- The descriptor clause carried at the outer ingestion-loop re-entry. -/
def Spike3IngestionIovec (state : WasmMachineState) : Prop :=
  readCiovec state.memory 0 = some (0x100, 512)

theorem spike3InitialMemory_has_ingestion_iovec :
    Spike3IngestionIovec { memory := initWasmMemory spike3DataSegments } :=
  spike3InitialMemory_input_iovec

/-- The fixed `nread` cell is exactly byte eight, and its guest `i32` address is represented
    without an arithmetic wrap before the interpreter forms the natural effective address. -/
theorem spike3_nreadPtr_address : (8 : UInt32).toNat = 8 := by decide

theorem spike3_nreadPtr_after_iovec : 8 ≤ (8 : UInt32).toNat := by decide

/-- The concrete fixed-offset word stores used to prepare stdout ciovecs are after the stdin
    descriptor; these closed facts discharge the effective-address side condition at those two
    literal call sites. -/
theorem spike3_stdout_ciovec_store0_after_iovec : 8 ≤ (0x10 : UInt32).toNat + 0 := by decide

theorem spike3_stdout_ciovec_store4_after_iovec : 8 ≤ (0x14 : UInt32).toNat + 0 := by decide

/-- The first real stdout-ciovec setup store has a closed guest-i32 address proof: `0x10` is
    represented as natural 16 before the interpreter adds its zero offset. -/
theorem spike3_stdout_ciovec_store0_preserves_ingestion_iovec
    (state : WasmMachineState) (value : UInt32) (rest : List WasmVal) (written : WasmMemory)
    (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.write32 state.memory (0x10 : UInt32).toNat value = some written) :
    Spike3IngestionIovec
      (evalLeafInstr (.i32_store 2 0)
        { state with stack := [.i32 value, .i32 0x10] ++ rest }
        (wasiHostCall ["fd_read", "fd_write", "proc_exit"])).1 := by
  unfold Spike3IngestionIovec
  rw [readCiovec_preserved_of_prefix8 _ _
    (evalLeafInstr_i32_store_preserves_prefix8 2 0 state value 0x10 rest written
      _ spike3_stdout_ciovec_store0_after_iovec hwrite)]
  exact hciovec

/-- The second real stdout-ciovec setup store is likewise outside the fixed stdin descriptor. -/
theorem spike3_stdout_ciovec_store4_preserves_ingestion_iovec
    (state : WasmMachineState) (value : UInt32) (rest : List WasmVal) (written : WasmMemory)
    (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.write32 state.memory (0x14 : UInt32).toNat value = some written) :
    Spike3IngestionIovec
      (evalLeafInstr (.i32_store 2 0)
        { state with stack := [.i32 value, .i32 0x14] ++ rest }
        (wasiHostCall ["fd_read", "fd_write", "proc_exit"])).1 := by
  unfold Spike3IngestionIovec
  rw [readCiovec_preserved_of_prefix8 _ _
    (evalLeafInstr_i32_store_preserves_prefix8 2 0 state value 0x14 rest written
      _ spike3_stdout_ciovec_store4_after_iovec hwrite)]
  exact hciovec

/-- One production `fd_read` with Spike 3's statically installed single
    512-byte iovec consumes exactly the available prefix, advances `stdinPos`
    by that amount, and writes the corresponding `nread`.  The memory facts
    are retained explicitly because the full loop invariant must prove that
    the program does not overwrite its input iovec. -/
theorem spike3_fdRead_single_iovec
    (state : WasmMachineState) (nreadPtr : UInt32) (pos : Nat)
    (memoryAfterRead memoryAfter : WasmMemory)
    (hpos : pos < state.stdin.size)
    (hciovec : readCiovec state.memory 0 = some (0x100, 512))
    (hwrite : WasmMem.writeBytes state.memory 0x100
      (state.stdin.extract pos (pos + Nat.min 512 (state.stdin.size - pos))) = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead nreadPtr.toNat
      (Nat.min 512 (state.stdin.size - pos)).toUInt32 = some memoryAfter) :
    wasiHostCall ["fd_read", "fd_write", "proc_exit"] 0
      { state with stack := [.i32 nreadPtr, .i32 1, .i32 0, .i32 0], stdinPos := pos } =
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos + Nat.min 512 (state.stdin.size - pos), stack := [] }), .next) := by
  exact wasiHostCall_fd_read_single state nreadPtr pos memoryAfterRead memoryAfter
    hpos hciovec hwrite hnread

/-- A positive fixed-site read at `nread = 8` preserves the ingestion descriptor. -/
theorem spike3_fdRead_at_nread_cell_preserves_ingestion_iovec
    (state : WasmMachineState) (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.writeBytes state.memory 0x100
      (state.stdin.extract pos (pos + Nat.min 512 (state.stdin.size - pos))) = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead 8
      (Nat.min 512 (state.stdin.size - pos)).toUInt32 = some memoryAfter) :
    Spike3IngestionIovec { state with memory := memoryAfter } := by
  exact wasiHostCall_fd_read_single_preserves_iovec state 8 pos memoryAfterRead memoryAfter
    hciovec hwrite hnread spike3_nreadPtr_after_iovec

/-- The `call 0` instruction used at the head of every Spike 3 ingestion
    iteration consumes a fixed two-unit interpreter prefix and hands the exact
    host-read post-state to the rest of that *same production loop body*. -/
theorem spike3_step_fdRead
    (fuel : Nat) (rest : List WasmInstr) (state : WasmMachineState)
    (nreadPtr : UInt32) (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hbefore : state.trapped = false) (hexit : state.exitCode = none)
    (hpos : pos < state.stdin.size)
    (hciovec : readCiovec state.memory 0 = some (0x100, 512))
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
      hpos hciovec hwrite hnread)

/-- The real `call 0` prefix in the production ingestion body uses the fixed `nread` cell and
    carries the descriptor into the remaining instructions after a positive read. -/
theorem spike3_step_fdRead_at_nread_cell
    (fuel : Nat) (rest : List WasmInstr) (state : WasmMachineState)
    (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hbefore : state.trapped = false) (hexit : state.exitCode = none)
    (hpos : pos < state.stdin.size) (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.writeBytes state.memory 0x100
      (state.stdin.extract pos (pos + Nat.min 512 (state.stdin.size - pos))) = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead 8
      (Nat.min 512 (state.stdin.size - pos)).toUInt32 = some memoryAfter) :
    Spike3IngestionIovec (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos + Nat.min 512 (state.stdin.size - pos), stack := [] })) ∧
    evalInstrs (fuel + 2) (.call 0 :: rest)
      { state with stack := [.i32 8, .i32 1, .i32 0, .i32 0], stdinPos := pos }
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) =
    evalInstrs (fuel + 1) rest
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos + Nat.min 512 (state.stdin.size - pos), stack := [] }))
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) := by
  constructor
  · simpa [Spike3IngestionIovec, pushVal] using
      spike3_fdRead_at_nread_cell_preserves_ingestion_iovec state pos memoryAfterRead memoryAfter
        hciovec hwrite hnread
  · exact spike3_step_fdRead fuel rest state 8 pos memoryAfterRead memoryAfter
      hbefore hexit hpos hciovec hwrite hnread

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
    (hciovec : readCiovec state.memory 0 = some (0x100, 512))
    (hwrite : WasmMem.writeBytes state.memory 0x100 ByteArray.empty = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead nreadPtr.toNat 0 = some memoryAfter) :
    wasiHostCall ["fd_read", "fd_write", "proc_exit"] 0
      { state with stack := [.i32 nreadPtr, .i32 1, .i32 0, .i32 0], stdinPos := pos } =
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos, stack := [] }), .next) :=
  wasiHostCall_fd_read_single_eof state nreadPtr pos memoryAfterRead memoryAfter
    heof hciovec hwrite hnread

/-- EOF at Spike 3's fixed count cell preserves the same descriptor. -/
theorem spike3_fdRead_eof_at_nread_cell_preserves_ingestion_iovec
    (state : WasmMachineState) (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.writeBytes state.memory 0x100 ByteArray.empty = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead 8 0 = some memoryAfter) :
    Spike3IngestionIovec { state with memory := memoryAfter } := by
  exact wasiHostCall_fd_read_single_eof_preserves_iovec state 8 pos memoryAfterRead memoryAfter
    hciovec hwrite hnread spike3_nreadPtr_after_iovec

/-- EOF carries the descriptor into the production continuation just as the positive read does. -/
theorem spike3_step_fdRead_eof_at_nread_cell
    (fuel : Nat) (rest : List WasmInstr) (state : WasmMachineState)
    (pos : Nat) (memoryAfterRead memoryAfter : WasmMemory)
    (hbefore : state.trapped = false) (hexit : state.exitCode = none)
    (heof : state.stdin.size ≤ pos) (hciovec : Spike3IngestionIovec state)
    (hwrite : WasmMem.writeBytes state.memory 0x100 ByteArray.empty = some memoryAfterRead)
    (hnread : WasmMem.write32 memoryAfterRead 8 0 = some memoryAfter) :
    Spike3IngestionIovec
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos, stack := [] })) ∧
    evalInstrs (fuel + 2) (.call 0 :: rest)
      { state with stack := [.i32 8, .i32 1, .i32 0, .i32 0], stdinPos := pos }
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) =
    evalInstrs (fuel + 1) rest
      (pushVal (.i32 0) ({ state with memory := memoryAfter, stdinPos := pos, stack := [] }))
      (wasiHostCall ["fd_read", "fd_write", "proc_exit"]) := by
  constructor
  · simpa [Spike3IngestionIovec, pushVal] using
      spike3_fdRead_eof_at_nread_cell_preserves_ingestion_iovec state pos memoryAfterRead memoryAfter
        hciovec hwrite hnread
  · apply spike3_evalInstrs_step
    · simpa using hbefore
    · simpa using hexit
    · simpa [evalInstrMatch, evalLeafInstr] using
        (spike3_fdRead_single_iovec_eof state 8 pos memoryAfterRead memoryAfter
          heof hciovec hwrite hnread)

end Spikes.Spike3SortLines.Wasm
