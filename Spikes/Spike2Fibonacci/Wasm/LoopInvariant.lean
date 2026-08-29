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
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.Semantics
import Spikes.Spike2Fibonacci.Spec
import Spikes.Spike2Fibonacci.Wasm.Program

/-!
# PA15 (Wasm half): loop-invariant induction for `fibIterWasmInstructions`

`Spikes.Spike2Fibonacci.Wasm.Equivalence`'s `fib_iter_wasm_soundness` used to be discharged by
`native_decide` over `(List.range 91)` -- a trusted-oracle enumeration of 91 concrete inputs, each
one *executed* by the in-Lean Wasm interpreter and compared against `fibIter`. This file replaces
that with a genuine structural proof: a named loop invariant (`FibLocals`, carried by `loop_correct`),
established by the routine's four-instruction prologue and preserved by one pass through the
sixteen-instruction `loop` body, from which correctness for *every* iteration count follows by
induction on the iteration count.

This is the Wasm sibling of `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`, which did the same
for the x86-64 routine. The shape is the same in outline (per-instruction step lemmas, one generic
"one interpreter step" unfolding lemma, an invariant preserved by one loop pass, an induction on the
remaining iteration count) but the mechanics differ in two ways worth naming, because Spikes 3/4/5
will hit both when they copy this template:

1. **Structured control flow instead of addresses.** There is no `instructionAtRip` fetch obligation
   at all: `evalInstrs` walks a *list*, so "which instruction runs next" is syntactic. What replaces
   the fetch lemmas is the `block`/`loop`/`br` signal plumbing of Part 3 -- a `.br 1` raised inside
   the `loop` body is decremented to `.br 0` by `evalLoop`, then consumed by the enclosing `.block`
   and turned into `.next` (see `evalLoop_exit` / `evalInstrMatch_block_br0`).

2. **Fuel is a bound, not a budget.** `Gasm/Targets/Wasm/Semantics.lean`'s interpreter threads one
   `fuel : Nat` that decreases by exactly one per `evalInstrs`/`evalInstrMatch`/`evalLoop` entry and
   is *not* returned to the caller, so there is no "leftover fuel" to thread. Every lemma below is
   therefore stated in the `fuel + k` shape (`k` a literal): the caller's surplus rides along
   untouched, and `Nat` literal addition unfolds one `Nat.succ` at a time under `rw [show fuel + k =
   (fuel + (k-1)) + 1 from rfl]`, exactly as the x86 sibling does against `runProgramWithLoops`.

## The one asymmetry the Wasm routine has and the x86 one does not

`runFibIterWasm` calls `runWasmFunction fibIterWasmInstructions [.i64 n.toUInt64]` -- i.e. the
function's *declared* locals (`fibIterFunction.locals = [.i64, .i64, .i64]`) are not pre-materialized
by this simulation entry point; only the parameter is. `evalLeafInstr`'s `.local_set` therefore takes
its out-of-range *extension* path for the first write to each of locals 1, 2 and 3, and its in-range
`List.set` path thereafter. The consequence is that the machine reaches the top of the loop with a
locals list of length **3**, and leaves the first iteration with one of length **4**. `FibLocals`
below is exactly that two-shape disjunction, and `FibLocals.getD0`/`getD1`/`getD2`/`set3` are the
four (and only four) places the difference is actually observed -- every later step in the loop body
runs against a concrete length-4 list. Stating the invariant this way is what lets the induction be
uniform over all `m` instead of needing a separate "first iteration" lemma.
-/

namespace Spikes.Spike2Fibonacci.Wasm

open Gasm.Core
open Gasm.Targets.Wasm
open Spikes.Spike2Fibonacci

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/- REF: wasm-exec-instructions#instructions -/
/-- The host-call callback the Wasm interpreter threads through structured control flow. Named so
    the lemmas below can quantify over it uniformly; `fibIterWasmInstructions` contains no `.call`,
    so nothing here ever invokes it. -/
abbrev HostCall := Nat → WasmMachineState → WasmMachineState × ControlSignal

/- REF: wasm-exec-instructions#function-calls -/
/-- The specific host-call callback `runWasmFunction` installs (it has no imports to dispatch to).
    Kept as a `def` rather than written inline so `runWasmFunction_eq` below can be stated -- and
    proved by `rfl` -- without an anonymous lambda appearing in every intermediate goal. -/
def fibHost : HostCall := fun _ st => (st, .next)

/-
## Part 0: the state shape and the loop invariant's locals component
-/

/- REF: wasm-exec-runtime#configurations -/
/-- The machine states this proof ever visits: some `base` configuration (memory, stdin, events --
    none of which the pure-arithmetic Fibonacci routine reads or writes) with an explicit operand
    stack and locals list, definitely not trapped and definitely not exited. Writing every
    intermediate state in this one shape is what makes the per-instruction lemmas of Part 2 close by
    `rfl`: each interpreter step is a record update of a record update, which collapses
    definitionally, so the untouched fields never have to be tracked by hand. -/
def FibState (base : WasmMachineState) (stk locs : List WasmVal) : WasmMachineState :=
  { base with stack := stk, locals := locs, trapped := false, exitCode := none }

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **The locals half of the loop invariant.** At the top of the loop, local 0 holds the remaining
    iteration count, local 1 holds `fib k` and local 2 holds `fib (k+1)`; local 3 (the loop body's
    scratch temporary) either does not exist yet -- on the first entry, see this file's header --
    or holds whatever the previous iteration left there, which no later step reads before
    overwriting. The disjunction is the whole content of that "either"; see `set3` for why both
    branches converge after the body's first write. -/
def FibLocals (mv av bv : UInt64) (l : List WasmVal) : Prop :=
  l = [.i64 mv, .i64 av, .i64 bv] ∨ ∃ t : UInt64, l = [.i64 mv, .i64 av, .i64 bv, .i64 t]

/- REF: wasm-exec-instructions#variable-instructions -/
/-- `local.get 0` reads the remaining iteration count, under either locals shape. -/
theorem FibLocals.getD0 {mv av bv : UInt64} {l} (h : FibLocals mv av bv l) :
    l.getD 0 (.i32 0) = .i64 mv := by
  rcases h with h | ⟨t, h⟩ <;> subst h <;> rfl

/- REF: wasm-exec-instructions#variable-instructions -/
/-- `local.get 1` reads `fib k`, under either locals shape. -/
theorem FibLocals.getD1 {mv av bv : UInt64} {l} (h : FibLocals mv av bv l) :
    l.getD 1 (.i32 0) = .i64 av := by
  rcases h with h | ⟨t, h⟩ <;> subst h <;> rfl

/- REF: wasm-exec-instructions#variable-instructions -/
/-- `local.get 2` reads `fib (k+1)`, under either locals shape. -/
theorem FibLocals.getD2 {mv av bv : UInt64} {l} (h : FibLocals mv av bv l) :
    l.getD 2 (.i32 0) = .i64 bv := by
  rcases h with h | ⟨t, h⟩ <;> subst h <;> rfl

/- REF: wasm-exec-instructions#variable-instructions -/
/-- **Where the two locals shapes converge.** `local.set 3` writes the same four-element list either
    way: from the length-3 shape `evalLeafInstr` takes its extension path (`l ++ replicate 0 _ ++
    [v]`), from the length-4 shape its in-range `List.set 3 v` path. After this single step the loop
    body is running against a concrete length-4 list, which is why no other lemma in this file has to
    case-split on the shape. -/
theorem FibLocals.set3 {mv av bv : UInt64} {l} (h : FibLocals mv av bv l) (v : WasmVal) :
    (if 3 < l.length then l.set 3 v
     else l ++ List.replicate (3 - l.length) (.i32 0) ++ [v])
      = [.i64 mv, .i64 av, .i64 bv, v] := by
  rcases h with h | ⟨t, h⟩ <;> subst h <;> rfl

/-
## Part 1: generic one-instruction unfolding lemmas

The two workhorses. Everything in Part 2 is an instance of one of them; nothing below ever reduces
through more than one interpreter step at a time, which is what keeps the whole file inside
`maxRecDepth` (the sibling x86 proof records the same finding for the same reason).
-/

/- REF: wasm-exec-instructions#expressions -/
/-- An exhausted instruction list returns the state unchanged with a `.next` signal, given at least
    one unit of fuel to notice it is empty. -/
theorem evalInstrs_nil (fuel : Nat) (st : WasmMachineState) (h : HostCall) :
    evalInstrs (fuel + 1) [] st h = .ok (st, .next) := rfl

/- REF: wasm-exec-instructions#expressions -/
/-- **One `evalInstrs` step, `.next` case.** Costs two units of the caller's fuel: one for the
    `evalInstrs` entry that dispatches the head instruction, one for the `evalInstrMatch` entry that
    evaluates it. The `hg`/`he` premises are the interpreter's trap/exit short-circuit guard, which
    for a `FibState` are both `rfl`. -/
theorem evalInstrs_step (fuel : Nat) (i : WasmInstr) (rest : List WasmInstr)
    (st st' : WasmMachineState) (h : HostCall)
    (hg : st.trapped = false) (he : st.exitCode = none)
    (hstep : evalInstrMatch (fuel + 1) i st h = .ok (st', .next)) :
    evalInstrs (fuel + 2) (i :: rest) st h = evalInstrs (fuel + 1) rest st' h := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  simp only [evalInstrs, hg, he, Option.isSome_none, Bool.or_self, Bool.false_eq_true, if_false,
    hstep]

/- REF: wasm-exec-instructions#control-instructions -/
/-- **One `evalInstrs` step, branch case.** An instruction that raises `.br d` abandons the rest of
    the sequence and propagates the signal to the enclosing `block`/`loop`. -/
theorem evalInstrs_step_br (fuel : Nat) (i : WasmInstr) (rest : List WasmInstr)
    (st st' : WasmMachineState) (d : Nat) (h : HostCall)
    (hg : st.trapped = false) (he : st.exitCode = none)
    (hstep : evalInstrMatch (fuel + 1) i st h = .ok (st', .br d)) :
    evalInstrs (fuel + 2) (i :: rest) st h = .ok (st', .br d) := by
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
  simp only [evalInstrs, hg, he, Option.isSome_none, Bool.or_self, Bool.false_eq_true, if_false,
    hstep]

/-
## Part 2: per-instruction steps over `FibState`

One lemma per instruction form the Fibonacci routine actually uses. Each is a single application of
Part 1 whose `evalInstrMatch` premise closes by `rfl`, because `FibState`'s explicit shape makes
`evalLeafInstr`'s stack/locals manipulation a closed term.
-/

/- REF: wasm-exec-instructions#variable-instructions -/
theorem step_local_get (fuel idx : Nat) (rest : List WasmInstr) (base : WasmMachineState)
    (stk locs : List WasmVal) (v : WasmVal) (h : HostCall)
    (hv : locs.getD idx (.i32 0) = v) :
    evalInstrs (fuel + 2) (.local_get idx :: rest) (FibState base stk locs) h
      = evalInstrs (fuel + 1) rest (FibState base (v :: stk) locs) h := by
  subst hv
  exact evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#variable-instructions -/
/-- `hset` is deliberately left as the interpreter's own in-range/extension `if`, so a call site
    discharges it either by `rfl` (concrete list) or by `FibLocals.set3` (invariant-carried shape)
    without this lemma having to know which. -/
theorem step_local_set (fuel idx : Nat) (rest : List WasmInstr) (base : WasmMachineState)
    (stk locs locs' : List WasmVal) (v : WasmVal) (h : HostCall)
    (hset : (if idx < locs.length then locs.set idx v
             else locs ++ List.replicate (idx - locs.length) (.i32 0) ++ [v]) = locs') :
    evalInstrs (fuel + 2) (.local_set idx :: rest) (FibState base (v :: stk) locs) h
      = evalInstrs (fuel + 1) rest (FibState base stk locs') h := by
  subst hset
  exact evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#numeric-instructions -/
theorem step_i64_const (fuel : Nat) (c : UInt64) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall) :
    evalInstrs (fuel + 2) (.i64_const c :: rest) (FibState base stk locs) h
      = evalInstrs (fuel + 1) rest (FibState base (.i64 c :: stk) locs) h :=
  evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#numeric-instructions -/
theorem step_i64_add (fuel : Nat) (v1 v2 : UInt64) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall) :
    evalInstrs (fuel + 2) (.i64_add :: rest) (FibState base (.i64 v2 :: .i64 v1 :: stk) locs) h
      = evalInstrs (fuel + 1) rest (FibState base (.i64 (v1 + v2) :: stk) locs) h :=
  evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#numeric-instructions -/
theorem step_i64_sub (fuel : Nat) (v1 v2 : UInt64) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall) :
    evalInstrs (fuel + 2) (.i64_sub :: rest) (FibState base (.i64 v2 :: .i64 v1 :: stk) locs) h
      = evalInstrs (fuel + 1) rest (FibState base (.i64 (v1 - v2) :: stk) locs) h :=
  evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#numeric-instructions -/
theorem step_i64_eqz (fuel : Nat) (v : UInt64) (c : UInt32) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall)
    (hc : (if v == 0 then (1 : UInt32) else 0) = c) :
    evalInstrs (fuel + 2) (.i64_eqz :: rest) (FibState base (.i64 v :: stk) locs) h
      = evalInstrs (fuel + 1) rest (FibState base (.i32 c :: stk) locs) h := by
  subst hc
  exact evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#control-instructions -/
/-- `br_if` with a false condition falls through. Stated at the literal `0` the routine's own
    `i64.eqz` produces (rather than for a symbolic condition with a `≠ 0` side condition) so the
    premise is discharged by kernel reduction, not by a `Bool` case split. -/
theorem step_br_if_zero (fuel depth : Nat) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall) :
    evalInstrs (fuel + 2) (.br_if depth :: rest) (FibState base (.i32 0 :: stk) locs) h
      = evalInstrs (fuel + 1) rest (FibState base stk locs) h :=
  evalInstrs_step fuel _ rest _ _ h rfl rfl rfl

/- REF: wasm-exec-instructions#control-instructions -/
/-- `br_if` with a true condition raises `.br depth`, abandoning the rest of the sequence. -/
theorem step_br_if_one (fuel depth : Nat) (rest : List WasmInstr)
    (base : WasmMachineState) (stk locs : List WasmVal) (h : HostCall) :
    evalInstrs (fuel + 2) (.br_if depth :: rest) (FibState base (.i32 1 :: stk) locs) h
      = .ok (FibState base stk locs, .br depth) :=
  evalInstrs_step_br fuel _ rest _ _ depth h rfl rfl rfl

/- REF: wasm-exec-instructions#control-instructions -/
theorem step_br (fuel depth : Nat) (rest : List WasmInstr) (st : WasmMachineState) (h : HostCall)
    (hg : st.trapped = false) (he : st.exitCode = none) :
    evalInstrs (fuel + 2) (.br depth :: rest) st h = .ok (st, .br depth) :=
  evalInstrs_step_br fuel _ rest _ _ depth h hg he rfl

/-
## Part 3: structured control flow

The `block`/`loop`/`br`-depth plumbing that replaces the x86 proof's jump-displacement arithmetic.
-/

/- REF: wasm-exec-instructions#blocks -/
theorem evalInstrMatch_loop (fuel : Nat) (bt : BlockType) (body : List WasmInstr)
    (st : WasmMachineState) (h : HostCall) :
    evalInstrMatch (fuel + 1) (.loop bt body) st h = evalLoop fuel body st h := rfl

/- REF: wasm-exec-instructions#blocks -/
/-- A `block` whose body branches to depth 0 exits the block normally. -/
theorem evalInstrMatch_block_br0 (fuel : Nat) (bt : BlockType) (body : List WasmInstr)
    (st st' : WasmMachineState) (h : HostCall)
    (hb : evalInstrs fuel body st h = .ok (st', .br 0)) :
    evalInstrMatch (fuel + 1) (.block bt body) st h = .ok (st', .next) := by
  simp only [evalInstrMatch, hb, finishBlockResult]

/- REF: wasm-exec-instructions#blocks -/
/-- A `block` whose body runs off the end likewise exits normally. -/
theorem evalInstrMatch_block_next (fuel : Nat) (bt : BlockType) (body : List WasmInstr)
    (st st' : WasmMachineState) (h : HostCall)
    (hb : evalInstrs fuel body st h = .ok (st', .next)) :
    evalInstrMatch (fuel + 1) (.block bt body) st h = .ok (st', .next) := by
  simp only [evalInstrMatch, hb, finishBlockResult]

/- REF: wasm-exec-instructions#blocks -/
/-- **Loop re-entry.** A `.br 0` out of the body re-enters the same `loop` with one unit less fuel.
    This is the single place the interpreter's non-structural recursion lives, and the reason
    `evalLoop` needs fuel at all. -/
theorem evalLoop_iter (fuel : Nat) (body : List WasmInstr) (st st' : WasmMachineState)
    (h : HostCall) (hb : evalInstrs fuel body st h = .ok (st', .br 0)) :
    evalLoop (fuel + 1) body st h = evalLoop fuel body st' h := by
  simp only [evalLoop, hb]

/- REF: wasm-exec-instructions#blocks -/
/-- **Loop exit.** A branch past the loop's own label (`.br (d+1)`) leaves the loop, decremented. -/
theorem evalLoop_exit (fuel : Nat) (body : List WasmInstr) (st st' : WasmMachineState) (d : Nat)
    (h : HostCall) (hb : evalInstrs fuel body st h = .ok (st', .br (d + 1))) :
    evalLoop (fuel + 1) body st h = .ok (st', .br d) := by
  simp only [evalLoop, hb]

/-
## Part 4: one pass through the loop body
-/

/- REF: docs/TARGETS/WASM.md#2-structured-ast-control-flow -/
/-- The sixteen instructions inside `fibIterWasmInstructions`'s `loop`, named so the lemmas below
    can be stated about it. `fibIterWasmInstructions_eq` (`rfl`) is what ties this name back to the
    program actually emitted, so a divergence between the two fails to typecheck rather than
    silently proving something about a different loop. -/
def fibWasmLoopBody : List WasmInstr :=
  [ .local_get 0, .i64_eqz, .br_if 1,
    .local_get 1, .local_get 2, .i64_add, .local_set 3,
    .local_get 2, .local_set 1,
    .local_get 3, .local_set 2,
    .local_get 0, .i64_const 1, .i64_sub, .local_set 0,
    .br 0 ]

/- REF: docs/TARGETS/WASM.md#2-structured-ast-control-flow -/
/-- The emitted routine, decomposed into the prologue, the `block`/`loop` nest whose body is
    `fibWasmLoopBody`, and the epilogue that reads the result out of local 1. -/
theorem fibIterWasmInstructions_eq :
    fibIterWasmInstructions =
      [ .i64_const 0, .local_set 1, .i64_const 1, .local_set 2,
        .block .empty [.loop .empty fibWasmLoopBody],
        .local_get 1 ] := rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- `(m + 1).toUInt64` is never zero below the `UInt64` wraparound point -- what the loop's
    `i64.eqz`/`br_if` test needs in order not to exit while iterations remain. -/
theorem succ_toUInt64_ne_zero (m : Nat) (hm : m + 1 < 2 ^ 64) : (m + 1).toUInt64 ≠ 0 := by
  simp only [ne_eq, ← UInt64.toNat_inj]
  simp [Nat.toUInt64]
  omega

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **The induction step, as a single pass through the body.** With a nonzero counter the `br_if`
    is not taken and the body runs to its trailing `br 0`, advancing the locals from
    `(mv, av, bv, _)` to `(mv - 1, bv, av + bv, av + bv)` -- the Fibonacci pair shift. Seventeen
    units of fuel: two per instruction dispatched, sharing one between neighbours, plus the final
    `br`. Proved by chaining Part 2's lemmas, never by executing the interpreter. -/
theorem loopBody_iteration (fuel : Nat) (mv av bv : UInt64) (base : WasmMachineState)
    (locs : List WasmVal) (h : HostCall)
    (hs : FibLocals mv av bv locs) (hmv : mv ≠ 0) :
    evalInstrs (fuel + 17) fibWasmLoopBody (FibState base [] locs) h
      = .ok (FibState base [] [.i64 (mv - 1), .i64 bv, .i64 (av + bv), .i64 (av + bv)], .br 0) := by
  have hc0 : (if mv == 0 then (1 : UInt32) else 0) = 0 := by simp [hmv]
  rw [fibWasmLoopBody, show fuel + 17 = (fuel + 15) + 2 from rfl]
  rw [step_local_get (fuel + 15) 0 _ base [] locs (.i64 mv) h hs.getD0]
  rw [show fuel + 16 = (fuel + 14) + 2 from rfl]
  rw [step_i64_eqz (fuel + 14) mv 0 _ base [] locs h hc0]
  rw [show fuel + 15 = (fuel + 13) + 2 from rfl]
  rw [step_br_if_zero (fuel + 13) 1 _ base [] locs h]
  rw [show fuel + 14 = (fuel + 12) + 2 from rfl]
  rw [step_local_get (fuel + 12) 1 _ base [] locs (.i64 av) h hs.getD1]
  rw [show fuel + 13 = (fuel + 11) + 2 from rfl]
  rw [step_local_get (fuel + 11) 2 _ base _ locs (.i64 bv) h hs.getD2]
  rw [show fuel + 12 = (fuel + 10) + 2 from rfl]
  rw [step_i64_add (fuel + 10) av bv _ base [] locs h]
  rw [show fuel + 11 = (fuel + 9) + 2 from rfl]
  rw [step_local_set (fuel + 9) 3 _ base [] locs
    [.i64 mv, .i64 av, .i64 bv, .i64 (av + bv)] (.i64 (av + bv)) h (hs.set3 _)]
  rw [show fuel + 10 = (fuel + 8) + 2 from rfl]
  rw [step_local_get (fuel + 8) 2 _ base [] _ (.i64 bv) h rfl]
  rw [show fuel + 9 = (fuel + 7) + 2 from rfl]
  rw [step_local_set (fuel + 7) 1 _ base [] _
    [.i64 mv, .i64 bv, .i64 bv, .i64 (av + bv)] (.i64 bv) h rfl]
  rw [show fuel + 8 = (fuel + 6) + 2 from rfl]
  rw [step_local_get (fuel + 6) 3 _ base [] _ (.i64 (av + bv)) h rfl]
  rw [show fuel + 7 = (fuel + 5) + 2 from rfl]
  rw [step_local_set (fuel + 5) 2 _ base [] _
    [.i64 mv, .i64 bv, .i64 (av + bv), .i64 (av + bv)] (.i64 (av + bv)) h rfl]
  rw [show fuel + 6 = (fuel + 4) + 2 from rfl]
  rw [step_local_get (fuel + 4) 0 _ base [] _ (.i64 mv) h rfl]
  rw [show fuel + 5 = (fuel + 3) + 2 from rfl]
  rw [step_i64_const (fuel + 3) 1 _ base _ _ h]
  rw [show fuel + 4 = (fuel + 2) + 2 from rfl]
  rw [step_i64_sub (fuel + 2) mv 1 _ base [] _ h]
  rw [show fuel + 3 = (fuel + 1) + 2 from rfl]
  rw [step_local_set (fuel + 1) 0 _ base [] _
    [.i64 (mv - 1), .i64 bv, .i64 (av + bv), .i64 (av + bv)] (.i64 (mv - 1)) h rfl]
  exact step_br fuel 0 [] _ h rfl rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **The base case, as a single pass through the body.** With a zero counter the body's first
    three instructions raise `.br 1`, leaving the state -- and in particular local 1, which holds
    the answer -- untouched. -/
theorem loopBody_exit (fuel : Nat) (av bv : UInt64) (base : WasmMachineState)
    (locs : List WasmVal) (h : HostCall) (hs : FibLocals 0 av bv locs) :
    evalInstrs (fuel + 4) fibWasmLoopBody (FibState base [] locs) h
      = .ok (FibState base [] locs, .br 1) := by
  rw [fibWasmLoopBody, show fuel + 4 = (fuel + 2) + 2 from rfl]
  rw [step_local_get (fuel + 2) 0 _ base [] locs (.i64 0) h hs.getD0]
  rw [show fuel + 3 = (fuel + 1) + 2 from rfl]
  rw [step_i64_eqz (fuel + 1) 0 1 _ base [] locs h (by decide)]
  exact step_br_if_one fuel 1 _ base [] locs h

/-
## Part 5: the induction
-/

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **The main induction.** From the invariant at `k` iterations done with `m` remaining, and enough
    fuel to finish (`m + 17 ≤ fuel`: one `evalLoop` unit per remaining iteration, plus the seventeen
    the last body pass needs), the `loop` exits with local 1 holding `fib (k + m)`. Induction on the
    remaining iteration count `m`, using `loopBody_exit` for the base case and `loopBody_iteration`
    for the step -- not `native_decide` on any concrete input.

    `hm : m < 2 ^ 64` is the one structural side condition: it feeds `succ_toUInt64_ne_zero` (the
    counter must not wrap to zero early) and the `(m + 1).toUInt64 - 1 = m.toUInt64` decrement. Note
    it is *not* a no-overflow condition on the Fibonacci values themselves -- both sides of the
    equation wrap `UInt64` identically, because `Nat.toUInt64` distributes over `+` (`hadd` below),
    so the result holds regardless of how far past `fib 93` the accumulator has wrapped. -/
theorem loop_correct (base : WasmMachineState) (h : HostCall) : ∀ (m k fuel : Nat)
    (locs : List WasmVal),
    FibLocals m.toUInt64 (fibNat k).toUInt64 (fibNat (k + 1)).toUInt64 locs →
    m < 2 ^ 64 → m + 17 ≤ fuel →
    ∃ locs', evalLoop fuel fibWasmLoopBody (FibState base [] locs) h
        = .ok (FibState base [] locs', .br 0) ∧
      FibLocals 0 (fibNat (k + m)).toUInt64 (fibNat (k + m + 1)).toUInt64 locs' := by
  intro m
  induction m with
  | zero =>
    intro k fuel locs hs hm hfuel
    have hz : (0 : Nat).toUInt64 = 0 := rfl
    rw [hz] at hs
    refine ⟨locs, ?_, ?_⟩
    · rw [show fuel = (fuel - 5 + 4) + 1 from by omega]
      exact evalLoop_exit (fuel - 5 + 4) _ _ _ 0 h
        (loopBody_exit (fuel - 5) _ _ base locs h hs)
    · rw [show k + 0 = k from rfl]; exact hs
  | succ m ih =>
    intro k fuel locs hs hm hfuel
    have hne : (m + 1).toUInt64 ≠ 0 := succ_toUInt64_ne_zero m (by omega)
    have hsub : (m + 1).toUInt64 - 1 = m.toUInt64 := by simp [Nat.toUInt64]
    have hadd : (fibNat k).toUInt64 + (fibNat (k + 1)).toUInt64 = (fibNat (k + 2)).toUInt64 := by
      rw [show fibNat (k + 2) = fibNat k + fibNat (k + 1) from by
        rw [show fibNat (k + 2) = fibNat (k + 1) + fibNat k from rfl, Nat.add_comm]]
      simp [Nat.toUInt64]
    have hiter := loopBody_iteration (fuel - 18) (m + 1).toUInt64 (fibNat k).toUInt64
      (fibNat (k + 1)).toUInt64 base locs h hs hne
    rw [hsub, hadd] at hiter
    have hstep : evalLoop fuel fibWasmLoopBody (FibState base [] locs) h
        = evalLoop (fuel - 18 + 17) fibWasmLoopBody
            (FibState base [] [.i64 m.toUInt64, .i64 (fibNat (k + 1)).toUInt64,
              .i64 (fibNat (k + 2)).toUInt64, .i64 (fibNat (k + 2)).toUInt64]) h := by
      rw [show fuel = (fuel - 18 + 17) + 1 from by omega]
      exact evalLoop_iter (fuel - 18 + 17) _ _ _ h hiter
    have hs' : FibLocals m.toUInt64 (fibNat (k + 1)).toUInt64 (fibNat (k + 1 + 1)).toUInt64
        [.i64 m.toUInt64, .i64 (fibNat (k + 1)).toUInt64, .i64 (fibNat (k + 2)).toUInt64,
          .i64 (fibNat (k + 2)).toUInt64] :=
      Or.inr ⟨(fibNat (k + 2)).toUInt64, rfl⟩
    obtain ⟨locs', hrun, hshape⟩ :=
      ih (k + 1) (fuel - 18 + 17) _ hs' (by omega) (by omega)
    refine ⟨locs', ?_, ?_⟩
    · rw [hstep, hrun]
    · rw [show k + (m + 1) = k + 1 + m from by omega]
      exact hshape

/-
## Part 6: prologue, epilogue, and the whole routine
-/

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **The prologue establishes the invariant, and the epilogue reads the answer out.** The four
    prologue instructions install `local 1 = 0 = fib 0` and `local 2 = 1 = fib 1` (extending the
    locals list from length 1 to length 3 as they go -- see this file's header), `loop_correct`
    carries them to `fib n`/`fib (n+1)`, and the trailing `local.get 1` pushes the result. -/
theorem prologue_and_loop (n g : Nat) (base : WasmMachineState) (hn : n < 2 ^ 64) (hng : n ≤ g) :
    ∃ locs', evalInstrs (g + 25) fibIterWasmInstructions
        (FibState base [] [.i64 n.toUInt64]) fibHost
      = .ok (FibState base [.i64 (fibNat n).toUInt64] locs', .next) := by
  obtain ⟨locs', hrun, hshape⟩ :=
    loop_correct base fibHost n 0 (g + 17)
      [.i64 n.toUInt64, .i64 (0 : UInt64), .i64 (1 : UInt64)] (Or.inl rfl) hn (by omega)
  refine ⟨locs', ?_⟩
  rw [fibIterWasmInstructions_eq, show g + 25 = (g + 23) + 2 from rfl]
  rw [step_i64_const (g + 23) 0 _ base [] _ fibHost]
  rw [show g + 24 = (g + 22) + 2 from rfl]
  rw [step_local_set (g + 22) 1 _ base [] _ [.i64 n.toUInt64, .i64 (0 : UInt64)]
    (.i64 (0 : UInt64)) fibHost rfl]
  rw [show g + 23 = (g + 21) + 2 from rfl]
  rw [step_i64_const (g + 21) 1 _ base [] _ fibHost]
  rw [show g + 22 = (g + 20) + 2 from rfl]
  rw [step_local_set (g + 20) 2 _ base [] _
    [.i64 n.toUInt64, .i64 (0 : UInt64), .i64 (1 : UInt64)] (.i64 (1 : UInt64)) fibHost rfl]
  have hblock : evalInstrMatch (g + 20) (.block .empty [.loop .empty fibWasmLoopBody])
      (FibState base [] [.i64 n.toUInt64, .i64 (0 : UInt64), .i64 (1 : UInt64)]) fibHost
        = .ok (FibState base [] locs', .next) := by
    refine evalInstrMatch_block_br0 (g + 19) _ _ _ _ fibHost ?_
    refine evalInstrs_step_br (g + 17) _ [] _ _ 0 fibHost rfl rfl ?_
    rw [evalInstrMatch_loop]
    exact hrun
  rw [show g + 21 = (g + 19) + 2 from rfl]
  rw [evalInstrs_step (g + 19) _ [WasmInstr.local_get 1] _ _ fibHost rfl rfl hblock]
  rw [show g + 20 = (g + 18) + 2 from rfl]
  rw [step_local_get (g + 18) 1 _ base [] locs' (.i64 (fibNat (0 + n)).toUInt64) fibHost
    hshape.getD1]
  rw [show (0 : Nat) + n = n from by omega]
  exact evalInstrs_nil (g + 18) _ fibHost

/- REF: wasm-exec-instructions#function-calls -/
/-- `runWasmFunction` in the `FibState` shape the lemmas above are stated in: its initial
    configuration has an empty stack, is not trapped, and has not exited, so the outer `evalInstr`'s
    trap/exit short-circuit guard is `false` by kernel reduction. -/
theorem runWasmFunction_eq (body : List WasmInstr) (locs : List WasmVal) (fuel : Nat) :
    runWasmFunction body locs fuel
      = (collapseWasmRunResult (evalInstrMatch fuel (.block .empty body)
          (FibState { locals := locs } [] locs) fibHost)).1 := rfl

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- **PA15 (Wasm).** The WebAssembly routine leaves exactly `fib n` on the operand stack, for every
    `n` the supplied fuel can complete within (`n + 26 ≤ fuel`: one interpreter unit per loop
    iteration plus the fixed cost of the prologue, the `block`/`loop` entry, the last body pass and
    the epilogue). Stated for arbitrary `fuel` so a caller needing a larger `n` than the interpreter
    default admits can simply pass more. -/
theorem fibIterWasm_run (n fuel : Nat) (hn : n < 2 ^ 64) (hfuel : n + 26 ≤ fuel) :
    (runWasmFunction fibIterWasmInstructions [.i64 n.toUInt64] fuel).stack
      = [.i64 (fibNat n).toUInt64] := by
  obtain ⟨locs', hb⟩ := prologue_and_loop n (fuel - 26)
    { locals := [WasmVal.i64 n.toUInt64] } hn (by omega)
  rw [runWasmFunction_eq, show fuel = ((fuel - 26) + 25) + 1 from by omega,
    evalInstrMatch_block_next ((fuel - 26) + 25) _ _ _ _ fibHost hb]
  rfl

end Spikes.Spike2Fibonacci.Wasm
