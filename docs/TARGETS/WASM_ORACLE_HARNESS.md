<!--
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
-->

# WebAssembly Differential-Test Oracle & Harness

This document is **first-party design prose that `gasm` owns the copyright to**. It is NOT
vendored specification text, and none of its content should be read as describing anything the
W3C WebAssembly Core Specification mandates. It exists because `Gasm/Targets/Wasm/HostOracle.lean`
and `Gasm/Targets/Wasm/SemanticsFuzzer.lean` implement Gasm's own differential-fuzzing test
infrastructure for the WebAssembly target — machinery that compares the Lean instruction-semantics
model (`Gasm.Targets.Wasm.Semantics`) against a real host WebAssembly engine, one fuzzed state at a
time — and that infrastructure has no counterpart anywhere in the W3C spec to cite. Per
`docs/REVIEW.md` Law 1, every Lean declaration needs a `REF:` citation; per Law 4, that citation
must not point at a self-authored approximation of an external standard. This document is the
honest resolution of that tension for exactly the declarations named below: it is the genuine
design source for our own harness, cited as itself rather than dressed up as spec-derived.

One WAT (WebAssembly Text format) pretty-printing convention — indentation width — is documented
here for the same reason: it is a formatting choice this project made, not something the spec text
prescribes.

---

## 1. Purpose and Scope

The differential fuzzer's job is to catch divergence between `Gasm.Targets.Wasm.Semantics`'s
single-step interpreter (`stepWasm` / `evalInstr` / `evalInstrs` / `evalLoop`) and what a real
engine actually does. For each instruction or structured control-flow shape under test, the
harness:

1. Generates one or more fuzzed initial machine states (operand stack, locals, memory).
2. Runs the Lean model on that state directly (`stepWasm`).
3. Synthesizes a minimal, standalone `.wasm` module that reproduces the same starting state and
   instruction, and runs it on a real host engine (`references/wasm/` documents the spec that
   engine is expected to implement; this harness does not re-derive that spec, it only exercises
   it as a black box).
4. Compares the two outcomes — result value(s), or a genuine trap — and reports a mismatch as a
   failure.

Everything in this document is the "how" of that loop: how the host process is spawned and
policed, what its result types mean and why they are shaped the way they are, how a case is
represented and generated, and how the mandatory sanity controls keep the whole loop honest.

---

## 2. Host Oracle Process Model

`runWasmHostExecution` (`Gasm/Targets/Wasm/HostOracle.lean`) is the only place this codebase spawns
a host WebAssembly engine. It takes an already-built `WasmModule`, serializes it to a real `.wasm`
binary via the target's own encoder (`emitWasmBinary`), and drives a `node` child process through
it:

- **Temp file naming.** The scratch `.wasm` file is named from the current process id
  (`IO.Process.getPID`) and a monotonic timestamp (`IO.monoMsNow`) —
  `.tmp_wasm_fuzzer_{pid}_{nowMs}.wasm` — so concurrent fuzzer invocations (e.g. two test runs, or
  a leaf-instruction pass racing a control-flow pass) never contend for the same path. The file is
  always removed before returning, on every exit path, including failure.
- **The generated script** first validates the module with `new WebAssembly.Module(...)` in its
  own `try`/`catch`, deliberately separate from instantiation and execution. This lets the harness
  tell a module V8 rejects as statically invalid apart from a module that runs and genuinely traps
  at runtime — see §3 for why that distinction is load-bearing. On success it instantiates the
  module, calls the single exported `test_fn`, and prints a tagged line to stdout: `I32:<value>`,
  `I64:<value>`, `VOID` (a function declaring zero results), `TRAP:<message>` (a runtime trap), or
  `INVALID:<message>` (module rejected at validation).
- **Timeout and hang policy.** Rather than blocking on `child.wait` indefinitely, the harness polls
  `child.tryWait` every 50ms up to a caller-supplied `timeoutMs` (default 10 seconds). If the
  process has not exited by the deadline it is killed, reaped, and its buffered stdout/stderr are
  drained (not merely ignored) so the pipe handles can be released cleanly. A hang is reported as
  `OracleFailure.processError`, never silently swallowed — a genuinely infinite loop in the
  interpreter under test must fail the vector loudly.
- **Output parsing is exhaustive and fail-closed.** Every stdout shape the script can print is
  matched explicitly (`I32:`, `I64:`, `TRAP:`, `VOID`, `INVALID:`); anything else — unparseable
  digits, unrecognized text, a non-zero node exit code, or a Lean-side `IO` exception while
  spawning — becomes `OracleFailure.processError` rather than defaulting to any `WasmOracleResult`
  constructor. There is no code path in this function that can turn "the harness could not get a
  trustworthy answer" into what looks like a real result.

---

## 3. Oracle Result Types

Three small types, all in `HostOracle.lean`, exist to make it structurally impossible for a caller
to mistake "the oracle malfunctioned" for "the oracle answered":

- **`WasmRunOutcome`** is the successful outcome of running a *validated* module: either it
  produced a definite result (`.ran (vs : List WasmVal)`) or it genuinely trapped at runtime
  (`.trapped (msg : String)`). Both are legitimate, comparable outcomes. There is deliberately no
  constructor here for "didn't run" or "output was unparseable" — those are not real outcomes of
  running the module, they are oracle malfunctions, and belong to a different type entirely.
- **`OracleFailure`** is that different type: a failure of the harness itself, as distinct from any
  real outcome of the module under test. `.invalidModule (msg : String)` means the synthesized
  module never validated — almost always a bug in the *test case* construction, not the interpreter
  under test (see §6's negative control for the other half of that story). `.processError
  (msg : String)` covers every harness-level failure described in §2: spawn failure, non-zero exit,
  hang/timeout, or unparseable output.
- **`WasmOracleResult`** is `Except OracleFailure WasmRunOutcome` — an `Except`, not an `Option` or
  a bare `WasmRunOutcome` with a sentinel value, specifically so every caller is forced by the type
  checker to handle both arms explicitly. There is no `Inhabited`-style default that could let a
  failure silently read as an accepted result.
- **`describeOracleResult`** renders any `WasmOracleResult` as a human-readable diagnostic string
  (`"ran -> ..."`, `"trapped -> ..."`, `"invalidModule -> ..."`, `"processError -> ..."`) without
  requiring `Except` itself to carry a `Repr` instance. It backs every error message the mandatory
  controls and the per-case verifier print when something goes wrong.

---

## 4. Stack Reconstruction for Synthesized Test Modules

A fuzzed `WasmMachineState` in the Lean model can start with a non-empty operand stack, but a
synthesized standalone `.wasm` module has no way to be handed a pre-populated stack directly — it
starts execution with an empty one, like any real function. `stackSetupInstrs` bridges that gap: it
takes the captured stack (top-of-stack first, matching the model's own LIFO convention) and emits
the `i32.const` / `i64.const` instructions that, run in order, reconstruct the same stack from
empty. Because the model's stack is top-first, the values are pushed bottom-up — the list is
reversed before being mapped to constant-push instructions — so the constant sequence, once run,
leaves the stack in exactly the state the fuzzer generated. The synthesized module's test function
body is this setup sequence followed by the instruction under test, so the host engine sees the
same starting stack the Lean model stepped from.

---

## 5. Differential Case Result Type

**`WasmInstructionDiffResult`** (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`) is the outcome of
comparing one case (a leaf instruction or a structured control-flow construct, see
`WasmDiffCase` in `SemanticsFuzzer.lean`) against the host oracle across all of its fuzzed vectors:
`passed`, the case's display `mnemonic`, `totalTested` and `failedCount` vector counts, an optional
`errorMessage` for the first mismatch encountered, and a `skipped` flag. `skipped` is deliberately
distinct from `passed`: it marks the zero-vector case (no fuzzable host states, whether because
`canFuzzWasmRuntime` excludes the instruction or state generation otherwise yielded nothing), and a
skip means "verified nothing", not "verified and matched". A zero-vector case silently reporting
`passed := true` would be exactly the kind of mock-verification facade `docs/REVIEW.md` Law 8 and
Law 13 (and `TCB.md` T11-b) prohibit — see §7's vacuity handling for how this flag is kept out of
the pass count.

---

## 6. Mandatory Oracle Sanity Controls

Before any fuzz vector is allowed to count toward a passing suite, `runMandatoryOracleControls`
runs three fixed checks against the host oracle and **aborts the entire fuzz session** (via
`IO.userError`, uncaught) if any of them fails. An oracle that cannot be trusted must not be
allowed to silently report a green suite:

1. **Positive control.** `i32.const 42` must run and return exactly `42`. This is what fails first
   if `node` is missing from `PATH` entirely — the spawn fails, `runWasmHostExecution` reports
   `OracleFailure.processError`, which can never equal the expected `WasmRunOutcome.ran [.i32 42]`.
2. **Negative control.** A module declaring one `i32` result whose body is `nop` (which produces
   none) must be rejected as `OracleFailure.invalidModule`. This pins exactly the "fallthrough
   arity" class of bug that, before this harness's own review cycle, let several structured
   control-flow cases silently report PASS: a synthesized module with a declared result type that
   the body does not actually produce is invalid Wasm, and the harness must be able to see that
   rejection rather than misreading it as some other outcome.
3. **Trap control.** `1 / 0` (`i32.div_u`) must be reported as a genuine `WasmRunOutcome.trapped`,
   not conflated with either of the above.

`oracleControlsRanRef` is a per-process `IO.Ref Bool` memo backing `ensureOracleControlsRan`, which
runs `runMandatoryOracleControls` exactly once per process. `verifyWasmDiffCase` (§7) calls
`ensureOracleControlsRan` itself, rather than relying on a single call site further up the stack —
there is no visibility modifier in Lean that would stop some other caller in the same file from
invoking `verifyWasmDiffCase` directly and bypassing a suite-level control gate, so the guarantee is
placed on the callee instead of assumed at the caller.

---

## 7. Per-Case Verification and Reporting

`verifyWasmDiffCase` is the single place a `WasmDiffCase` is checked against the host oracle. It
always begins by calling `ensureOracleControlsRan` (§6), so a case can never be verified against an
oracle that has not itself been sanity-checked, regardless of what calls this function or in what
order. For each fuzzed state it generates:

1. Runs the Lean model (`stepWasm`) directly and derives the model's own result types from its
   final stack.
2. Runs a **pre-module sanity assertion**: the case's declared `resultTypesFor` must match what the
   Lean model itself actually produced (when it didn't trap). An authoring bug in a case — a
   `WasmDiffCase` whose declared result type disagrees with its own model — is reported as such
   directly, rather than only surfacing indirectly as a downstream host mismatch that would be
   harder to diagnose.
3. Synthesizes the corresponding host test module and runs it via `runWasmHostExecution` (§2).
4. Matches exhaustively on the resulting `WasmOracleResult`: `OracleFailure.invalidModule` and
   `OracleFailure.processError` are always hard failures of the vector — there is no arm that lets
   either fall through as a pass — `WasmRunOutcome.trapped` is compared against the model's own
   `trapped` flag, and `WasmRunOutcome.ran` is compared value-for-value against the model's stack.

`reportWasmDiffResult` prints one case's `[PASS]` / `[FAIL]` / `[SKIP]` line and folds it into the
running totals threaded through `runWasmSemanticsFuzzerSuite`. A `skipped` result (§5) is reported
distinctly from both PASS and FAIL and never increments the passed count. The suite driver itself
additionally enforces a **vacuity floor**: a run that exercises zero host-engine test vectors across
every candidate case — whatever the reason — hard-fails rather than printing a clean summary, per
`docs/REVIEW.md` Law 13 ("Findings Become Gates") and `TCB.md` T11-b. Verifying nothing must never
read as a passing run.

---

## 8. WAT Text Formatting Conventions (Non-Spec)

`indent` (`Gasm/Targets/Wasm/Text.lean`) pads a line with `level * 2` spaces — two spaces per
nesting level — when pretty-printing an instruction tree into WebAssembly Text format. This is a
convention this project chose for human-readable output; it is not required, or even mentioned, by
the WebAssembly text-format grammar. The genuine spec grammar (vendored under
`references/wasm/text/{values,types,instructions,modules}.md`) treats whitespace uniformly as a
token separator between S-expression atoms and does not prescribe any particular indentation
scheme — a WAT module with different, or no, indentation is exactly as valid. Every other formatter
in `Text.lean` (`formatValType`, `formatBlockType`, `formatInstr`, `formatInstrList`,
`formatWatDataString`) cites the genuine W3C text-format chapters directly, because the *tokens*
they emit (`i32`, `block`, `local.get`, string escape sequences, …) are spec-mandated; `indent`
alone is cited here because the *whitespace* it emits is not.
