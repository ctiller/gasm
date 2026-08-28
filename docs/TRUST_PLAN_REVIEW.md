# Independent review of `docs/TRUST_PLAN.md`

**Status**: this is a review artifact, not a specification and not a report of built machinery. It
proposes changes to a plan; nothing in it is implemented, and every mechanism it names as absent is
marked as absent. No file other than this one was changed by the review.

Reviewed against `docs/TRUST_PLAN.md` at commit `8e28043` ("Spike 4 is not categorically blocked --
correct Track B"), with the working tree's uncommitted `Stdlib/Zlib/Deflate.lean` and
`docs/tasks/PA17-...md` changes read as well, because two of the plan's claims are already being
overtaken by them. The plan's own stated baseline is `75cfe3e`, now many commits behind.

The plan moved once during this review. The Spike 4 correction it received is one I had already
reached independently before it landed (§1.3); that agreement is itself a data point, and the
correction is a real improvement. But it introduced a new gap that nothing now covers (§5.1), and it
left every other stale claim in place.

## Verdict

**The plan's spine is sound.** Its central structural claim — that the 44 `axiom-only` entries are
propagation from `grandfathered` roots, so retiring a root cascades — is **true**, and I verified it
at four independent points rather than accepting it. The leverage argument built on it holds. Naming
a retirement target per step, Rule 5's before/after allowlist measurement, and Rule 6's explicit ban
on further `bv_decide` work are the right disciplines and should stay exactly as written.

**Four things are wrong enough to change execution:**

1. **The correction to Track B deleted the plan's only consumer of `TraceStepLemmas.lean`, while two
   tracks still depend on it.** Old B2 was "build the first induction on `TraceStepLemmas.lean` —
   pathfinder for A6, B and C". New B2 is two `recvHook` rewrite lemmas, which are Spike-4-specific
   and involve no peeling at all. Yet A6 still reads "Depends on A2 + the Track B technique", and the
   plan still records that `TraceStepLemmas.lean` has zero consumers and unproven fitness. After the
   correction, **nothing in the plan establishes that module's fitness, and A6 and all of Track C
   need precisely that.** This is the highest-priority fix.
2. **7 of the 78 entries have no step at all**, and the per-file table's `axiom-only` column sums to
   37, not 44.
3. **Track D's premise is false for two of its three entries.** Spike 2's x86 programs *do* compute
   Fibonacci at runtime; only the Wasm one does not.
4. **Track A still repeats the `bv_decide` pattern**, and its own corrected "established" section now
   says so without the Steps section noticing.

Findings are numbered `F#`, each stated TRUE, FALSE, or STALE.

## 1. Factual claims, checked against the tree

### 1.1 Composition and the per-file table

**F1 — the totals are TRUE.** `scripts/gate_allowlist.txt` holds exactly 78 non-comment entries:
34 `grandfathered`, 44 `axiom-only`, 0 `finite-forall`.

**F2 — the per-file table is FALSE in two rows, and does not sum.** Measured by directory:

| directory | grandfathered | axiom-only | plan says |
|---|---|---|---|
| `Spikes/Spike4HttpServer/` | 9 | 12 | 9 / 12 — correct |
| `Spikes/Spike5Gzip/` | 7 | 11 | 7 / 11 — correct |
| `Stdlib/Zlib/Equivalence.lean` | 8 | 0 | 8 / 0 — correct |
| `Spikes/Spike3SortLines/` | 5 | **13** | 5 / 11 — **understates by 2** |
| `Spikes/Spike2Fibonacci/` | 3 | **8** | 3 / 3 — **understates by 5** |
| `Stdlib/Png/Equivalence.lean` | 2 | 0 | 2 / 0 — correct |

The plan's `axiom-only` column sums to 37 against its own stated total of 44. That is a
self-inconsistency visible without touching the tree, and it is not cosmetic: those seven entries are
exactly the seven no step then owns (§3).

**F3 — "those three spikes are 68 of 78" is FALSE.** Spike 4 is 21, Spike 5 is 18, Spike 3 is 18 —
**57** of 78. Under the plan's own understated numbers it would be 55. Neither is 68. The figure
appears to be transplanted from step F2's `check_gates_axioms` count, which measures something else.
Relatedly, Spike 3's leverage is **18, not ~16**.

**F4 — the central structural claim is TRUE.** I verified it at four independent points:

- `Spikes/Spike3SortLines/Windows/Equivalence.lean:139-148` — `spike3VerifiedProgram`'s
  `traceEquivalence` field is literally `cases b; exact spike3_empty_..._inst | exact
  spike3_canonical_..._inst`. The `axiom-only` entry is the `native_decide` axiom flowing through a
  record field.
- Same file, `:114-130` — both `spike3_effect_trace_equivalence_for_*_stdin` wrappers close by
  `exact`ing the grandfathered `_inst` theorems.
- `Spikes/Spike5Gzip/Equivalence.lean:179-232` — all five `spike5*VerifiedProgram` definitions have
  the identical one-line `cases op; exact <grandfathered theorem>` shape.
- `Spikes/Spike5Gzip/Windows/Emit.lean:20,28` and `Spikes/Spike2Fibonacci/Linux/Emit.lean:20,28` —
  each `main` imports its spike's `Equivalence` and calls `emitVerifiedExecutable` /
  `emitVerifiedLinuxExecutable` on the `VerifiedProgram` value. That is why every `Emit.lean` and
  `Test.lean` `main` carries an entry.

The leverage argument does not collapse. Retiring a root genuinely does cascade, and organizing the
plan around roots rather than leaves is correct.

### 1.2 The Spike 5 walls, as revised

**F5 — Wall 2 is TRUE.** `decompress` and `decodeHuffmanStream` are well-founded recursions
(`Stdlib/Zlib/Deflate.lean` carries `termination_by`/`decreasing_by` at `:429-430` and `:851-852`),
and `docs/PA16_CODEC_SOUNDNESS.md` records the measurement directly: `decide +kernel` on
`decompress (flushBitWriter (emitFixedBlock #[]))` is stuck even for the empty token stream.

**F6 — the revised Wall 1 bullet is TRUE as to `main`, and already being overtaken.** Two halves:

- `findLongestMatch` was converted to structural fuel recursion (`matchExtend` / `matchScan`) in
  `cdc98bf` — confirmed. The line reference `Deflate.lean:944` is stale; the definition is now at
  `:982`.
- `compressFixed` does carry a second, independent `while` loop — confirmed at `HEAD`, where it is
  still `Id.run do` with a `while pos < data.size`. The stated location "~1325" is off; it is at
  `:1344`.

But an in-flight agent has already converted it: the uncommitted `Stdlib/Zlib/Deflate.lean` in the
working tree replaces that loop with `compressFixedLoop`, a `fuel`-indexed structural recursion at
`:1348`. **The correction landed a claim that a live agent is in the middle of disproving.** That is
not a defect in the claim; it is evidence for the reliability point in §6 — the plan's factual base
has a shorter half-life than its dispatch cycle, so steps must be re-measured at dispatch time, not
inherited from the document.

**F7 — Track A's framing is contradicted by A1's own landing document, and now by the plan's own
"established" section.** `docs/PA16_CODEC_SOUNDNESS.md` (committed at `4745ce4`, by the same effort
as `cdc98bf`) states that the conversion buys proof tractability only, not `decide`, and that any
claim that removing a `while` loop unblocks `decide` end-to-end is false. Track A's heading still
reads "remove the reduction walls (gates Spike 5's ~18)". The established section now concedes that
removing the first wall left `compressFixed` and `gzipCompress` stuck; the Steps section has not
absorbed that.

**F8 — A1's step text now contradicts the bullet above it.** The established section says
`findLongestMatch` was "**Converted to structural fuel recursion in `cdc98bf`**". A1 still reads
"Convert `findLongestMatch` to fuel-based structural recursion. Kills Wall 1. … **DISPATCHED.**"
A1 is done. It should be marked done, with its measured retirement recorded — **which is zero**
(§4). Leaving a completed step listed as dispatched is how a plan comes to look fuller than it is.

### 1.3 The Spike 4 characterization — corrected, and I concur

**F9 — the previous "categorically blocked" claim was FALSE, and the correction is right.** I reached
this independently, from `docs/tasks/PA17-spike3-spike4-domain-honesty.md` in the working tree, before
the corrected plan landed. PA17 records that the earlier diagnosis "was wrong in a way that matters":
kernel reduction of the Windows canonical trace succeeds by plain `rfl` through fuel 29 and fails
from fuel 30, the first instruction inspecting a `recvHook` product; the obstruction is localized to
`recvHook` (`Gasm/Targets/Windows/Win32API.lean:207`) routing through `@[extern]` `String.toUTF8` /
`String.fromUTF8?`. 130 instructions, 59 steps, not a scale problem.

Two consequences worth stating explicitly, because the plan groups them and should not:

- **Spike 4's obstruction is not the same class as Spike 5's.** One is two `@[extern]` primitives at
  one hook; the other is a fixpoint/`Acc.rec` reduction problem across a codec. Any sentence covering
  both hides the difference that determines effort.
- **Spike 4 needs no trace-peeling technique.** 29 of 59 steps already reduce, and B3's remaining
  30 are of the same kind. That is exactly why the correction dissolves the plan's only
  `TraceStepLemmas.lean` consumer (§5.1) — the benefit and the new gap arrive together.

**F10 — B5's substance is TRUE, verified.** The nine Spike 4 `grandfathered` justifications in
`scripts/gate_allowlist.txt` do cite the route-prefix bug as the live falsity reason — the
`spike4_windows_root_trace_equivalence` entry names "the confirmed route-prefix-confusion
counterexample" and the `_status_` entry names "the confirmed /stat-prefix divergence". N8 fixed
that. And `parseRequestLine` really can fail exactly four ways: `Stdlib/Http11/Parser.lean:53,56,60,61`
return `malformedRequestLine`, `unknownMethod`, `unsupportedVersion`, `invalidTarget` — so the three
survivors the plan names are exactly right. `spike4GeneralClaimCounterexamples` exists at
`Spikes/Spike4HttpServer/Equivalence.lean:476` with a `#guard` at `:512`. One naming slip: the plan
calls the fourth class `invalidMethod`; the constructor is `unknownMethod`
(`Stdlib/Http11/Basic.lean:48`). B5 is a well-founded step and, under Law 13, the right shape — a
false ledger justification is a live defect, not bookkeeping.

### 1.4 `TraceStepLemmas.lean`

**F11 — TRUE, and I looked for the ways it could be false.** `Spikes/Spike3SortLines/TraceStepLemmas.lean`
is 137 lines, four theorems, all closed by `simp only`/`rfl` with no oracle. Tree-wide, the only
references to the module name or any of its four theorem names outside the file are one sentence in
`docs/tasks/PA17-...md` and the plan's own mentions. Nothing imports it. Zero consumers is exact.

**But the plan's inventory around it is incomplete, and this now matters more than it did.** Two
further oracle-free modules sit on `main`, unmentioned anywhere in the plan:
`Spikes/Spike3SortLines/Windows/InstructionStepLemmas.lean` (per-instruction `step` unfolding lemmas,
PA15's Part 1 pattern) and `Spikes/Spike3SortLines/Windows/InterceptLemmas.lean` (the generic "this
address is not an IAT slot" propositional detour). Both were built for exactly the C1 chain. Spike 3
Windows is three modules deep in purpose-built scaffolding; Spike 4 is zero deep and, per F9, needs
none.

### 1.5 Spike 2 — unchanged by the revision, and half false

**F12 — the claim is HALF FALSE, and the false half is the half Track D rests on.**

The Wasm half is TRUE, and stronger than stated. `spike2WasmInstructions`
(`Spikes/Spike2Fibonacci/Wasm/Program.lean:104-116`) is eight straight-line instructions: `fd_write`,
`drop`, `proc_exit`. The verified `fibIterWasmInstructions` (`:49-89`) is exported in the module but
never invoked — and *cannot* be: `Gasm/Targets/Wasm/Semantics.lean:521` dispatches every `.call idx`
to the host-import table, so there is no frame mechanism by which `_start` could call a module-local
function. Output comes from `spike2DataSegments`, derived at elaboration time from the same
Lean-level `fibIter` the spec uses, so the Wasm trace equivalence verifies ciovec encoding and memory
layout and verifies nothing about any Fibonacci implementation.

**The x86 half is FALSE.** `spike2SymbolicProgram` computes Fibonacci at runtime in registers — the
recurrence at `Spikes/Spike2Fibonacci/Windows/Program.lean:176-179`, a real `div_r64` digit loop at
`:141-156`, per-line `WriteFile` at `:173`, and the Linux twin at
`Spikes/Spike2Fibonacci/Linux/Program.lean:75-183`. Both are linked with an empty `dataItems` list
(`Windows/Program.lean:192`, `Linux/Program.lean:188`), so no precomputed byte blob exists in either
binary. The two x86 trace equivalences do exercise a runtime computation against `fibonacciSpec`.

What is true on x86 is a different fact: the separately-verified `fibIterSymbolicProgram`
(`Windows/Program.lean:49-68`) is redundant duplication — not in the emitted binary — and its Linux
copy (`Linux/Program.lean:49-68`) is fully dead, with neither a proof nor an emission consuming it.
That is a Law 8 dead-abstraction finding and a Law 12 unlinked twin. It is not a reason to defer two
retirements.

### 1.6 `gzipCompress` / `compressFixed`

**F13 — TRUE.** `compressFixed` has exactly two `.lean` occurrences tree-wide: its definition
(`Stdlib/Zlib/Deflate.lean:1344`) and the single call site `Stdlib/Zlib/Gzip.lean:42`. Nothing links
it to `compress`. A3 is correctly typed as a Law 12 connection theorem and correctly identified as
the step without which no zlib theorem reaches Spike 5. It is the best-argued step in the document.

## 2. Retirement targets: are the claimed numbers honest?

**F14 — A5 undercounts by 2; E4 then overcounts by 2.** `Spikes/Spike5Gzip/Spec.lean:57-63` defines
`compressData := gzipCompress` and `decompressData := gzipDecompress` — thin wrappers. So
`Spikes.Spike5Gzip.gzip_roundtrip_soundness_inst` is a ground instance of exactly A5's universal
statement. But so is `Stdlib.Zlib.gzip_roundtrip_soundness_inst`
(`Stdlib/Zlib/Equivalence.lean:152-157`) — the same proposition on a different literal — and likewise
for both `gzip_idempotent_canonical_roundtrip_inst` entries. A5's theorem discharges **four** entries,
not two; two of those four sit inside E4's claimed 8, so once A5 lands, E4 retires 6. The plan
double-counts 2 across tracks while under-crediting its strongest step.

**F15 — C1's "Retires 2" is ambiguous and probably wrong, and the harder half is unscheduled.**
Spike 3 Windows has two grandfathered roots: `spike3_empty_effect_trace_equivalence_inst` and
`spike3_canonical_effect_trace_equivalence_inst`. C1's described work — the empty-stdin chain —
reaches only the first. On the most favourable reading, "2" means the empty root plus its
`axiom-only` wrapper `spike3_effect_trace_equivalence_for_empty_stdin`; `spike3VerifiedProgram` and
the three `Emit`/`Test` entries stay blocked on the canonical root. **The canonical Windows chain
appears in no step**, and it is the harder of the two: it must trace an actual multi-line sort, not a
program that reads zero bytes and exits. The same gap applies to C2. C3 (Wasm, one root) is the only
Track C step whose number is unambiguous.

**F16 — D2's number is correctly stated as conditional.** That is honest and I credit it. Track D's
problem is its premise, not its arithmetic (§4).

## 3. What is missing

**F17 — 7 entries have no step.** Summing every claimed retirement (A5 2, A6 16, B4 21, C1 2, C2 2,
C3 12, D2 6, E4 8, E5 2) gives 71 against a target of 78. The shortfall is exactly the two rows F2
found understated: **2 Spike 3 `axiom-only` entries and 5 Spike 2 `axiom-only` entries** have no
owner. A plan whose stated goal is zero cannot leave 9% of the debt unassigned.

**F18 — no step supplies the WASI analogue of `TraceStepLemmas.lean`, and three steps need it.**
`TraceStepLemmas.lean`'s four theorems are all about `runProgramTraceWithLoops` — the x86-64 trace
interpreter. The Wasm trace equivalences run through `runWasiTrace` (`Gasm/Targets/WASI/ABI.lean`),
for which no step-peeling lemmas exist anywhere in the tree.
`Spikes/Spike2Fibonacci/Wasm/LoopInvariant.lean` is a genuine Wasm induction, but it is about
`runWasmFunction`, not the trace interpreter, so it is not the missing piece. C3, and the Wasm thirds
of A6 and of the Spike 4 group, all depend on machinery that does not exist and that the plan does not
schedule. **Status**: this module is not built; it needs its own step.

**F19 — F1 and F2 are correctly identified as cheap and decisive, then scheduled last.** F1 decides
whether Tracks C/D/E are proof work or research — for 18 entries. F2 may correct the denominator
itself. Both are undispatched while C/D/E steps are written as though their answers were known.

## 4. Does the plan repeat the `bv_decide` pattern?

Yes, in three places. The pattern is: a tractable, countable, satisfying target whose completion
moves `scripts/gate_allowlist.txt` by zero.

**A1 is the clearest instance, and it has already run its course.** It was dispatched. It landed
(`cdc98bf`). It is a real, well-executed refactor with a 241,480-pair differential behind it.
**The allowlist was 78 before it and is 78 after it.** Its own landing document
(`docs/PA16_CODEC_SOUNDNESS.md`, `4745ce4`) states the conversion does not unblock `decide`, and the
plan's revised Wall 1 bullet now concedes `compressFixed` and `gzipCompress` remain stuck. A1 is a
legitimate *prerequisite* for A3 — that is a real reason to have done it. It is not wall-removal
gating 18 entries, and Track A's heading still sells it as that.

**A2 is the same shape, one level up, and not yet spent.** It proposes converting
`decodeHuffmanStream`/`decompress` off well-founded recursion to fuel — a second whole-function
refactor of the codec, with a stated retirement target of zero. The plan does not argue why A6 needs
it: A6 is described as "structural trace proof", which is Law 10 rung 1, not `decide`. Note also that
these functions were converted *to* well-founded recursion deliberately, at `4ae2ab8` and `542041f`,
on `docs/PA16_CODEC_SOUNDNESS.md`'s own recommendation. Re-converting them a second time, to a third
form, needs a named consumer before it is worth an agent.

**F4 (citation adequacy review) has no retirement target at all** and is DISPATCHED. It may be worth
doing for Law 1 reasons; it is not progress toward zero, and a plan whose Rule 5 says no step counts
as done until measured against the allowlist should not carry a dispatched step that cannot be
measured that way.

**Track D is the sharpest instance, because it converts provable obligations into an owner
question.** D1 defers to the owner on the grounds that "retiring these three entries by proof would
verify a routine the program never runs." F12 establishes that is false for two of the three: the
Windows and Linux emitted programs *do* compute Fibonacci at runtime, and their trace equivalences
*do* exercise it. Those two are ordinary proof problems of C1's shape — arguably easier, since PA15
already built the loop-invariant induction for this very program
(`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`). **The Law 8 design question is real, but only
for Wasm**, where the emitted program does no computation at all. Asking the owner to rule on all
three defers two retirements behind a question that does not apply to them.

**Steps that are *not* instances, stated plainly because a review that only finds fault has not
calibrated itself:** B1 fixed a real defect with a checked witness. **B2 as revised is genuinely the
plan's highest-leverage item** and the revision is right about that — two rewrite lemmas against a
measured 30-step remainder, gating 9 roots and ~12 propagated entries, is the best ratio in the
document. B5 is a live Law 13 defect, verified (F10). A3 is the step without which Track A reaches
nothing (F13). A4's justification — without L3 the roundtrip is *genuinely false*, not merely
unproven — is the kind of load-bearing reasoning the rest of the plan would benefit from. F3 is real
and larger than stated: **11** branches are ahead of `main`, not nine. E1 is in flight with a landed
target. Rule 5 and Rule 6 are exactly right.

## 5. Sequencing

### 5.1 The gap the correction opened

**F20 — the Track B revision deleted the plan's only `TraceStepLemmas.lean` consumer while two tracks
still depend on it.** Before `8e28043`, B2 read: "Build the **first induction on
`TraceStepLemmas.lean`**. This is the pathfinder step for Tracks A6, B, and C — the module exists and
nothing uses it, so its fitness for purpose is unproven." After `8e28043`, B2 is two `recvHook` /
`X86_64Mem.writeBytes` rewrite lemmas — correct for Spike 4, and involving no peeling whatsoever.

What did not change:

- The established section still says `TraceStepLemmas.lean` "has zero consumers. No spike has built
  an induction on it."
- **A6 still says "Depends on A2 + the Track B technique."** The Track B technique is now a pair of
  hook-content lemmas about `recvHook`. They say nothing about peeling a Spike 5 x86 trace. A6's
  stated dependency no longer points at anything that would help it.
- All of Track C still needs exactly the peeling technique that no step now builds.

So the plan currently schedules a module it describes as unproven, depends on it from two tracks, and
has no step that exercises it. **Status**: no induction on `TraceStepLemmas.lean` exists anywhere in
the tree; the module remains unconsumed.

**The fix is to promote C1 to pathfinder.** It is the better-instrumented target by a wide margin:
three purpose-built oracle-free modules on `main` (F11) plus a fourth stranded (F21), against Spike
4's zero — and per F9 Spike 4 does not need one. Re-point A6's dependency at C1, not at Track B.

### 5.2 Remaining ordering problems

**F21 — C1 is ordered before its prerequisite, which is stranded.** C1 states that `IATLemmas.lean`
landed, with `alignUp_ge`, `foldl_append_size`, `loadMemory_excludes_sections` and four IAT
self-reference facts. **Status**: none of those names exists on `main`. The file exists — 294 lines,
all seven facts, matching the description — on the unmerged branch `spike3-empty-trace-equivalence`
at commit `8044ffb`. C1 has a hard, unstated dependency on F3 landing that branch. Dispatching C1
first would put an agent on a chain whose four Win32-intercept steps sit behind the ~57-second
per-fact kernel reduction wall that `8044ffb` exists specifically to remove.

**F22 — "~96 instructions" is unsourced, and the revision propagated it.** The figure appears nowhere
else in the tree. B3 now uses it comparatively ("not the 96-step hand-trace that Track C faces"),
so an unmeasured number is doing load-bearing work in two steps. By contrast PA17 measured Spike 4's
chain precisely: 130 instructions linked, 59 machine steps. Nothing comparable has been measured for
Spike 3, whose Windows `Program.lean` is 545 lines.

On the substance I judge C1 tractable and **not** the same categorical blocking Spikes 4 and 5 hit.
I checked the obvious candidate and it is clean: `readFileHook`
(`Gasm/Targets/Windows/Win32API.lean:101-119`) uses `ByteArray.extract` / `.size` /
`X86_64Mem.writeBytes` and never touches `String.toUTF8` or `String.fromUTF8?`; on empty stdin
`count = 0`, so the extern-opacity failure mode that stops Spike 4 does not arise. But C1 should open
by *measuring* its step count the way PA17 did, before an agent commits to hand-tracing it — all the
more so now that it is the proposed pathfinder.

### 5.3 Recommended re-sequencing

1. **Fix F20 first, before dispatching anything in A6 or Track C.** Promote **C1** to pathfinder;
   re-point A6's dependency from "the Track B technique" to C1; state in the established section that
   `TraceStepLemmas.lean`'s fitness is now C1's first deliverable.
2. **F1 and F2 before any further Track C/D/E dispatch.** Both are cheap. F1 decides whether 18
   entries are proof work or research; F2 may correct the denominator. Dispatching steps whose status
   F1 exists to determine is the ordering error the plan warns against elsewhere.
3. **F3 before C1.** C1's prerequisite is on `8044ffb`. Land the branch, then dispatch C1. Reword C1
   to require a measured step count as its first deliverable, and to say which of the two Windows
   roots it retires.
4. **Mark A1 done, with its measured retirement recorded as zero**, and rewrite Track A's heading so
   it no longer claims wall removal gates ~18.
5. **Gate A2 on a named consumer.** If A6 is a structural trace proof, state why A2 is required; if
   it is not, cut A2.
6. **Split Track D.** D1 (owner design ruling) applies to Spike 2 **Wasm only**. Spike 2 Windows and
   Linux become a new proof step of C1's shape, reusing `Windows/LoopInvariant.lean`.
7. **Add the two missing steps**: the WASI trace-step lemma family (F18), and coverage for the 7
   unassigned entries (F17) — most cheaply by correcting the table first, then extending Track C to
   the canonical Windows/Linux chains (F15) and Track D to Spike 2's `Emit`/`Test` propagation.
8. **Re-baseline the "established" section against `main` and re-date it.** Its header still says
   `75cfe3e`. Four of its five bullets have moved since.
9. **Keep B2, B3, B5 as written.** They are the strongest part of the document.

## 6. Reliability of the plan's factual base

Three of the plan's obstruction claims came from relayed agent reports rather than fresh measurement.
Two have now broken (Spike 4's "categorically blocked"; Wall 1's `findLongestMatch` characterization),
one broke *while this review was being written* (`compressFixed`'s second `while` loop, already
converted in the working tree), and one has never been checked at all against `main`
(`IATLemmas.lean` "landed" — F21). The Spike 2 bullet, which no correction has touched, is also half
false (F12).

The load-bearing conclusion is not that any individual agent was careless. It is that **this
document's factual base has a shorter half-life than its dispatch cycle.** Under Law 13 the fix is
mechanical, not exhortative, and three candidates are cheap:

- **Generate the per-file table from `scripts/gate_allowlist.txt`** rather than transcribing it. F2
  is a transcription error that a short script makes unrepresentable, and it is the direct cause of
  F17's seven unowned entries.
- **Make "landed" checkable.** A step asserting a prerequisite landed should name a commit reachable
  from `main`. F21 is a claim that would not survive that rule.
- **Require a measurement citation for every obstruction claim** — a commit or a task-doc section
  where the measurement is recorded. PA17 is the model: it states what it ran, what reduced, and
  where it stopped. "Categorically blocked" with no such citation is exactly the shape that broke.

**Status**: none of these three gates exists; each is a proposal, and none is required for the plan
to proceed.

## 7. Law bearing

- **Law 5** — F18's missing WASI machinery and F21's stranded prerequisite are both cases of a step
  demanding a mechanism not yet in the tree. Both should stop-and-design, or stop-and-land, before
  dispatch.
- **Law 9** — the plan aims at the right target, but retiring a `native_decide` root by a *narrower*
  structural proof would satisfy Law 10 while still failing Law 9. C1/C2 in particular retire a
  pointwise check by proving the same pointwise fact structurally; the `∀ stdin` domain that
  `Spikes/Spike3SortLines/Windows/Equivalence.lean:71-93` documents at length stays open. Each step
  should say which of the two it is buying.
- **Law 10** — Rule 6 correctly reflects the ADR-0037/D28 ratification. Nothing in the plan re-opens
  it, and nothing in this review does either.
- **Law 12** — A3 is correctly typed as a connection theorem (F13). Two further unlinked twins turned
  up while checking F12: `fibIterSymbolicProgram` on Windows (proved, not emitted) and its Linux copy
  (neither proved nor emitted).
- **Law 13** — B5 is the plan's own best example of this law applied. Three further findings here
  should become gates rather than one-off corrections: the three in §6, plus the comment at
  `Spikes/Spike2Fibonacci/Wasm/Equivalence.lean:78-81`, which justifies a fuel `#guard` by asserting
  the program "DOES contain a real `.loop`" — false of `spike2WasmInstructions`, and the same
  doc-facade shape `scripts/check_doc_facade.py` exists to catch, one layer down in a Lean comment.

## 8. Summary of false or stale claims

| # | Claim in the plan (at `8e28043`) | Finding |
|---|---|---|
| F2 | Spike 3 has 11 `axiom-only`; Spike 2 has 3 | FALSE — 13 and 8; column sums to 37, not 44 |
| F3 | "those three spikes are 68 of 78" | FALSE — 57 of 78; Spike 3 gates 18, not ~16 |
| F6 | Wall 1 at `:944`; `compressFixed`'s loop at ~1325 | line refs stale (`:982`, `:1344`); the second loop is already converted in the working tree |
| F7 | Track A "remove the reduction walls (gates ~18)" | FALSE per `docs/PA16_CODEC_SOUNDNESS.md` and per the plan's own revised bullet |
| F8 | A1 **DISPATCHED** | STALE — landed at `cdc98bf`; retired 0 |
| F10 | fourth failure class is `invalidMethod` | constructor is `unknownMethod`; rest of B5 verified TRUE |
| F12 | "the x86 side is the same shape" | FALSE — x86 computes Fibonacci at runtime |
| F14 | A5 retires 2; E4 retires 8 | A5 retires 4; E4 then retires 6 |
| F17 | every entry is covered by a step | FALSE — 7 unassigned |
| F20 | A6 "depends on … the Track B technique" | STALE after `8e28043` — that technique no longer exists |
| F21 | `IATLemmas.lean` landed | FALSE as to `main` — stranded on `8044ffb` |
| F22 | "~96 instructions" | unsourced; no such measurement exists in the tree |

Claims checked and found TRUE: the 78/34/44 totals; the Spike 4, Spike 5, Zlib and PNG table rows;
the `axiom-only`-is-propagation structural claim; Wall 2; the revised Spike 4 measurement; the
existence of `compressFixed`'s second `while` loop at `main`; B5's stale-justification finding and
its three surviving `Stdlib.Http11.Error` classes; `TraceStepLemmas.lean` built, oracle-free and
unconsumed; `gzipCompress` calls `compressFixed` with nothing connecting it to `compress`; and the
Spike 2 **Wasm** execution-path claim.
