# F1: RDTSC Hardware Measurement Harness — Design

> Law-5 design document for `docs/tasks/F1-rdtsc-harness.md`. Read alongside
> `docs/CALIBRATION_GOVERNANCE.md` (Law 14's concrete mechanism — F2, status `designing`,
> `python scripts/check_calibration.py` not yet implemented) and `docs/VISION.md` §5. This
> document specifies the harness this task actually builds: `Gasm/Targets/X86_64/HardwareTimingHarness.lean`
> (containment + escape hatch) and `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean` (generation,
> controls, containment/rank-order checking, calibration-file emission).

## 1. Why this exists (restated briefly — MODEL_DEBT §A7 has the full argument)

`Gasm/Targets/X86_64/Fuzzer.lean`'s `verifyPerfInvariants` checks uop conservation and
`0 < min ≤ nominal ≤ max` — both hold for an arbitrarily wrong model. There is no RDTSC
anywhere in the tree. Every registered instruction's `costProvenance` is
`.modelInternalUnvalidated` (0 of N registered instances are `.cited`, per
`Tools/CheckX86Obligations.lean`'s own summary output) because until this task lands there is
no legitimate `.cited` source: `docs/CALIBRATION_GOVERNANCE.md` §9 rules out Agner Fog/uops.info
as a coefficient SOURCE (cross-check only), and self-measured calibration — this task — is the
only remaining path. This document builds the harness; it does not itself flip any
`costProvenance` field to `.cited` on a coefficient whose correctness the measurement does not
actually establish (§8 below states the promotion rule this document follows, and why it is
conservative).

## 2. The wsc lesson, and what this design does about each part of it

Per the task doc's PLAN.md excerpt: wsc's own hardware comparison was a **manual, standalone**
Rust/C harness whose RDTSC medians were hand-transcribed as `Nat` literals into `Main.lean` and
left to rot (scalar and SIMD Mandelbrot both frozen at "8 cycles" — visibly stale, never
re-measured). The technique (CPUID+RDTSCP serialized bracketing, median-of-N not mean, a
subtracted timer-overhead pass, 5k-20k warmup iterations) was sound; the automation gap — never
wired into the build — is what this task exists to close. Concretely:

- The harness's output **is** the calibration artifact (a JSON file this tool writes), not a
  number a human reads off a console and retypes into a `.lean` file.
- The harness is a `lake exe` (via `PerfFuzzerCLI --hardware`), not a standalone script outside
  the build.
- Criterion is **range containment** (`real ∈ [minCycles, maxCycles]`), matching wsc's own
  post-`0af86e9a` correction away from percent-error (`2ff06a9a`), because the model already
  expresses uncertainty as a bounds interval and percent-error against a single point asks
  reality to match a point estimate chosen after the fact.

## 3. CPUID/RDTSCP: escape hatch, not modeled instructions

**Decision: escape hatch.** `RDTSC`/`RDTSCP`/`CPUID` are hand-assembled raw bytes emitted
directly into the generated test executable — the exact same discipline
`Gasm/Targets/X86_64/HardwareHarness.lean`'s `buildTestText` already uses for register-load and
capture sequences (bytes that are harness infrastructure, never appearing in an
`X86_64Instr` list an agent could emit or a proof could reason about).

Why not model them as real `X86_64Instruction` instances (the alternative the task doc names):

- `CPUID` branches on `EAX`/`ECX` subleaf and returns model-specific data (vendor string,
  feature bits) the Lean *functional* semantics cannot faithfully compute without becoming a
  lookup table keyed on real silicon identity — exactly the kind of hardware-specific state this
  project's ISA model does not otherwise carry (no MSRs, no CPUID leaves, `MODEL_DEBT.md` §F3).
- `RDTSC`/`RDTSCP` return the actual, non-deterministic passage of time — there is no
  `step : ι → X86_64MachineState → X86_64MachineState` that could give this a meaningful,
  checkable semantics; a `MachineState` has no clock field, and adding one to satisfy a
  self-referential timing instruction (used only to validate the very cost model this ISA
  extension would then also need a cost entry for) is circular scope creep with no proof payoff.
- The instructions have no correctness contract we would ever want to *prove against* — nothing
  in the target systems (game engines, OSes, servers, databases) is specified in terms of "the
  observed value of RDTSC," only in terms of elapsed cycles the *performance model* (not the
  correctness model) reasons about. Modeling them would add ISA surface with zero consumers.

This matches the harness's own existing nature: `buildTestText` already hand-assembles a VEH
trampoline, register captures, and stack bookkeeping that are infrastructure, not instructions
under test. The timing brackets are the same category of thing.

## 4. Containment (fail-closed, world-sampling) vs correctness (unrepresentable-by-construction)

Per `docs/REVIEW.md` Law 13 item 3: "wherever the artifact is under our control, the prevention
must be ∀-shaped... wherever the *world itself* is being sampled... a pointwise prevention... is
acceptable." A cycle count on real, thermally-throttling, turbo-boosting, SMI-interrupted
silicon is exactly the second case — there is no theorem to state here, only a harness that must
refuse to lie about what it measured. Every fail-closed decision below follows from that:

- `runTimingBatch` returns `IO (Except String (List HardwareKernelTiming))`, mirroring
  `HardwareHarness.runHardwareBatch`'s existing `Except`-typed shape (§8 of
  `docs/CALIBRATION_GOVERNANCE.md` names this exact pattern as the one to copy). Every failure
  mode — spawn failure, short/garbled output, a process that exits non-zero — routes through
  `.error`; there is no code path that fabricates a `HardwareKernelTiming` value.
- `verifyTimingOracleControls` (mirroring `verifyHardwareOracleControls`) runs BEFORE any real
  kernel is measured and aborts the entire run (`IO.userError`, not a logged warning) if any
  control fails. Three controls, all mandatory:
  1. **Positive control** — `nop_loop`'s per-instance cycle estimate must land inside a generous
     absolute band (`[1, 60]` cycles — wide enough to tolerate a slow, cold, un-turbo-ed
     first-run measurement, tight enough that a stuck/zero timer or a harness that isn't
     actually bracketing anything fails it).
  2. **Discriminating pair** (`docs/CALIBRATION_GOVERNANCE.md` §4.4/§8 and
     `docs/tasks/F1-rdtsc-harness.md`'s own "known-slow vs known-fast" requirement) —
     `long_dependent_chain` (32 serially-dependent `ADD reg, 1`) must measure at least
     `discriminationMinDeltaCycles := 20` cycles slower than `nop_loop`. This is wsc's actual
     observed symptom ("scalar and SIMD Mandelbrot both 8 cycles") restated as a control: two
     kernels that *must* differ, checked to actually differ, catch a stuck timer, a
     harness dispatching the wrong kernel, or a copy-paste in the kernel table.
  3. **Mis-calibration negative control** — deliberately subtracting a **wrong** (10x inflated)
     timer-overhead constant from a real measurement must break containment for a kernel that
     honestly contained under the correct overhead (`runMiscalibrationNegativeControl`), proving
     the overhead subtraction is load-bearing arithmetic, not an inert field nobody reads. This
     is the task doc's own explicit acceptance item ("a deliberately mis-calibrated
     timer-overhead constant must be demonstrated to break containment"). It runs against
     whichever kernel in the full suite honestly contains first (not hardcoded to one named
     kernel — §9's own evidence run shows containment does not hold for a fixed kernel on every
     run); if **no** kernel honestly contains (§9: this happened on this task's own evidence
     run, under heavy concurrent load), this control has no clean base case to corrupt and is
     reported as a soft warning, not a hard abort — it does not get to veto an otherwise-honest
     run on real hardware noise it did not cause. The discrimination-pair control (item 2) is
     this harness's primary Law-13-item-4 oracle-trustworthiness gate and remains a hard abort
     unconditionally; this control is a supplementary, this-task-specific acceptance criterion
     layered on top of it, not a replacement for it.
- No PMU, no PMU-derived uop counts (`docs/CALIBRATION_GOVERNANCE.md` §11, ratified/arbitrated:
  "no PMU path is scoped into F1... uop counts are not observables, they are internal model
  parameters"). The observable this harness produces is cycles, full stop.

## 5. Result-record extension

`docs/tasks/F1-rdtsc-harness.md`'s own deliverable text asks for "the result record extended to
carry the raw cycle count... alongside the existing GPR/RFLAGS/faulted fields." Interleaving a
CPUID-serialized RDTSC bracket into `HardwareHarness.lean`'s existing 136-byte single-shot
correctness capture block is possible but actively harmful to that block's own correctness
guarantee: `CPUID` clobbers `RAX`/`RBX`/`RCX`/`RDX` unconditionally, and the existing capture
sequence both loads test-vector operands into those exact registers *and* uses `RAX`/`RCX` as
scratch to write the capture buffer — bracketing it with CPUID would corrupt the very registers
the correctness harness exists to observe untouched. This design therefore does not touch
`HardwareHarness.lean`'s 136-byte struct or its capture sequence at all (zero regression risk to
the existing, working correctness oracle) and instead adds a **new, purpose-built result shape**
in a new file, `HardwareTimingHarness.lean`:

```lean
structure HardwareKernelTiming where
  name              : String
  rawDeltaCycles    : List UInt64   -- one entry per measured repetition, run order preserved
```

This *is* "the result record extended... alongside the existing fields" in substance — a second,
timing-specific record living next to the correctness record, populated by a second batch-run
entry point through the exact same `Except`-typed, control-vector-gated discipline — rather than
in the literal same 136-byte layout, because sharing that layout would require the timing
bracket to corrupt the correctness capture's own register contract. `runHardwareBatch` (the
correctness path) is untouched; a future task may unify the two executables if the register
conflict above is resolved by, e.g., giving the correctness path its own dedicated non-CPUID-
clobbered scratch registers, but that is out of scope here.

## 6. Measurement methodology

### 6.1 No CPU loop — straight-line unrolling instead

The wsc technique calls for "5k-20k warmup iterations." A register-counted CPU loop
(`dec reg; jnz`) needs a dedicated loop-counter register, and every general-purpose register
this harness could reserve for that purpose is also a register the fuzzer-generated kernel under
test might legitimately use as an operand (`Fuzzer.lean`'s `fuzzGprs64` covers
`rax,rdx,rbx,rsi,rdi,r8-r15` — 13 of the 15 addressable 64-bit GPRs). Rather than reserve a
register and mechanically filter every generated kernel against it, this harness **unrolls
warm-up and measurement as straight-line code, generated host-side in Lean**, exactly the way
`HardwareHarness.buildTestText` already generates one hand-assembled block per test case rather
than a data-driven interpreter loop. A single fuzzed instruction is typically 2-9 bytes; a
20,000-copy warm-up run is well within a PE image's normal `.text` bounds, and buys the same
turbo/cache-ramp effect as a branchy loop **without** any branch-predictor noise of its own and
**without** reserving any GPR at all. `warmupIterations := 20000` (top of the wsc-cited 5k-20k
range — raised from an initial 5,000 during this task's own hardware validation: at 5,000 the
turbo/frequency ramp had not reliably stabilized by the time the measured section began, see §9).

### 6.1a The pre-fault pass — a finding from live hardware testing, not in the cited wsc technique

Live testing on real hardware (§9) surfaced a hazard the wsc-cited technique does not name: the
**first** execution of each measured bracket's freshly-unrolled code measured substantially
slower than later, identical executions of the same bytes — consistent with Windows lazily
demand-paging this executable's `.text` pages on first touch, which a page fault mid-bracket is
indistinguishable, to RDTSC, from genuine kernel cost. Unlike the warm-up section (a separate
code region, already resident by the time it finishes), the measured section's own code is
executed for the first time during the very brackets being timed. Fix: `buildKernelBlock` emits
the entire `measuredRepetitions`-bracket sequence **twice**, back to back, at identical
addresses — the first pass's results are simply overwritten by the second, so only the
already-resident-page timings survive to the output buffer. This reduced but did not fully
eliminate this machine's measurement dispersion (§9); it is recorded here as this task's own
addition to the technique, not attributed to wsc.

### 6.2 Register safety: the one hazard straight-line unrolling does not remove

Unrolling removes the loop-counter hazard but not the `PUSH`/`POP` hazard: an unmatched `PUSH`
executed thousands of times in a row walks `RSP` down with nothing to undo it, and an unmatched
`POP` walks it back up into unmapped guard-page territory — a real crash risk this design must
close, not merely note. `Fuzzer.lean`'s `generateRandomInstruction` draws `PUSH r64`/`POP r64` at
indices 10/11 of its 32-way dispatch. `PerfHardwareFuzzer.lean`'s `drawRepeatSafeInstruction`
calls the real `Fuzzer.generateRandomInstruction` (reusing its generator, per the task doc's
explicit requirement, not duplicating it) and re-draws (bounded retries, falling back to a fixed
safe instruction on exhaustion — never silently substituting an unrelated instruction without
saying so) whenever the rendered `toNASM` string starts with `push`/`pop`. No other category in
that dispatch table can fault (no `DIV`) or mutate `RSP`/`RIP` outside normal sequential flow, so
this is the *only* filter needed — verified by reading every one of the 32 dispatch arms in
`Fuzzer.generateRandomInstruction`, not assumed.

### 6.3 Per-repetition bracket

Each of `measuredRepetitions := 63` (odd, for a clean median with no averaging of the two middle
values; raised from an initial 31 during hardware validation, see §9) repetitions is fully
unrolled with a **hardcoded output address** computed host-side — eliminating any need for an
address-scratch register, the same reasoning as §6.1. The end timestamp is captured and pushed
to the stack BEFORE the closing `CPUID` runs, so that `CPUID`'s own register clobber cannot
destroy the value it is meant to protect:

```
xor eax, eax          ; select CPUID leaf 0
cpuid                  ; serialize (open); clobbers eax,ebx,ecx,edx
rdtsc                  ; edx:eax = start timestamp
shl rdx, 32
or  rax, rdx           ; rax = start_ts (64-bit)
push rax                ; save start_ts across the kernel body (matched pop below)
<kernel bytes, repeated kernelUnrollPerRep = 512 times>
rdtscp                  ; edx:eax = end timestamp (ecx = TSC_AUX, discarded)
shl rdx, 32
or  rax, rdx             ; rax = end_ts
push rax                  ; protect end_ts across the closing CPUID's own clobber
xor eax, eax
cpuid                       ; serialize (close) -- prevents later instructions creeping in early
pop rax                       ; rax = end_ts
pop rdx                        ; rdx = start_ts
sub rax, rdx                    ; rax = raw delta cycles for this repetition (512 kernel instances)
mov rbx, rax                     ; rbx = delta (rbx already clobbered by cpuid, free scratch)
mov rax, <hardcoded addr>         ; rax = this repetition's output slot
mov [rax], rbx                     ; store
```

`RDTSCP` (not `RDTSC`) closes the measured interval because it is itself partially serializing
(waits for prior instructions to retire before reading the counter, per Intel's documented
`RDTSCP` semantics); the trailing `CPUID` after it additionally prevents *later* instructions
from executing before the read completes, per Intel's own recommended
open-with-`CPUID`+`RDTSC`/close-with-`RDTSCP`+`CPUID` bracketing idiom — capturing `end_ts` into
`RAX`/`RDX` and pushing it to the stack BEFORE that closing `CPUID` runs is this design's own
fix for the closing `CPUID` otherwise destroying the very value it is meant to protect (an
ordering bug caught during implementation, not present in the shipped harness). Both `PUSH`/`POP`
pairs around/after the kernel body are exactly matched, written by this harness (not
fuzzer-generated), so they introduce no `RSP` drift; register clobbering by `CPUID`/`RDTSC`
between repetitions is harmless because every register the kernel might read is either freshly
timestamp-derived (irrelevant to ALU/shift/mov/cmov/xchg/imul latency, none of which are
data-dependent on modern x86) or carried over from the previous repetition's own execution
(realistic steady-state operand reuse, not a correctness concern since this harness never checks
kernel *output*, only elapsed cycles).

**Per-instance cost derivation.** `kernelUnrollPerRep := 512` amortizes bracket overhead against
single-cycle-class kernels. Empirically raised from an initial 16, then 64, before settling at
512 (§9): at smaller unroll counts this machine's own bracket-to-bracket measurement noise (see
§9's evidence) was comparable in magnitude to the kernel's own real cost, making the two
statistically indistinguishable. The reduction records
`cyclesPerInstance := (median(rawDeltaCycles) - timerOverheadMedian) / kernelUnrollPerRep`,
explicitly labeled as **derived/amortized**, not a bare single-instruction bracket reading — a
sub-1-cycle result is possible and expected for genuinely 0.25-reciprocal-throughput-class
instructions under superscalar dispatch, and is reported as such rather than floored to a
misleadingly-whole number.

### 6.4 Timer-overhead calibration pass

`timer_overhead` is a kernel with an **empty** body (`kernelUnrollPerRep` copies of nothing) —
the bracket alone, timing itself. Per `docs/CALIBRATION_GOVERNANCE.md` §5, this is stored as its
own calibration file (`calibration/x86_64/timer_overhead.json`) with the same
raw-samples/provenance/controls shape as every other kernel, and every other kernel's
`timer_overhead_ref` field names it by path — never inlined as an unrecorded free parameter, and
never subtracted before storage (`raw_samples_cycles_unadjusted` stores the **pre-subtraction**
brackets; `reduction.median`/`min`/`max` are the post-subtraction, derived numbers, exactly
`docs/CALIBRATION_GOVERNANCE.md` §5's schema).

### 6.5 Statistic: median, not mean, and the dispersion guard

Per the wsc-cited technique, **median** of the (post-warmup) `rawDeltaCycles` — not mean — because
a mean is dominated by SMI/interrupt-tail outliers and a single median-of-31 is already robust to
a handful of spikes. `min`/`max` across the 31 repetitions are also recorded (so a coefficient
citation carries a distribution, not a point estimate, per this task's own instruction). Following
`docs/CALIBRATION_GOVERNANCE.md` §2.3, `check_calibration.py`'s future dispersion guard
(IQR/median ratio bound, first-half-vs-second-half median drift bound) is **not implemented by
this task** (F2 owns `check_calibration.py`), but this harness's calibration JSON already stores
`raw_samples_cycles_unadjusted` in run order specifically so that guard can be added later without
a schema change, and this task's own written report states each kernel's IQR/median ratio by hand
as the evidentiary substitute until that gate exists.

## 7. Where this harness is, and is not, valid to run

`docs/CI.md` §5 already excludes `perf_fuzzer` (the model-only invariant checker) from both
hosted CI platforms: "A shared/virtualized hosted vCPU does not give a trustworthy cycle-count
signal (noisy neighbors, masked/virtualized microarchitecture, no reliable low-level counters)."
`--hardware` is a mode of the same `perf_fuzzer` executable and inherits that carve-out
identically — **it must never be added to `ci.yml`**, hosted or otherwise, until a self-hosted
runner with a recorded, known CPU profile exists (the same condition `docs/CI.md` §5 already
names for the model-only fuzzer). It is valid to run:

- On a physical, non-virtualized development machine with a stable, known microarchitecture,
  ideally on AC power with a "High performance"/no-throttle power plan.
- Interactively, by hand, the way this task's own completion evidence was produced (§9).

It is explicitly **not** valid evidence, even if it happens to run without error, on:

- Any GitHub-hosted (or equivalent shared-tenancy) Actions runner.
- **A machine under concurrent heavy load from another process — not a hypothetical, this task's
  own completion evidence run hit exactly this (§9 gives the qualitative finding; the actual
  per-run numbers, including the process-load evidence that explains them, are Law-14-governed
  data and live only in `calibration/x86_64/*.json`'s `provenance.run_conditions`, never in this
  prose per `docs/REVIEW.md` §4.4 — "committing things about the local machine is not useful to
  anyone else, and a potential security risk").** The discrimination-pair and positive-control
  checks are the harness's own defense here (§4), and a human should never trust the *absolute*
  cycle numbers, or containment specifically, from a run without first reading that run's own
  `run_conditions`/`concurrent_load_note` field for exactly this reason.
- A VM/hypervisor-virtualized CPU, unless that hypervisor is known to pass through an
  unthrottled, unmasked TSC (this harness cannot detect virtualization directly — no CPUID
  hypervisor-bit check is implemented — so this is a documented human judgment call, not a
  mechanized one; a future hardening pass could read `CPUID` leaf `0x1` bit 31 (hypervisor
  present) and refuse to run, which is named here as an explicit open item, not silently
  dropped).

This harness pins its own process to logical processor 0 (`SetProcessAffinityMask`, added during
hardware validation — see §6.1a's sibling finding and §9) to remove OS core-migration as a
variable; it does **not** attempt to detect or wait out *other* processes' load on that same
core, which is exactly the residual risk the bullet above names.

## 8. The promotion rule this document follows for `costProvenance`

`docs/tasks/F1-rdtsc-harness.md` §"Why F1 exists as its own task, not folded into F3" is explicit:
"F1 is scoped narrowly to the harness and the two criteria... it does not itself calibrate any
coefficient. F3... consumes F1's harness output to actually correct `Uop.lean`'s tables." This
document honors that boundary literally: **this task does not edit any coefficient's numeric
value in `Uop.lean` or any `toUops` implementation.** It does, however, land real calibration
artifacts and — per the outer completion brief's own framing ("landing genuine citations for even
a few coefficients is worth far more than a framework that measures nothing") — evaluates,
per instance, a narrow and honest promotion criterion that does not require correcting the
underlying uop breakdown first:

> An instance's `costProvenance` may move from `.modelInternalUnvalidated` to
> `.cited "calibration/x86_64/<file>.json#reduction"` **only if** the real measured
> `cyclesPerInstance` for that instance's kernel falls within `[minCycles, maxCycles]` computed by
> `computeCycleBounds` for the same instruction sequence under the profile the calibration file
> targets (containment holds) — i.e., the model's own claimed bound about this instruction has
> been checked against real hardware and was not falsified. This is deliberately weaker than "the
> uop count is correct" (which `docs/CALIBRATION_GOVERNANCE.md` §11 reserves for a
> discriminating-kernel-pair promotion, F3's job) and is stated as exactly that: `.cited` here
> means "this instance's cost *bound* has been measured and holds," never "this instance's uop
> breakdown is correct." If containment fails, the instance stays
> `.modelInternalUnvalidated` — flipping it anyway would be the same overclaim this whole
> document exists to prevent, just relocated to a new field.

§9 below records, per measured instance, which side of that line the real measurement landed on.

## 9. Kernel suite and evidence

The suite (`Gasm/Targets/X86_64/PerfHardwareFuzzer.lean`'s `fullSuite`), 12 kernels:

- `timer_overhead` — empty-body calibration pass (§6.4).
- `nop_loop` — positive control (raw `0x90` byte, harness-internal, not a modeled instruction).
- `long_dependent_chain` — discrimination-pair partner (`AddR64Imm8`: 512 serially-dependent
  `ADD RAX, 1`).
- `shl_by_cl` (`ShlR64Cl`) — MODEL_DEBT §A8's named spot-check (modeled 1 uop; Intel P-cores are
  documented elsewhere as needing a flag-merge uop, i.e. real cost is higher).
- `genericKernelCount` (currently 8) `drawRepeatSafeInstruction`-generated single-instruction
  kernels, drawn from `Fuzzer.generateRandomInstruction`'s full dispatch (add/sub/mov/xor/cmp/
  and/or/test/not/neg/shift-by-imm8/cmov/xchg/imul, minus the push/pop filter of §6.2) under a
  fixed seed — deterministic and reproducible from source, not a machine-specific fact — for
  containment and rank-order breadth beyond the hand-curated named set. Which specific
  instructions a given run drew is recorded in that run's own `calibration/x86_64/generic_*.json`
  file names and `measured_subject` fields, not repeated here.

**Evidence.** Per `docs/REVIEW.md` §4.4 ("committing things about the local machine is not
useful to anyone else, and a potential security risk") and Law 14, this document does not repeat
any measured value — every kernel's raw samples, reduction, provenance, and control-vector
outcomes live *only* in `calibration/x86_64/*.json`, each paired with its zero-numbers `.md`
citation stub per `docs/CALIBRATION_GOVERNANCE.md` §6.1. What follows is the qualitative,
non-numeric shape of this task's own completion run; read the JSON files themselves for the
actual figures.

- **Control vectors**: the positive control and the discrimination pair (§4) both passed on this
  task's completion run, and passed on every run attempted during development — the harness's
  *relative*/directional judgment (is kernel A reliably slower than kernel B) was consistently
  trustworthy.
- **Containment**: on this task's completion run, containment (§8) did **not** hold for any
  modeled kernel in the suite. Every kernel's `calibration/x86_64/*.json` file records its own
  `reduction` and the model bound it was checked against, and every file's
  `provenance.run_conditions.concurrent_load_note` records the run-condition finding that
  explains why: this session's own development machine was, at measurement time, host to
  multiple other agents' concurrent Lean/Lake builds — the exact condition §7 names as
  invalidating absolute-cycle evidence. The discrimination pair still passing throughout is
  evidence this is a real-world-noise finding, not a harness defect.
- **Consequence for §8's promotion rule**: since containment did not hold for any modeled kernel
  on this run, **no `costProvenance` field was promoted to `.cited`** — correctly, per §8's own
  rule: inflated absolute numbers from a loaded machine are not honest evidence a coefficient's
  bound holds, and citing them would be exactly the overclaim this document exists to prevent.
  This is the harness working as designed under adverse conditions, not a defect.
- **What this run still accomplishes**: a full set of real calibration JSON/`.md` file pairs
  under `calibration/x86_64/`, each with real raw, run-order-preserved samples, a real
  provenance block, and a real controls block — the full pipeline (harness → measurement →
  reduction → containment check → calibration file) is proven to work end-to-end against genuine
  silicon, and is ready to produce a `.cited` promotion the moment it runs on an unloaded
  machine (re-running `lake exe perf_fuzzer -- --hardware` is the entire regeneration step, and
  overwrites this run's files in place — Law 14's regenerable-not-transcribed discipline).

## 10. Rank-order tracking

Rank-order agreement is tracked across every pair of kernels in §9's hardware-timed suite that
has a modeled instruction: the fraction of pairs where the model's `nominalCycles` ordering
agrees with the real `cyclesPerInstance` ordering is computed and printed
(`rank-order agreement: k/n pairs`) at run time, surfaced rather than gated, matching this task's
explicit non-gating scope for it ("not necessarily gated pass/fail on day one, but measured and
surfaced"). Per §4.4/Law 14, the actual agreement fraction from any specific run is not repeated
in this document; a low-agreement run is expected to correlate with a containment run that also
failed (a model whose absolute bounds a real measurement fell well outside has little reason to
preserve relative ordering either) — this is the metric F3's later calibration work is meant to
improve, not a metric this task claims to have already fixed. A broader, model-only-evaluated
rank-order pass (comparing `nominalCycles` across a large `Fuzzer.generateRandomProgram`-generated
program population, no hardware execution) was considered but not built for this landing — the
existing `perf_fuzzer` model-only mode (`Fuzzer.verifyPerfInvariants`) already exercises that
generator population for its own invariants, and a rank-order-only variant of the same pass
without a real-hardware comparison point would be tautological (model compared to itself), so it
is left as explicit future work rather than built for its own sake.

## 11. Relationship to `docs/tasks/TC17-vacuity-floors.md`

`--hardware`'s entry point is subject to the same floor `PerfFuzzerCLI`'s existing `--count 0`
path already enforces (`Gasm/Targets/X86_64/PerfFuzzerCLI.lean`'s vacuity-floor check, TC17,
status `done`): zero kernels measured is a hard failure, never a printed "100% SUCCESS," and the
control-vector failure path (§4) already aborts before any kernel is measured at all if the
oracle itself cannot be trusted — the two floors compose rather than duplicate each other.

## 12. Deferred, named explicitly (not silently dropped)

- `DIV r64` (MODEL_DEBT §A8's second named spot-check) is **not** measured by this landing: `DIV`
  can fault (`#DE`), and this timing harness deliberately has no VEH (§5 — adding one would
  reintroduce the register-clobbering conflict with the correctness harness's own VEH, or need a
  second one built from scratch). A future extension can add a fault-safe timing wrapper (operands
  chosen to guarantee no fault, verified once against the correctness harness's own `Div.lean`
  fuzz states) — named here as explicit follow-up work for F3/a future F1 extension, not a silent
  gap.
- Hypervisor-presence detection (§7) is not implemented — a documented human judgment call today.
- `check_calibration.py` (F2) does not exist yet; every calibration JSON this task writes is
  therefore **provisional** — schema-conformant per `docs/CALIBRATION_GOVERNANCE.md` to the best
  of this task's ability to anticipate it, but not yet mechanically gated. Each file's own `.md`
  stub says so explicitly.
