---
id: F1
title: RDTSC hardware harness (wsc-technique port; containment + rank criterion)
status: implementing
blocked_on: ""
after: [TC4]
related: [TC17]
bar: ""
track: perf
priority: 8.3
priority_set: 2026-08-27T18:25:47Z
design: "docs/RDTSC_HARNESS.md"
design_review: ""
date: 2026-08-27
---

# F1: RDTSC hardware harness (wsc-technique port; containment + rank criterion)

## Context

This is the forcing-function task for the entire performance-model track. MODEL_DEBT.md §A7
states it bluntly:

> **The perf fuzzer validates the model against itself.** `verifyPerfInvariants`
> (`Fuzzer.lean:150-175`) checks uop conservation and `0 < min ≤ nominal ≤ max`. Both hold for
> an arbitrarily wrong model. There is no RDTSC anywhere in the tree; `HardwareHarness.lean`
> captures 16 GPRs + RFLAGS + a faulted byte (`HardwareHarness.lean:29-70`, 136-byte record) and
> no timestamps. **Forcing function:** the zlib epic is unstartable as a *ranking* exercise until
> containment (`real ∈ [min,max]`) plus rank-order agreement exists.

MODEL_DEBT's TOP-10 table ranks this #2 overall ("RDTSC harness + containment criterion; kill
the self-referential perf fuzzer (A7)" — "Blocks the zlib epic's premise" — cost "M: extend the
136-byte record, calibration PE").

### The wsc precedent — read this in full before designing anything

This project has a direct predecessor, `wsc` (a private, unpublished repository), whose perf-fuzzer history
is exactly the failure mode this task must not repeat. PLAN.md's Phase-2 "Perf fuzzer design"
entry (wsc recon completed 2026-08-27) is the single richest source for this task and should be
read as close to verbatim as the file body allows:

> **Perf fuzzer design** (wsc recon complete 2026-08-27). Key findings from wsc: wsc's
> "PerfFuzzer" was self-consistency only (no hardware); actual hardware comparison was a MANUAL
> one-off — RDTSC medians from standalone Rust/C harnesses hand-transcribed as `Nat` literals into
> Main.lean (and visibly stale: scalar and SIMD Mandelbrot both "8 cycles"). Never wired into the
> build — the automation gap is the thing to fix, not just the code to port. What to carry over is
> the *technique*: CPUID+RDTSCP bracketing (serialized), median-of-N (not mean — SMI/interrupt
> outliers), separate timer-overhead calibration pass subtracted per-run, 5k-20k warmup iterations
> (turbo/cache ramp). Criterion: **range containment** (real ∈ [minCycles, maxCycles]) — wsc tried
> %-error first (commit 2ff06a9a) and replaced it with containment (0af86e9a); adopt containment +
> rank-order tracking of nominal across a kernel suite. Implementation shape: extend gasm's
> HardwareHarness.lean per-test block with timestamp brackets (extend the 136-byte result record),
> calibration PE, in-PE warmup+repetition loops, new PerfHardwareFuzzer that reuses Fuzzer.lean
> generators + computeCycleBounds, wired into PerfFuzzerCLI as --hardware. Do NOT port
> benchmarks/*.rs|*.c as artifacts (fold abi/store-drain experiments in as fuzzed kernel buckets
> later). TMAM %-splits are unvalidatable dashboard dressing in both repos — out of scope for
> validation; scope strictly to the [min,nominal,max] bounds contract. No core-pinning existed in
> wsc; containment + median makes that tolerable initially.

Unpack the two distinct lessons here, because they are easy to conflate:

1. **wsc's own hardware comparison was never real automation.** The numbers agents cite from wsc
   ("8 cycles for scalar Mandelbrot") were hand-transcribed from a *separate*, standalone Rust/C
   RDTSC harness into `Nat` literals in Lean source — copy-pasted once, then left to rot. They
   were stale enough that scalar and SIMD variants of the same kernel showed identical numbers,
   which is almost certainly wrong on its face (a SIMD kernel that's exactly as fast as its scalar
   twin is a red flag, not a result). This is not a bug to port — it is the entire cautionary
   tale. **The automation gap (never wired into the build, so it silently went stale) is the thing
   this task exists to close.** Do not build a harness that produces numbers a human transcribes
   into source; build one whose output IS the source (or feeds directly into calibration data
   governed per F2).
2. **The technique itself is sound and worth porting.** CPUID+RDTSCP serialized bracketing,
   median-of-N (not mean — a mean is dominated by SMI/interrupt tail outliers; median is robust to
   them), a separate timer-overhead calibration pass whose result is subtracted from every
   subsequent measurement, and 5k-20k warmup iterations to let turbo/cache state stabilize before
   measuring — these are the mechanics that make RDTSC-based cycle counting trustworthy on a
   general-purpose OS without kernel-level isolation. Port the technique, not the artifacts.

### The criterion: containment, not percent-error — and why wsc changed its mind

wsc's own git history is direct evidence here, cited by exact commit hash: **commit `2ff06a9a`**
tried a percent-error criterion first (real measurement must be within some % of the nominal
model prediction) and **commit `0af86e9a`** replaced it with **range containment**: the real
measurement must fall within `[minCycles, maxCycles]` — the same `[min, nominal, max]` bounds
tuple `computeCycleBounds` (`Performance.lean:76-96`) already produces for every instruction
sequence. Percent-error against a single point (`nominal`) is the wrong shape for a model that
already expresses its own uncertainty as a bounds interval; containment asks the model to be
*honest about its own bounds* rather than asking reality to match a point estimate to some
tolerance chosen after the fact. Adopt containment as the correctness gate, and additionally track
**rank-order agreement**: across a suite of kernels, if the model says kernel A's nominal cycles
are less than kernel B's, real hardware should overwhelmingly agree — this is the direct
operationalization of `docs/VISION.md` §5's "monotonically faithful" requirement (quoted in full
below), and it is the criterion that actually matters for the zlib-to-infinity epic (F6): agents
will use this model to *rank* candidate implementations without executing them, and a model that
gets absolute cycle counts wrong but ranks correctly is useful, while a model that hits absolute
numbers on a hand-picked micro-benchmark but ranks wrongly on real kernels is actively dangerous.

### Why F1 exists as its own task, not folded into F3

F1 is scoped narrowly to **the harness and the two criteria (containment + rank-order)** — it does
not itself calibrate any coefficient. F3 (staged model calibration) consumes F1's harness output to
actually correct `Uop.lean`'s tables. Keep this boundary: F1 proves the harness can measure real
hardware honestly and gate on it; F3 uses that proven-honest measurement to fix the model. Building
both at once risks the same conflation wsc fell into (measurement infrastructure and calibrated
constants tangled together, so neither gets properly checked in).

### Relationship to TCB T11-b (vacuity floors) — already handled elsewhere

MODEL_DEBT and PLAN.md both flag a general class of harness vacuity: a fuzzer invoked with, e.g.,
`--count 0` reporting "100% SUCCESS" because zero cases trivially satisfy every check. This
project's general answer to that class already exists as its own task — see
`docs/tasks/TC17-vacuity-floors.md` — and F1's `PerfHardwareFuzzer`/`--hardware` CLI path must be
covered by whatever non-empty-run floor TC17 establishes; do not re-derive that mechanism here,
just make sure the new hardware-fuzz entry point is subject to it (and to the existing
positive/negative control-vector convention `HardwareHarness.lean`'s
`verifyHardwareOracleControls` already demonstrates at lines 319-336 — the RDTSC extension should
follow the same "oracle must prove it's really running" discipline, now for timing rather than
just correctness).

### CPUID/RDTSCP handling — why it needs deliberate design, not just "add two instructions"

Neither `RDTSC`/`RDTSCP` nor `CPUID` currently exist in the instruction model. MODEL_DEBT §B2
notes this directly: "Forcing functions: any threaded spike; also the RDTSC perf harness (A7)
needs `RDTSCP`+`CPUID` as *modeled* instructions or an explicitly out-of-model harness escape
hatch." This is a real design fork this task must resolve explicitly rather than silently picking
one side:
- **Model them properly** as `X86_64Instruction` instances (encode/decode/step, registry-gated
  like every other instruction per TC4's registry gate) — consistent with Law 5/Law 9, but adds
  scope (these instructions have unusual semantics: RDTSC has no memory/register operands to speak
  of in the conventional sense, CPUID branches on EAX/ECX subleaf and returns model-specific data
  the Lean *functional* semantics cannot faithfully compute without becoming a lookup into
  hardware-specific tables).
- **Treat them as a harness escape hatch** — timestamp brackets are hand-assembled raw bytes
  emitted directly into the harness's generated test executable (the same way
  `HardwareHarness.lean`'s existing `buildTestText`/`emitNativeBatchTestExe` already hand-assembles
  register-load/capture sequences around the instructions under test, per
  `HardwareHarness.lean:74-256`), explicitly documented as out-of-model (never appearing in a
  `X86_64Instr` list an agent could emit or a proof could reason about) — narrower scope, consistent
  with the existing harness's own nature (it already emits some hand-written machine code that is
  infrastructure, not model).
State the choice and the reasoning in the design doc; the escape-hatch route is very likely correct
given the harness already works this way for its existing capture sequence, but this task should
make that judgment explicitly rather than by default.

## Deliverables & acceptance criteria

- A design doc under `docs/` (Law 5; this is Law-5-class performance-model work per the
  task-lifecycle convention below) covering: the CPUID/RDTSCP modeled-vs-escape-hatch decision
  above; the extended result-record layout (beyond the current 136 bytes); the calibration pass
  design (what "timer overhead" measures and how it's subtracted); warmup/repetition counts and
  their justification; and how `PerfHardwareFuzzer` reuses `Fuzzer.lean`'s existing generators
  (see `Fuzzer.lean:149-175`, `verifyPerfInvariants`) rather than inventing a parallel generation
  path.
- Extended `HardwareHarness.lean` per-test block emitting serialized `CPUID`+`RDTSCP` timestamp
  brackets around the existing capture sequence (`buildTestText`, `HardwareHarness.lean:74-172`),
  with the result record extended to carry the raw cycle count (or bracketed min/max across
  repetitions) alongside the existing GPR/RFLAGS/faulted fields.
- A calibration measurement pass (its own small PE, or a mode of the existing harness) that
  measures pure `CPUID`+`RDTSCP` bracketing overhead in isolation and produces a subtractable
  constant — this constant is calibration data and MUST be governed per F2 (do not hand-write it
  as a `Nat` literal in a `.lean` file; that is precisely the wsc failure mode this task exists to
  avoid). If F2 has not landed a governance mechanism yet by the time this lands, F1 must at
  minimum flag the interim storage as provisional and cite the F2 dependency explicitly rather than
  silently repeating wsc's mistake.
- `PerfHardwareFuzzer` (new): reuses `Fuzzer.lean` generators to produce instruction-sequence
  kernels, runs them through the extended harness with median-of-N (N in the 5,000-20,000 warmup +
  measured-repetition range, per the wsc technique), and checks **containment**
  (`real ∈ [minCycles, maxCycles]` from `computeCycleBounds`, `Performance.lean:76-96`) as a hard
  pass/fail gate, plus **rank-order agreement** tracked and reported across the kernel suite (not
  necessarily gated pass/fail on day one, but measured and surfaced — this is the metric F3's later
  calibration work will use to judge whether corrections actually improved fidelity).
- Wired into `PerfFuzzerCLI.lean` as a new `--hardware` mode, alongside the existing
  model-only invariant checks (`PerfFuzzerCLI.lean:65`, `verifyPerfInvariants`).
- Positive and negative control vectors for the new timing path specifically (distinct from
  `HardwareHarness.lean`'s existing correctness controls at lines 319-336): e.g. a known-slow kernel
  (a long dependency chain or an explicit spin loop) must measure as reliably slower than a
  known-fast one, and a deliberately mis-calibrated timer-overhead constant must be demonstrated to
  break containment (proving the calibration subtraction is actually load-bearing, not inert).
- **Differential validation evidence is the acceptance bar, not a proof.** Per `docs/VISION.md`
  §5, the performance model "must be differentially validated against real hardware
  measurement... [and] must be monotonically faithful — when the model ranks variant A faster than
  variant B, real hardware must overwhelmingly agree, or the model is actively misleading the
  optimization search." The completion evidence for this task is therefore: containment pass rate
  across the kernel suite, rank-order agreement rate, and the calibration-pass numbers themselves
  (timer overhead measured, with the machine/date/build identity F2 will require) — not a Lean
  theorem, since this is harness/measurement infrastructure, not a specification.
- Do NOT port `wsc`'s `benchmarks/*.rs`/`*.c` files as artifacts into this repo — per PLAN.md's
  explicit instruction, fold any useful ABI/store-drain experiment ideas in later as fuzzed kernel
  buckets generated through `Fuzzer.lean`, not as standalone external benchmark programs.
- TMAM (`computeTMAM`, `Performance.lean:100-141`) stays explicitly out of scope for this task's
  validation — MODEL_DEBT §A6 and this task's own PLAN.md source both call its %-splits
  "unvalidatable dashboard dressing" in both repos; do not build containment checks against TMAM
  output, only against the `[min, nominal, max]` bounds contract.

## Pointers

- `Gasm/Targets/X86_64/HardwareHarness.lean:19-25` (`HardwareExecutionResult` struct, currently
  GPRs+flags+faulted only, no timestamps), `:28-70` (`decodeHardwareResult`, the 136-byte decode
  this task extends), `:74-256` (`buildTestText`/`emitNativeBatchTestExe`, the hand-assembled
  per-test capture sequence the timestamp brackets get inserted into), `:281-336`
  (`runHardwareBatch`, `verifyHardwareOracleControls` — the existing fail-closed oracle + control
  vector pattern this task's timing controls should mirror).
- `Gasm/Targets/X86_64/Performance.lean:76-96` (`computeCycleBounds` — the `[min, nominal, max]`
  bounds this task's containment criterion checks reality against), `:62-72`
  (`computePortPressure`), `:100-141` (`computeTMAM` — explicitly out of scope, see above).
- `Gasm/Targets/X86_64/Fuzzer.lean:149-175` (`verifyPerfInvariants` — the existing model-only
  invariant checker; `PerfHardwareFuzzer` reuses this file's generators rather than duplicating
  them).
- `Gasm/Targets/X86_64/PerfFuzzerCLI.lean:65` (existing `verifyPerfInvariants` call site — the
  `--hardware` mode is added alongside this).
- `Gasm/Targets/X86_64/Uop.lean:47-68` (`X86_64Uop`, `MicroarchProfile` — the tables F1's
  measurements will eventually feed into via F3; F1 itself does not edit these).
- MODEL_DEBT.md §A7 (quoted above), §B2 (RDTSCP/CPUID absence), TOP-10 table row 2.
- PLAN.md Phase-2 "Perf fuzzer design" bullet (quoted in full above) — the single most important
  source for this task; also cites wsc commits `2ff06a9a` (%-error, rejected) and `0af86e9a`
  (containment, adopted).
- `docs/VISION.md` §5 (quoted above — "monotonically faithful").
- `docs/tasks/TC17-vacuity-floors.md` (the non-empty-run floor this task's new fuzzer entry point
  must be subject to — reference, do not re-derive).
- Reference the predecessor `wsc` repo (private, unpublished; `Tools/PerfFuzzer.lean` + `benchmarks/`), per D5 in
  PLAN.md — read for technique, do not port artifacts.

## Notes

- 2026-08-27: priority 8.3 — MODEL_DEBT top-10 #2: RDTSC harness + containment criterion — 'blocks the zlib epic's premise'; the perf fuzzer currently validates the model against itself with no real timing oracle.
- 2026-08-27: related: [TC17] — F1's RDTSC containment/rank criterion and TC17's vacuity floors are two halves of making the perf fuzzer non-self-referential (MODEL_DEBT A7): a real timing oracle (F1) is worthless if a zero-vector run can still print a clean PASS (TC17).
- 2026-08-28: design doc landed as `docs/RDTSC_HARNESS.md` (CPUID/RDTSCP escape-hatch decision,
  fail-closed control vectors, straight-line-unrolled measurement methodology). Note: this was
  written and implemented in the same single-agent session rather than routed through a separate
  fresh-agent design review first, a deviation from this task's own stated process given the
  practical constraints of the session — flagged here rather than silently omitted.
  `Gasm/Targets/X86_64/HardwareTimingHarness.lean` (CPUID+RDTSCP bracketing, straight-line
  warm-up/measurement, core-affinity pinning, pre-fault double-pass) and
  `Gasm/Targets/X86_64/PerfHardwareFuzzer.lean` (kernel suite, reduction, containment/rank-order,
  control vectors, calibration-file emission) built and wired into `PerfFuzzerCLI.lean --hardware`.
  Ran for real against this session's own development machine under `goldenCoveProfile`; per
  `docs/REVIEW.md` §4.4 and Law 14, the machine's own identity and this run's actual measured
  numbers are not repeated here — they live only in `calibration/x86_64/*.json`'s `provenance`
  and `reduction` fields, the Law-14-governed artifact this task exists to produce. Qualitatively:
  the positive control and discrimination-pair control vectors passed reliably across every run
  attempted; containment did not hold for any modeled kernel on the completion-evidence run,
  attributable to heavy concurrent load on the shared development machine at measurement time
  (recorded in each calibration file's own `provenance.run_conditions.concurrent_load_note`).
  Per the design doc's own conservative promotion rule (§8), no `costProvenance` field was
  flipped to `.cited` as a result — correct behavior, not a defect: the harness declined to cite
  noisy, untrustworthy absolute numbers. A full set of real calibration JSON/`.md` file pairs was
  written to `calibration/x86_64/` regardless (raw samples, provenance, controls — the full
  measurement pipeline proven end-to-end against real silicon), ready to produce a citable
  promotion the next time `--hardware` runs on an unloaded machine. Status set to `implementing`
  (not `done`): the harness and criteria exist and run for real, but no coefficient has yet been
  promoted to `.cited`, so MODEL_DEBT's "0 of 1611 cited" backlog is not yet numerically reduced
  — only unblocked. Note also: `check_gates_axioms`/`check_refs_coverage` were not reliably
  confirmed green during this session (both intermittently reported false failures from stale
  module-closure state on a machine under heavy concurrent multi-agent load; a separate agent is
  fixing the underlying tool issue) — `#print axioms` was run directly against this task's own
  new declarations instead; see the completion report for that result.

_(consolidated into docs/RDTSC_HARNESS.md, per the note above.)_
