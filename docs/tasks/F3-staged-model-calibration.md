---
id: F3
title: Staged model calibration vs silicon (uop/latency, dependency chains, branch model, hierarchy)
status: ready
blocked_on: ""
after: [F1, F2]
related: []
bar: ""
track: perf
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# F3: Staged model calibration vs silicon (uop/latency, dependency chains, branch model, hierarchy)

## Context

This task is where the RDTSC harness (F1) and the calibration-data governance mechanism (F2)
actually get used to fix the x86-64 performance model. It is the single largest performance-model
task in this batch, because MODEL_DEBT.md §A enumerates a genuinely large amount of debt in
`Gasm/Targets/X86_64/Uop.lean` and `Performance.lean`, and TASKS.md deliberately sequences the
repair in a specific four-stage order rather than leaving it open-ended:

> F3 staged model calibration vs silicon: uop/latency tables (A8), dependency chains (A1), branch
> model (A4), then hierarchy (A0) — after: F1, F2

That ordering is not arbitrary — read the four MODEL_DEBT entries in the order TASKS.md gives them
and the reasoning becomes visible: each stage's fix is a precondition for correctly measuring the
next.

### Stage 1 — uop/latency tables (A8)

MODEL_DEBT §A8, quoted in full:

> **A8. Concrete coefficients have no vendored source (Law 4 gap).** Every perf declaration cites
> `references/intel_sdm/vol_1.../ch_03_basic_execution_environment.md#32-overview...` — a generic
> anchor that contains no port, latency, or throughput data. Spot-check of two coefficients against
> public data: `SHL/SHR r64, CL` is modeled as **1 uop** (`Shift.lean:146,174`) but is 3 uops on
> Intel P-cores (flag-merge) — directly relevant to DEFLATE bit-readers; `DIV r64` is modeled as 5
> uops / 14 cycles (`Div.lean:43-49`) against a real ~36-uop, 30-90-cycle operation. These numbers
> are currently *invented*, not cited. (Both spot-checks are hypotheses-to-measure, not vendored
> facts — which is itself the argument for this entry.)

This is stage 1 because it is the most basic layer: if the per-instruction uop count and latency
numbers are wrong at the single-instruction level, every downstream stage inherits that error.
Notice MODEL_DEBT's own hedge — the SHL/DIV numbers "are from memory, not a vendored source; treat
as hypotheses to measure" (Auditor's uncertainty notes, item (b)) — this stage's job is precisely
to turn those hypotheses into measurements, using F1's harness, governed by F2's mechanism.

### Stage 2 — dependency chains (A1)

MODEL_DEBT §A1, quoted in full:

> **A1. Dependency chains are not modeled in the nominal cost.** `computeCycleBounds`
> (`Performance.lean:76-96`) computes `nominalCycles = max(minCycles, maxPortCycles,
> divLatencyTotal)`. `latencyCycles` enters *only* via the `intDiv` filter (line 88). Ten dependent
> `ADD`s and ten independent `ADD`s produce identical nominal cycles. `maxCycles` is the fully-serial
> sum (line 92), i.e. the model offers throughput-only or latency-only, never the true
> `max(port-bound, critical-path)`. **Severity: critical for the zlib epic.** Every latency-hiding
> transformation — unrolling to break a CRC or adler accumulator chain, software pipelining,
> reassociation into independent accumulators — is exactly the class this cannot rank. **Validation:**
> RDTSC on paired kernels (dependent vs independent chains). **Cost to model:** moderate — requires
> uops to carry register read/write sets, which `X86_64Uop` (`Uop.lean:47-53`) does not.

This stage requires a real structural change to `X86_64Uop` (adding register read/write sets) before
it can even be measured against — flag this explicitly as scope, not just a coefficient tweak. It is
staged second because it is the debt item MODEL_DEBT itself flags as "critical for the zlib epic"
(F6) — F6 cannot rank unrolling/pipelining/reassociation transformations correctly until this lands,
and F6's `after:` list includes F4, which itself depends on F3, so this is squarely on F6's critical
path.

### Stage 3 — branch model (A4)

MODEL_DEBT §A4, quoted in full:

> **A4. Branch prediction is "every branch mispredicts, in the pessimistic bound only."**
> `maxCycles` adds `branchCount * branchMispredictPenalty` (`Performance.lean:93-94`) —
> unconditionally, for every branch uop including unconditional `JMP` and `CALL`. Nominal adds
> nothing. There is no taken/not-taken model, no loop-exit special case, no BTB/indirect-branch cost.
> **Bites hard on zlib:** branchless (CMOV) vs branchy Huffman decode is *the* canonical DEFLATE
> tradeoff, and the model ranks it purely on uop count — CMOV loses, always, regardless of entropy.
> Under an unpredictable-symbol stream the real answer inverts. **Validation:** RDTSC on
> branchy/branchless decode pairs over high- and low-entropy inputs.

The CMOV-vs-branchy example is worth dwelling on precisely because it names a real instruction
family already in the ISA (`Instructions/Cmov.lean` exists) — this is not a hypothetical future
tradeoff, it is a decision the zlib-to-infinity epic (F6) will actually face on the Huffman decode
path, and the current model cannot even in principle produce the entropy-dependent inversion the note
describes (branchless always looks worse by uop count alone, regardless of the real input
distribution).

### Stage 4 — hierarchy (A0), explicitly the largest and last

MODEL_DEBT §A0, quoted in full:

> **A0. There is no memory hierarchy at all — not even unused constants.** No L1/L2/L3 latency
> constants exist anywhere in `Gasm/`. `MicroarchProfile` (`Gasm/Targets/X86_64/Uop.lean:57-68`) has
> fields for fetch bandwidth, decode/rename/dispatch/retire widths, ROB capacity,
> branch-mispredict penalty and active ports — and *nothing* about caches, TLB, store buffer, line
> size, or frequency. Every load in the ISA is a flat `latencyCycles := 4` (`Mov.lean:380,477,514`,
> `Pop.lean:35`, `Ret.lean:25`, `Call.lean:29`), independent of address, stride, or working-set size.
> **When it bites:** immediately on zlib. A sliding-window LZ77 match loop over a 32 KB window and a
> Huffman table lookup have wildly different real costs and identical model costs; any
> blocking/tiling/prefetch/table-layout transformation is invisible to the model, and a variant that
> halves cache misses will be ranked *equal or worse* than one that reduces uop count. **Validation:**
> pointer-chase and stride-sweep microbenchmarks under the (planned) RDTSC harness. **References:**
> SDM is vendored, but it does not carry latency tables — Intel *Optimization Reference Manual*,
> Agner Fog, or uops.info must be ingested (Law 4). None are present in `references/`.

TASKS.md's own ordering and the TOP-10 table (row 7: "Memory hierarchy: line size, L1/L2/L3, miss
cost (A0) ... **L** — needs an address/working-set abstraction the uop model lacks") both mark this
as the last and largest stage — it needs a genuinely new abstraction (address/working-set awareness
the current flat per-instruction uop model has no concept of), and its correct sequencing after
stages 1-3 means the simpler, more localized fixes land first and give F1's harness a growing suite
of validated kernels to check hierarchy effects against once this stage starts.

### Why F1 and F2 are both hard prerequisites

Every one of the four stages' "Validation:" lines cites RDTSC measurement — this task cannot proceed
without F1's harness existing and producing trustworthy (containment-checked) numbers. And every
corrected coefficient this task produces is exactly the kind of "measured number from this machine"
MODEL_DEBT §E5 (F2's substance) says has no home under Law 4 as currently written — without F2's
governance mechanism, this task would either invent its own ad-hoc storage (repeating part of the
wsc mistake) or hand-transcribe numbers into `Uop.lean` literals with no provenance (repeating all of
it). Do not start this task's calibration work before both are real.

## Deliverables & acceptance criteria

- Stage-by-stage execution in the TASKS.md-specified order (A8 → A1 → A4 → A0), each stage producing:
  a measured correction (via F1's harness) governed as calibration data (via F2's mechanism), and an
  updated model coefficient/structure in `Uop.lean`/`Performance.lean` that cites the calibration file
  the way other declarations cite the SDM.
- Stage 1 (A8): re-measure `SHL/SHR r64, CL` uop count (`Shift.lean:146,174`) and `DIV r64` uop
  count/latency (`Div.lean:43-49`) against real hardware; update the model to match measurement, not
  memory-recalled public data — the spot-check hypotheses in MODEL_DEBT are a starting point for what
  to look at, not something to trust without measuring.
- Stage 2 (A1): extend `X86_64Uop` (`Uop.lean:47-53`) to carry register read/write sets sufficient to
  compute a true critical-path length distinct from port-bound throughput; update
  `computeCycleBounds` (`Performance.lean:76-96`) so that `nominalCycles` reflects
  `max(port-bound, critical-path)` rather than ignoring dependency structure; validate with paired
  dependent-vs-independent-chain kernels (e.g. a chain of 10 dependent `ADD`s vs 10 independent ones)
  under F1's containment criterion.
- Stage 3 (A4): replace the unconditional `branchCount * branchMispredictPenalty` maxCycles term
  (`Performance.lean:93-94`) with at minimum a taken/not-taken distinction and correct treatment of
  unconditional `JMP`/`CALL` (which do not mispredict in the same sense conditional branches do);
  validate with the CMOV-vs-branchy Huffman-decode-style pair described in A4, over both
  high-entropy and low-entropy synthetic inputs.
- Stage 4 (A0): introduce a minimal address/working-set-aware cost dimension — at least L1/L2/L3
  latency constants and a way for a load's modeled cost to depend on stride/working-set size rather
  than the current flat `latencyCycles := 4` everywhere; validate with pointer-chase and stride-sweep
  kernels. This stage may reasonably be scoped down to "introduce the abstraction and calibrate its
  simplest form" rather than a fully general cache simulator — state explicitly in the design doc
  what's in scope for this task versus deferred, since TOP-10 already marks this the largest (`L`)
  item in the batch.
- **Differential validation evidence, per stage, is the acceptance bar** (per `docs/VISION.md` §5's
  "monotonically faithful" requirement, same as F1): each stage's completion evidence is containment
  pass rate and rank-order agreement on that stage's specific validation kernels (as named above),
  not a proof — this is calibration work correcting an empirical model, not specification work.
- Reference-ingestion follow-through: if the licensing determination from F2 permits it, cite Intel's
  Optimization Reference Manual, Agner Fog's tables, or uops.info (per A0's "References:" line) as
  corroborating evidence alongside the actually-measured numbers — measurement is the primary source
  of truth per this project's differential-validation discipline, but citing an ingested public source
  where available strengthens the calibration file's provenance story.
- Do not silently skip a stage or reorder them without documenting why in this file's Notes — the
  staging order is deliberate (see Context above) and downstream consumers (F4, F6) may depend on
  knowing which stages have actually landed.

## Pointers

- `Gasm/Targets/X86_64/Uop.lean:47-53` (`X86_64Uop`, including the currently-dead
  `reciprocalThroughput` field at line 52 — see MODEL_DEBT §A3, adjacent debt this task may touch),
  `:57-68` (`MicroarchProfile`), `:72-127` (`goldenCoveProfile`/`skylakeProfile`/`zen4Profile`/
  optimistic profile definitions — note per §A3 these currently differ only in dispatch width, port
  count, and mispredict penalty; stage 2's dependency-chain work and stage 4's hierarchy work are
  exactly what would let these profiles diverge meaningfully).
- `Gasm/Targets/X86_64/Performance.lean:62-72` (`computePortPressure`), `:76-96`
  (`computeCycleBounds` — the central function every stage of this task modifies), `:88`
  (`intDiv` filter, the only current path by which `latencyCycles` enters nominal cost), `:92`
  (`maxCycles`, the fully-serial-sum line stage 2 fixes), `:93-94` (unconditional mispredict-penalty
  line stage 3 fixes), `:100-141` (`computeTMAM` — out of scope per MODEL_DEBT §A6, do not calibrate).
- `Gasm/Targets/X86_64/Instructions/Shift.lean:146,174` (SHL/SHR r64,CL uop count — stage 1 target).
- `Gasm/Targets/X86_64/Instructions/Div.lean:29,37,43-49` (DIV r64 uop count/latency — stage 1
  target; lines 29/37 are also the *only* two `faulted := true` sites in the entire tree per
  MODEL_DEBT §B3, worth being aware of if this task's measurement kernels include DIV).
- `Gasm/Targets/X86_64/Instructions/Mov.lean:380,477,514`, `Pop.lean:35`, `Ret.lean:25`,
  `Call.lean:29` (the flat `latencyCycles := 4` load-cost sites stage 4 addresses).
- `Gasm/Targets/X86_64/Instructions/Cmov.lean` (the branchless-decode side of stage 3's canonical
  validation pair).
- MODEL_DEBT.md §A0, §A1, §A3, §A4, §A8 (all quoted above), TOP-10 table rows 3, 5, 6, 7.
- `docs/VISION.md` §5 ("monotonically faithful").
- `docs/tasks/F1-rdtsc-harness.md` (the harness this task's every validation step runs through),
  `docs/tasks/F2-calibration-data-governance.md` (the mechanism every corrected coefficient this task
  produces must be governed by).
- `docs/adr/0006-performance-model-as-strategic-asset.md` (D5).

## Notes

- 2026-08-27: priority 7.5 — staged model calibration vs silicon is the direct consumer of F1's harness and F2's governance policy — where MODEL_DEBT A1/A4/A8 actually get measured.

_(none yet — first entries append here as work begins; this is Law-5-class performance-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
