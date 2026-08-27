# 0006. Performance Model as a Strategic Asset

## Status

Accepted, 2026-08-27. (PLAN.md D5.)

## Context

The project's predecessor, `wsc`, carries a cautionary history directly relevant here:
its "PerfFuzzer" was self-consistency-only (no hardware comparison); actual
hardware-vs-model comparison was a manual one-off with RDTSC medians from standalone
Rust/C harnesses hand-transcribed as `Nat` literals into `Main.lean` — and visibly stale
(scalar and SIMD Mandelbrot both recorded as "8 cycles"). It was never wired into the
build. `MODEL_DEBT.md` [§E](../../MODEL_DEBT.md#e-system-level-transport-placement-cost-models)
generalizes the failure mode (E5): any measured-calibration-data model risks becoming "a
second wsc" without governance, and (E2) notes the codebase's current cost type,
`PerfCycleBounds`, is bare `Nat` cycles under an implicit, unnamed, single clock —
incomparable across devices and unstable under turbo/DVFS.

## Decision

Treat the performance model as strategic infrastructure, not an accessory, per
[`docs/VISION.md` §5](../VISION.md#5-performance-modeling-agents-as-the-optimizing-compiler):
a static, checked-in model lets agents optimize assembly without executing it. The
end-state is **parametric cost functions with concrete coefficients**
(`5·N² + 3·N + 293` cycles under a named microarchitectural profile), never bare
asymptotic classes, living on routine contracts and regression-gated like proofs. Costs
compose across devices/transports as **layered views** — native precision per system
(cycles, device ticks, latency+bandwidth terms) plus an explicit-conversion
system-architect view in µs/ms carried by named device profiles — rather than one
flattened unit system. The `wsc` recon's *technique* (CPUID+RDTSCP bracketing,
median-of-N, separate calibration-subtraction pass, range containment as the
faithfulness criterion) is adopted; its artifacts (benchmark files, hand-transcribed
constants) are not.

## Consequences

The performance model inherits the same differential-validation obligation as the
correctness models (VISION §3.2): monotonic faithfulness against real hardware, checked
by a dedicated perf fuzzer (TASKS.md F1/F3), not cycle-exactness. Calibration data
becomes a governed third reference class alongside vendored specs and generated code
(MODEL_DEBT E5): checked in, regenerable, provenance-stamped, never hand-edited. The
"zlib to infinity" optimization epic and the GPU/PCIe placement-cost work (MODEL_DEBT §E)
are both blocked on this decision landing first.

## Provenance

Mixed. The owner set both the sequencing and the source to revisit, in his own words:
"we should also expand the performance work (not now, after repair i expect) -- perform
big-O modelling, but with performance numbers baked in -- instead of saying its
O(N**2), say its 5*N**2 + 3*N +293 cycles" (the parametric-cost-function end-state is a
direct paraphrase of this), and separately: "perf: yes, it needs a fuzzer -- an earlier
spike on this work ([local path redacted]\wsc iirc) had this, we should bring it back." The
owner's directive was to *bring the fuzzer back*; the decision actually adopted, after
the wsc reconnaissance, departs from that instruction — it carries over the recon's
*technique* (CPUID+RDTSCP bracketing, median-of-N, calibration-subtraction, range
containment) and explicitly does not port wsc's artifacts (the benchmark files, the
hand-transcribed constants). That technique-not-artifacts departure was the coordinator's
synthesis of the reconnaissance findings, not a restatement of the owner's "bring it
back" — recorded here so the two are not conflated.
