# 0013. TCB Ledger: Everything Trusted-but-Unprovable Gets a Fuzzer

## Status

Accepted, 2026-08-27. (PLAN.md D13.)

## Context

The repository's trust story ([`0001`](0001-vision-and-insights.md),
[`0003`](0003-universal-equivalence-via-modular-decomposition.md)) is precise about what
proofs cover, but the self-audit (PLAN.md Gaps register) surfaced a growing list of
things that are trusted *without* being either proven or discovered as gaps organically:
the Lean kernel/toolchain, elaboration-time metaprograms (the registry `run_cmd` audit is
itself trusted code), both gate tools, the PE emitter (everything past
`serializeInstructions` is validated only by spike executables running — the last-mile
gap), unpinned oracle environment versions (node/python/NASM — drift silently changes
gate results), the hand-written machine code inside `HardwareHarness`, and calibration
data ([`0006`](0006-performance-model-as-strategic-asset.md)'s E5). Trust boundaries
discovered piecemeal, after the fact, is itself the failure mode this decision closes.

## Decision

Maintain `TCB.md` as an explicit, chosen ledger of everything in the trusted computing
base that is trusted-but-unprovable (environment, hardware, APIs, tools) — trust is
*chosen*, not discovered. Every ledger entry gets a differential fuzzer validating the
project's model of it, following the same discipline as the ISA/Wasm/OS model harnesses
(VISION §3.2): positive and negative control vectors, fail-closed on an absent oracle
(Law 13, [`0009`](0009-findings-become-gates.md)).

## Consequences

`TC7` (TASKS.md) tracks the TCB research and ledger population; `TC8` tracks the
buildout of one validation harness per TCB item — emitter/loader differential validation,
references-pipeline verification, oracle version pinning, harness self-hosting. Nothing
enters the TCB silently: a new tool or dependency added to the build or gate pipeline
obligates a `TCB.md` entry and, per this decision, a validator for it.

## Provenance

Owner-stated. The owner's own words: "let's establish a ledger (opus agent researches the
debts, you fold them into the plan -- other debts should be in the plan too) -- and
everything we trust that we can't prove -- environment, hardware, apis, etc -- get a
fuzzer that validates our model." The ledger's specific structure (per-item severity,
shrinkability, differential-fuzzer obligation) and the "trust is chosen, not discovered"
framing are the coordinator's elaboration of that directive.
