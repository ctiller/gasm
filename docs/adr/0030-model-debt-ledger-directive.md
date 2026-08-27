# 0030. Model-Debt Ledger Directive

## Status

Accepted, 2026-08-27. (PLAN.md "Model debt ledger.")

## Context

[`0013`](0013-tcb-ledger-and-trust-implies-fuzzer.md) establishes `TCB.md` as the ledger
of everything trusted-but-unprovable — tools, toolchains, environments. It does not cover
a distinct and asymmetric category: what the machine/OS *models themselves* are known to
omit or simplify, for both performance (cache hierarchy, store buffers, branch
prediction, TLB, frontend limits — anything that could mis-rank an agent's optimization
choice) and correctness (TSO/atomics, interrupts, FPU/SSE state, partial/short reads,
Wasm float/`br_table`/limits semantics). Without a deliberate ledger, this class of gap
is discovered piecemeal, the same failure mode `TCB.md` was created to close for the
trust-boundary side.

## Decision

The owner's own words: "also for the plan (maybe kick off an opus researcher now to
flesh this out): what's missing from the machine model (memory latency? cache?) for
performance, for correctness (i'm guessing things like serial io and the like) -- no need
to build yet, but we should have a debt ledger." A related, later scope addition
extended the same ledger to system-level placement questions: performance models for
GPU/PCIe transfer, disk, and network, in a common currency with CPU cycles, for answering
"is it better to run on CPU vs graphics hardware" — traced to the owner's own framing:
"at some point i want to start asking optimization questions around 'is it better to run
on cpu vs graphics hardware', and have a model able to answer -- including read backs
etc -- so we probably want some perf model of graphics hardware separately, and a model
of pci bandwidth baked in[;] similarly for large scale work we probably want a disk
performance model included, and a network."

## Consequences

`MODEL_DEBT.md` (repo root; migration to `docs/` tracked under
[`0027`](0027-planning-output-lives-under-docs.md)) is the deliverable: an inventory, not
a spec, of what the machine/OS models omit — per-item severity, forcing function,
validation strategy, and reference-ingestion status, with a top-10 priority table. Debt
is *chosen*, not discovered — the same principle [`0008`](0008-demand-driven-model-growth.md)
applies to model growth applies here to model gaps: known and tracked before it causes a
problem, rather than found reactively. Section E of the ledger (system-level
placement-cost models: PCIe transfer, GPU compute in a common currency with CPU cycles,
disk, network) is the direct consequence of the owner's CPU-vs-GPU framing, and connects
to the performance-model architecture ratified in [`0006`](0006-performance-model-as-strategic-asset.md).
No item in this ledger is built merely by being entered — entry is explicitly "no need to
build yet."

## Provenance

Owner-stated. Both quotes above are the owner's own words. The ledger's specific
structure (per-item severity/forcing-function/validation-strategy fields, the top-10
table) is the coordinator's design for satisfying the owner's directive, executed by an
opus researcher per the owner's own instruction.
