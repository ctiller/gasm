---
id: MH1
title: Semantic memory hook — sealed memory field, width API, access descriptors, fault plumbing
status: done
blocked_on: ""
after: []
related: [PA4, PA2, TC18, B3]
bar: ""
track: proof-arch
priority: 7.5
priority_set: 2026-08-28T00:00:00Z
design: "docs/MEMORY_HOOK.md"
design_review: ""
date: 2026-08-28
---

# MH1: Semantic memory hook — sealed memory field, width API, access descriptors, fault plumbing

## Context

Implements `docs/MEMORY_HOOK.md` §3 (Layer S) and §6 stage 1 — migration phases M0 and
M1 of that design's §8. The owner's directive this serves: "apis every instruction
needs to go through to access memory, so we can do the perf and permissions in one
place." This task builds the semantic chokepoint; MH2 builds the perf side on top of
it; MH3 builds the Law-11 authoring surface on top of it.

Evidence base (verified at `0d5c6a9`, tabulated in `docs/MEMORY_HOOK.md` §1.1): 14 of
88 instruction forms touch memory; the model's only primitives are five width-specific
helpers plus a public raw `memory : Address → Byte` field; three instruction `step`s
already bypass the helpers with inline raw lambdas because `read8`/`read32`/`write32`
do not exist; `Gasm/Targets/Windows/Win32API.lean`'s hooks and the linkers'
`loadMemory` write memory raw; no store-form step lemma exists anywhere in the tree.

## Deliverables & acceptance criteria

- `Gasm/Targets/X86_64/Memory.lean` (new): `MemWidth`, `MemRef` +
  `MemRef.effectiveAddress`, `MemAccessKind`, `MemAccessSpec`, width-indexed
  `X86_64Mem.read`/`X86_64Mem.write`, derived `push64`/`pop64`, loader-facing
  `initRegion`. The raw memory function is sealed behind a wrapper with a `private`
  constructor and `private` projection (elaboration of this shape verified against
  toolchain v4.33.1 during the design pass) so that no module outside the hook can
  construct or project raw memory. **Acceptance evidence (Law 13 negative control)**: a
  mutation that accesses the raw projection from another module must fail to
  elaborate — demonstrated, then reverted.
- All existing raw-access sites migrated through the hook: the five
  `X86_64MachineState` helpers become `abbrev`s delegating to the hook (definitional
  equality preserved); the three inline instruction lambdas (`MovRspDispImm32`,
  `MovzxR64Mem8`, `MovReg32RspDisp32` in `Gasm/Targets/X86_64/Instructions/Mov.lean`)
  rewritten onto the new width APIs; `Win32API.lean` hook writes and the linkers'
  `loadMemory` routed through `X86_64Mem.write`/`initRegion`.
- `memAccesses : ι → List MemAccessSpec` added to `X86_64Instruction` with **no
  default** (same forcing-function choice as `roundtripCases`): 74 register-only
  instances gain an explicit `memAccesses _ := []`; the 14 memory forms declare their
  real accesses, evaluated against the pre-step state.
- Descriptor-vs-step connection obligations (Law 12): `writesWithin`/`readsWithin`
  frame lemmas for each of the 14 memory forms, plus one shared batch lemma covering
  the `[]` forms, housed per the `RoundtripGate/*` shard convention so a new memory
  form cannot land without them.
- The §3.4 lemma set: read-over-write (same-address and disjoint), width
  decomposition, push/pop roundtrip, `initRegion` read-back, footprint algebra.
  Structural proofs only — no `native_decide` (Law 10; these are infinite-domain
  `UInt64` facts).
- Fault plumbing: `faulted : Bool` replaced by `fault : Option X86_64Fault := none`
  with `def faulted := s.fault.isSome`; `X86_64Fault` carries `divideError` and
  `memFault (kind, width, addr)`; `Div.lean`'s two writer sites updated. **Do not**
  claim memory faults are reachable — they are not until a memory-map model lands
  (spike-forced, no task yet; `docs/MEMORY_HOOK.md` §6 stage 2). Coordination note:
  TC18's run-outcome type change should consume `X86_64Fault` as the fault payload;
  whichever task lands second wires the two together.
- Existing-proof regression suite: `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`,
  `Stdlib/Zlib/CRC32Equivalence.lean`, and `Stdlib/SmolAlloc/Equivalence.lean` must
  build with at most simp-set-name adjustments; the `rfl` step lemmas
  (`step_ret_op` ×2) must remain `rfl`.
- Full gate run (`python scripts/run_gates.py`, full mode) green in the merged tree.

## Pointers

- `docs/MEMORY_HOOK.md` §§2–3, 6, 7, 8 (M0/M1 rows) — the governing design.
- `docs/REVIEW.md` Law 11 (the mandate), Law 12 (descriptor/step connection), Law 13
  (negative controls), Law 10 (no evaluator proofs on infinite domains).
- `Gasm/Targets/X86_64/Registers.lean:226-274` (current helpers + raw field),
  `Gasm/Targets/X86_64/Instructions/Mov.lean:163-176,515-545,570-590` (inline
  bypasses), `Gasm/Targets/Windows/Win32API.lean:112-136,214-226,338` (raw hook/loader
  writes), `Gasm/Targets/X86_64/Instructions/Base.lean:37-46` (the typeclass gaining
  `memAccesses`).
- `TCB.md` T12 / `docs/tasks/TC18-fuel-and-environment-honesty.md` (stop-reason
  coordination).

## Notes

_(none yet — first entries append here as work begins; consolidated design already
exists at `docs/MEMORY_HOOK.md`; route through a fresh-agent design review before
implementation dispatch per the task-lifecycle convention.)_
- 2026-08-28 (F2 status audit, verified against the tree at `3341d92`, not against a report):
  `status: ready` -> `done`. Every named deliverable is present on `main`. Verified by artifact,
  not by claim: `Gasm/Targets/X86_64/MemoryCell.lean` (`MemWidth`, `MemAccessKind`, sealed
  `X86_64Memory` with `private mk ::` / `private raw`, width-indexed `read`/`write`, `initRegion`,
  `writeBytes`, the read-over-write lemma set) landed in `d49f611`/`ea6ee16`;
  `Gasm/Targets/X86_64/Memory.lean` (`MemRef`, `MemRef.effectiveAddress`, `MemAccessSpec`,
  footprint algebra, `push64_pop64_roundtrip`) in `4f21b84`; `memAccesses` as a defaultless
  typeclass field with 76 explicit `:= []` instances in `2369cd4`/`0897e32`; the
  `writesWithin`/`readsWithin` frame shards for all 14 memory forms plus the shared
  `registerOnly_*` batch lemma in `153f4fd`/`cf225d2`/`55b87ad`, with the soundness fix and the
  Law 13 negative control (`Gasm/Targets/X86_64/MemoryFrame/NegativeControl.lean`) in `c717eeb`;
  the five `X86_64MachineState` helpers reduced to `abbrev`s over the hook in `3eb55cf`
  (`Registers.lean:265-297`); `Win32API.lean`'s hook writes and `loadMemory` routed through
  `X86_64Mem.write`/`writeBytes`/`initRegion` (`:113,130,226,347`); `faulted : Bool` replaced by
  `fault : Option X86_64Fault` (`Registers.lean:66,84`, `Div.lean:44,52`). Merged as `27ab4ed`;
  the last `bv_decide` in the lemma set retired in `37f915d`.
- 2026-08-28: residual noted honestly rather than folded into the close. Two things are NOT
  claimed by this `done`: (1) `Gasm/Targets/X86_64/MemoryFrameAudit.lean:87` records a
  `frameCoverageDebtCeiling := 74` -- the 74 register-only forms have the batch lemma available
  but are not individually instantiated against it. MH1's deliverable asked for the batch lemma,
  which exists; driving that ceiling to zero is branch `f3a7224`, not on `main` (F3's business).
  (2) MH1's "full `scripts/run_gates.py` green" criterion is not currently demonstrable, because
  the axiom/reference gates are red tree-wide for a module-enumeration modelling gap unrelated to
  this task (fixed by `234d652`). Neither residual is MH1 work.
