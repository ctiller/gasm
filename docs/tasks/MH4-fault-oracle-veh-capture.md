---
id: MH4
title: Fault-oracle VEH capture — widen the hardware record to exception code, faulting address, and access kind
status: ready
blocked_on: ""
after: [MH1]
related: [TC18, TC9, F1]
bar: ""
track: proof-arch
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: "docs/BARE_METAL_VALIDATION.md"
design_review: ""
date: 2026-08-28
---

# MH4: Fault-oracle VEH capture — widen the hardware record to exception code, faulting address, and access kind

## Context

MH1 landed `X86_64Fault` (`divideError | memFault (kind, width, addr) | halted`) in
`Gasm/Targets/X86_64/Registers.lean`, replacing the one-bit `faulted` flag the TCB had
flagged as indistinguishable across stop reasons. But the hardware oracle still
observes exactly one bit: `HardwareHarness.lean`'s VEH handler writes `faulted := 1`
into byte 135 of the 136-byte record and discards the rest of the exception, and
`SemanticsFuzzer.lean` compares only `modelS.faulted != hwRes.faulted`.

**The model's fault taxonomy is now richer than the oracle's observation.** A model
that mislabels a #GP as a #DE, or reports the wrong faulting address, passes today's
differential. `docs/BARE_METAL_VALIDATION.md` §2.1 assesses the fix: the VEH already
receives everything needed and throws it away. At VEH entry, RCX points to
`EXCEPTION_POINTERS`; the handler currently reads only `[rcx+8]` (the CONTEXT). The
`EXCEPTION_RECORD` at `[rcx+0]` carries:

- `ExceptionCode` at offset 0 — `0xC0000094` (integer divide by zero, the model's
  `divideError`), `0xC0000005` (access violation, the model's `memFault`),
  `0xC000001D` (illegal instruction), `0xC0000096` (privileged instruction), etc.
- For access violations: `ExceptionInformation[0]` (offset 0x20 within the record's
  parameter array region) — 0 = read, 1 = write, 8 = DEP/execute — mapping to
  `MemAccessKind`; and `ExceptionInformation[1]` — the faulting virtual address,
  Windows' relay of CR2.

This is a userspace extension on the existing real-silicon path — the cheapest
sufficient observer for MH1's taxonomy. It is also the assessment's step 1, chosen
explicitly instead of a bare-metal investigative kernel (see the verdict and trigger
list in `docs/BARE_METAL_VALIDATION.md` §6/§8).

## Deliverables & acceptance criteria

- Extend the VEH handler's hand-assembled capture block in
  `HardwareHarness.lean` (`buildTestText`) to store, alongside the existing
  faulted byte: the 32-bit `ExceptionCode`, the 64-bit faulting address
  (`ExceptionInformation[1]`, zero when not an access violation), and the 64-bit
  access disposition (`ExceptionInformation[0]`). Extend the per-test record from
  136 bytes accordingly and update `decodeHardwareResult` and every size constant in
  lockstep (the record length appears in `buildTestText`, `emitNativeBatchTestExe`,
  and `runHardwareBatch`; TCB.md T10 already flags these hand-asserted constants —
  do not add another unchecked one, derive or cross-check them).
- Extend `HardwareExecutionResult` with a decoded fault field (e.g. an
  `Option`-shaped structure carrying code/kind/addr) — and per TCB.md T10's residual
  finding, do NOT let an `Inhabited` instance fabricate a plausible default that
  `getD` can reach.
- Extend `SemanticsFuzzer.lean`'s differential: when both sides fault, compare fault
  *identity* — model `divideError` must correspond to `0xC0000094`, model
  `memFault (kind, _, addr)` to `0xC0000005` with matching access kind and address.
  Width is deliberately excluded from the comparison: no hardware fault observation
  reports access width at any privilege level (it exists only in the instruction
  encoding), so a width diff would be the model diffed against itself.
- Extend `verifyHardwareOracleControls` with taxonomy controls, mirroring the
  existing positive/negative pattern: the existing `div rbx` (RBX=0) control must now
  decode as the divide code, and a new known-address access-violation control (e.g. a
  store to an unmapped fixed address) must decode as access-violation with the exact
  expected address and write disposition. Per Law 13, a capture path that cannot
  produce these must abort the run.
- Vacuity: the new comparisons fall under the existing TC17 floor machinery — a run
  in which no vector exercises the fault-identity path must be visible in the
  summary (report the count of fault-vectors exercised; do not silently report a
  taxonomy-green run that never decoded a fault).
- Gate evidence: `lake exe x86_fuzzer` green with the widened record on real
  hardware, including at least one instruction family whose fuzz states genuinely
  reach `memFault` (coordinate with MH1's access-descriptor work and Phase 3's
  scratch-region plan; if no in-tree family can yet fault on memory, the
  access-violation *control vector* is the minimum bar and the limitation must be
  stated in the run summary).

## Pointers

- `Gasm/Targets/X86_64/HardwareHarness.lean` — VEH handler bytes (`buildTestText`,
  the `mov byte ptr [rax+135], 1` capture this task widens), `decodeHardwareResult`
  (136-byte layout), `verifyHardwareOracleControls` (control-vector pattern to
  extend).
- `Gasm/Targets/X86_64/Registers.lean` — `X86_64Fault`, `MemAccessKind`,
  `X86_64MachineState.fault`.
- `Gasm/Targets/X86_64/SemanticsFuzzer.lean` — the `modelS.faulted != hwRes.faulted`
  comparison this task deepens.
- `docs/MEMORY_HOOK.md` §6 (faults and observability — the design MH1 implemented).
- `docs/BARE_METAL_VALIDATION.md` §2.1 (this task's design rationale and its
  relationship to the deferred investigative kernel), §8 trigger 5 (an MH4 finding
  that Windows' exception translation cannot distinguish a fault class that matters
  is a named trigger for the kernel task).
- `TCB.md` T10 (harness self-hosting debt and the `Inhabited` fabrication residual —
  constraints on how this task extends the record), T12 (the original
  indistinguishability defect).

## Notes

- 2026-08-28: created from the bare-metal investigative kernel assessment
  (`docs/BARE_METAL_VALIDATION.md`): chosen as the demanded, cheapest-sufficient
  observer for MH1's fault taxonomy, in place of building a kernel now.
