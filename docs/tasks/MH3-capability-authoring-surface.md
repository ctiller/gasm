---
id: MH3
title: Capability authoring surface v1 — checked programs, erasure, bypass ledger, pathfinder routine
status: ready
blocked_on: ""
after: [MH1]
related: [PA4, PA2, PA1, N8]
bar: ""
track: proof-arch
priority: 7.2
priority_set: 2026-08-28T00:00:00Z
design: "docs/MEMORY_HOOK.md"
design_review: ""
date: 2026-08-28
---

# MH3: Capability authoring surface v1 — checked programs, erasure, bypass ledger, pathfinder routine

## Context

Implements `docs/MEMORY_HOOK.md` §4 (Layer A) — migration phase M3. This is Law 11's
fail-to-assemble mechanism and the "instruction-level obligation shape"
`docs/X86_ISA_EXPANSION_PREREQUISITES.md` P2 requires before memory-operand
instructions are mass-authored: how a memory-operand instruction carries its
capability obligation, what elaboration checks, and what failing-to-assemble looks
like — exercised on at least one real routine end-to-end.

Scope boundary with PA4: this task builds the surface and proves it on one pathfinder
routine; PA4 remains the tree-wide migration epic (new/small modules first,
`Stdlib/Zlib/X86_64.lean` last, per its ratified ordering) and consumes this task's
output as the migration-plan design input its own deliverables call for.

**Owner ruling required before implementation**: `docs/MEMORY_HOOK.md` §10 Q1 (v1
obligation strength — entry-anchored frames with invariant-discharged dynamic bounds
vs full flow-sensitive typestate). Implementation must not be dispatched until Q1 is
answered; the design recommends the former.

## Deliverables & acceptance criteria

- `RegionSpec`/`Frame`/`AccessOK` and the checked-program type: memory-operand
  constructors demand a capability citation plus an in-bounds proof; the
  literal-displacement case discharges via a `decide`/`omega` auto-param (Law 10
  rung 2 — kernel-checked, no allowlist entry); the computed-address case takes an
  explicit invariant-derived proof term. **Acceptance evidence (Law 13)**: a
  literal-overrun mutation (e.g. `[rsp + 4096]` store against a 4096-byte frame) and
  an omitted-proof mutation must both fail to elaborate — demonstrated, then reverted.
- Backing in Core: frames connect to `MemoryPerm`/`DisjointTokens`
  (`Gasm/Core/Permissions.lean`) so the dormant capability machinery gains real,
  semantically-invoked call sites (Law 8 — no decoration; the tokens must appear in
  the discharged obligations, not alongside them).
- `erase : CheckedProgram Γ → List SymbolicInstr` with encoding unchanged, so the
  assembler/linker/emitter pipeline is untouched (zero-cost proof erasure).
- The per-routine `MemSafe` soundness shape (`docs/MEMORY_HOOK.md` §4.4): carried
  obligations + routine precondition imply dynamic footprint ⊆ granted footprint,
  built on MH1's frame lemmas. Proven for the pathfinder routine; stated as the shape
  PA4's migrations instantiate.
- Bypass ledger + gate: `scripts/mem_bypass_allowlist.txt` (5-field `::`-format)
  seeded with the complete current raw-authoring population; a build-failing check
  that flags memory-operand smart-constructor use (enumerated from the registry's
  memory forms, not hand-listed) outside the ledger and designated infrastructure
  modules; entries counted and printed every run; ratchet — entries may only be
  removed. **Acceptance evidence (Law 13 negative control)**: a mutation adding a raw
  memory-operand use to an unledgered module must fail the gate; demonstrated, then
  reverted.
- One real routine migrated end-to-end (recommended: a small `Stdlib/SmolAlloc`
  routine or the `crc32SymbolicProgram` frame PA1's Theorem 3 already characterized),
  with its `MemSafe` theorem discharged — the P2 "exercised on one real instruction
  family end-to-end" bar.
- Read-binder composition demonstrated in statement form: the §4.6 composed obligation
  (write-safety inside the read quantifier) stated against the pathfinder or a Spike-4
  fragment, showing the `requested > capacity` case is undischargeable. Statement +
  discussion suffice; closing Spike 4 itself remains N8/PA17 scope.
- Fresh-agent design review before implementation dispatch (PA4's own convention: "do
  not waive review on this track").

## Pointers

- `docs/MEMORY_HOOK.md` §4, §8 (M3 row), §9, §10 Q1 — the governing design.
- `docs/REVIEW.md` Law 11 (the bar), Law 8, Law 10, Law 13.
- `docs/READ_BINDER_CONTRACT.md` §5 (the two-bounds composition this must not
  collapse); `docs/tasks/N8-spike4-stack-buffer-overflow.md` (the bug class the
  composed obligation makes undischargeable).
- `docs/tasks/PA4-capability-adoption.md` (the migration epic this feeds; its PA1
  Theorem-3 pointer is the pathfinder's frame-condition precedent);
  `docs/tasks/PA2-step-lemma-composition-design.md` (the typestate upgrade path — §4.3
  of the design states the compatibility contract).
- `Gasm/Core/Permissions.lean`, `Gasm/Core/BlockM.lean`, `Gasm/Core/Obligations.lean`
  (the dormant machinery gaining call sites);
  `Gasm/Targets/X86_64/Assembler.lean:43-73` (`SymbolicInstr`, the erasure target);
  `Stdlib/Zlib/X86_64.lean` (the eventual largest migration target — PA4's, not this
  task's).

## Notes

_(none yet — first entries append here as work begins; consolidated design already
exists at `docs/MEMORY_HOOK.md`; owner ruling on §10 Q1 and a fresh-agent design
review are both required before implementation dispatch.)_
