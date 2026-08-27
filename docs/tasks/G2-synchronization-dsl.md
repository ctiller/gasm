---
id: G2
title: Synchronization DSL design (Vulkan memory model, happens-before, RAW)
status: ready
blocked_on: ""
after: [G1]
related: []
bar: ""
track: graphics
priority: 7.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G2: Synchronization DSL design (Vulkan memory model, happens-before, RAW)

## Context

`GRAPHICS_PREBUILD_AUDIT.md` §1 (Law 5 stop-and-design backlog) lists "GPU observation &
synchronization model" as item 4 and calls it, verbatim, **"the single largest undesigned
item"** in the entire graphics pre-build backlog. This task is that item. It is
deliberately sequenced `after: [G1]` only — it does not wait on G3/G4/G5/G6 — because the
audit's ranked amendment #3 (§9) puts it ahead of the FP-determinism, harness, and
validator work: without a sound sync model, nothing dispatched against a GPU buffer can be
said to race-free, so every later design (G5's validator, G6's capability model, G7's
Spike 6 implementation) needs this one settled first, or needs to explicitly punt on
synchronization in a way that would just move this debt downstream.

### What is currently wrong, quoted exactly

`docs/TARGETS/SPIRV_VULKAN.md:67` states: "In Vulkan, issuing a compute dispatch or draw
command before previous write hazards are flushed produces undefined GPU behavior. `gasm`
requires formal proof of `ValidBarrierTransition` before dispatches, preventing
Write-After-Read (WAR) and Write-After-Write (WAW) pipeline hazards." The audit's §2
(observation standard mapping) diagnoses the defect precisely: "`SPIRV_VULKAN.md:65-67`
models barriers as a resource-layout FSM claiming WAR/WAW prevention — **RAW is
omitted** (Spike 6's critical hazard: shader store → transfer read), and a layout FSM
will 'prove' a barrier correct with an empty `srcAccessMask` (the classic real bug)." This
is not a hypothetical gap: Spike 6's entire readback path is exactly a shader-store →
transfer-read dependency, i.e. the one hazard class the current doc's model cannot even
state, let alone prove absent.

### The proposed fix, quoted exactly

Audit §2 again: "The right shape: Vulkan's own memory model — synchronizes-with /
happens-before / availability+visibility (`appendix_b` §§367, 481, 545, 563) mapped onto
the repo's VectorClock machinery. **vkQueueSubmit = host→queue edge; fence =
queue→host; semaphores = queue→queue; barriers = intra-queue with availability/visibility.**
GPU work is where the dormant causal machinery becomes load-bearing FIRST — earlier than
threading." Audit §9 ranked amendment #3 restates the deliverable: "Author the GPU sync
model on Vulkan's memory model — synchronizes-with edges in `canonicalizeTrace`,
availability/visibility, **add RAW**. (`SYSTEM_EFFECTS` §6.3-6.4.)"

The "dormant causal machinery" referred to is real and already in the tree, unused:
`Gasm/Core/Types.lean:32-47` defines `VectorClock`, `VectorClock.happensBefore`,
`VectorClock.join`, and `VectorClock.tick`; `docs/OBLIGATIONS_AND_CAUSALITY.md` §3
documents the same machinery and its "synchronizes-with" edge concept for CPU threads
(lock release/acquire). `docs/SYSTEM_EFFECTS.md:225,227` already commits the project to a
"causally-ordered event set... stamped with its position in the happens-after partial
order (vector clocks per `docs/OBLIGATIONS_AND_CAUSALITY.md`)" as the canonical trace
representation once concurrency lands — this task is the GPU instantiation of that
already-ratified representation, arriving before the first CPU-threading spike, exactly as
the audit predicts.

### Why this is a DSL, not a per-spike proof (Law 5 / VISION §4 / D11)

`docs/VISION.md` §4 states the operating rule directly: "anywhere there is a population of
artifacts — even a closed population, even a population of one — reach for a DSL... A
closed population gets exhaustive language-level theorems." The command-buffer recording
sequence (`vkCmdDispatch`, `vkCmdCopyBuffer`, `vkCmdPipelineBarrier`, `vkQueueSubmit`,
fence/semaphore waits) is exactly such a closed population. `docs/adr/0011` (already
ratified, read for consistency only — do not edit it) names this task explicitly: "a
**synchronization DSL** (race-freedom/happens-before soundness proven in total over the
command-stream language, replacing the layout-FSM approach the audit flagged...)." The
deliverable is therefore total theorems about the command language — race-freedom and
happens-before soundness proven once, for every well-typed command sequence — not a
per-shader or per-dispatch proof obligation. This is the D11 DSL-as-proof-leverage pattern
(`docs/VISION.md` §4) applied to the GPU command stream, mirroring how G3 applies it to
the shader kernel language and G5 applies it to the SPIR-V binary encoding.

### Relationship to G6 and downstream tasks

G6 (Vulkan host model + capability mapping) is sequenced `after: [G2, PA4]` because the
capability model's fence-guarded release obligations (`MustNotFree until fence signaled`)
are only sound once this task's fence = queue→host edge exists to reason about "signaled"
formally. G5's grammar/validator work and G7's Spike 6 implementation both depend
transitively on this task through G6/G3 needing it settled. G9 (Spike 7) reuses this task's
host+device-queue-as-two-agents framing directly (see G9's own file) — audit §6 notes that
framing "applies at Spike 6 already," i.e. this task's synchronization model, not a later
one, is what G9's multi-loop composition builds on.

## Deliverables & acceptance criteria

- A design document (path TBD under `docs/`, e.g. `docs/GRAPHICS_SYNC.md` or a section of
  the reworked `docs/TARGETS/SPIRV_VULKAN.md` — the reviewing fresh agent should confirm
  placement) stating: the GPU synchronizes-with / happens-before / availability+visibility
  model, with the four edge mappings quoted above (`vkQueueSubmit`, fence, semaphores,
  barriers) stated as formal relations over `VectorClock`/`canonicalizeTrace`-shaped
  structures; and a RAW (Read-After-Write) hazard clause alongside the existing WAR/WAW
  claims, closing the gap the audit identifies at `SPIRV_VULKAN.md:65-67`.
- Total theorems over the command-stream DSL: race-freedom (no unsynchronized
  read/write or write/write pair on overlapping GPU memory ranges without an intervening
  happens-before edge) and a soundness statement connecting `ValidBarrierTransition`-style
  typestate proofs to the actual availability/visibility semantics in `references/vulkan`
  `appendix_b__memory_model.md` (§§367, 481, 545, 563 per the audit — confirm exact
  section numbers against the vendored file when authoring, since the audit's citation
  gives paragraph anchors from the spec, not this repo's file line numbers).
- Explicit rejection criterion: the design must state what an *invalid* barrier looks like
  (e.g. a `vkCmdPipelineBarrier` with an empty `srcAccessMask` guarding a shader-store →
  transfer-read dependency) and show the DSL's typestate makes that case unconstructible —
  this is the concrete "classic real bug" the audit calls out, and the design review must
  verify the DSL actually excludes it, not just declares an intent to.
- Per Law 13(4): state what differential/control-vector evidence downstream implementation
  (G7) will need to produce against this design once built — at minimum, a positive case
  (a correctly-barriered store→read dependency validates), a negative case (the
  empty-`srcAccessMask` case above must be rejected at construction, not merely flagged at
  runtime), and a case exercising the RAW hazard specifically, since that is the hazard the
  current doc omits and the one Spike 6's readback path actually exercises.
- Since this is Law-5-class new model/DSL design work, the design doc must be authored,
  then reviewed by a fresh agent with no access to this task's authoring session, before
  `design_review` is set to `"approved <date>"` and before any Lean implementation cites
  it. Do not waive review on this track — see the Notes-convention rationale below.

## Pointers

- `docs/TARGETS/SPIRV_VULKAN.md:65-67` (the current WAR/WAW-only layout-FSM claim to be
  replaced/extended) — grep-verified: line 67 reads "`gasm` requires formal proof of
  `ValidBarrierTransition` before dispatches, preventing Write-After-Read (WAR) and
  Write-After-Write (WAW) pipeline hazards" (note: despite the "WAR" label the text and the
  audit agree RAW is what's actually missing from the *model*, not merely mislabeled here).
- `GRAPHICS_PREBUILD_AUDIT.md` §1 item 4, §2 (full paragraph on sync), §9 ranked amendment
  #3 — read in full; this task file's Context section quotes but does not exhaust it.
- `Gasm/Core/Types.lean:32-47` — `VectorClock`, `VectorClock.happensBefore`,
  `VectorClock.join`, `VectorClock.tick` (grep-verified present, currently unused by any
  graphics code since none exists yet).
- `docs/OBLIGATIONS_AND_CAUSALITY.md` §3 (Monotonic Causality & Vector Clocks) and §3.1
  (Inter-Thread Causal Handover & Synchronizes-With) — the CPU-side precedent this task
  extends to the GPU queue/host relationship.
- `docs/SYSTEM_EFFECTS.md:225,227` — the ratified causally-ordered-event-set trace
  representation this task's GPU edges must slot into.
- `docs/VISION.md` §4 (DSL-as-proof-leverage, D11) — the justification for treating this as
  a total-theorem-over-a-language design rather than a per-program proof obligation.
- `references/vulkan/appendix_b__memory_model.md`, `references/vulkan/ch_07_synchronization_and_cache_control.md`
  (grep-verified present in `references/vulkan/`) — the Law 4 ground truth for the
  synchronizes-with/happens-before/availability/visibility formalism.
- `docs/adr/0011-dsls-as-unit-of-proof-leverage.md` (read-only; another agent owns this
  file) — already names "a synchronization DSL" as one of two mandated graphics DSLs,
  confirming this task's framing is consistent with ratified project direction.
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing), so all pointers above are doc-only; this
  design will eventually populate a location under `Gasm/Targets/` (exact module name to be
  decided during authoring, consistent with G1's housekeeping fix resolving the
  `Gasm.Targets.Spirv` vs `Gasm/SPIRV/` naming drift to the real `Gasm/Targets/*` convention).

## Notes

- 2026-08-27: priority 7.5 — synchronization DSL design (Vulkan memory model / happens-before) gates G5 and G6 — a core graphics-track chokepoint.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_
