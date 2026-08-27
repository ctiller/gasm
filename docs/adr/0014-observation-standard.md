# 0014. Observation Standard Ratified

## Status

Accepted, 2026-08-27, with Craig-ratified refinements the same date. (PLAN.md, Phase 4.)

## Context

Every equivalence proof in the codebase needs a single, non-negotiable answer to "what
counts as observable," stated once, so that no individual proof or spec can quietly
invent a laxer or stricter observation set of its own. Left implicit, this had already
drifted: the current `traceEquivalence` implementation compares raw, uncoalesced traces,
making internal chunking accidentally observable — a violation of the standard this
decision ratifies, tracked as an implementation gap to close before the zlib optimization
epic. The graphics pre-build audit independently found the same gap class one domain
over: `GpuEvent` mixing audit-trace and contract-trace events in one stream, and a
readback event recording that a copy happened without recording what came back — the
VISION §2 canned-output exhibit rebuilt in a new domain.

## Decision

Ratify [`docs/EQUIVALENCE_PROOFS.md` §1.1](../EQUIVALENCE_PROOFS.md#11-the-definition-of-observation-canonical-equivalence-standard)
as the canonical, binding definition of observation for every equivalence obligation in
`gasm`: equivalence both ways (equality for deterministic specs; refinement+liveness for
nondeterministic specs, with non-terminating reactive loops enforced as mandatory
inner/outer proof pairs); observables are syscall-boundary effects up to the declared
coalescing congruence, plus contract-footprint memory; the capability frame ([`0004`](0004-adopt-core-capability-machinery-for-memory-safety.md))
*is* the observability boundary; internal structures are excluded; timing is never
observable; and the audit trace (`VirtualAlloc` and peers) is not the contract trace.
Concretely, the coalescing congruence itself is ratified as living in the effects
library, once per effect, in
[`docs/SYSTEM_EFFECTS.md` §6](../SYSTEM_EFFECTS.md#6-the-observation-algebra-canonical-coalescing-congruence),
via a `canonicalizeTrace` normal form carrying happens-after tracking from day one
([§6.3](../SYSTEM_EFFECTS.md#63-canonical-trace-normal-form-with-happens-after-tracking)),
and input events (`recv`, reads, `accept`) are ratified as first-class contract-trace
events — causal anchors and coalescing barriers — per
[§6.4](../SYSTEM_EFFECTS.md#64-input-events-are-causal-anchors-and-coalescing-barriers-protocol-causality).

## Consequences

Building `canonicalizeTrace` and migrating every equivalence obligation onto it, ahead of
the zlib optimization epic, is now required work, not optional cleanup — raw-trace
equality is prohibited once it lands. The `FileSystemEvent`/`TraceM` model's silent
omission of read events is reclassified from a minor gap to a defect against this
standard and is fixed alongside the canonicalization work. Threading/multiprocessing is
ratified in advance to generalize this to one inner/outer pair *per reactive loop* plus
explicit cross-loop composition obligations (deadlock/livelock freedom, stated fairness)
confined to the causal layer — full design still gated by Law 5 before the first threaded
spike. The graphics audit's readback-payload and audit/contract-trace-split findings
(`GRAPHICS_PREBUILD_AUDIT.md` §2) are direct instances of this standard being applied to
a new target family, not a separate decision.

## Provenance

Mixed, and the pieces should not be read as equally owner-attributed. This ADR's title
calls the refinements below "Craig-ratified" as a block; the transcript supports that for
some clauses and not for others.

- **Owner-stated**, as direct "yes" responses to a numbered set of coordinator questions:
  the inner/outer proof-pair requirement for infinite loops — "yes -- though i'd like to
  find a way to enforce inner/outer proofs for infinite loops: progress/liveness for the
  outer, both ways for the deterministic inner"; the coalescing congruence living in the
  library/target spec — "yes, and this should live in the library/target spec"; and
  audit-obligations attaching per-target rather than portably — "i agree, but possibly
  more needed: VirtualAlloc is a windows implementation requirement; linux will have
  something else -- i think we've got this spelled with a typeclass now, we should be
  precise."
- **Owner-stated, tentatively** — the basic multi-loop-on-threading point and the
  happens-after tracking idea, both hedged in the owner's own words: "we'll need to
  adjust when we build threading/multiprocessing -- we will have more than one infinite
  loop in a typical program," and "we should probably have a happens-after tracking in
  the trace normalization." Note the hedge: "probably."
- **Coordinator-decided**, filed under "Craig additions" in `PLAN.md` but not owner
  utterances: the specific composition obligations for concurrency — deadlock/livelock
  freedom at declared synchronization points and explicit fairness assumptions — go
  beyond what the owner stated (he named only that there would be more than one loop);
  and `canonicalizeTrace` "carrying happens-after tracking from day one" upgrades the
  owner's hedged "probably" into a ratified certainty he did not state. Both are
  reasonable engineering elaborations, but they are the coordinator's, not the owner's,
  and `PLAN.md`'s "Craig additions" heading over this material has been corrected
  accordingly.
