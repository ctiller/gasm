# 0019. Review Model and Spec Before Implementation

## Status

Accepted, 2026-08-27. (PLAN.md D14.)

## Context

The owner's own rationale for this discipline is temporal, not one of artifact size: get
the model and spec reviewed while the context needed to review them well is still small
and fresh, rather than after it has been displaced by everything that comes with
implementation. A design is also, incidentally, orders of magnitude smaller than the
implementation built from it — a design review reads pages, an implementation review
reads thousands of lines of generated assembly and proof, and a finding against an
unbuilt design costs nothing to apply where the same finding against shipped code costs a
fix cycle — and that size difference is real supporting rationale, but it is the
coordinator's restatement of the owner's point, not the point itself. This is not
hypothetical here: the graphics pre-build
audit reviewed `docs/GRAPHICS_ARCHITECTURE.md` and `docs/TARGETS/SPIRV_VULKAN.md` while
**zero graphics Lean code existed and no `REF:` cited either document**, and caught three
load-bearing defects that would otherwise have been discovered only after code was
written against them: a trace design that cannot observe the actually-rendered result
(`readbackPixels` carrying no pixel payload), a bit-exact cross-implementation equality
assumption the Vulkan specification itself prohibits, and a synchronization model built as
a resource-layout FSM that omits the RAW hazard class — see
[`GRAPHICS_PREBUILD_AUDIT.md` §2](../../GRAPHICS_PREBUILD_AUDIT.md#2-observation-standard-mapping).
This is also the shape the repair epic's own exit criterion already commits to: spec &
model review is something the project does; implementation review is something it trusts
mechanically.

## Decision

Models and specifications are built **and reviewed** — by fresh reviewer agents, against
the full set of ratified lenses (Laws, `docs/VISION.md`, `docs/EQUIVALENCE_PROOFS.md` §1.1,
`docs/SYSTEM_EFFECTS.md` §6) — **before** their implementation is dispatched. This
design-review stage is mandatory for every [Law 5](../REVIEW.md#law-5-the-stop-and-design-invariant)-class
task (new models, contracts, or law-shaped design work); implementation dispatch does not
proceed on a design that has not cleared it.

## Consequences

The task lifecycle gains a distinct design-review stage, tracked via the `design_review`
frontmatter field already present on task files (`docs/tasks/PA1-crc32-pathfinder.md`,
`docs/tasks/TC5-gate-runner.md`); the planned task-DAG checker (tracked as `TC13` in the
concurrent `docs/tasks` buildout) is expected to enforce it mechanically once it lands.
Implementation-stage review is expected to shrink toward mechanical-gate confirmation as
this stage absorbs more of the "are we even modeling the right thing" class of finding —
the same convergence [`0001`](0001-vision-and-insights.md) and
[`0009`](0009-findings-become-gates.md) already commit the project to. This decision and
the [BAR](0010-bar-triggered-deep-re-reviews.md) mechanism are complementary, not
redundant: BARs review accumulated *built* systems at DAG checkpoints, while design
review guards each individual *entry* into implementation before it happens. Ratified
alongside [`0018`](0018-task-notes-consolidate-to-design.md) as D14's second half.

## Provenance

Mixed. The owner's own words, and his own rationale: "one more discipline that will
probably pay off: get the model and the spec built and *REVIEWED* and only then build
them implementation (front load the review when the context is small)." His stated
reason is temporal — review while context is small — not that a design is a smaller
artifact than an implementation; this ADR's Context section previously restated the
rationale in artifact-size terms only, which is the coordinator's supporting argument, not
a paraphrase of what the owner said. Both are recorded above, attributed separately. The
graphics pre-build audit's specific findings, the `design`/`design_review` frontmatter
mechanics, and the "complementary to BARs" framing are the coordinator's elaboration.
