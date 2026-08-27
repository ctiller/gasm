---
id: G9
title: "Spike 7 design: windowed swapchain, multi-loop reactive contracts"
status: ready
blocked_on: ""
after: [G7, PA7]
related: []
bar: ""
track: graphics
priority: 6.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# G9: Spike 7 design — windowed swapchain, multi-loop reactive contracts

## Context

This task designs the reactive-loop contract for Spike 7 (interactive windowed
presentation), the last item on the graphics path's `TASKS.md` list. It is sequenced
`after: [G7, PA7]`: `after: G7` because Spike 7's swapchain loop is built on top of the same
device/queue/command-recording machinery Spike 6 exercises headlessly — G7 is where that
machinery first gets proven correct, and this task extends it to the windowed-presentation
case rather than re-deriving device/queue correctness from scratch; `after: PA7` because
PA7 (`VerifiedReactiveProgram` — inner/outer proof pairs) is the general reactive-loop
contract shape this task instantiates for the GPU present loop specifically. Consult PA7's
own `docs/tasks/` file if it exists by the time this task is picked up; otherwise treat
`docs/EQUIVALENCE_PROOFS.md` §1.1's third paragraph (quoted below) as PA7's substantive
content, since that paragraph is where `VerifiedReactiveProgram` is defined in this repo's
ratified documents.

Note that Spike 8/9 windowing prerequisites are explicitly out of scope for this design:
`GRAPHICS_PREBUILD_AUDIT.md` §1 items 8–9 name `docs/TARGETS/WIN32_WINDOWING.md` (not yet
authored; "nothing windowing is vendored") and a WSI/swapchain doc as blocking Spike 7
*additionally* to everything blocking Spike 6. This task designs the **reactive contract
shape** for the present loop; it does not itself ingest Win32 windowing references or
author the WSI doc — those remain open Law-4/Law-5 prerequisites for whichever task
actually implements Spike 7, separate from this task's contract design.

### The reactive contract shape (PA7 / EQUIVALENCE_PROOFS §1.1)

`docs/EQUIVALENCE_PROOFS.md` §1.1: "**Non-terminating programs (reactive loops) are
enforced as inner/outer proof pairs.** A program whose spec is an infinite service loop
(e.g. a server) carries a distinct contract type — `VerifiedReactiveProgram` — with two
*mandatory* proof fields, so neither half can be omitted: the **inner** obligation is
deterministic both-ways trace equality for one iteration (∀ request/session in the request
domain, the handler's contract trace equals the spec's), and the **outer** obligation is
progress/liveness (the loop always returns to its accept state, consumes every arriving
request, and never wedges)." For Spike 7, "one iteration" is one frame; the request domain
is the space of input events (window messages, resize events) a frame may consume.

### Why this applies to Spike 6 already, not just Spike 7

Audit §6 (Reactive contracts), quoted in full: "The present loop is a
`VerifiedReactiveProgram`: inner = per-frame deterministic equality for every input-event
sequence; outer = liveness. Complications: `vkAcquireNextImageKHR` returns a
nondeterministic image index and OUT_OF_DATE/SUBOPTIMAL on resize are spec-permitted — so
the outer obligation is refinement + liveness, with the recreate-swapchain path *inside*
the ∀ domain. **Host + device queue are two agents even single-threaded, so multi-loop
composition (deadlock-freedom of frames-in-flight fence/semaphore rings, explicit
fairness) applies at Spike 6 already.**" This last sentence is the reason this task exists
as a distinct design from G7 rather than being folded into it: the *multi-loop composition*
obligation (host loop + device queue as two independently-progressing agents, per
`docs/EQUIVALENCE_PROOFS.md` §1.1's concurrency-generalization paragraph: "a typical
program contains *several* reactive loops... plus **composition obligations** across
loops — absence of deadlock/livelock at the declared synchronization points, and any
fairness assumptions stated explicitly") is *already* present in G7's headless Spike 6,
because a single in-flight-fence-guarded submission is already a two-agent system. This
task's composition-obligation design should therefore be written so that G7 can adopt its
frames-in-flight-ring reasoning even though Spike 6 has no actual window or swapchain —
Spike 6 needs the deadlock-freedom argument for its (single) in-flight submission; Spike 7
needs it for a full frames-in-flight ring across multiple presented frames. Confirm during
authoring whether G7 should cite this task's design directly for that shared piece, or
whether the shared piece should be factored out into its own note — either is acceptable,
but the redundancy must not be silently duplicated per Law 12.

### Refinement + liveness, not equality, for the outer obligation

Per `docs/EQUIVALENCE_PROOFS.md` §1.1's nondeterministic-specification pattern: "For
**nondeterministic specifications** (permitted-behavior sets)... the obligation splits
into **refinement** (every machine behavior is spec-permitted) **plus progress/liveness**...
Demanding literal both-ways equality there is wrong." `vkAcquireNextImageKHR`'s
nondeterministic image index and the spec-permitted `OUT_OF_DATE`/`SUBOPTIMAL` resize
signals mean Spike 7's outer obligation cannot be plain trace equality — it must be exactly
this refinement + liveness shape, **with the recreate-swapchain path treated as inside the
∀ domain** (i.e. a correct Spike 7 program must handle every resize/out-of-date signal the
spec permits, not merely the steady-state no-resize case) rather than as an exceptional
case handled outside the proof.

### Windowed observability

Audit §6's closing sentence: "Windowed observability: defensible answer = **contract-trace
observables are the sequence of presented image contents** (validated headlessly via an
offscreen mirror), presentation itself audit-trace." This directly parallels G1's
contract/audit trace split for Spike 6: what actually gets shown on screen (the sequence of
presented image contents) is the contract-trace observable — validated without a real
display, via an offscreen mirror that captures what would have been presented — while the
mechanics of presentation itself (`vkQueuePresentKHR` calls, swapchain image acquisition
events) are audit trace, proven to occur (Law 8) but not part of the cross-run equivalence
obligation. This resolves the "how do you even observe a window" question the audit implies
is otherwise open: the answer is not to attempt to observe the literal display surface, but
to mirror presented contents offscreen and treat that mirror's sequence as the observable.

## Deliverables & acceptance criteria

- A design document instantiating `VerifiedReactiveProgram` (or its natural extension) for
  the Spike 7 present loop: inner obligation = per-frame deterministic trace equality for
  every input-event sequence a frame may receive (window messages, resize signals); outer
  obligation = refinement + liveness (not equality), explicitly covering the
  `vkAcquireNextImageKHR` nondeterministic-index case and the `OUT_OF_DATE`/`SUBOPTIMAL`
  resize case as in-domain behaviors the loop must handle, with the recreate-swapchain path
  proven correct as part of the ∀ domain rather than special-cased outside it.
- A multi-loop composition design covering deadlock-freedom of the frames-in-flight fence/
  semaphore ring (host loop and device queue as two independently-progressing agents, per
  the audit quote above) plus explicit fairness assumptions stated as part of the contract,
  per `docs/EQUIVALENCE_PROOFS.md` §1.1's composition-obligations clause — and an explicit
  note on whether/how this composition argument is shared with or duplicated from G7's
  Spike 6 in-flight-submission reasoning (Law 12: no silent unlinked duplication).
- The windowed-observability answer stated formally: contract-trace observables = the
  sequence of presented image contents, validated via an offscreen mirror; presentation
  mechanics (queue-present calls, acquisition events) = audit trace only, per Law 8 and
  consistent with G1's contract/audit split for Spike 6.
- An explicit scope boundary: this task does not ingest `references/` for Win32 windowing
  or author `docs/TARGETS/WIN32_WINDOWING.md` — those are separate, still-open Law-4/Law-5
  prerequisites (per `GRAPHICS_PREBUILD_AUDIT.md` §1 items 8–9) for whichever task actually
  implements Spike 7; this task's deliverable is the reactive-contract design only.
- Per Law 13(4): state the differential/control-vector evidence downstream Spike-7
  implementation will need — at minimum, a resize/out-of-date injection test proving the
  recreate-swapchain path is actually exercised and not merely assumed correct, and an
  offscreen-mirror validation harness proving the mirror's captured content sequence
  actually matches what a real swapchain would have presented (i.e. that the mirror itself
  is differentially validated, not asserted correct by construction).
- Law-5/Law-13 discipline: design doc authored, then routed through fresh-agent design
  review before `design_review` is marked approved and before any Lean cites it.

## Pointers

- `GRAPHICS_PREBUILD_AUDIT.md` §1 items 8–10 (Spike-7-blocking backlog: Win32 windowing doc
  absent, WSI/swapchain doc partially covered — `references/vulkan/ch_40` is ingested per
  the audit, reactive multi-loop design), §6 in full (Reactive contracts, quoted extensively
  above) — read in full.
- `docs/EQUIVALENCE_PROOFS.md` §1.1 in full, especially the reactive-loop paragraph
  (`VerifiedReactiveProgram`, inner/outer pairs) and the concurrency-generalization
  paragraph (per-loop pairs plus composition obligations) — this task's core contract
  vocabulary comes directly from here.
- `references/vulkan/ch_40_window_system_integration_(wsi).md` (grep/`ls`-verified present)
  — the WSI/swapchain chapter the audit refers to as "`ch_40`" (already ingested, per audit
  §1 item 9: "WSI/swapchain doc... `references/vulkan/ch_40` IS ingested").
- `docs/tasks/G1-graphics-doc-rework.md` and `docs/tasks/G7-spike6-headless-compute.md` —
  the contract/audit trace split (G1) and the headless Spike 6 pipeline this task's
  windowed extension builds on, including G7's own multi-loop-composition obligation that
  this task's design should stay consistent with per Law 12.
- TASKS.md's PA7 entry ("`VerifiedReactiveProgram` (inner/outer pairs) — after: PA5") —
  consult PA7's own `docs/tasks/` file if it exists by the time this task is authored;
  otherwise `docs/EQUIVALENCE_PROOFS.md` §1.1 (as cited above) is treated as its
  substantive content.
- `docs/OBLIGATIONS_AND_CAUSALITY.md` §3/§3.1 and `docs/tasks/G2-synchronization-dsl.md` —
  the causal/happens-before machinery this task's host+device-queue two-agent framing
  reuses, consistent with G2's edge mapping (fence = queue→host, etc.).
- Zero graphics Lean exists yet (verified: `grep -rn "Gasm/Targets/Spirv\|Gasm/Targets/Vulkan\|Gasm/Graphics" Gasm/` returns nothing); this design targets a future
  Spike 7 module under `Gasm/Targets/*`/a dedicated `Spikes/Spike7*` location, following
  whatever convention prior spikes (e.g. `Spikes/Spike5Gzip/`) establish.

## Notes

- 2026-08-27: priority 6.0 — Spike 7 design (windowed swapchain) is the furthest-out graphics-track item, gated on G7 and PA7.

_(none yet — first entries append here as work begins; this is Law-5-class graphics-model
design work — consolidate Notes into a real docs/ design doc before implementation, and
route it through a fresh-agent design review before any implementation dispatch. Do not
waive review on this track — the pre-build audit this whole track responds to is the proof
that reviewing designs before code is where this project's cheapest findings come from.)_
