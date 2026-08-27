---
id: PA7
title: VerifiedReactiveProgram — mandatory inner/outer proof pairs for reactive loops
status: ready
blocked_on: ""
after: [PA5]
related: []
bar: ""
track: proof-arch
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA7: VerifiedReactiveProgram — mandatory inner/outer proof pairs for reactive loops

## Context

This task designs the contract type for non-terminating programs — servers, event loops, anything
whose spec is an infinite service loop rather than a program that halts and returns. `TASKS.md`
names it tersely ("VerifiedReactiveProgram (inner/outer pairs)"); `docs/EQUIVALENCE_PROOFS.md` §1.1
is the canonical source, and it must be read and honored precisely, because the design here is
already Craig-ratified (per PLAN.md's Phase 4 entry) and this task's job is to specify it fully and
implement the contract type, not to relitigate whether inner/outer pairs are the right shape.

### The exact contract this task must produce — quoted in full

`docs/EQUIVALENCE_PROOFS.md` §1.1 states the requirement precisely:

> **Non-terminating programs (reactive loops) are enforced as inner/outer proof pairs.** A program
> whose spec is an infinite service loop (e.g. a server) carries a distinct contract type —
> `VerifiedReactiveProgram` — with two *mandatory* proof fields, so neither half can be omitted:
> the **inner** obligation is deterministic both-ways trace equality for one iteration (∀
> request/session in the request domain, the handler's contract trace equals the spec's), and the
> **outer** obligation is progress/liveness (the loop always returns to its accept state, consumes
> every arriving request, and never wedges). A reactive program verified only per-request (no
> liveness) or only live (no per-request equality) must be unrepresentable as verified;
> `emitVerifiedExecutable` for reactive programs accepts only the paired contract.

Read the phrase "mandatory fields, so neither half can be omitted" as the design's central
constraint, and take it structurally, not just as a naming convention: this task's `VerifiedReactiveProgram`
type must make it a type error — not a lint warning, not a missing-review-checklist-item, an
actual failure to construct the contract — to supply only the inner half or only the outer half.
`emitVerifiedExecutable`'s reactive-program path must be unable to consume anything less than the
full pair; this is the same "unrepresentable by construction" discipline Law 13's preference order
puts first, applied to a contract type rather than an artifact property.

### Why both halves independently, and why neither substitutes for the other

Understand *why* this shape was chosen, not just what it says, because that understanding is what
lets this task's design generalize correctly to the concurrent case (below) rather than just
satisfying the letter of the single-loop version:

- **Inner alone is vacuous against a wedged server.** A handler that is proven correct for every
  request it receives says nothing if the accept loop can stop accepting after the first request —
  per-request correctness and "the server keeps working" are logically independent claims, and a
  server that silently stops after one request would still satisfy an inner-only proof.
- **Outer alone is vacuous against a server that discards work.** A loop proven to always return to
  its accept state and never wedge says nothing about whether it computed the right *response* for
  each request — outer-only liveness is satisfied even by a server that accepts every request and
  replies with garbage.
- Both together are what `docs/EQUIVALENCE_PROOFS.md` §1.1's general "both ways" observational
  standard demands for a program whose full behavior cannot be captured by trace *equality* alone
  (that requires the program to halt); the inner/outer split is how the both-ways standard is made
  to apply to non-terminating specs at all, per the same section's earlier framing: "the obligation
  splits into refinement... plus progress/liveness" for nondeterministic/reactive specs, and
  "demanding literal both-ways equality [for a permitted-behavior set] is wrong."

### The concurrency generalization — read this before designing, even for the single-loop case

`docs/EQUIVALENCE_PROOFS.md` §1.1 also specifies, in the same subsection, how this contract type
must generalize once threading/multiprocessing lands — design this task's single-loop contract type
so that generalization is additive, not a rewrite:

> **Concurrency generalizes the pair, it does not replace it.** Once threading/multiprocessing
> lands, a typical program contains *several* reactive loops. The contract then becomes: one
> inner/outer pair **per loop**... plus **composition obligations** across loops — absence of
> deadlock/livelock at the declared synchronization points, and any fairness assumptions stated
> explicitly as part of the contract rather than assumed. The per-loop pairs must remain
> independently checkable (a loop's inner proof must not depend on another loop's scheduling);
> cross-loop interaction is confined to the composition layer, expressed through the causal-order
> machinery of `docs/OBLIGATIONS_AND_CAUSALITY.md`... Full design under Law 5 before the first
> threaded spike.

This task is scoped to the single-loop contract type (the concurrent composition-obligation design
is explicitly deferred to its own Law-5 design before the first threaded spike), but the type must
be built so a later per-loop generalization is a straightforward parameterization rather than a
redesign — e.g. do not bake "there is exactly one reactive loop in a program" into the type in a way
that would need undoing.

### Why this depends on PA5, and what it is needed for downstream

This task is sequenced `after: PA5` because both proof halves are stated in terms of trace
equivalence, and per PA5's work, trace equivalence must be stated against `canonicalizeTrace`'s
causally-ordered normal form, not raw traces — the inner obligation's "handler's contract trace
equals the spec's" is exactly the kind of statement PA5 exists to make correctly stated (coalescing-
aware, causally ordered) rather than accidentally observing chunking.

Two concrete downstream consumers depend on this task, per `TASKS.md`'s edges:

- **N5 (Spike4 re-verified as VerifiedReactiveProgram)** — `after: N3, PA7`. Spike4 is an HTTP
  server (`Spikes/Spike4HttpServer/`), the paradigm case of a reactive loop; N5 cannot proceed
  without this task's contract type existing.
- **G9 (Spike 7 design — windowed swapchain; multi-loop reactive; presented-contents observables)**
  — `after: G7, PA7`. Spike 7's design explicitly needs this task's inner/outer contract shape as
  the basis for a windowed rendering loop's reactive contract (a swapchain present loop is itself a
  reactive loop with its own inner/outer split).
- **PA8 (Law 9 migration)** needs this task specifically for its Spike4 portion — `TASKS.md`:
  "after: PA6 (+PA7 for Spike4)." Spike4's Tier-3 legitimate finite-∀ pattern
  (`Spikes/Spike4HttpServer/Equivalence.lean`'s `HttpRoute`, per PLAN.md's mock-verification
  census) still needs to be re-expressed as a `VerifiedReactiveProgram` inner/outer pair once this
  task's contract type exists, since Spike4 is a server and its current verification predates this
  contract shape.

## Deliverables & acceptance criteria

- A design doc (Law-5-class; consolidate Notes into it, fresh-agent design review required before
  implementation) specifying the `VerifiedReactiveProgram` contract type: its inner field
  (deterministic both-ways trace equality for one iteration, `∀` request/session in the request
  domain), its outer field (progress/liveness: return-to-accept-state, consumes every arriving
  request, never wedges), and the type-level mechanism that makes both fields mandatory (e.g. a
  structure with two non-optional proof-carrying fields, rather than a checklist or a lint rule).
- `emitVerifiedExecutable`'s reactive-program code path specified (and, once implemented, enforced)
  to accept only the fully-paired contract — no code path that emits a reactive executable from an
  inner-only or outer-only proof.
- Explicit design note on how this single-loop type is structured to generalize additively to the
  per-loop-pair-plus-composition-obligations shape `docs/EQUIVALENCE_PROOFS.md` §1.1 describes for
  concurrency, without attempting to design the concurrent composition obligations themselves (that
  is out of scope, deferred to its own Law-5 design before the first threaded spike, per the quoted
  text above).
- Both proof obligations, once implemented (this task may include a first real instance, or may be
  design-only depending on scope — state the choice explicitly in the completion report), are
  discharged by kernel-checked structural proof: the inner obligation is `∀`-quantified over the
  request domain and must not be proven by `native_decide`/`decide` except for a genuinely
  exhaustive finite sub-case (Law 10); the outer liveness obligation is an existential/progress
  argument (per `docs/EQUIVALENCE_PROOFS.md` §3's total-correctness shape) and likewise must be
  structural, not sampled.
- Zero `sorry`, zero unauthorized axioms for any Lean code this task produces (`lake build` + `lake
  exe check_gates_axioms` clean); `scripts/check_refs.py` clean, citing
  `docs/EQUIVALENCE_PROOFS.md#11-the-definition-of-observation-canonical-equivalence-standard`.
- Completion report states explicitly which of N5/G9/PA8's Spike4 portion this task's landed
  design/implementation is sufficient to unblock, and flags anything about the concurrency
  generalization note that later proved wrong once a real per-loop case was attempted (if attempted
  within this task's scope).

## Pointers

- `docs/EQUIVALENCE_PROOFS.md` §1.1 in full — the canonical, already-ratified specification this
  task implements; quoted extensively above. Do not treat this task as open design on whether
  inner/outer pairs are correct — that question is settled; the task is to specify the type fully
  and implement it faithfully.
- `docs/adr/0014-observation-standard.md` — the ratified ADR covering the observation standard
  including the inner/outer reactive-loop enforcement.
- PLAN.md Phase 4's "Observation standard ratified... Craig-ratified refinements" entry — the
  paragraph (a) specifically, which is the source of the inner/outer mandate, and (d) which is the
  concurrency generalization this task's type must accommodate additively.
- `TASKS.md`'s Proof architecture section (`PA7` line) and Networking path (`N5` line: "after: N3,
  PA7") and Graphics path (`G9` line: "after: G7, PA7") — the downstream consumers.
- `docs/tasks/PA5-canonicalize-trace.md` — the direct prerequisite; this task's inner-obligation
  trace-equality statement must be phrased against PA5's `canonicalizeTrace` normal form.
- `Spikes/Spike4HttpServer/Equivalence.lean` (the current Spike4 verification, predating this
  contract type; `HttpRoute` is PLAN.md's cited Tier-3 "legit pattern" example — grep to confirm
  current structure before N5/PA8 attempt to re-express it against this task's type).
- `docs/OBLIGATIONS_AND_CAUSALITY.md` — the vector-clock/causal-order machinery the deferred
  concurrent composition-obligation design will eventually build on; read enough of it now to avoid
  designing this task's single-loop type in a way incompatible with it.
- `docs/REVIEW.md` Law 10 (kernel-checked vs `native_decide` boundary for both proof halves;
  `docs/adr/0002-native-decide-restricted-to-exhaustive-finite-domains.md`), Law 8 (no dead
  abstractions — `emitVerifiedExecutable`'s reactive path must actually invoke/require both fields,
  not merely declare them).

## Notes

- 2026-08-27: priority 6.5 — VerifiedReactiveProgram inner/outer pairs are required before N5 (Spike4 re-verification) and G9 (Spike7 design) can proceed.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
