---
id: N5
title: Spike4 re-verified as VerifiedReactiveProgram
status: ready
blocked_on: ""
after: [N3, PA7]
related: []
bar: ""
track: networking
priority: 7.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# N5: Spike4 re-verified as VerifiedReactiveProgram

## Context

`TASKS.md`'s line for this task: "Spike4 re-verified as VerifiedReactiveProgram — after: N3, PA7."
This task has two prerequisites for a reason: N3 supplies the real socket semantics (blocking
`accept`/`recv`/`send`, the graceful-close/error/short-read distinctions) that a server loop's
*inner* per-iteration contract must actually be proven against, and PA7 supplies the contract
*type itself* — `VerifiedReactiveProgram` does not exist yet as a Lean declaration; PA7 is where
it gets designed and built.

### Why Spike4 specifically, and what "first instance" means

`PLAN.md`'s "Observation standard ratified" entry (dated 2026-08-27, in `EQUIVALENCE_PROOFS.md`
§1.1) is where this contract type was decided:

> Craig-ratified refinements (2026-08-27): (a) infinite loops ENFORCED as inner/outer proof pairs
> — new `VerifiedReactiveProgram` contract type with mandatory fields: inner = deterministic
> both-ways per-iteration equality, outer = progress/liveness; reactive emit accepts only the pair
> (Spike4 = first target)...

Two things follow directly from this. First, `VerifiedReactiveProgram` requires **two** proof
obligations per reactive program, not one: an **inner** obligation (each iteration of the
program's event loop is deterministic and both-ways-equivalent to its specification — the same
kind of trace equality every other `VerifiedProgram` already proves, but scoped to one iteration)
and an **outer** obligation (the loop as a whole makes progress and does not livelock/deadlock —
a liveness property with no counterpart in the current, non-reactive `VerifiedProgram`). A
`VerifiedReactiveProgram` is only accepted with *both* fields present — per PLAN's phrasing,
"reactive emit accepts only the pair," meaning an inner-only proof (equivalent to what
`VerifiedProgram` already demands) is explicitly insufficient for a program whose defining
behavior is an unbounded accept/serve loop.

Second, PLAN.md names Spike4 explicitly as the **first target** for this contract type. That
makes this task a genuine milestone, not a routine re-verification pass: **Spike4 becomes gasm's
first `VerifiedReactiveProgram` instance.** Every other spike's current `VerifiedProgram`
instances prove trace equivalence for a single execution that terminates (per PLAN's original
framing, `ProcessEvent.exit` is the terminal event and appears exactly once); Spike4's HTTP
server, by contrast, is precisely the shape PLAN.md's ratified refinement was written for — an
`accept`-loop server that runs indefinitely, serving requests until externally stopped, for which
"prove it terminates correctly" is the wrong question and "prove each iteration is correct, and
prove the loop as a whole progresses" is the right one. Verifying Spike4 under the old
non-reactive `VerifiedProgram` contract (which is what the current `Test.lean`/`Equivalence.lean`
effectively do — see `docs/tasks/N4-socket-e2e-spike4.md`'s finding that the current test compares
three individual `handleRawRequest` calls, not an actual running accept-loop) never actually
proved the loop's liveness/progress at all; it proved that three individual request/response
transformations are correct in isolation. N5 is where Spike4 is re-proven against the contract
shape its real behavior (an unbounded server loop) actually demands.

### Why N3 must land first

N5's inner obligation ("each iteration of the event loop is deterministic and equivalent to spec")
is only meaningful if the model of what happens inside one iteration — `accept` yields a
connection, `recv` yields a request (possibly short, possibly blocking), `send` emits a response —
reflects real WinSock behavior. Proving inner-equivalence against N3's *predecessor* model (the
invented `acceptHook`/`recvHook`/`sendHook` from `MODEL_DEBT.md` §C5 — fixed-value sockets,
single-shot `recv`, `rip := 0` on an empty accept queue) would prove something about an OS that
does not exist; PLAN's own C5 note is explicit that "nothing opens a real socket against an
emitted binary" today. N5 depends on N3 precisely so the inner per-iteration proof is a proof
about the real socket semantics N3 establishes, not the invented ones it replaces.

### Relationship to N4

N4 (end-to-end socket exercise) and N5 (formal reverification) are complementary, not redundant:
N4 is empirical — it runs the actual emitted binary as a process and drives real socket traffic
at it to observe that it behaves correctly. N5 is the formal counterpart — a kernel-checked proof
that the *model* of Spike4's server loop, now built on N3's real socket semantics, satisfies the
`VerifiedReactiveProgram` inner/outer obligations. Per `docs/VISION.md` §3.1/§3.2, the proof and
the empirical harness are both required and neither substitutes for the other: N4 validates that
the model is faithful to reality (§3.2); N5 validates that the stated theorem is sound given the
model (§3.1).

### Governing laws

`docs/REVIEW.md` Law 9 (universal quantification — the inner obligation must be proven for all
inputs a real `recv` can return per N3, not a hardcoded request set); Law 5 (this is new contract
surface being applied for the first time — stop-and-design applies to *how* Spike4's loop is
restructured/proven against the pair, even though the contract type itself is PA7's design
responsibility, not this task's). `docs/VISION.md` §1 (web/gRPC servers — this is the concrete
first instance of "threading and async I/O" surfacing as a verification obligation) and §3.1/§3.2
(the two trust obligations this task discharges jointly with N4, as above).

## Deliverables & acceptance criteria

- **Spike4 restated as a `VerifiedReactiveProgram` instance** (PA7's type, once it exists) rather
  than (or in addition to, during migration) its current `VerifiedProgram`/ad-hoc trace-equality
  framing.
- **Inner obligation**: a kernel-checked proof that one iteration of Spike4's accept/recv/send
  loop — built on N3's real socket model — is deterministic and both-ways-equivalent to its
  specification, universally quantified over the real domain of what `accept`/`recv` can return
  post-N3 (per Law 9: any accepted connection, any request byte sequence including short/chunked
  arrivals, not a fixed set of hardcoded request strings).
- **Outer obligation**: a kernel-checked proof (or, if full liveness proof is not yet tractable, an
  explicitly-scoped partial statement with the gap named rather than silently omitted) that the
  loop makes progress — it does not deadlock or livelock waiting on a connection/request, and
  successive iterations are reachable from one another under the real blocking-accept semantics
  N3 establishes.
- **The reactive-emit constraint honored**: per PLAN's "reactive emit accepts only the pair," the
  emission/verification path for `VerifiedReactiveProgram` instances must actually enforce that
  both inner and outer proofs are present — Spike4 must not be accepted as verified with only one
  half supplied, and this task's work is a live check that PA7's mandatory-pair enforcement
  actually holds for a real (not toy) instance.
- **Consistency with N4's empirical exercise**: the real request/response behavior N4 observes
  running the actual binary should agree with what the inner-obligation proof claims about one
  iteration — divergence between the two is itself a finding (either the model built for the
  proof or the harness in N4 is wrong) and must be reconciled, not left standing.
- Since this is the first-ever instantiation of a brand-new contract type against a real spike
  (not a mechanical reapplication of an existing pattern), it is Law-5-adjacent and warrants
  design review before implementation rather than being waived — say so explicitly: getting the
  first `VerifiedReactiveProgram` instance right sets the pattern every subsequent reactive
  spike (including multi-loop/threaded programs per PLAN's Phase-4 refinement (d)) will follow.
  `status` should progress `ready → designing → design-review → implementing → done`.

## Pointers

- `Spikes/Spike4HttpServer/Equivalence.lean`, `Spikes/Spike4HttpServer/Spec.lean`,
  `Spikes/Spike4HttpServer/Test.lean` — the current (non-reactive) verification surface this task
  restates; `Test.lean`'s three-hardcoded-request pattern (lines 60-70, per N4's file) is exactly
  what the inner obligation's universal quantification must move past.
- `docs/tasks/N3-real-socket-model.md` — supplies the real socket semantics the inner obligation
  is proven against; must land first.
- `docs/tasks/N4-socket-e2e-spike4.md` — the empirical complement; read together, since N4's
  end-to-end exercise and N5's formal proof should agree on what "one iteration" observably does.
- `PA7` (VerifiedReactiveProgram design/implementation — check `docs/tasks/PA7-*.md` if by the
  time this is read another agent has written it; at the time this file was authored, PA7's own
  task file did not yet exist in `docs/tasks/`, only its one-line description in `TASKS.md`: "PA7
  VerifiedReactiveProgram (inner/outer pairs) — after: PA5") — the contract type this task
  instantiates; this task cannot proceed until PA7's type exists.
- `PLAN.md` "Observation standard ratified (EQUIVALENCE_PROOFS.md §1.1, 2026-08-27)" — the
  paragraph quoted above in full; also Phase-4 refinement (d) (threading/multiprocessing ⇒
  multiple reactive loops per program — relevant context for why this contract type is designed
  the way it is, even though Spike4 itself is single-loop).
- `docs/VISION.md` §1 (web/gRPC servers class), §3.1 ("the proofs must be sound"), §3.2 ("the
  models must be faithful to reality").
- `docs/REVIEW.md` Law 9 (universal quantification), Law 5 (stop-and-design for new
  contract-instantiation surface).

## Notes

- 2026-08-27: priority 7.0 — Spike4 re-verified as VerifiedReactiveProgram is the proof-side payoff of N3/N4's socket work, gated on PA7.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
