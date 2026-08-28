---
id: PA6
title: read-binder contract shape — ∀ read results including partial/EOF
status: ready
blocked_on: ""
after: [PA5, N2]
related: []
bar: ""
track: proof-arch
priority: 8.6
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA6: read-binder contract shape — ∀ read results including partial/EOF

## Context

This task is the direct enforcement mechanism for Law 9. `docs/REVIEW.md` states the law's
read-binder clause in full — read it carefully, because this task's entire deliverable is making
this paragraph a contract shape rather than a sentence:

> **`read` is the universal binder (the enforcement vector for this law)**: every monadic input
> operation in a specification (`readFile`, `recv`, `accept`, console reads — all forms of `read`)
> binds an arbitrary result, and the verification contract MUST be parametric in that result: the
> continuation after a read is proven correct for **any** returned `ByteArray` — any contents, any
> length, including partial reads, empty reads, and EOF. Contracts that pin a read's result to a
> concrete vector are unrepresentable as verified, which closes the three known evasion shapes
> structurally: hardcoded-output stubs (a spec that reads cannot be satisfied by a constant),
> domain-shrinking via purpose-built input enums (the read binds the real byte-array domain), and
> pointwise evaluation (no evaluator can discharge a claim over a bound variable). Because `read`
> may return any chunking of the input, robustness to input chunking is itself a forced universal
> obligation — the input-side dual of the output coalescing congruence.

PLAN.md's Phase 4 entry states the same requirement as a design mandate for this exact task:

> **`read` as the universal binder**: contract shape for Phase 4 must thread ∀ read-results —
> every monadic input op in a spec binds an arbitrary ByteArray (any contents/length/partial/EOF)
> and the continuation is proven for all of them; pinning a read result is unrepresentable. This is
> the enforcement mechanism for Law 9 (kills canned outputs, domain-shrinking, pointwise eval
> structurally) AND forces input chunk-robustness (dual of output coalescing). Design the
> VerifiedProgram-successor contract around read-continuations as the ∀ entry points.

Note the last sentence: this task's contract shape is explicitly the seed of PA9's
`VerifiedProgram`-successor design (rebuilding `VerifiedProgram` as a derived theorem) — PA9 depends
on PA6 transitively through PA8 (`after: [PA6, PA7]`), and the read-continuation shape this task
designs is what a routine's contract must expose for the composition calculus (PA2/PA3) to chain
read-then-continuation proofs across routine boundaries.

### Why this cannot be designed before PA5 and N2 land

This task is sequenced `after: [PA5, N2]` for two independent, necessary reasons:

1. **PA5 (`canonicalizeTrace`)** establishes that input events are first-class, causally-ordered
   trace events and act as coalescing barriers (`docs/SYSTEM_EFFECTS.md` §6.4). A read-binder
   contract that quantifies over read results but does not also record *that* a read occurred at a
   specific causal position would silently reintroduce the exact "ack before read ≡ ack after read"
   confusion §6.4 exists to prevent. This task's contract shape must build on PA5's trace
   representation, not invent a parallel one.
2. **N2 (aliased `OS1` in PLAN.md/MODEL_DEBT.md — the ReadFile/WriteFile/handle-model rebuild)**
   is needed because a contract that quantifies `∀` over read results is only as meaningful as the
   underlying OS model's ability to actually *produce* varied read results. `MODEL_DEBT.md` §C1 is
   explicit that today's model cannot:
   > `readFileHook` reads `min(nNumberOfBytesToRead, |stdinBuffer|)` and always returns `RAX=1`. It
   > therefore models *disk* semantics only. It cannot express: a pipe delivering 7 bytes when 4096
   > were requested with more coming; console line-buffering... or handle-type differences at
   > all... Given "`read` as the universal binder" (Law 9 / PLAN Phase 4), this is the single most
   > load-bearing OS gap: a `∀ read-result` contract proven against a model that can only produce
   > maximal reads proves nothing about chunk-robustness. **The Win32 differential harness must
   > pin this first.**
   Designing this task's contract shape against the pre-N2 model would produce a contract that is
   universal *in form* but vacuous *in substance* — exactly the C7 "vacuous ∀" failure mode
   `MODEL_DEBT.md` documents for `Environment`'s dead fields, one layer down at the read-result
   level instead of the environment-field level. The dependency on N2 is not bureaucratic
   sequencing; it is what keeps this task's contract from being Law-9-shaped without being
   Law-9-true.

### What "contract shape" concretely means here

This is a design-doc task (per `TASKS.md`'s own phrasing, "contract shape"), not an implementation.
The deliverable is the specification of what a verified routine's/program's contract must look like
so that:

- Every monadic read operation's result is a **universally bound variable** in the contract's
  precondition/postcondition, never a concrete instantiation — the continuation's correctness
  proof must hold for the entire `ByteArray` domain that read could return, including the empty
  array and any length up to and including a full/maximal read.
- **Partial reads and EOF are not edge cases bolted on after the fact** — they are ordinary
  elements of the same universally-quantified domain the contract already ranges over. A contract
  shape that special-cases "the happy path" and separately patches in EOF handling has not actually
  achieved what this task requires; EOF, empty, and partial results must be indistinguishable in
  the contract's proof obligation from any other `ByteArray` value.
- **Chunking robustness is a corollary, not a separate requirement.** Per Law 9's closing sentence
  above, if the read binder is genuinely universal, the fact that a caller cannot control how its
  input is chunked falls directly out of the same quantifier — this task should verify (not just
  assert) that its contract shape actually has this property, e.g. by checking that a program
  proven correct for one chunking of an input is provably equal (via composition, not by a second
  proof) to the same program under any other chunking of the same logical input.
- The contract shape must compose with PA2's step-lemma/composition calculus — a read followed by
  a computation followed by a write is exactly the "sequential composition across an input-event
  coalescing barrier" case PA5 introduces; this task specifies how a routine's contract exposes its
  read-continuation obligation so PA2/PA3's composition rules can chain it.

## Deliverables & acceptance criteria

- A design doc (Law-5-class; consolidate Notes into it, fresh-agent design review required before
  any implementation of this contract shape is dispatched — likely as part of PA9's later
  implementation work) specifying the read-binder contract shape: how a monadic read's result is
  represented as a universally-quantified variable in a routine's/program's contract, how partial/
  empty/EOF results are covered by that same quantifier (not special-cased), and how the shape
  integrates with PA5's causally-stamped trace representation (a read is a trace event with a
  causal position; the contract's universal quantifier ranges over that event's payload).
- Explicit demonstration (in the design doc, worked through on at least one concrete example — a
  small program that reads then writes, in the spirit of `docs/EQUIVALENCE_PROOFS.md`'s worked
  `memcpy` example) that the shape actually forces chunk-robustness as a consequence rather than
  merely permitting it.
- Explicit connection to Law 9's three named evasion shapes (hardcoded-output stubs,
  domain-shrinking input enums, pointwise evaluation): state, for each, why this contract shape
  makes it unrepresentable rather than merely discouraged — this is the standard PA8's later
  migration work will be judged against when closing the Tier-1/Tier-2 mock-verification census
  (see `docs/tasks/PA8-law9-migration.md`).
- Since this is a design-doc task, acceptance evidence at this stage is the fresh-agent design
  review verdict plus `scripts/check_refs.py` passing once the doc exists and is cited. Any Lean
  code produced to validate the shape against a worked example must itself be zero-`sorry`,
  clean under `lake exe check_gates_axioms`, and must never use `native_decide`/`decide` as a
  stand-in for the infinite-domain universal quantification this contract shape exists to enforce
  (Law 10) — a worked example that only "checks" via `decide` over a small finite instantiation has
  not validated the shape at all.

## Pointers

- `docs/REVIEW.md` Law 9 in full (the read-binder paragraph quoted above is its enforcement-vector
  clause; read the whole law for the three-evasion-shape framing);
  `docs/adr/0015-read-as-universal-binder.md` (the ratified ADR for this exact task's mandate).
- PLAN.md Phase 4, "`read` as the universal binder" bullet (quoted above, in full).
- `MODEL_DEBT.md` §C1 in full (quoted above) — the short-read gap this task's substance depends on
  N2/OS1 to close; TOP-10 table item 1 names this as the highest-priority correctness gap tied to
  "Phase 4 `read`-as-binder is unsound without it."
- `docs/SYSTEM_EFFECTS.md` §6.4 (input events as causal anchors and coalescing barriers) — this
  task's contract shape must be stated in terms of PA5's trace representation, not a parallel one;
  read PA5's design doc once available.
- `docs/tasks/PA5-canonicalize-trace.md` — the direct prerequisite; do not start this task's design
  until PA5's causal-trace representation is settled.
- `docs/tasks/N2-...` (the ReadFile/handle-model rebuild — referred to as "OS1" in PLAN.md/
  MODEL_DEBT.md) — the direct prerequisite for real read-result variation to design against.
- `Gasm/Effects/FileSystem.lean:47-51`-shaped typeclasses (`MonadFileSystem`'s `readFile`
  signature — grep to confirm exact lines) and `Gasm/Targets/Windows/Win32API.lean`'s
  `readFileHook` — the concrete read operations this contract shape must cover.
- `docs/EQUIVALENCE_PROOFS.md` §5 (`VerifiedProgram`, the universal-∀-environment law) — the
  existing whole-program quantification this task's read-binder shape refines to the
  operation-level granularity of individual reads.
- `docs/tasks/PA8-law9-migration.md` — the downstream consumer of this task's contract shape;
  PA8's Tier-1/Tier-2 mock-verification fixes are judged against the shape this task defines.
- `docs/tasks/PA9-verified-program-derived.md` — the `VerifiedProgram`-successor rebuild PLAN.md's
  quote above names as this task's ultimate destination.

## Notes

- 2026-08-27: priority 6.8 — read-binder contract shape is the direct proof-side consumer of N2's short-read model; gates PA8's Law-9 migration.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 6.8 → 8.6. Direct
  prerequisite for PA8 (8 grandfathered entries covered) and PA17 (8 more, Spike3-Windows/Spike4
  domain honesty) — both now top-priority per the owner's zero-axiom mandate.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
