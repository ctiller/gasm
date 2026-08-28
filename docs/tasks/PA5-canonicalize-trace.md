---
id: PA5
title: canonicalizeTrace — causal-stamped observation normal form
status: implementing
blocked_on: ""
after: [PA2, N2]
related: [N2]
bar: ""
track: proof-arch
priority: 8.8
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# PA5: canonicalizeTrace — causal-stamped observation normal form

## Context

This task is arguably the single most load-bearing item on the entire proof-architecture track: it
is what makes the observation standard (`docs/EQUIVALENCE_PROOFS.md` §1.1, ratified 2026-08-27)
actually true of the code, rather than true only on paper. `TASKS.md` states its scope tersely
("canonicalizeTrace: causal-stamped normal form, input events as first-class trace events,
coalescing per SYSTEM_EFFECTS §6"); this file expands each clause, because each one is doing real
work.

### The current state is actively wrong, not merely incomplete

PLAN.md's Phase 4 entry does not soften this: it says outright that the codebase's present trace-
equivalence check violates the observation standard it claims to implement.

> **IMPLEMENTATION GAP**: current `traceEquivalence` uses raw `==` on uncoalesced traces —
> chunking accidentally observable. Build `canonicalizeTrace` + migrate obligations BEFORE the zlib
> optimization epic.

"Chunking accidentally observable" means: today, a routine that writes `"ab"` in one syscall and a
routine that writes `"a"` then `"b"` in two syscalls are *not* proven equivalent by the current
`VerifiedProgram.traceEquivalence` definition (`Gasm/Core/Verification.lean:64-72`, using bare
`==`), even though `docs/EQUIVALENCE_PROOFS.md` §1.1 explicitly declares them equivalent
("consecutive writes to the same stream compose by byte concatenation; chunking is an internal
buffering detail"). This is precisely backwards from what a correctness gate should do: it makes
today's gate *reject* a correct optimization (an implementation that batches writes differently)
while doing nothing to *catch* an incorrect one that reorders observably-distinct effects. Until
`canonicalizeTrace` lands, every existing `VerifiedProgram` trace-equivalence proof is proving a
strictly stronger, spec-violating statement than the one the observation standard actually asks
for — which also means it is silently *harder to satisfy* than intended, not merely imprecise.

### Why this must land before the zlib optimization epic (F6)

PLAN.md's Phase 4 entry states the ordering explicitly ("Build canonicalizeTrace + migrate
obligations BEFORE the zlib optimization epic"), and F6 in `TASKS.md`'s Performance path lists this
task as a hard prerequisite: `F6 zlib-to-infinity epic — after: PA8 (Spike5 honest), PA4 (Zlib
capabilities), F4, TC12`. The reasoning is direct: the entire point of the "zlib to infinity"
optimization epic (PLAN.md's candidate post-repair epic) is that agents can freely reorder,
re-chunk, and re-batch zlib's internal I/O as long as correctness is held fixed by universal
contracts. If the trace-equivalence gate itself accidentally treats re-chunking as an observable
difference, the optimization epic cannot proceed — every legitimate optimization would fail the
gate exactly as often as an actual bug would, which defeats the entire "gate is the product"
premise of `docs/VISION.md` §2. This task is the fix that makes optimization-without-regression
possible at all for effectful routines.

### The exact algebra this task implements — read SYSTEM_EFFECTS §6.3-§6.4 in full

`docs/SYSTEM_EFFECTS.md` §6.3 specifies the canonical-form target directly:

> The congruence is implemented as a **normalization function** `canonicalizeTrace` in
> `Gasm.Effects`, and equivalence obligations are stated as `canonicalizeTrace machTrace =
> canonicalizeTrace specTrace`. Stating obligations against raw traces is prohibited once this
> lands: raw-trace equality accidentally observes chunking, which violates the exclusion of
> internal detail.
>
> The normal form carries **happens-after tracking** from day one, even while all programs are
> single-threaded:
>
> - The canonical representation is conceptually a **causally-ordered event set** — each event
>   stamped with its position in the happens-after partial order (vector clocks per
>   `docs/OBLIGATIONS_AND_CAUSALITY.md`) — not a bare list. In a single-threaded program the
>   partial order is total and the representation degenerates to today's list, so nothing is lost
>   now.
> - **Coalescing respects causality**: adjacent same-stream writes fold together only when
>   causally consecutive — no observable event ordered between them... two writes with an
>   intervening causally-ordered observable on another stream must not merge.
> - **Equivalence under concurrency** is then equality of canonical causal orders — equivalently,
>   agreement up to linearizations consistent with the declared happens-after relation...
> - Implementation guidance: build `canonicalizeTrace`'s signature and event representation to
>   accommodate the causal stamp now (single-threaded programs stamp trivially); do not bake
>   total-order assumptions into consumers.

§6.4 is the reason this cannot be built as a naive "concatenate adjacent same-stream events"
function — that shape would be wrong the moment input events exist in the trace at all, which is
why input events must be modeled as first-class trace events in this same task rather than deferred:

> **Writing an ack *in response to* a read IS NOT EQUIVALENT to writing an ack *before* the read.**
>
> A server that pre-emptively emits `OK` and then reads the request is a different — broken —
> program from one that reads and then acks, even though each direction's byte stream is identical
> in isolation. The distinction lives entirely in the cross-direction causal order...
>
> - **Input events (`recv`, file/console reads, `accept`) are first-class contract-trace events**,
>   recorded with their position in the causal order — not silent environment consumption... (The
>   current `FileSystemEvent`/`TraceM` model records no read events; that is a defect to fix under
>   this section, not a precedent.)
> - **Inputs are coalescing barriers**: output coalescing (§6.1) applies only within input-free
>   causal segments. Outputs on either side of an input event never merge and never commute across
>   it.
> - **The input→dependent-output happens-after edge is observable** and must be preserved by
>   `canonicalizeTrace`: an implementation that hoists an output above an input it
>   specification-depends on is NOT equivalent, no matter how the per-stream bytes compare.

This is why PLAN.md's findings ledger separately promotes the missing read-event modeling to a
task-worthy defect: "FileSystemEvent lacks open/read events; TraceM stubs them silently →
PROMOTED... input events (recv/reads/accept) must be first-class contract-trace events — causal
anchors and coalescing barriers... Required for canonicalizeTrace and any protocol spike; fix with
the trace-canonicalization work (Phase 4)." That promotion is this task, concretely: `Gasm/Effects/
Trace.lean`'s current `TraceState`/`TraceM`/`emitEvent` machinery (`:13,20,31`) has no read-event
emission today, and adding it is in scope here, not a prerequisite handled elsewhere.

### The N2/OS1 dependency, and why it is needed for the input-event model specifically

`TASKS.md` phrases this task's dependency as "after: PA2; needs OS1 (short reads) for the
input-event model." **OS1 is the name PLAN.md/MODEL_DEBT.md use for the task now tracked as `N2`**
in this docs/tasks/ scheme (`docs/tasks/N2-...` — see `N2`'s own file, the ReadFile/WriteFile/
handle-model rebuild against the real OS). The dependency is narrow and specific, not a blanket
blocker: this task needs a *real* short-read model to quantify the input-event coalescing-barrier
behavior over, because `MODEL_DEBT.md` §C1 states plainly that today's `ReadFile` hook cannot
produce anything but a maximal read:

> `readFileHook` reads `min(nNumberOfBytesToRead, |stdinBuffer|)` and always returns `RAX=1`. It
> therefore models *disk* semantics only. It cannot express: a pipe delivering 7 bytes when 4096
> were requested with more coming... Given "`read` as the universal binder" (Law 9 / PLAN Phase
> 4), this is the single most load-bearing OS gap: a `∀ read-result` contract proven against a
> model that can only produce maximal reads proves nothing about chunk-robustness.

Concretely: this task's input-event trace representation needs to record *that* a read occurred and
*how much/what* it returned, as a real dimension of variation (partial, empty, EOF, multi-chunk) —
not a placeholder that always looks the same because the underlying OS model cannot yet produce
anything else. Designing the causal-anchor/coalescing-barrier shape without N2's real short-read
model risks baking in the same "maximal read only" assumption MODEL_DEBT.md flags as vacuous, one
layer up.

## Deliverables & acceptance criteria

- A design doc (Law-5-class; consolidate Notes into it before implementation, per the
  task-lifecycle convention) specifying `canonicalizeTrace`'s signature and the causally-stamped
  event representation, consistent with §6.3's guidance to accommodate the causal stamp now even
  though single-threaded programs degenerate it to a list.
- Fresh-agent design review of that doc before implementation is dispatched.
- `canonicalizeTrace` implemented in `Gasm.Effects` (`Gasm/Effects/Trace.lean` or a sibling module)
  as a normalization function over traces, per §6.3.
- Input events (`recv`, file/console reads, `accept`) modeled as first-class trace events with
  their causal position recorded — closing the "FileSystemEvent lacks open/read events" gap PLAN.md
  promotes — and proven to act as coalescing barriers (output coalescing never crosses an input
  event) per §6.4.
- Coalescing implemented per §6.1's per-effect table (console/file same-stream concatenation, net
  message-boundary rules, exit/clock exclusions) with causal-consecutiveness as the precondition
  for folding two events, per §6.3.
- `VerifiedProgram.traceEquivalence` (`Gasm/Core/Verification.lean:64-72`) and any other obligation
  currently stated against raw traces migrated to state equivalence as `canonicalizeTrace machTrace
  = canonicalizeTrace specTrace`, per §6.3's explicit instruction that raw-trace equality is
  prohibited once this lands.
- Proof that the causal-order equivalence is correct with respect to §6.3's stated semantics:
  equivalence of canonical forms should coincide with equality up to causal-order-consistent
  linearizations — this is itself a universally-quantified structural theorem (Law 9/10), not a
  spot-checked property.
- Zero `sorry`, zero unauthorized axioms (`lake build` + `lake exe check_gates_axioms` clean);
  `native_decide`/`decide` is never a substitute for the infinite-domain proofs about trace
  equivalence this task requires (Law 10) — trace length and event-payload domains are unbounded.
- `scripts/check_refs.py` clean, citing `docs/SYSTEM_EFFECTS.md` §6.1/§6.3/§6.4 and
  `docs/EQUIVALENCE_PROOFS.md` §1.1 per Law 1/2 (once §6.3/§6.4 are cited, they must be 100%
  implemented, including the causal-stamp accommodation, not just the single-threaded degenerate
  case).
- Completion report states explicitly whether N2/OS1's short-read model landed with enough real
  variation (partial reads, empty reads, EOF, multi-chunk) to genuinely exercise the input-event
  coalescing-barrier logic, or whether this task had to proceed against a still-thin model and flag
  the residual risk.

## Pointers

- `docs/SYSTEM_EFFECTS.md` §6 in full (§6.1 per-effect coalescing table, §6.2 exclusions restated,
  §6.3 canonical trace normal form — quoted above, §6.4 input events as causal anchors — quoted
  above). Read this section in full before designing; it is short and it is this task's direct
  specification.
- `docs/EQUIVALENCE_PROOFS.md` §1.1 (observation standard) — the standard this task's implementation
  makes real; note its own citation of §6 for the coalescing congruence.
- PLAN.md Phase 4's "Observation standard ratified" entry (the IMPLEMENTATION GAP paragraph quoted
  above, in full) and the findings-ledger "FileSystemEvent lacks open/read events... PROMOTED" entry
  (quoted above); `docs/adr/0014-observation-standard.md` (the ratified ADR for the observation
  standard this task implements) and `docs/adr/0015-read-as-universal-binder.md` (adjacent —
  governs PA6, but its causal-anchor reasoning about input events overlaps with this task's §6.4
  scope).
- `Gasm/Effects/Trace.lean:13` (`TraceState`), `:20` (`TraceM`), `:31` (`emitEvent`), `:95`
  (`runModelTrace`) — the current trace machinery this task extends; no read-event emission exists
  here today, confirmed by grep at time of writing.
- `Gasm/Core/Verification.lean:19-26` (`Environment`), `:64-72` (`VerifiedProgram`,
  `traceEquivalence` — the raw-`==` obligation this task must migrate).
- `MODEL_DEBT.md` §C1 (quoted above, in full) — the short-read gap this task's input-event model
  depends on N2/OS1 to close; §C7 (`Environment` dead fields — related vacuous-∀ concern, tracked
  separately as TC18).
- `docs/tasks/N2-...` (the ReadFile/handle-model rebuild task — referred to as "OS1" throughout
  PLAN.md/MODEL_DEBT.md; this task's dependency is on N2's short-read model specifically, not on N2
  as a whole).
- PA2's design doc (path TBD — see `docs/tasks/PA2-step-lemma-composition-design.md`) — its
  trace-algebra interface sketch (the fourth of PA2's four design pieces) is a direct input to this
  task's design; PA2 deliberately deferred the full causal-order machinery here.
- `docs/OBLIGATIONS_AND_CAUSALITY.md` — the vector-clock machinery §6.3 cites for the causal-stamp
  representation.
- `TASKS.md`'s Performance path, `F6 zlib-to-infinity epic` line — confirms this task is a listed
  prerequisite (`after: PA8..., PA4..., F4, TC12`, itself implicitly requiring PA5 to have landed
  first per the IMPLEMENTATION GAP ordering above).

## Notes

- 2026-08-27: priority 7.0 — canonicalizeTrace unblocks PA6, PA7, and (via N2) the whole read-binder proof line — a mid-DAG chokepoint.
- 2026-08-27: related: [N2] — beyond the existing `after: N2` build-order edge, PA5's causal-stamped observation normal form and N2's short-read model share the same underlying concern (what counts as one observable unit of a read result); flagged here so a fresh agent sees the conceptual overlap, not just the sequencing.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 7.0 → 8.8. This task
  gates PA6, which gates PA8 (8 grandfathered entries) and PA17 (8 more), per the coverage matrix in
  `docs/ORACLE_DEBT.md` Part 2 — the owner has named oracle-debt closure the top priority, and this
  is a mid-DAG chokepoint on the largest single existing-task contribution to it.

_(none yet — first entries append here as work begins; this is Law-5-class proof-architecture
work — consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch; do not waive review on this track.)_
- 2026-08-28 (F2 status audit): `status: ready` -> `implementing`. **This task was named in an
  earlier audit as one of eight whose work was "demonstrably complete". That assessment is wrong
  and is corrected here.** `Gasm/Effects/CanonicalizeTrace.lean` has landed and is real work
  (`CausalEvent`, `stampSingleThreaded`, `canonicalizeCausalTrace`, `canonicalizeTrace`,
  `netEvent_mergeKey_none`, and the concrete `ack_after_read_ne_ack_before_read` barrier witness),
  but the module's own closing comment block ("What remains (PA5, honestly scoped)", `:192-226`)
  enumerates five acceptance criteria it does NOT meet, and the tree confirms each: (a)
  `FileSystemEvent.write` coalescing is unimplemented -- `mergeKey` recognizes only the
  `ConsoleEvent` domain; (b) console/file **read** events are still not first-class trace events,
  so PLAN.md's promoted "FileSystemEvent lacks open/read events" finding is not closed; (c)
  `VerifiedProgram.traceEquivalence` (`Gasm/Core/Verification.lean:88-90`) and
  `VerifiedRoutine.traceEquivalence` (`:112-117`) still use raw `==`, which is the migration
  SYSTEM_EFFECTS §6.3 makes mandatory and is the largest single deliverable on this task; (d) the
  general forall-quantified "coalescing never crosses a barrier" theorem is not proved -- only the
  concrete instance; (e) no design doc and no fresh-agent design review exist, both of which this
  Law-5-class task requires before implementation. `implementing` (not `done`, not `ready`) is
  what the tree supports.
