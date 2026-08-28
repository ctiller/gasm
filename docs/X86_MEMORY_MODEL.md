# X86_MEMORY_MODEL: Causality and Memory Ordering for x86-64

- REF: docs/TARGETS/X86_64.md#3-memory-ordering-x86-tso-hardware-ground-truth-vs-the-current-model
- REF: docs/MEMORY_HOOK.md#33-the-declarative-access-descriptor-the-one-source-four-consumers-read
- REF: docs/SYSTEM_EFFECTS.md#63-canonical-trace-normal-form-with-happens-after-tracking
- REF: docs/SYSTEM_EFFECTS.md#64-input-events-are-causal-anchors-and-coalescing-barriers-protocol-causality
- REF: docs/OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality--vector-clocks
- REF: docs/SPIKES/SPIKE8_MULTITHREADING.md
- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md
- REF: docs/CALIBRATION_GOVERNANCE.md
- REF: MODEL_DEBT.md (§B1, §B2)

## 1. Status and scope

**Status**: this is a design document, not a report of built machinery. **Nothing specified
here exists in the tree**; every mechanism below is design-only unless a sentence explicitly
says it was verified in the tree. Everything described as existing was verified by reading
the tree or running commands at commits `27ab4ed`–`3da22dc` (2026-08-28).

**The question this answers** (owner, verbatim): *"are we doing atomic accesses yet for x86?
they need a causality memory model stated."*

The short answer, verified: **no atomic accesses exist, and no memory model exists either —
but until this change, the target spec claimed one did** (the fictional
`x86_mov_store_is_release` theorem, removed from `docs/TARGETS/X86_64.md` §3 alongside this
document). This document *states* the model: what it is, what it honestly asserts today, how
it composes with the trace-level causality machinery already in the tree, what its first
consumers must cite from it, and how its claims get differentially validated rather than
asserted.

**Relationship to Spike 8** (`docs/SPIKES/SPIKE8_MULTITHREADING.md`, designed concurrently
with this document): the owner ruled a multithreading spike happens before scale-up, which is
precisely the Law 5 demand that makes this model buildable rather than speculative. The
ownership split is as Spike 8 §5.2 states it: **this document owns the model** — structure,
ordering rules, trust posture; **Spike 8 owns the demand list and the validation programs**.
Implementation is tracked as MT1–MT6 (`docs/tasks/`), of which MT1 (atomic primitives) and
MT2 (multi-threaded machine state) are blocked on this document landing; §2.3 and §7 below
answer Spike 8's five demands explicitly. The linter gap found while auditing the old §3
fiction is tracked separately as TC22 (`docs/tasks/TC22-doc-lean-fence-facade.md`).

### 1.1 Verified current state

| Fact | Evidence |
| :-- | :-- |
| Zero atomic instruction forms: no `LOCK` prefix, no `CMPXCHG`, no `XADD`, no `MFENCE`/`LFENCE`/`SFENCE`, no non-temporal store | case-insensitive grep over `Gasm/Targets/X86_64/` at `27ab4ed`; every hit for "lock" is the word "block" |
| `XCHG` exists only as `XchgR64R64` — register-register, no memory operand, `memAccesses _ := []` | `Gasm/Targets/X86_64/Instructions/Xchg.lean` |
| The machine model is single-threaded: one sealed byte image, one interpreter, program order | `X86_64Memory` (`MemoryCell.lean`, MH1's seal); `runProgramTraceWithLoops` steps one instruction stream; `ThreadId` exists only in trace-layer vocabulary |
| The previously displayed ordering theorem was fiction | `x86_mov_store_is_release` / `getMemoryType` / `isNonTemporalInstr` / `PreservesStoreStoreOrder` appear nowhere in any `.lean` file; removed from `docs/TARGETS/X86_64.md` §3 in this change (`MODEL_DEBT.md` §B1, `docs/X86_ISA_EXPANSION_PREREQUISITES.md` §7.5) |
| MH1's access descriptor landed and is the mandatory per-form declaration surface | `MemAccessSpec` (kind, width, ref) in `Memory.lean`; `memAccesses : ι → List MemAccessSpec`, defaultless, on all forms (ADR-0040) |
| Trace-level causality exists and is single-thread-degenerate by construction | `CausalEvent` = `AnyEvent` × `VectorClock`; `stampSingleThreaded`; `NetEvent`s are coalescing barriers with a concrete proof (`ack_after_read_ne_ack_before_read`, `Gasm/Effects/CanonicalizeTrace.lean`) |
| A happens-before vocabulary already exists in Core | `VectorClock.happensBefore`/`join`/`tick` (`Gasm/Core/Types.lean:43-64`) |

## 2. The model, and its honest scope

### 2.1 What model: x86-TSO over Write-Back memory

The model is **x86-TSO**: the operational store-buffer formalization of what Intel and AMD
actually guarantee for ordinary Write-Back cacheable memory. The vendor ground truth is the
Intel SDM Vol. 3A memory-ordering chapter (the registered `intel-sdm` reference corpus is
where Lean-side claims cite it, per Law 1/Law 4); the operational machine below is the
academic-consensus formalization known as x86-TSO. Its content, stated once so every
consumer can cite rather than restate it (Spike 8 demands 1–2):

- Each hardware thread has a **FIFO store buffer**. A store enqueues; it becomes globally
  visible when it drains to shared memory. Stores drain in program order (S→S preserved).
- A load reads the youngest same-address entry of **its own** store buffer if one exists
  (store forwarding), else shared memory. Loads are not reordered with other loads (L→L) or
  with later stores (L→S).
- The one visible relaxation: a load may complete while an **earlier store to a different
  address** still sits in the buffer (S→L reordering) — the SB litmus shape.
- A **locked RMW** (any `LOCK`-prefixed instruction, and `XCHG` with a memory operand, which
  is architecturally locked with or without the prefix) drains its thread's buffer, then
  performs its read-modify-write as one indivisible global action. Locked RMWs are totally
  ordered across threads.
- **`MFENCE`** drains the store buffer. For WB memory and the instruction surface this
  repository will plausibly model, `SFENCE`/`LFENCE` add nothing over TSO's built-in
  guarantees (their content is non-temporal stores and speculation control — out of scope).

Scope: **WB cacheable memory only** (Spike 8 demand 3). No memory types, no WC/MMIO, no
non-temporal stores, no self-modifying-code interactions. `docs/TARGETS/X86_64.md` §3.1
keeps the hardware background; MMIO ordering (which bare-metal SMP will eventually need for
the LAPIC — MT6's territory) forces a scope extension through Law 5, not a silent widening.

### 2.2 What the model asserts NOW, and why the timing is finally right

Today the machine model has **one thread**. Under one thread, TSO, sequential consistency,
and plain program order are observationally identical: store forwarding guarantees a thread
always reads its own latest write, and there is no second observer to witness a buffered
store. So a memory-model theorem stated against today's tree would be vacuous (the TC17
class), and an ordering annotation consumed by nothing would be a Law 8 dead abstraction and
a Law 12 twin born unlinked. **This document therefore adds zero Lean today.** That is not
deferral for its own sake — it is the same Law 5 / ADR-0039 (P1) discipline that declined
speculative machine state, applied to ordering.

What changed, and why the model gets built now anyway: the owner ruled a multithreading
spike happens before scale-up (Spike 8), and that spike is *deliberately constructed* so its
programs are unprovable and its hardware runs unfalsifiable without a real ordering model
(litmus battery + spinlock counter — `docs/SPIKES/SPIKE8_MULTITHREADING.md` §1). The demand
has arrived; the Lean embodiment of §2.1 lands via MT1 (instructions) and MT2 (machine
state), both blocked on this document precisely so ordering semantics are **cited from
here, not restated per instruction** — the anti-twin discipline at the planning level.

### 2.3 The shape MT1/MT2 build (this document's structural decisions)

**Status**: design-only; nothing below exists. MT1/MT2's deliverables cite this section.

**Decision 1 — atomic RMW is ONE descriptor entry, not a load+store pair.** Spike 8 demand
4 is adopted as a structural rule: `MemAccessKind` (currently `load | store`) gains a third
constructor, `rmw` — an access that atomically reads and writes its footprint. A locked RMW
instruction declares exactly one `MemAccessSpec` with `kind := .rmw`; it is therefore
*unrepresentable* for a scheduler to interleave between the read and write halves, by
construction rather than by side condition. Footprint algebra counts `.rmw` entries in both
`loadFootprint` and `storeFootprint`; the `writesWithin`/`readsWithin` frame-lemma
convention (`MemoryFrame/`) extends to the new kind unchanged in shape. No separate
`MemOrder` annotation field is added: on x86-TSO the ordering taxonomy the tree needs is
exactly "plain access" (TSO defaults) vs. "`.rmw`" (locked, fencing) — a parallel ordering
enum would duplicate the kind distinction with nothing to distinguish. If a future
model-relaxation ever needs per-access orderings beyond that (it will not for x86; it might
for ARM), the field slots into `MemAccessSpec` then, next to its first consumer.

**Decision 2 — fences are instruction-level effects, not fake empty-footprint accesses.**
A fence orders, it does not access; it gets no `MemAccessSpec`. MT1's `MFENCE` lands with an
instruction-level declaration (a `fenceEffect`-shaped optional field or an equivalent
registry predicate — exact spelling is MT1's to choose) whose single v1 meaning is "drains
this thread's store buffer," citing §2.1. Defaulted to none: unlike memory-touchingness
(where silent omission was the P4 failure mode), "not a fence" is the overwhelming, safe
default.

**Decision 3 — the multi-thread machine is the operational store-buffer machine, and the
buffer is per-thread machine state.** Answering the question MT2 explicitly leaves to this
document: per-thread execution state includes a FIFO store buffer (list of
address×width×value entries), over one shared sealed `X86_64Memory`. The step relation
(MT2) is: pick a runnable thread and step its view through the hook — loads consult own
buffer (youngest same-address entry) then shared memory; stores enqueue; — or perform a
model-internal **drain** step moving one oldest buffer entry to shared memory; `.rmw`
accesses and fences drain-then-act per §2.1. Nondeterminism lives entirely in the
choice of thread and drain moments — never inside an instruction's semantics.

**Decision 4 — the outcome-set query interface** (Spike 8 demand 5): the machine ships with
an enumeration of reachable final states for bounded straight-line multi-threaded programs
(`reachableOutcomes`-shaped; litmus state spaces are tiny by construction), decidable so
MT4's outcome-set theorems close by `decide`-tier reasoning (Law 10 rung 2) — allowed-outcome
sets are *derived* from the machine, never hand-transcribed from literature tables.

**The two connection theorems that make the model linked rather than a twin** (Law 12; both
part of MT2's bar):

- **Single-thread degeneration**: for one thread, running the store-buffer machine to a
  drained state is observationally equal to the existing sequential interpreter. This is
  what keeps every landed proof (all in the one-thread world) valid against the new machine,
  and it is the multi-thread analogue of MH1's "existing `rfl` lemmas keep closing" bar.
- **Descriptor fidelity for `.rmw`**: a `.rmw` descriptor entry corresponds to one
  indivisible machine action — the annotation is data linked to machine behavior, never a
  label the semantics ignores.

## 3. Composition with trace-level causality

This is the part that must be exact, because the vocabulary already exists twice-adjacent:
`VectorClock.happensBefore` in Core, consumed by `CanonicalizeTrace`'s `CausalEvent` stamps
at the effect boundary, and sketched for lock handover in `docs/OBLIGATIONS_AND_CAUSALITY.md`
§3.1.

**The relation, in one sentence: the memory model is the *generator* of happens-before
edges; the trace layer is a *projection* of them onto effect events.** They are one
causality at two granularities, not two causalities.

- **Machine causality** (this design) orders *memory accesses*: per-thread program order
  (po), plus — once threads exist — synchronizes-with edges (sw) created exactly where TSO
  creates them. For the tree's v1 surface the sw edges are precisely MT3's three:
  **spawn** (parent→child), **join** (child→parent), and **release→acquire** (the `.rmw`
  acquire that reads a given release store). Machine happens-before is the transitive
  closure of po ∪ sw.
- **Observable causality** (`docs/SYSTEM_EFFECTS.md` §6.3–§6.4, built in
  `Gasm/Effects/CanonicalizeTrace.lean`) orders *effect events* — syscall-boundary
  observations. Every effect event is emitted by some instruction; its stamp must be the
  machine happens-before position of the emitting instruction, projected onto the (much
  smaller) set of effectful instructions.

Today that projection is trivially correct by construction: one thread, machine hb =
program order, and `stampSingleThreaded`'s strictly increasing single-thread ticks *are*
program order restricted to emitted events. That is §6.3's degeneration statement, now with
its machine-level justification attached.

With threading (MT3 implements the trace side), the composition contract is:

1. **One vocabulary** (Law 12): the memory model defines no second happens-before. It
   defines edge *sources* (po, sw); positions are expressed through the existing
   `VectorClock` algebra. An sw edge is precisely a `VectorClock.join` point in
   `stampMultiThreaded` — the exact shape `docs/OBLIGATIONS_AND_CAUSALITY.md` §3.1 sketches
   for lock handover. MT3's stamping consumes the machine's sw edges as input; it does not
   invent its own. (MT3 additionally carries the coordination duty with G2's Vulkan sync
   edges — same rule, same clock algebra, no forks.)
2. **Trace-order soundness** (a connection obligation on MT3): if the canonical trace
   asserts `stamp e₁ happensBefore stamp e₂`, the emitting instructions are machine-hb
   ordered — the trace layer never claims causality the machine does not enforce. An
   "ack happens after read" edge is backed by po (same thread) or a chain through sw
   (cross-thread), or it is a stamping bug.
3. **No contradiction is possible in the other direction, and no strength is lost.** The
   coalescing rules constrain what the trace layer may *merge or reorder* (`NetEvent`s are
   barriers; the owner's directive — "writing an ack for a read IS NOT EQUIVALENT to
   writing an ack before a read" — is `ack_after_read_ne_ack_before_read`). Those rules are
   *stricter* than anything the memory model licenses, and memory-model nondeterminism (a
   buffered store draining late) is invisible at the effect boundary unless some load
   observes it — in which case it is an sw edge and hence a trace edge. TSO's S→L
   relaxation reorders memory accesses, never syscalls: effect events on one thread stay in
   program order regardless. The memory model refines *interleavings of memory*; the trace
   model constrains *equivalence of observations*; the projection in (2) is the only
   interface between them. Equivalence of concurrent runs is equality of causal orders —
   linearization-insensitive, per PLAN.md item (e) and MT3's bar — which is exactly what
   makes TSO's unobservable reorderings non-observables in the contract sense.

**Status**: item 1's shape exists today only on the trace side (`VectorClock`,
single-thread stamping); items 2–3 are MT3-era obligations, recorded here so the spike's
proof architecture inherits them as requirements rather than rediscovering them.

## 4. What the memory hook already provides, and what changes for the model

The memory model deliberately **extends MH1's descriptor rather than sitting beside it**
(§2.3 Decision 1). What this buys, concretely:

- **One declaration site per instruction**: MT1's memory-operand `XCHG` declares one
  `.rmw` entry; permissions, faults, perf, measurement, *and* ordering read the same
  descriptor. No fifth per-form annotation surface, and no atomic that can be torn into
  read+write by construction.
- **The address stream is already causal-ready**: `memAccesses` evaluated along a trace is
  the per-thread access stream (`docs/MEMORY_HOOK.md` §3.3 consumer 4); the store-buffer
  machine's event alphabet is exactly that stream tagged with thread and kind. The hook's
  measurement seam and the memory model's event structure are the same data.
- **Frame lemmas extend, not fork**: `writesWithin`/`readsWithin` (landed for all 14 memory
  forms) extend to `.rmw` in the same shard convention instead of a parallel proof surface.
- **The seal composes with threads**: MT2's threaded access goes through the same sealed
  hook (its negative control: a second thread's raw-memory bypass must fail to elaborate) —
  the chokepoint MH1 built is what makes "every access is a machine-model event" a
  structural fact rather than a convention.

What the hook does *not* give and MT2 must add: per-thread buffer state, the multi-thread
step relation with drain, and the degeneration theorem (§2.3). **Status**: all unbuilt.

## 5. `XCHG` today — the honest finding

The suspicion that prompted this section: x86's `XCHG` with a memory operand is implicitly
locked (atomic even without the `LOCK` prefix), so an unannotated `XCHG` in the tree would
be an existing instruction whose real-hardware atomicity we silently fail to model.

**Verified: that gap does not exist today — but only by luck of scope.** The tree's only
form is `XchgR64R64` (register-register, `Xchg.lean`): it touches no memory
(`memAccesses _ := []` is its honest descriptor), and on hardware the implicit-lock rule
applies only to the memory form — reg-reg `XCHG` has no atomicity semantics to model. So
there is **no unmodelled atomicity in the tree**, and nothing about `XCHG` needs the memory
model, or any local ordering statement, today.

What it needs today is a **tripwire, stated locally**: the memory form is the single most
likely way an author introduces the first atomic without noticing (it looks like "just
another MOV-shaped memory form"; nothing in its mnemonic says LOCK). `Xchg.lean` now
carries a doc-comment note stating the implicit-lock fact and pointing at MT1 as the
sanctioned landing for `XchgR64Mem64` — whose atomicity is declared as one `.rmw`
descriptor citing this document, per §2.3. A fact about a form that does not exist belongs
next to the place the form would be born, as a landing precondition — not as semantics
attached to a reg-reg instruction it is false for.

## 6. The dependency rule for atomics, fences, and the ISA expansion

The ruling this operationalizes: machine state grows on spike demand (ADR-0039), **and
atomics arriving means the memory model arrives with them, not after** — a retrofit over an
already-authored atomic population is the predecessor's failure mode. Concretely:

1. **Spike 8's minimal atomic surface** (`XCHG r64,[m64]`, `MFENCE`, optionally `PAUSE`)
   lands via MT1, blocked on this document, with ordering semantics **cited from §2.1, not
   restated** — one source, many citations, no drift.
2. **Everything else stays deferred**: general `LOCK`-prefix machinery, `CMPXCHG`, `XADD`,
   `SFENCE`/`LFENCE` are explicitly out of Spike 8's demand set and remain unbuilt until a
   spike demands CAS or non-temporal stores (Spike 8 §5.1's own deferral list; this
   document concurs and adds the ordering-side reason: each new atomic class must state its
   ordering by citation into §2.1, which today covers them — locked RMWs and drains — so no
   model extension is expected, only instruction work).
3. **The ISA expansion inherits this as a wave-gating rule**
   (`docs/X86_ISA_EXPANSION_PREREQUISITES.md`): GPR/ALU and plain memory-form waves are
   unaffected; any wave containing a `LOCK`-prefixed form, `CMPXCHG`/`XADD`, a memory-operand
   `XCHG`, or a fence acquires MT1 (the pattern-setting landing) and this document as
   prerequisites. `MODEL_DEBT.md` §B2 records the same dependency. **Status**: enforcement
   is review plus the `Xchg.lean` tripwire; a mechanical "no atomic mnemonic without a
   `.rmw` descriptor" check becomes possible the day `.rmw` exists and belongs in MT1's
   registry-audit deliverable, not in a speculative linter now.

## 7. Validation: how TSO claims get falsified, not just stated

Everything in this repository that claims a hardware property is checked against silicon or
an oracle (`x86_fuzzer` vs. silicon, `encoding_fuzzer` vs. NASM). A memory model asserted
and never tested would be §3-of-the-target-spec fiction with better typography. The
instrument is the **litmus battery**, built as MT4 per Spike 8 §2/§7; this section states
the model-side criteria that battery must satisfy, so the model's trust posture is pinned
here with the model itself:

- **Model side**: allowed-outcome sets for every battery test (SB, MP, SB+MFENCE in v1) are
  *derived by enumeration* over the store-buffer machine (§2.3 Decision 4) — never
  hand-transcribed. The SB set must contain `(0,0)` (proving at proof time the model is not
  SC); the MP set must exclude `(1,0)` (proving it is not weaker than TSO); SB+MFENCE must
  exclude `(0,0)` (proving the fence drains).
- **Hardware side**: multi-threaded harness runs on real silicon (Windows and Linux phases;
  QEMU for bare metal with its honesty caveats), histograms as diagnostic artifacts,
  deterministic verdict lines, per Spike 8 §2.4–§2.5.
- **The differential criterion, honestly asymmetric** (Spike 8 §4's falsification table is
  the operational form): (a) **soundness** — a silicon-observed outcome outside the model's
  allowed set falsifies the model, hard exit; (b) **the witness floor as negative control**
  — a run that never observes SB's `(0,0)` did not exercise the race and validated nothing
  (honest exit 2, never a synthesized pass) — Law 13's the-gate-must-be-shown-able-to-fail
  discipline applied to hardware validation; (c) **forbiddenness is never established by
  hardware** — absence claims rest on the Lean-side enumeration plus the SDM citation;
  observed absence is a bounded statement ("not in N iterations"), recorded as such.
- **Sequential atomics validate immediately**: MT1's forms get single-threaded silicon
  fuzzing (`x86_fuzzer`) and NASM encoding differential the day they land; what those
  cannot see is precisely the multi-thread ordering content, which is why the battery is
  the model's permanent regression instrument, not a one-shot experiment.
- **Measurement governance**: v1 histograms are diagnostic/failure artifacts. The moment
  any measured outcome frequency is *consumed* — by the perf model or as a cited validation
  artifact — it enters Law 14 calibration governance (checked in, harness-regenerable,
  provenance-stamped, controls recorded — `docs/CALIBRATION_GOVERNANCE.md`), matching
  MT4's own note.

## 8. Rejected alternatives

- **State a single-thread ordering theorem now** ("all loads/stores occur in program
  order"): true, vacuous (one thread admits no other order), and it would decorate the
  tree with a memory-model-shaped artifact that verifies nothing — the same
  confidence-manufacturing the old §3 fiction performed, minus the false symbols (TC17
  class).
- **Land the ordering vocabulary ahead of its consumer**: a `.rmw` kind (or any ordering
  field) consumed by nothing is a Law 8 dead abstraction and a Law 12 twin born unlinked.
  It lands inside MT1/MT2, next to the instructions and machine that consume it.
- **A per-access `MemOrder` annotation field alongside the kind**: on x86-TSO it would
  duplicate the plain-vs-locked distinction the `.rmw` kind already draws, with no third
  value to express — speculative generality for a hypothetical weaker target (Law 8 risk).
  Slots in next to its first real consumer if one ever exists.
- **A second happens-before vocabulary for the machine level**: Law 12's unlinked-twin
  warning applied to relations. One `VectorClock` algebra; the memory model produces edges,
  the trace layer consumes positions (§3).
- **An axiomatic (execution-graph) model instead of the operational store-buffer machine**:
  axiomatic models shine at checking many candidate executions; this repository needs a
  model that *composes with a step interpreter* and degenerates definitionally to the
  existing sequential semantics. The operational machine gives the degeneration theorem,
  interpreter integration, and decidable litmus enumeration cheaply. Revisit only if
  enumeration proves unwieldy at larger litmus shapes.
- **Sequential consistency as the stated model**: refuted by the first SB run on any real
  x86 — stating a model known-refutable by the first measurement is anti-calibration. TSO
  is barely more complex and is what the vendor promises.
- **Modeling memory types / non-temporal stores / MMIO ordering now**: no consumer, no
  instruction forms; the bare-metal LAPIC need is MT6's Stop-and-Design to raise (Law 5).

## 9. Open questions

None requiring an owner ruling beyond those already made: the fence-timing question this
design would otherwise have asked (land fences before threading?) was answered by the
concurrent Spike 8 ruling — `MFENCE` lands with the spike that gives it meaning; and the
validation-venue question is settled by the spike's three-target structure with QEMU's
limitations stated honestly (Spike 8 §6.3). If MT1/MT2 implementation surfaces a conflict
between this document's structural decisions (§2.3) and the spike's demand list, the
protocol is Spike 8 §5.2's: this document owns the model and gets amended deliberately,
never silently.

## 10. Tracking

| Vehicle | Relation to this design |
| :-- | :-- |
| `docs/tasks/MT1-atomic-primitives.md` | builds §2.3 Decisions 1–2's first instances (`XchgR64Mem64` as one `.rmw` descriptor; `MFENCE`); cites §2.1 for ordering semantics |
| `docs/tasks/MT2-multithreaded-machine-state.md` | builds §2.3 Decision 3's machine + Decision 4's enumeration + both connection theorems |
| `docs/tasks/MT3-causal-trace-generalization.md` | builds §3's projection: `stampMultiThreaded`, the three sw edge kinds, trace-order soundness |
| `docs/tasks/MT4-litmus-battery.md` | builds §7's instrument, both sides of the differential |
| `docs/tasks/MT5-spike8-windows-linux.md`, `docs/tasks/MT6-baremetal-smp-design.md` | the spike's target phases; consume, never restate, the model |
| `docs/tasks/TC22-doc-lean-fence-facade.md` | the Law 13 missing-gate finding from the old §3 fiction: fenced ` ```lean ` theorem blocks are invisible to `check_doc_facade.py`; measured precision analysis in the task file |
