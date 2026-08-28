# Spike 8: Multithreading — TSO Litmus Battery & Verified Spinlock Counter

**Status**: This is a **design document for a spike that is not yet built**. Nothing
described below exists in the Lean tree today unless explicitly marked otherwise; every
Lean identifier named here is proposed, not implemented. Implementation is tracked as
`MT1`–`MT6` in `docs/tasks/`, and is blocked on the sequencing dependencies in §9.
The memory model this spike consumes is `docs/X86_MEMORY_MODEL.md` (landed in the same
change window as this document, by a separate design effort); its Lean embodiment is
that design's XM1, and its validation instrument is its XM2 — both demand-gated on
exactly this spike (its §2.2 trigger 2). §5.2 maps this spike's demands onto that
document's answers.

Spike 8 is the first concurrent spike. The owner's direction, verbatim: *"are we doing
atomic accesses yet for x86? they need a causality memory model stated"* and *"we can
grow a multithreading spike for this, and i think that's a reasonable thing to do before
scaleup (and validate it against windows, linux, bare metal)"*. Per the spike discipline
(`docs/SPIKES.md` §1, ADR-0008), the memory model is not written speculatively and then
searched for a use: this spike is the demand that forces it to be real, and the
instrument that validates it against three real machines.

The spike is one program, three targets:

1. **x86_64 Windows (`.exe`)** — threads via `CreateThread` / `WaitForSingleObject`
   through the existing Win32 import machinery.
2. **x86_64 Linux (static ELF)** — threads via raw `SYS_clone` with an `mmap`'d child
   stack, consistent with the existing raw-syscall Linux target.
3. **x86_64 bare metal (QEMU)** — genuine SMP bring-up (INIT–SIPI–SIPI, real-mode
   trampoline, per-CPU stacks). Materially more expensive than the other two; sequenced
   as Phase C with its own Stop-and-Design gate (§8.3, MT6).

---

## 1. What the Spike Must Force (and Why Threads-and-Join Proves Nothing)

A spike that spawns threads, joins them, and prints a result exercises the *spawn
mechanism* but places zero demand on the memory model: any model from sequential
consistency down to no-model-at-all makes it pass. Spike 8 is therefore built from
programs whose **observable outcomes depend on the ordering model**:

- A **litmus battery** (§2) whose per-test outcome histograms distinguish x86-TSO from
  both stronger (SC) and weaker (ARM-like) models. This is the model's validation
  instrument, playing the role `x86_fuzzer` plays for single-instruction semantics.
- A **verified computation** (§3) — a spinlock-protected shared counter — whose
  correctness theorem is only provable *given* TSO ordering and *given* atomic
  read-modify-write, and whose hardware execution fails observably if either is wrong
  in the implementation.

The two halves have complementary failure diagnostics: a litmus violation indicts the
*model*; a counter mismatch with a clean litmus battery indicts the *implementation*.

---

## 2. The Litmus Battery

Three classic tests, two threads each, shared locations `x`, `y`, `data`, `flag`
initialized to `0` before every iteration and placed on **distinct cache lines**.
Notation: `r0`, `r1`, `r2` are per-thread registers whose final values are the outcome.

### 2.1 SB (Store Buffer) — the test that falsifies sequential consistency

| Thread 0          | Thread 1          |
|-------------------|-------------------|
| `MOV [x], 1`      | `MOV [y], 1`      |
| `MOV r0, [y]`     | `MOV r1, [x]`     |

| Outcome `(r0,r1)` | SC        | x86-TSO   | Role |
|-------------------|-----------|-----------|------|
| `(1,1)` `(1,0)` `(0,1)` | allowed | allowed | uninteresting |
| `(0,0)`           | **forbidden** | **allowed** | **witness outcome** |

`(0,0)` is only reachable when each thread's store is still in its store buffer while
the other thread's load reads memory — the store→load reordering that defines TSO. On
real silicon it appears reliably within thousands of iterations of a properly staggered
harness. **If the model were SC, this outcome would falsify it on the first witnessed
run.** Conversely, a harness that never witnesses `(0,0)` on silicon is not exercising
the race and its "pass" is vacuous (§7.2).

### 2.2 MP (Message Passing) — the test that falsifies a too-weak model

| Thread 0            | Thread 1            |
|---------------------|---------------------|
| `MOV [data], 1`     | `MOV r1, [flag]`    |
| `MOV [flag], 1`     | `MOV r2, [data]`    |

| Outcome `(r1,r2)` | x86-TSO | ARM/weak | Role |
|-------------------|---------|----------|------|
| `(0,0)` `(0,1)` `(1,1)` | allowed | allowed | uninteresting |
| `(1,0)`           | **forbidden** | allowed | **forbidden outcome** |

`(1,0)` requires either store–store or load–load reordering, both of which TSO
prohibits. Observing it on x86 silicon would mean the model's ordering guarantees are
claims the hardware does not honor — model unsound, hard failure. This test is also
what makes the *spinlock unlock* argument in §3 non-vacuous: unlocking with a plain
`MOV` is correct **only because** of exactly these two preserved orderings.

### 2.3 SB+MFENCE — the test that validates the fence

Same as SB with `MFENCE` inserted between the store and the load in **both** threads.
Under TSO-with-fences, `MFENCE` drains the store buffer, so `(0,0)` becomes
**forbidden**. Observing it means the fence semantics (or its encoding) are wrong.

### 2.4 Harness shape

Two persistent worker threads; per-iteration handshake (start flag, completion flags),
randomized stagger loops (0–63 empty iterations per thread per run) to move the race
window; `K` iterations per test per run (default 100,000, env-overridable); outcome
histogram accumulated per test. The handshake itself uses the primitives under test —
this circularity is standard litmus-harness practice (herd/litmus7 does the same) and
is acceptable because a broken primitive surfaces as a forbidden outcome or a hang, not
as a silent pass.

### 2.5 Output protocol (deterministic verdicts over nondeterministic runs)

Histograms are nondeterministic; the spike test protocol (`docs/SPIKES.md` §4) is
exact-match on stdout. Resolution: **stdout carries only quantized verdict lines;
histograms go to stderr** as a diagnostic artifact.

```
SPIKE8 SB       forbidden=0 witness=present
SPIKE8 MP       forbidden=0
SPIKE8 SB+FENCE forbidden=0
SPIKE8 LOCKCOUNT value=200000 expected=200000
SPIKE8 PASS
```

Exit codes follow the honest-runner convention (`docs/SPIKES.md` §4 item 5): `0` = all
verdicts pass *including* the SB witness floor; `1` = a forbidden outcome was observed
or the counter is wrong (verification failure — the stderr histogram and the iteration
seed are the failure artifact); `2` = the run could not meaningfully validate the model
(SB witness absent — the race was not exercised, e.g. single-CPU host or QEMU TCG,
§6.3) and this is reported honestly rather than synthesized into a pass.

---

## 3. The Verified Computation: XCHG Spinlock Counter

Two threads each perform `M = 100,000` increments of a shared 64-bit counter under a
test-and-set spinlock:

```
acquire:  MOV  rax, 1
spin:     XCHG rax, [lock]      ; atomic RMW (implicit LOCK), full fence
          TEST rax, rax
          JNZ  spin
          ; --- critical section ---
          MOV  rax, [count]
          ADD  rax, 1
          MOV  [count], rax
          ; --- end critical section ---
release:  MOV  qword [lock], 0  ; plain store: release IS enough — but only under TSO
```

Assertion at join: `[count] = 2 * M = 200,000`.

Every line of this program leans on the model:

- **`XCHG r64, [m64]` must be an atomic read-modify-write** (implicit `LOCK`, Intel
  SDM). Today the tree has only `XchgR64R64` (`Gasm/Targets/X86_64/Instructions/
  Xchg.lean`) — no memory form exists, and no atomicity is modelled anywhere. Without
  atomic RMW in the model, mutual exclusion is simply unprovable — the forcing is at
  proof time. (New form tracked as MT1.)
- **Unlock by plain `MOV` is correct only under TSO**: the release store cannot be
  reordered before the critical-section store (store–store order) nor before the
  critical-section load (load–store order). Under a weaker model the proof does not
  close without an `SFENCE`; under SC the SB litmus falsifies the model instead. The
  proof of this line *is* the memory model earning its keep.
- **The critical section is a deliberate load/add/store**, not a locked `ADD [m], r`:
  if mutual exclusion is broken, the lost-update window is wide and the final count is
  observably short on hardware with high probability.
- **The spin loop is unbounded** — the first loop in the tree whose termination is a
  liveness property, not a fuel bound. It instantiates the ratified inner/outer
  reactive contract (§5.4).

What would be observably wrong: `LOCKCOUNT value=199987 expected=200000` — a lost
update. With a clean litmus battery this indicts the implementation (broken atomic,
misencoded fence, wrong lock protocol), not the model.

---

## 4. Falsification Table — What a Wrong Model Looks Like

| If the model is…            | Formal symptom                                        | Hardware symptom                                  |
|-----------------------------|-------------------------------------------------------|---------------------------------------------------|
| SC (too strong)             | Model outcome set for SB excludes `(0,0)`             | SB witnesses `(0,0)` on silicon → run exits `1` against the model's predicted set |
| Weaker than TSO             | MP `(1,0)` appears in the model's allowed set; the model-side MP theorem (§7.1) is unprovable as stated | None — hardware cannot exhibit an outcome to prove *forbiddenness*; the guard is the Lean-side enumeration theorem plus SDM citation |
| Missing RMW atomicity       | Mutual-exclusion theorem unprovable                   | Counter short (lost updates)                       |
| Wrong fence semantics       | SB+MFENCE enumeration retains `(0,0)`                 | SB+MFENCE witnesses `(0,0)` → exit `1`             |
| Right model, wrong encoding | Proofs all close                                      | Litmus/counter failures with clean proofs → indicts emitter/encoding, caught by hardware run |

The asymmetry in row 2 is fundamental and stated honestly: hardware runs can only
falsify claims of *forbiddenness* (by witnessing) — they can never establish it. Claims
of forbiddenness rest on the Lean-side model enumeration plus the ingested Intel SDM
memory-ordering text (the `intel_sdm` reference corpus, Law 4). Claims of
*allowedness* get witness floors where reliably observable (§7.2).

---

## 5. What This Spike Forces Into the Repository

This section is the design's real output: the demand list. Each item is
proposed-and-unbuilt (**Status**: none of §5 exists in the tree today; tracked
MT1–MT4).

### 5.1 ISA surface (MT1) — deliberately minimal

| Instruction | Why | Notes |
|---|---|---|
| `XCHG r64, [m64]` | spinlock acquire | Memory form of existing `Xchg.lean`; implicit-LOCK atomicity is the point. Encodes `87 /r`. |
| `MFENCE` | SB+MFENCE litmus | `0F AE F0`. First fence in the tree. |
| `PAUSE` (optional) | spin-loop hygiene | `F3 90`. Semantically a no-op; perf-model-relevant only. May be deferred without harming the spike. |

**Deliberately deferred, not forgotten**: general `LOCK` prefix machinery, `CMPXCHG`,
`XADD`, `SFENCE`/`LFENCE`. No program in this spike demands them; growing them now
would be the wsc failure mode (ADR-0008). They arrive when a spike needs CAS.

Both new forms carry the full instruction contract: `memAccesses` descriptors using
XM1's ordering vocabulary (`docs/X86_MEMORY_MODEL.md` §2.3: the atomic RMW's entries
carry `order := .locked`; `MFENCE` is not an access and declares a `fenceEffect`
instead of a fake empty-footprint descriptor), roundtrip/registry entries, NASM
differential (`encoding_fuzzer`), silicon fuzz (`x86_fuzzer`) for the single-threaded
semantics, and sourced cost coefficients per D30's P4/P5 ruling. Per that design's §6:
the first atomic form, its `.locked` descriptors, and XM1's TSO machine (with its
degeneration theorem) are **one indivisible landing** — MT1 cannot land before or
without XM1. Its §6 class 2 recommends fences land only with the first threaded spike;
this spike *is* that spike, so `MFENCE` arriving here is consistent with its Q1
default.

### 5.2 Demands on the memory model — and how the landed design answers them

`docs/X86_MEMORY_MODEL.md` was designed concurrently by a separate effort and landed
in the same change window as this document. **Ownership split**: that document owns
the model — its structure, SDM citations, memory-type scope, trust posture, and the
XM1/XM2 implementation tasks. This document owns the *demand list*: what Spike 8
needs the model to answer. The mapping, demand by demand:

1. **An operational small-step model with enumerable litmus outcome sets** →
   satisfied: its §2.1 states x86-TSO operationally (per-thread FIFO store buffers,
   store forwarding, locked-RMW drain-and-indivisible, `MFENCE` drain); its §7 makes
   litmus outcome sets mechanically enumerable (`decide`-class, Law 10 rung 2) as
   XM2's model-side deliverable.
2. **Exactly four primitive behaviors** (plain store, plain load, locked RMW, fence)
   → satisfied: §2.3's `MemOrder.plain`/`.locked` on the MH1 descriptor plus the
   `fenceEffect` field with `drainStoreBuffer` as TSO's only needed constructor.
3. **WB-only scope for v1** → satisfied verbatim (its §2.1 scope paragraph); MMIO/UC
   ordering for the bare-metal LAPIC (§6.3 here) is exactly the "spike forces a scope
   extension through Law 5" case it anticipates, owned by MT6's design pass.
4. **Atomic RMW rides the MH1 hook, untearable** → satisfied by construction: the
   ordering vocabulary attaches to `MemAccessSpec` itself, and §2.3's descriptor
   fidelity obligation (frame-lemma convention extended with atomicity) makes
   `.locked` a proof-linked property, not a label.
5. **An outcome-set query usable in theorem statements** → XM2's model-side
   enumeration, from which §7.1's outcome-set theorems are stated. This spike embeds
   the SB/MP/SB+MFENCE **subset** in its emitted binaries; XM2's host harness owns
   the full battery (LB, 2+2W, IRIW, fenced/locked variants) and the Law 14
   calibration-artifact regime for silicon results. One source for test definitions
   and expected outcome sets (Law 12): the spike consumes XM2's encodings, never
   re-transcribes them.

Two obligations the model document explicitly leaves to this spike design (its §3
items 1–2 and closing note), accepted here and assigned to MT3: the multi-threaded
successor of `stampSingleThreaded` consumes the machine model's synchronizes-with
edges as input (one `VectorClock` vocabulary, no second happens-before), and the
**trace-order soundness** connection theorem — a causal edge asserted in the
canonical trace must be backed by machine happens-before (po, or a chain through sw).

### 5.3 Machine state (MT2) — the D30 demand arriving

ADR-0039/D30 ruled machine state grows on spike demand. This spike is that demand.
The store-buffer half is already claimed: XM1 (`docs/X86_MEMORY_MODEL.md` §2.3) builds
the two-level TSO state — shared `X86_64Memory` plus per-thread FIFO store buffers,
the `TsoStep`/`drain` relation, and the single-thread degeneration theorem. What
remains for this spike (MT2) is the execution layer above it:

- **Per-thread execution state**: registers, flags, RIP — composed with XM1's
  per-thread buffers. Indexed by the existing `ThreadId` (`Gasm/Core/Types.lean`,
  already in tree).
- **Shared sealed memory**: one memory, MH1's hook, accessed by all threads.
- **Thread lifecycle**: spawn/terminate/join transitions emitting the causal edges
  MT3 stamps.
- **A preservation constraint on the generalization**: the single-threaded
  `X86_64MachineState` and its ~88 instruction step functions and step lemmas must
  survive as the **one-thread specialization** — per-instruction semantics stay
  written against a thread-view (that thread's registers plus the shared memory hook),
  and the multi-threaded step is "pick a thread (or drain a buffer), step its view."
  A migration that rewrites 88 instruction semantics is a design failure; the
  interleaving lives in the scheduler layer, not in the instructions.

No XMM, no MXCSR, no fault taxonomy, no interrupt state — this spike does not demand
them (same Law 5 logic that declined P1).

### 5.4 Trace semantics (MT3) — how a multi-threaded trace is even stated

Ratified groundwork already exists and this spike makes it load-bearing:
`VectorClock`/`happensBefore`/`join`/`tick` (`Gasm/Core/Types.lean`), the
synchronizes-with edge design (`docs/OBLIGATIONS_AND_CAUSALITY.md` §3.1), the
causally-ordered-event-set canonical form (`docs/SYSTEM_EFFECTS.md` §6.3/§6.4, PLAN.md
Phase-4 items (d)/(e)), and `CausalEvent`/`stampSingleThreaded`
(`Gasm/Effects/CanonicalizeTrace.lean`, in tree).

The answer to "interleavings or per-thread traces?" was effectively ratified in
PLAN.md item (e) and this spike adopts it: **per-thread event traces plus a
happens-before partial order — never a distinguished interleaving.**

- `stampMultiThreaded` (proposed) generalizes `stampSingleThreaded`: each thread ticks
  its own clock component; cross-thread edges join clocks at exactly three places —
  **spawn** (parent→child), **join** (child→parent), and **lock release→acquire**
  (the §3.1 synchronizes-with edge: the XCHG that reads a given unlock store joins the
  releaser's clock).
- **Equivalence is equality of causal orders** — linearization-insensitive, exactly as
  ratified. Two hardware runs that schedule differently but have the same
  happens-before structure are the same canonical trace.
- **The schedule is a universal binder.** PLAN.md Phase 4 establishes `read` as the
  ∀-vector that makes pinning input unrepresentable (Law 9). The concurrent analogue:
  contract shapes quantify over the scheduler oracle; a proof that pins one
  interleaving must be unrepresentable, the same way a pinned read result is.
- **Multiple unbounded loops** get the ratified per-loop inner/outer treatment
  (`docs/EQUIVALENCE_PROOFS.md` §1.1, PA7 `VerifiedReactiveProgram`; generalization to
  multiple loops per PLAN.md item (d)): for the spin loop, **inner** = deterministic
  both-ways equality of the critical section per acquisition; **outer** =
  progress/liveness — under an explicit fairness assumption (every runnable thread is
  scheduled infinitely often; every buffered store eventually drains), every acquire
  eventually succeeds. Fairness is stated as a named hypothesis on the theorem, never
  smuggled in. Deadlock-freedom at the declared sync points is part of the outer
  obligation.
- **Coordination note**: G2 (GPU synchronization DSL) builds synchronizes-with edges
  into the same causal layer for Vulkan. MT3 and G2 share `VectorClock` and the edge
  machinery; neither should fork it. Whichever lands second consumes the first's
  vocabulary.

---

## 6. Three Targets, Three Mechanisms, Honest Costs

### 6.1 Windows — Phase A (cheapest)

Mechanism: extend `Gasm/Targets/Windows/Win32API.lean`'s import list and hook pattern
(the same machinery that models `GetStdHandle`/`WriteFile`/`VirtualAlloc` today) with:

- `CreateThread` — hook semantics: allocate a stack (existing `VirtualAlloc` model),
  create a model thread with `RIP` = start routine, `RCX` = parameter (Microsoft x64
  ABI), fresh `ThreadId`; returns a handle; emits the spawn causal edge.
- `WaitForSingleObject` (on a thread handle, `INFINITE`) — join: blocks until the
  target thread terminates; emits the join causal edge.
- `ExitThread` (or return from the start routine) — thread termination.

Cost: **low** — the import/hook pattern is established; the new cost is that hooks
must interact with the multi-thread scheduler layer (MT2) rather than a single state.

### 6.2 Linux — Phase B (cheap, shares everything but spawn/join)

Mechanism: raw syscalls in the existing static-ELF style
(`Gasm/Targets/Linux/Syscall.lean` already models numbers 0–50; `SYS_mmap` is in
tree):

- `SYS_clone` (56) with `CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
  CLONE_THREAD`, child stack from the existing `mmap` model.
- **Join by spin, not futex**: the child writes a per-thread done-flag (a plain TSO
  release store) and calls `SYS_exit` (60); the parent spins on the flag. This keeps
  `futex` — a large, subtle syscall — out of the v1 demand set. Filed as deliberate
  debt: a later spike that needs blocking waits grows `SYS_futex` on demand.

Cost: **low**, marginally above Windows (clone's flag semantics need careful SDM/man
citation), and the entire model/proof/trace layer is shared with Phase A. The litmus
battery and counter are target-independent by construction; only spawn/join differ.

### 6.3 Bare metal — Phase C (materially harder; sequenced last, with reasons)

The current bare-metal target (`Gasm/Targets/BareMetal/`, boots under QEMU via the PVH
note path, UART console — in tree, Spike 1 runs on it) starts **one** CPU. There is no
OS to ask for a thread; "spawn" means SMP bring-up:

- **INIT–SIPI–SIPI** to each application processor via the LAPIC interrupt command
  register — which means a LAPIC device model (xAPIC MMIO page at `0xFEE00000`, or
  x2APIC via `RDMSR`/`WRMSR`, which are themselves unmodelled instructions).
- **The SIPI vector is a real-mode entry point**: a 16-bit trampoline below 1 MB that
  must load a GDT, enter protected mode, enable paging/long mode, and far-jump to
  64-bit code — three execution modes, two of which (`docs/TARGETS/X86_REALMODE.md`,
  `docs/TARGETS/X86_32.md`) are design-only documents with no Lean implementation.
  The alternative — an unverified byte-blob trampoline — is a TCB entry that the
  proof-carrying discipline would have to declare loudly.
- **Per-CPU stacks**, an AP parking/rendezvous protocol, and MMIO ordering for the
  LAPIC (UC semantics — outside the v1 WB-only model scope, §5.2 item 3).
- **QEMU accel honesty**: under TCG emulation, guest memory operations do not go
  through a modelled store buffer — the SB witness outcome may simply never appear.
  A TCG run therefore reports `witness=absent` and exits `2` (validation did not run),
  never a synthesized pass; the witness floor binds only under hardware-accelerated
  virtualization (WHPX/KVM) or real silicon. Windows and Linux native runs *are*
  silicon, which is why Phases A and B carry the witness floors.

Cost: **high — roughly comparable to the original bare-metal target bring-up itself**,
and it sits on model scope (MMIO ordering, new instructions, new execution modes) that
Phases A/B do not need. Treating all three targets as equal-cost would be dishonest.
Sequencing ruling this design proposes: **Phases A and B first, together; Phase C
after both are green**, gated on its own Stop-and-Design task (MT6) that ingests the
SDM MP-initialization material and decides the trampoline question *before* any Lean.
The owner's "validate against windows, linux, bare metal" is honored in full — as a
sequence, not a simultaneous start.

---

## 7. Verification & Validation Contract

### 7.1 Lean-side theorems (proposed; names illustrative)

| Theorem | Statement (informal) | Discharge |
|---|---|---|
| `sb_outcome_set` | Model's reachable outcomes for SB = `{(0,0),(0,1),(1,0),(1,1)}` — `(0,0)` **included** | enumeration over the bounded operational model |
| `mp_outcome_set` | Model's reachable outcomes for MP exclude `(1,0)` | enumeration |
| `sb_mfence_outcome_set` | With fences, `(0,0)` excluded | enumeration |
| `spinlock_mutual_exclusion` | ∀ schedules, critical sections do not overlap | invariant over the model, ∀-bound scheduler |
| `spike8_counter_correct` | ∀ schedules, joined final state has `count = 2*M` | mutual exclusion + per-section determinism |
| `spike8_progress` | Under the named fairness hypothesis, every acquire succeeds and the program terminates | outer half of the inner/outer pair |
| `spike8_trace_equivalence` | Canonical causal trace of the lowered program refines the nondeterministic spec's allowed set (refinement + liveness direction, per `docs/EQUIVALENCE_PROOFS.md` §1.1 for nondeterministic specs) | per-target |

The first three are the formal half of validation and are XM2's model-side
deliverable (`docs/X86_MEMORY_MODEL.md` §7: outcome sets derived mechanically by
enumeration, never hand-transcribed from the literature); they appear here as spike
acceptance criteria, not as a second implementation. They pin the model's *predicted*
outcome sets, which the hardware histograms are then checked against — XM2's
differential criterion, honestly asymmetric: observed-on-silicon ⊆ model-allowed is
the hard soundness check; witness observation proves the harness can see reordering;
never-observed forbidden outcomes are evidence of tightness, not proof. A model too
weak fails `mp_outcome_set` at proof time; a model too strong fails `sb_outcome_set`
at proof time; and if a wrong model somehow proves both, the hardware runs are the
backstop (§4).

### 7.2 Hardware validation protocol

A single green run proves almost nothing about a nondeterministic system — a
one-in-ten-thousand interleaving bug is the *normal* case. The protocol:

- **Repetition**: `K = 100,000` iterations per litmus per run (env-overridable), with
  randomized per-thread stagger; CI runs the full battery on every spike execution,
  and a scheduled stress lane runs a larger budget (e.g. 10×) off the critical path.
- **Soundness check (hard)**: `hardware-observed ⊆ model-allowed`, per test. One
  forbidden outcome in any run, ever, is a verification failure (exit `1`); the stderr
  histogram + PRNG seed is the reproduction artifact.
- **Witness floors (vacuity guard, TC17's principle applied to concurrency)**: for
  outcomes that are reliably observable on silicon — SB `(0,0)` is the designated one
  — the run must actually observe them (`witness=present`), else it exits `2`:
  the race was not exercised and nothing was validated. This is the same
  negative-control discipline `docs/X86_MEMORY_MODEL.md` §7 imposes on XM2's host
  harness. Division of artifacts: XM2's host-harness silicon results are Law 14
  calibration-class artifacts (checked in, regenerable, never hand-edited); the spike
  binary's own runs are pass/fail verdicts with stderr histograms as diagnostics.
- **What a failing run looks like, concretely**: stdout
  `SPIKE8 MP forbidden=3 …` → exact-match failure against the expected verdict line →
  exit `1`; stderr carries `MP: (0,0)=61274 (0,1)=22409 (1,1)=16314 (1,0)=3 seed=0x…`.
  Three counts out of a hundred thousand is a *loud* result for this class of bug —
  which is precisely why the battery exists as a permanent regression instrument
  rather than a one-shot experiment.

---

## 8. Spec Shape (Sketch)

The high-level spec is deliberately small. The litmus spec is the **outcome set
itself** (the nondeterministic spec: the set of allowed final `(r,r)` pairs per test);
the counter spec is deterministic at the join point:

```lean
-- Proposed, not implemented (MT4/MT5).
def spike8CounterSpec (m : Nat) : Nat := 2 * m          -- observable at join
def sbAllowed : Finset (Bool × Bool) := {(false,false), (false,true), (true,false), (true,true)}
def mpAllowed : Finset (Bool × Bool) := {(false,false), (false,true), (true,true)}  -- (1,0) absent
```

Equivalence direction per the ratified observation standard: deterministic parts
(counter value at join, verdict lines) get both-ways equality; the nondeterministic
whole gets refinement (every model execution lands in the allowed set) plus the
liveness half. Observables are the syscall/effect-boundary events under the
established coalescing congruence; the causal order — not any particular
linearization — is what is compared.

---

## 9. Sequencing — What Must Land Before Lean Is Written

Law 5 order, stated plainly:

| # | Dependency | State today | Owner |
|---|---|---|---|
| 1 | `docs/X86_MEMORY_MODEL.md` — the model statement (§5.2's demand list) | **landed** (same change window as this document) | separate design effort; this spike consumes it |
| 2 | MH1 — sealed memory hook | task `ready`, implementation underway | MH1; atomic RMW rides its `MemAccessSpec` |
| 3 | XM1 — ordering vocabulary + TSO machine + degeneration theorem | filed with #1, demand-gated **on this spike** (its §2.2 trigger 2) | the model design's task set |
| 4 | MT1 — `XCHG r64,[m64]` + `MFENCE` instruction forms (one indivisible landing with XM1, per #1's §6) | not started | this spike's task set |
| 5 | MT2 (thread lifecycle/scheduler over XM1's machine) + MT3 (causal traces, trace-order soundness) | not started | this spike's task set |
| 6 | XM2 (litmus encodings, outcome enumeration, host silicon harness) + MT4 (the same battery embedded in emitted binaries) | not started | XM2: model design's; MT4: this spike's |
| 7 | Phases A+B implementation (MT5 counter+targets) | not started | after 2–6 |
| 8 | Phase C bare-metal SMP (MT6 Stop-and-Design first) | not started | after 7 |

The owner's "before scaleup" framing holds: nothing here blocks on ISA expansion, and
the expansion's Wave B (memory forms) independently wants MH1 — the two efforts share
a prerequisite, not a conflict. In the other direction, this spike *unblocks* part of
the expansion: `docs/X86_MEMORY_MODEL.md` §6 gates every atomic and fence form on XM1,
and XM1's demand trigger is this spike.

## 10. Follow-On Tasks

Filed under `docs/tasks/`, track `concurrency`, validated by
`python scripts/task_frontier.py --validate`. XM1/XM2 are filed by the memory model
design and referenced here via `blocked_on` prose (not `after:` ids) until both task
files are stably in-tree; converting those references to `after:` entries is part of
whichever change lands second.

| Task | Title | Sequenced on |
|---|---|---|
| MT1 | Atomic primitives: `XCHG r64,[m64]` (implicit LOCK) + `MFENCE` | MH1; indivisible with XM1 |
| MT2 | Thread lifecycle + per-thread execution state over XM1's TSO machine | MH1; XM1 |
| MT3 | Causal traces: `stampMultiThreaded`, sw edges from the machine model, trace-order soundness | PA5; coordinate with G2 |
| MT4 | Emitted-binary litmus battery, reusing XM2's test definitions and outcome sets | MT1, MT2, MT3; XM2 |
| MT5 | Spike 8 Phases A+B: Windows + Linux spinlock counter, verified | MT4, PA7 |
| MT6 | Bare-metal SMP bring-up: Stop-and-Design (MP init, trampoline, LAPIC, accel honesty) | MT5 |
