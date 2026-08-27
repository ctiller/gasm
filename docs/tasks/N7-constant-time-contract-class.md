---
id: N7
title: Constant-time/secrecy contract class design
status: ready
blocked_on: ""
after: [PA2]
related: []
bar: ""
track: networking
priority: 6.5
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# N7: Constant-time/secrecy contract class design

## Context

`TASKS.md`'s line for this task: "constant-time/secrecy contract class design (crypto
prerequisite; MODEL_DEBT F2) — after: PA2 (contract shapes)." This task depends on PA2 (the
step-lemma library + composition calculus design) because a non-interference contract needs to be
statable in terms of the same per-instruction/routine contract vocabulary PA2 establishes for
ordinary correctness contracts — N7 is adding a *third kind* of thing a routine contract can
assert, alongside the correctness and performance contracts PA2/PA4's machinery already supports,
so it needs PA2's contract shapes to exist first.

### F2 — quoting MODEL_DEBT verbatim

`MODEL_DEBT.md` §F2, quoted in full — this is the task's entire justification, stated by the
project's own debt ledger:

> **F2. Constant-time / secrecy debt (servers, crypto).** Unrepresentable in *either* current
> lens: correctness contracts say nothing about secret-dependence; the cost model reports one
> number per block with no notion of input-dependent timing. This is a **third contract class** —
> non-interference ("no branch condition or memory address depends on secret input"), a static
> analysis over the uop stream, not a proof about results. Cheap to state, and cheaper now than
> after the optimizer starts introducing data-dependent branches for speed.

Unpack what "unrepresentable in either current lens" means concretely, since it is the whole
argument for why this needs to be a *new* contract class rather than an extension of an existing
one:

- **The correctness lens** (routine contracts as `docs/VISION.md` §4 describes them:
  precondition/postcondition/memory-frame/ABI/trace) proves statements about *results* — given
  this input, the routine produces that output, following that trace. A constant-time violation
  produces the exact same result, on the exact same trace, whether or not the branch/memory-access
  pattern depended on a secret — correctness contracts as currently shaped have literally no
  vocabulary slot to say anything about *how* the result was computed with respect to which inputs
  are secret. A routine can be perfectly correct and leak its secret input through timing on every
  single call.
- **The performance lens** (cost contracts per `docs/VISION.md` §5 — `nominalCycles`,
  `computeCycleBounds`, the parametric cost-function end-state) reports, per MODEL_DEBT's words,
  "one number per block" — a single cost value (or bound) for a given routine/input-size class.
  It has no notion of the cost function's *shape as a function of secret-dependent branching* —
  whether two different secret values could ever cause the routine to take a measurably different
  number of cycles. A cost model that says "this routine costs `N` cycles" for a fixed `N` derived
  from the instruction sequence cannot distinguish "this routine always takes `N` cycles regardless
  of secret input" from "this routine takes `N` cycles for *this particular* secret input and a
  different number for another" — because it was never asked the question in terms of two
  different secret values at all.

**The forcing function — `docs/VISION.md` §1**, quoted:

> **Web/gRPC servers**: threading and async I/O; protocol causality (§ SYSTEM_EFFECTS 6.4);
> cryptography — which adds a third contract class beyond correctness and performance: **secrecy
> contracts** (constant-time execution, provable as input-independence of the cost function).

This is one of the four named target system classes (`docs/VISION.md` §1: game engines, operating
systems, web/gRPC servers, databases) stating explicitly that cryptography is a demand this
project has already committed to serving, and that serving it requires exactly the new contract
class F2 identifies. N7 is where that contract class gets *designed* — not where crypto routines
get written; per the task's own name, this is scoped as design work, with implementation (any
concrete constant-time-verified crypto primitive) left to a later, spike-demand-driven task, per
Law 5/D7's discipline of designing before code and growing model surface only when a spike
actually demands it.

### What "non-interference, a static analysis over the uop stream" means

MODEL_DEBT's phrasing is precise and worth preserving rather than paraphrasing loosely: this is
**not** a proof about the routine's *results* (that class already exists — ordinary correctness
contracts). It is a proof about the routine's *control/data flow structure* — specifically, that
no conditional branch's condition and no memory-access address anywhere in the routine's uop
stream depends on a value classified as secret. This is naturally stated as a taint/dependency
analysis over the same uop-level representation `Gasm.Targets.X86_64.Uop` already provides for the
performance model (per MODEL_DEBT §A0-A8's uop-stream cost analysis, which N7's non-interference
analysis is a structural sibling to, operating over the same representation but checking a
different property: data-dependence of branches/addresses on a secret-labeled input, rather than
cycle cost). This is why MODEL_DEBT calls it "cheap to state" — the uop stream already exists as
build-time-inspectable structure; what is missing is (a) a way to label which inputs to a routine
are secret, and (b) the non-interference theorem/analysis itself, not a new machine model.

### Why "cheaper now than after the optimizer starts introducing data-dependent branches"

This is MODEL_DEBT's own urgency argument, worth restating precisely: `docs/VISION.md` §5's
performance-modeling vision explicitly anticipates agents searching the implementation space for
faster variants of routines ("agents can search the implementation space aggressively... an
optimizing compiler... that explores like a superoptimizer"). An optimizer with no non-interference
constraint has no reason to prefer a constant-time variant of a branch over a faster
data-dependent one — branch-on-secret is frequently *faster* than the constant-time equivalent
(that is precisely why constant-time code is a deliberate, costly discipline in real cryptographic
implementations). If N7's contract class does not exist before the zlib-to-infinity-style
optimization search is ever pointed at a crypto routine, the search has no signal telling it that a
data-dependent-branch variant is disqualified rather than merely a valid faster option — and once
such variants exist in the codebase, retrofitting the constraint means re-auditing everything the
search already produced, rather than constraining the search from the start. This is the same
"grow the model before code depends on the wrong shape" argument `docs/VISION.md` §3.3 makes for
target models generally (the wsc predecessor's failure mode), applied specifically to secrecy
contracts.

### Governing laws

`docs/REVIEW.md` Law 5 (stop-and-design — this task's entire deliverable is a new contract class,
the canonical Law-5 case: "any concept... not yet fully designed in the repository" must stop and
be designed before code); Law 9 (universal quantification — a non-interference theorem must be
proven for *all* secret values, not spot-checked against sample inputs, exactly analogous to how
Law 9 already requires `∀`-quantification over environment inputs for correctness contracts — a
non-interference claim checked only pointwise against particular secret values is exactly as
unsound as a pointwise correctness claim, per `docs/VISION.md` §2's "any gate that an incomplete or
incorrect implementation can pass will eventually be passed by an incomplete or incorrect
implementation"); Law 11 (memory-access capability mandate — secret-dependent memory addresses are
exactly the failure mode Law 11's capability-as-frame-condition machinery is positioned to help
express, since a capability token could in principle carry secrecy-independence of the address it
authorizes, worth considering as part of this design rather than building a wholly separate
mechanism). `docs/VISION.md` §1 (the forcing-function quote above) and §4 (DSL discipline — if
non-interference is checked as a language-level property of the assembly DSL PA2/PA3 establish,
following the same "prove the language in total" principle already applied to step lemmas).

## Deliverables & acceptance criteria

- **A new `docs/` design doc** (this task's Law-5 deliverable) specifying the non-interference
  contract class: how a routine's inputs are labeled secret vs public, what "depends on" means
  precisely at the uop-stream level (branch conditions and memory-access addresses, per F2's exact
  wording — state explicitly whether other channels, e.g. cache-timing-relevant data-dependent
  *values* loaded rather than addresses, are in or out of scope for this first design, per Law
  5/D7 demand-driven scoping), and how the analysis integrates with PA2's contract shapes (a third
  field alongside correctness pre/postcondition and performance cost-bound, or a separate
  contract-attachment mechanism — this is a design decision this task must make and justify, not
  assume).
- **A worked example**: at least one concrete routine (a plausible near-term crypto primitive —
  e.g. a constant-time comparison, a simple XOR-based stream cipher step, or another routine of a
  scale the pathfinder-style approach favors) with both an intentionally-violating variant (a
  secret-dependent branch) and a constant-time variant, demonstrating the analysis actually
  distinguishes them — this is the non-interference analog of PA1's crc32 pathfinder: proving the
  design is buildable on a real instance before it is trusted as general, per `docs/VISION.md`
  §3.3's "validate before building on it."
- **Universal quantification over secret values (Law 9)**: the design must state the
  non-interference theorem shape as quantifying over *all* possible secret-input values, not a
  sampled or hardcoded set — matching the same anti-pointwise discipline Law 9 already mandates
  for ordinary correctness contracts, applied here to the new contract class rather than invented
  fresh.
- **Explicit relationship to the performance model**: state how (or whether) a non-interference
  violation is expected to correlate with an observable cost-model difference (MODEL_DEBT's "the
  cost model reports one number per block with no notion of input-dependent timing" — this design
  should state whether closing that cost-model gap is in scope here or is separately tracked
  performance-model debt, per D7 scoping — do not silently conflate the two).
- **Since this is a canonical Law-5 case** (an entirely new contract class with zero existing
  precedent in the codebase), a fresh-agent design review is mandatory before any implementation
  of a concrete constant-time-verified routine — not merely before this design doc is marked done,
  but as the gate any *future* task that consumes this design must also respect. `status` should
  progress `ready → designing → design-review → done` (this task's deliverable is the design
  itself, analogous to N1 — there may be no separate "implementing" stage unless the worked
  example above is judged substantial enough to warrant one).

## Pointers

- `MODEL_DEBT.md` §F2 (quoted in full above) and the TARGET-CLASS TAG TABLE row "F2 constant-time
  / secrecy | SRV, OS | third contract class."
- `docs/VISION.md` §1 (the web/gRPC servers forcing-function quote, quoted in full above), §4
  (DSL/total-theorem discipline — consider whether non-interference should be proven once over
  the assembly DSL PA2/PA3 establish, in the spirit of "prove the language in total, apply to
  every inhabitant"), §5 (the performance-modeling vision this contract class is deliberately
  distinct from, per F2's "unrepresentable in either current lens" framing).
- `docs/tasks/PA2-step-lemma-composition-design.md` — the direct prerequisite; read it for the
  exact contract-shape vocabulary this task's non-interference contract must slot into or extend.
- `Gasm/Targets/X86_64/Uop.lean` — the uop-level representation MODEL_DEBT's F2 entry names as the
  substrate for "a static analysis over the uop stream"; also see MODEL_DEBT §A0-A8 for the
  existing (performance-side) analysis this task's non-interference analysis is a structural
  sibling to, operating over the same representation.
- `docs/REVIEW.md` Law 5 (stop-and-design — this task's governing law), Law 9 (universal
  quantification, applied here to secret-value domains), Law 11 (memory-access capabilities —
  consider whether secret-independence of an authorized address belongs in the capability
  machinery).

## Notes

- 2026-08-27: priority 6.5 — constant-time/secrecy contract class design opens a third contract shape (MODEL_DEBT F2) that gets cheaper to add now, before the optimizer introduces secret-dependent branches.

_(none yet — first entries append here as work begins; this is Law-5-class networking-model work
— consolidate Notes into a real docs/ design doc before implementation, and route it through a
fresh-agent design review before any implementation dispatch.)_
