# The `gasm` Vision: The Specification Is the Program

This document states the project's founding insights and their consequences. It is the
"why" behind every law in [`docs/REVIEW.md`](REVIEW.md) and every architectural decision
in [`docs/ARCHITECTURE.md`](ARCHITECTURE.md). When a design question is ambiguous, resolve
it against this document.

---

## 1. The Three Insights

### Insight 0: Concrete implementation code is discardable
We no longer care about the concrete code that is written. Implementation text — whether
Rust, C, C++, or hand-written assembly — is a disposable artifact that can be regenerated
at will. In this worldview, implementation languages are dead languages: their value
proposition (human-maintainable safety and abstraction in the implementation itself) is
obsolete when the implementation is machine-generated and machine-checked. The durable,
valuable artifact is the **formal boundary**: the specification, the models, and the
proofs. Everything below that boundary can be thrown away and regrown.

### Insight 1: Programs are formal boundaries on what MUST be true
What we actually care about is **large-scale system correctness**. A "program" in `gasm`
is a high-level formal statement of what MUST be true of any implementation: behavioral
specifications, resource obligations, memory-safety capabilities, ABI contracts, and
performance budgets. Writing software means authoring and composing these boundaries,
not authoring implementation text.

### Insight 2: Agents generate the low level, boundaries keep them honest
AI agents can creatively and rapidly produce assembly and other low-level artifacts —
*especially* when they have a formal machine model to program against and formal
boundaries to satisfy. The economics of hand-written assembly are inverted: what was
prohibitively expensive for humans (exploring many low-level implementations, writing
simulation proofs, re-deriving code after a spec change) is cheap for agents, provided
the framework gives them fast, sound, mechanical feedback.

### Rebuild is the verb

The normal response to a poor implementation or proof architecture is to **rebuild it from its
stable formal boundary**, not to preserve and refactor its accidental shape. This applies
fractally: to one instruction leaf, a basic block, a lowering stage, a proof library, a spike, and
eventually a large system. Work top down from the semantics and currently accepted interfaces.
Mine prior work for reviewed lemmas, models, counterexamples, measurements, and implementation
ideas as spare parts; do not grant its module boundaries, representations, emitted code, or proof
structure an automatic right to survive.

Strong mechanical checking makes this replacement strategy safe. A clean implementation earns its
place by satisfying the same or a deliberately strengthened boundary, not by preserving textual
continuity. History remains valuable evidence, but compatibility with discarded proof architecture
is not itself a requirement.

Rebuild does not mean framework proliferation. The default failure mode is overengineering, so new
proof machinery—generic frameworks, generators, checkers, certificate layers, registries, and
speculative abstractions—requires explicit owner escalation before implementation. The proposal must
name the concrete burden, smallest interface, and immediate consumers. Prefer a small direct proof
when it is the easiest sound argument. Shared libraries should be un-gameable at their boundary and
fast to author against, while remaining only as general as demonstrated demand requires.

Large-program construction therefore alternates top-down generation and bottom-up learning:

```text
spec₀ → asm₀ → revised intermediate spec₁ → asm₁ → spec₂ → asm₂ → ...
```

Each correctness edge still points from an independently stated specification to its
implementation. The reverse-looking steps are engineering feedback: generated assembly exposes bad
representations, missing operations, poor block boundaries, and absent performance contracts; the
next round rebuilds the affected intermediate boundary and regenerates everything below it.
Unaffected proofs should transport across an explicit refinement/equivalence theorem. At millions
of lines, this repeatable derivation replaces the impossible task of mentally reverse-engineering
assembly back into intent.

### Bound the solution; do not prescribe the implementation

A high-level specification defines the exact **admissible set** of implementations, not a
preferred spelling of one implementation. It states the required behavior, authority and
lifetime transfers, safety and security properties, progress assumptions, observables, ABI,
and performance envelope. It names a concrete mechanism only when that mechanism is itself an
observable requirement or part of a platform contract.

Inside that boundary, an implementing agent retains maximum control: representation, algorithm,
instruction selection, synchronization strategy, implementation-owned work partitioning and
scheduling policy, and target-specific specialization are implementation choices, while external
scheduler/environment nondeterminism remains universally quantified by the contract. The agent may
combine compatible obligations into one mechanism
or discharge them separately, but acceptance requires a checked refinement witness for every
active obligation. A pre-canned library implementation is therefore a preferred proof-carrying
candidate, never an accidental restriction on the solution space.

Target and platform profiles provide the non-negotiable guardrails. They state which agents,
memory domains, scopes, atomic widths, barriers, ABIs, lifecycle transitions, device-completion
rules, failure modes, and progress assumptions really exist. A realization is rejected unless its
proof uses only those facilities and establishes every claimed consequence — spatial and temporal
memory safety, race freedom and atomicity, ownership and obligation preservation, synchronization
and visibility, deadlock/order requirements where demanded, and the relevant device, durability,
or security properties. Using a notionally “stronger” primitive is not automatically valid: it
must also preserve the contract's progress, performance, failure, and observable-behavior bounds.
The specification should make unsafe realizations unrepresentable or mechanically rejectable
while leaving everything inside the proved envelope open to creative implementation.

Proof burden is proportional to that envelope across all of gasm: functional equivalence, ABI and
linking, memory/provenance, effects and observables, lifecycle, security, performance bounds and
liveness/progress. Proof planning derives and records an applicability closure from
the selected targets, reachable effects and failure paths, and the guarantees actually advertised.
Every obligation in that closure is mandatory, but optional architectures, APIs, progress classes and
stronger properties outside it impose no work. Stage packaging is not a semantic dependency: when a
stage contains independent certificates, a consumer takes only the certificate it uses. Generic DSL,
contract and library theorems are proved once; an implementation proves its refinement delta and any
stronger property it elects to claim. A proof request should be traceable to the unsafe behavior,
platform rule or advertised consequence it excludes.

Until a separate repository-wide applicability-closure checker is implemented, that closure is a
required author/reviewer artifact, not a claimed automatic gate. A boundary-profile registry can
close concrete entries without deriving unrelated functional, security, performance or lifecycle
obligations. The absence of automation never excuses an applicable proof, but the mere existence of
an expressible optional profile never creates one.

Synchronization and communication preserve that freedom through three proof levels. A high-level
program states the demand and required consequences. A domain plan chooses an ISA-independent
architecture—such as a lock protocol, Vulkan/WebGPU dependency plan, asynchronous-I/O queue,
libverbs transport, network acknowledgement scheme, or durability protocol—and proves it satisfies
the demand. Target realizations then prove that plan against each concrete ISA, OS, device, provider,
and transport. This lets one domain architecture be reused across targets and lets agents explore
different domain plans, while preventing either an attractive ISA instruction or a convenient API
event from being credited with a consequence its owning profile does not guarantee.

Lifecycle and failure boundaries obey the same rule. Through M9 the hosted target is one root host
process with multiple CPU threads, while GPU/device/IOMMU/resource address domains remain separately
indexed; “single process” is not “one global address space.” Graceful root exit accounts for every
thread context, terminal bundle, guard, loan and join right. Fatal root/agent abort is not normal
discharge or global invalidation of surviving external effects.

Multiprocess creation, wait/reap, cross-process IPC and process-shared robust recovery are deferred
beyond M9 and add no current proof burden. `docs/FUTURE_PROCESS_MODEL.md` preserves the detailed
compatibility constraints for a later consumer-selected profile. A high-level task may still demand
eventual result transfer without prescribing a thread/process/remote mechanism; only an implementer
who selects the future process mechanism owes its lifecycle, channel and failure-domain proof.

Code callable from an interrupt, exception, signal, APC, trap or cancellation handler separately
proves that context's authority, nesting/mask/reentrancy, stack, blocking/allocation/fault, cleanup and
progress bounds. Bare-metal IRQ/NMI frames are agent-local; hosted signal/APC activations belong to
their logical thread. Unselected asynchronous surfaces impose no proof. This preserves implementation
freedom without allowing a convenient lifecycle or asynchronous event to inherit unproved thread
semantics.

### The Target Systems

The systems gasm exists to build are: **game engines, operating systems, web/gRPC
servers, and databases.** This is the owner's own scope statement, verbatim: "just to
push on scope here: the target systems we'll build with gasm are game engines, operating
systems, web/grpc servers, databases." This list is the demand horizon for §3.3's
demand-driven growth — models and capabilities grow toward these four classes.

The following per-class extensions, and the claim that nothing beyond this list drives
growth at all, are the coordinator's elaboration of that scope statement, not something
the owner specified in this detail — recorded here as the coordinator's design, to be
confirmed or revised with the owner rather than read as his own words:

- **Game engines**: performance contracts consumed as *deadline budgets* (frame-time
  bounds on parametric cost functions); multiple concurrent reactive loops as the norm;
  the graphics stack; floating-point determinism policy.
- **Operating systems**: the bare-metal model (interrupts, privilege, paging, MMIO);
  and the inversion where gasm's effect typeclasses are no longer models of a host OS
  but are *implemented by* the OS we build.
- **Web/gRPC servers**: threading and async I/O; protocol causality (§ SYSTEM_EFFECTS
  6.4); cryptography — which adds a third contract class beyond correctness and
  performance: **secrecy contracts** (constant-time execution, provable as
  input-independence of the cost function).
- **Databases**: durability semantics for storage (write ordering, fsync guarantees,
  torn writes) as *correctness* models, not just cost models; and **crash
  observability** — equivalence obligations over traces cut at arbitrary points with
  recovery, so durability is a provable property rather than a hope.

---

## 2. The Consequence: The Validation Gate Is the Product

If implementations are generated by untrusted, creative processes, then **all trust
concentrates in the validation gate**. The gate — not the generated code — is the product
of this repository.

This has a hard corollary, learned empirically in this codebase's own history:

> **Any gate that an incomplete or incorrect implementation can pass will eventually be
> passed by an incomplete or incorrect implementation.**

The canonical exhibit: a target realization that emitted a single hardcoded output stream
legitimately satisfied a pointwise equivalence theorem, because the theorem only examined
the one input the stream was precomputed from. This was not a violation of the gate — it
was the gate working as (badly) designed. Pointwise verification is not merely weak; under
generated implementations it is adversarially unsound.

Therefore:

1. **Contracts must be universal.** Verification obligations are universally quantified
   over their entire input domain (Law 9) and discharged by kernel-checked proof
   (Law 10). An implementation that is incomplete must be *unrepresentable as verified*,
   not merely likely to be caught.
2. **Generation is untrusted by construction.** Nothing about how an implementation was
   produced (which agent, which prompt, how many iterations) carries any evidential
   weight. Only the gate does.
3. **Never weaken a gate to make an implementation pass.** Gate changes are
   specification changes and go through stop-and-design (Law 5) and review.

**The end-state of review.** In a mature `gasm`, review has exactly one irreplaceable
question: **are we proving the right theorems?** — does the formal statement faithfully
capture the spec's intent, quantify over the real domain (not a shrunken stand-in), and
exclude nothing the spec permits? Everything else — does the proof hold, does the
artifact match its contract, is coverage complete, did the oracle actually run — must be
implementation and mechanical checking. We are not there yet; until we are, every review
finding that is *not* a right-theorem question marks a gate still missing (Law 13), and
closing those gaps is how review converges to its one question.

---

## 3. The Two Trust Obligations

Trust in the gate decomposes into exactly two obligations:

### 3.1 The proofs must be sound
The Lean kernel checks that the stated theorems hold of the stated models. Our obligation
is that the *stated theorems* actually say what we mean: universal quantification over the
real input domain, no pointwise bypasses, no dead abstractions, minimal trusted base
(Laws 8, 9, 10).

### 3.2 The models must be faithful to reality
A theorem about a wrong model is worthless. The machine and OS models (`Gasm.Targets.*`)
are our axioms about the world, and they are validated **differentially against real
implementations**:

- **x86-64 semantics** vs. real silicon (the hardware fuzz harness executes candidate
  instructions on the host CPU and compares every register and flag).
- **Wasm semantics** vs. production engines (differential execution against a host
  runtime oracle).
- **Windows API models** vs. the real OS: every modeled Win32 contract
  (`ReadFile`, `WriteFile`, `VirtualAlloc`, sockets, ...) must be exercised by a native
  harness that invokes the real API and compares observable behavior against the model's
  state-transition hooks — the same discipline the ISA models already follow.
- **Graphics API and shader models** (future): the same differential discipline against
  real drivers and reference rasterizers/executors.

A divergence between a model and reality is a soundness bug of the highest severity — it
invalidates every proof built on that model. Model-validation harnesses are therefore
first-class, permanent infrastructure, not one-off tests.

**What differential validation can and cannot deliver.** Measurement *refutes*; it never
confirms universally. A harness that agrees with the world on N sampled points has
produced N regression tests, and a model can always be built that reproduces exactly
those N points and nothing else — which is Law 9's domain-shrinking evasion relocated
from the contract layer to the model layer. The ∀-trust a model needs therefore comes
from three sources, and a validation design using only the first is not validating
anything universal:

1. **The vendored contract text is the ∀ source.** An official specification states the
   *permitted-outcome set* for an operation. This is Law 4's real purpose — not
   provenance hygiene, but the origin of every universal claim we can make about a world
   we cannot exhaustively sample. It gives three obligations where sampling gives one:
   `doc ⊨ model` (a stated, reviewable refinement), `observation ∈ doc` (is the world
   inside its own documented envelope), `observation ∈ model`.
2. **Outcome-set semantics, not point equality.** Models state permitted-outcome
   relations with every reachable behavior as a constructor (short reads, EOF, errors),
   and harnesses check *containment* rather than exact agreement — the criterion this
   project already ratified for its other world-sampling oracle. A design must say
   whether it targets exact characterization or sound over-approximation, because that
   choice decides what a divergence *means*: outside the model is unsoundness; permitted
   but unobserved is mere looseness.
3. **Coverage and discrimination obligations.** Every constructor of the outcome type
   carries a witness observation, and the suite must go red under mutation of each
   constructor — *executes ≠ discriminates*. These are finite and mechanizable, so they
   belong at Law 13's preference tiers 2–3, not as prose.

A model surface with no vendored contract text behind it cannot be universally trusted at
all, however many observations agree with it; the honest options are to ingest the
specification or to declare that surface outside the model's stated domain.

### 3.3 Grow models demand-driven; validate before building on them

This project's predecessor (`wsc`; its Lean library is namespaced `Lasm`) failed in a
specific, instructive way: it built out large portions of the ISA as code before the
instruction model was right. Once a mountain of code depended on a wrong model, going
back to fix the model was more expensive than rebuilding the project from scratch.

`gasm` is structured to make that failure impossible to repeat:

- **Target models are deliberately incomplete.** Instructions, API surfaces, and
  capabilities enter a model only when a spike demands them (Law 5) — never speculatively.
- **Every increment is validated before anything is built on it.** New model surface gets
  differential validation (against silicon, engines, the OS) in the same change that
  introduces it, and spike-by-spike development exercises each increment end-to-end while
  the dependent-code surface is still small enough to rebuild cheaply.

An incomplete, validated model is an asset. A complete, unvalidated one is a liability.

---

## 4. Tractability: Modular Contracts, Composed Proofs

Universal whole-program trace equivalence is not tractable as a single monolithic proof
for realistically sized programs. It **is** tractable as a composition:

1. **Routine contracts.** Every assembly routine carries a universal contract:
   precondition, postcondition, memory frame (the capabilities it may touch — Law 11),
   ABI discipline, and emitted-event trace. Contracts are stated over *all* valid inputs
   and framed states.
2. **Local proofs.** Each routine is proven against its contract in isolation, using
   per-instruction step lemmas and loop invariants. The proof burden is local: a routine's
   proof depends only on the step lemmas of the instructions it uses and the contracts of
   the routines it calls.
   The intended checker must derive an **applicability closure** from the routine's selected targets,
   effects, profiles, guarantees, reachable calls, and failure paths. Unselected GPU,
   process, RDMA, interrupt, architecture, or progress profiles impose no proof burden;
   once a feature or claim is selected, all of its transitive safety/platform obligations
   remain mandatory and cannot be escaped by omitting a nominal block identity. A generic DSL or library
   theorem is paid once and reused; a specialized implementation proves only its declared
   refinement delta and any stronger guarantee it advertises.
3. **Composition rules.** Sequential composition, call, and loop rules assemble routine
   contracts into whole-program theorems. The whole-program equivalence statement
   (`VerifiedProgram`) becomes a *derived theorem*, not an obligation discharged by
   evaluation. The current fixed composer combines reusable artifact/emission, link/export,
   provider/runtime, entry, admissibility, and behavioral certificates indexed by the same final
   artifact and composed by one general rule. The future mechanical applicability closure will
   derive the exact finite key set. A program
   author proves only missing leaves and local refinement deltas. The root theorem contains no
   bespoke replay of a certificate already established by an ISA, platform, linker, or library.
   The implemented spikes are required exemplars of this factoring. Trust repair exits only when
   every implemented spike obtains its sole universal `VerifiedProgram` through the general rule,
   with reusable certificates living at their owning layer and the spike proving only its local
   deltas. A green but monolithic spike is unfinished proof infrastructure, because it teaches the
   next implementation the wrong proof shape.
   Calls and jumps are both proof boundaries under this rule. A typed jump establishes the target
   basic block's entry relation—including its ghost authority/obligation world—just as a caller
   establishes a callee contract. A general CFG theorem composes those small edge certificates into
   routine preservation; loops reuse an invariant at the back-edge instead of expanding paths.
   Indirect control flow additionally proves that the resolved destination belongs to a closed set
   whose member contracts are all satisfied.
   Proof-producing macro assemblers and compilers reuse this boundary: their lowering theorem emits
   the same typed edge, call, instruction, and artifact certificates, so bulk code inherits one
   generic frontend proof and supplies only source contracts plus exceptional-form deltas. They do
   not become alternate whole-program authorities; `VerifiedProgram` remains the sole final gate.
4. **Agents write the proof with the code.** The unit of generated work is the triple
   (contract, assembly, proof). Agents iterate against the checker until it accepts;
   humans review contracts, not implementations. This is what makes universal
   verification economically feasible: invariant-invention is exactly the kind of
   fast-feedback search agents excel at, and every failure is local and actionable.

Memory safety and proof modularity are the same feature: the capability tokens that make
an unsafe access fail to assemble (Law 11) are also the frame conditions that let routine
proofs compose without global reasoning.

**DSLs are the unit of proof leverage.** A lesson imported from prior projects: a DSL in
Lean is a superpower for proofs, because theorems are proven about the *language in
total* — once — and then apply to every program written in it. Well-designed DSLs
compose, so lemma libraries stack: a bit-reader language inside an assembly language
inside a syscall-effect language, each layer carrying its own total theorems. The
operating rule: **anywhere there is a population of artifacts — even a closed
population, even a population of one — reach for a DSL.** A closed population gets
exhaustive language-level theorems (the instruction registry's roundtrip gate is exactly
this shape); a population of one still profits when the DSL separates the proof into a
reusable language-level part and a small program-level part. This is the concrete
mechanism behind everything in §4: step lemmas and composition rules are total theorems
about the assembly DSL; contracts are total theorems about the effect DSL; and proving
languages instead of programs is precisely what makes proof cost sublinear in system
size at the scale below.

**The scale target makes decomposition the first-class problem.** The target systems
(§1, The Target Systems) are millions to tens of millions of lines in conventional-
language terms — larger still as generated assembly. At that scale nothing whole-program
survives contact: builds, proofs, gates, fuzz suites, and reviews must all cost
proportional to the *change*, not to the system. Correctness and performance modeling
are crucial; the methods for **decomposing** them — seams, per-module contracts,
composition rules, sharded and incrementally-cached gates, per-module cost budgets that
sum — are more crucial still. Decomposition machinery is a primary deliverable of this
project, on equal footing with the models themselves, and every piece of infrastructure
should be designed against the question: *what does this cost at ten million lines when
one module changes?*

---

## 5. Performance Modeling: Agents as the Optimizing Compiler

A checked-in, static performance model (port pressure, latency/throughput tables, cycle
bounds) is a strategic superpower, not an accessory:

- **Fast iteration.** Agents evaluate the performance of candidate assembly *without
  executing it*, giving optimization loops that run at model-evaluation speed rather than
  benchmark speed.
- **Checked-in budgets.** Critical routines carry performance contracts (cycle bounds
  under a named microarchitectural profile) that are checked mechanically; a regression
  fails the build like a broken proof does.
- **Deep optimization of the critical path.** With correctness held fixed by universal
  contracts and cost ranked by the model, agents can search the implementation space
  aggressively — the combination turns agents into the world's foremost optimizing
  compiler: one that explores like a superoptimizer but only ever emits proven-correct
  code.

**Parametric cost functions, not asymptotics.** The end-state for performance contracts
is symbolic cost modeling with real coefficients baked in: a routine's cost is stated as
a closed-form function of its input parameters — `5·N² + 3·N + 293` cycles under a named
microarchitectural profile, not `O(N²)`. Asymptotic classes hide exactly the constant
factors that agents are best positioned to optimize; concrete-coefficient cost functions
make every optimization measurable, every regression mechanical, and cost composition
(caller cost = Σ callee costs + glue, loop cost = trip count × body + overhead) ordinary
polynomial arithmetic that Lean can check. Cost functions are part of a routine's
contract, derived from the per-instruction uop/latency model plus loop-structure
annotations, and regress like proofs do.

The performance model is itself a model, and inherits the obligation of §3.2: it must be
differentially validated against real hardware measurement. Static bounds do not need to
be cycle-exact, but they must be **monotonically faithful** — when the model ranks
variant A faster than variant B, real hardware must overwhelmingly agree, or the model is
actively misleading the optimization search.

**From optimizing compiler to optimizing system architect.** The end-state cost model
spans devices and transports — CPU compute, GPU compute, **PCIe transfer cost including
readback**, disk I/O, network — organized as **layered views that compose, not one
flattened unit system**:

- **Native precision views per system**: each domain keeps its own most-precise natural
  unit as a first-class model — cycle counts for x86 (valuable and measurable there),
  device ticks for GPU timestamps, bytes-and-latency terms for transports. Precision
  lives at the leaves and is never thrown away by premature conversion.
- **The system-architect view**: microseconds/milliseconds per operation, obtained from
  the native views through *explicit conversions* carried by named device profiles
  (a profile owns its clock/frequency provenance). Placement questions — "CPU or GPU,
  counting upload and readback?", "recompute or spill to disk?", "local or remote?" —
  are asked and answered at this level, by comparing closed-form parametric cost
  functions whose terms were converted from the native views.
- **Composition is the contract.** The requirement is not that all costs share a unit;
  it is that every native view composes into the architect view through a validated
  conversion, so cross-domain comparisons are always well-defined while within-domain
  reasoning keeps full native precision.

Each device/transport model is differentially validated like the CPU model (timestamp
queries, bandwidth benchmarks, under the same control-vector rules); measured
calibration data is governed like `references/` — checked in, regenerable, never
hand-edited.

---

## 6. What This Means Day to Day

- The gate is the product. Contracts, models, validation harnesses, and composition
  infrastructure are the highest-value work in the repository.
- Implementation text is regenerable. Do not spend review attention on its style;
  spend it on the contract it satisfies and the model it runs against.
- Every new capability follows the order: reference ingestion (Law 4) → model +
  differential validation (§3.2) → contract → generated implementation + proof.
- Incompleteness must fail loudly at the gate, never be discovered downstream.
- Duplicated encodings of the same fact are liabilities unless proven connected
  (Law 12); the model layer is single-source-of-truth.
