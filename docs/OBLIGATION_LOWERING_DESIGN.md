# Capability-directed obligation lowering

**Status:** design proposal; no implementation authorization.

This note proposes an authoring and lowering boundary for capability-directed, proof-carrying
effect handling. It is a review artifact, not evidence that the described Lean types, target
adapters, policies, or conservation rules exist. In particular, it does not authorize changes to
the ISA, checked authoring surface, lowering libraries, target profiles, spike proofs, or the
accepted trust rebuild plan.

Craig owns the semantic and architecture decision and is the sole authority for implementing a
shared or public interface. MP owns design refinement and soundness review. Reviewer owns
adversarial execution and un-gameability review. Trust Repair integrates only after those reviews
and explicit implementation approval.

The proposal addresses two failures at once:

1. Building one spike locally can choose an easy representation that generalizes badly when a
   materially different program arrives.
2. Generalizing a single high-level memory or obligation model too early can force garbage
   collection, borrowing, regional ownership, platform resources, and ISA access into one false
   ontology.

The proposed common structure is not a universal ownership policy. It is a typed protocol for
selecting capabilities and handlers, transporting their obligations through lowering, and proving
that every admitted target behavior refines an independent source contract.

## 1. Normative model and design intuition

The normative programming model is algebraic effect handling with typed operations, explicitly
selected handlers, and proof-producing lowering. Aspect-oriented programming is only an intuition
for where interception occurs, and the metaphor has strict limits. There are no textual pointcuts,
hidden global advice, or build-order-sensitive weaving.

| Effect-handling concept | Proposed role |
|---|---|
| Typed abstract operation | Join point |
| Selected implementation dictionary or handler | Advice |
| Proof-producing staged lowering | Weaving |
| Capability context | Offered authority/services plus implementation constraints |
| Lowering certificate | Proof that the selected weaving preserves the source contract |
| Artifact certificate | Reproducible handler, dictionary, target, profile, and version identity |

This is **capability-directed, proof-carrying effect handling**. Selection is explicit data. Lean
typeclass search may help construct a locally requested dictionary, but a global instance must not
silently select target semantics, choose an output sink, weaken a constraint, or manufacture
authority.

The artifact tree closes structural identity and supplies evidence to the proof. It is never
semantic authority and cannot choose the contract it is meant to implement.

A hand-crafted lowering is ordinary and expected. The architecture is optimized for repeatedly
choosing excellent whole-program implementations, not for preserving one generic compiler
pipeline. A program may lower an operation directly to an ISA leaf, through another abstract
block, or through a bespoke fused block, provided the selected lowering proves the same source
meaning and accounts for all effects, constraints, resources, and obligations.

## 2. The precious root determines substitutability

The stable top-level specification owns the full admissible behavior envelope: observables,
safety/non-fabrication, causal constraints, permitted failures and partial effects,
authority/provenance/cancellation/cleanup requirements, and every intentionally adopted progress,
resource, performance, or security claim. Handler substitution is sound only relative to that
envelope.

If the root promises a logical event such as:

```text
Log .info "server started"
```

then a Windows console, Linux terminal, bare-metal serial port, graphical overlay, or daemon logger
may each refine the event when its selected handler proves the required delivery, failure, order,
and cleanup semantics.

If the root instead promises literal bytes written to the process console, redirecting the message
to a graphical window or daemon log is not equivalent. The root must explicitly permit that sink or
state a more abstract logical event. Generated assembly and convenient handlers cannot select a
weaker meaning after the fact.

This applies equally to memory and resource policy. Source semantics should describe the program's
meaning and source-visible effects, not fields chosen to make one x86, Windows, borrowing, or GC
proof easy.

### 2.1 Source-independence test

A source artifact is independent of the unresolved safety and lowering protocol only when:

- its imports and public signatures contain source mathematics, effects, and required resource
  outcomes, not ISA instructions, registers, descriptors, layouts, grants, or lowering types;
- its state is observable or required by the root contract rather than a mirror of a selected
  allocation, register assignment, buffer layout, or capability encoding;
- its definitions survive at least two conceptually different policy or target realizations;
- its operations are specified extensionally by input, output, event, failure, and resource
  relations rather than evidence fields tailored to one lowering; and
- replacing the memory or effect policy changes the refinement proof, not the source definition.

The practical review is **two-realization erasure**: sketch two materially different realizations,
erase their implementation evidence, and compare the remaining source artifact. If the source type
must change merely because a borrow becomes a GC reference or a console becomes a logical logger,
the source layer probably selected the implementation protocol prematurely.

Observable policy choices remain precious. For example, atomic-row output versus a permitted byte
prefix on failure is not an implementation detail; it changes root behavior.

## 3. Capability contexts: four semantic polarities

A capability context distinguishes four semantic polarities. This proposal does not decide whether
Lean should represent them as separate types, indexed fields of one context, a row algebra, or
another demand-shaped encoding.

| Polarity | Meaning | Examples |
|---|---|---|
| Demand | An effect/service the program requires | Cancellable request scope, logical logging, allocation |
| Constraint | A property every selected implementation must satisfy | Peak-live-byte bound, cancellation-latency bound, no allocation in scope |
| Offer | A candidate service/runtime available for explicit selection | Request allocator/governor, cancellation runtime, Windows console logger |
| Authority | A right or owned resource enabling a transition | `CancelRight`, owned allocation, borrow, cleanup or join obligation |

The distinction is normative; the representation is not. A capability context therefore says what
a program requires, what candidates are available, what implementations are admissible, and which
authority/resources are currently owned. It is not merely a bag of effect methods.

Illustrative vocabulary includes:

```text
demand:     UseAllocator A
demand:     LogicalLogging contract
demand:     Cancellable scope contract
constraint: MaxPeakLiveBytes bytes
constraint: MaxSingleAllocationBytes bytes
constraint: MaxCumulativeAllocatedBytes bytes
constraint: MaxAllocationCount count
constraint: NoAllocationHere
offer:      RequestAllocatorGovernor profile
offer:      CancellationRuntime profile
authority:  CancelRight scope
authority:  OwnedAllocation allocation generation
```

This notation records semantic polarity only. It intentionally proposes neither four Lean types nor
one tagged sum. A later approved interface may use projections, rows, indices, separate contexts, or
another representation while preserving these distinctions.

`UseAllocator A` requires a selected allocation handler backed by allocator identity `A`.
Allocation constraints distinguish at least four measures: cumulative allocated bytes, peak live
bytes, maximum size of one allocation, and allocation count. No one `MaxLiveAllocation` name may
ambiguously stand for all four. `NoAllocationHere` forbids any reachable selected allocation effect
in its scope, including an allocation introduced by lowering or hidden inside buffering advice.
A logical logging demand separately describes accepted event, delivery, ordering, refusal,
buffering, failure, and cleanup behavior.

A capability can act as an obligation interceptor, but interception is a role rather than its whole
definition. A capability may also carry:

- persistent authority and resource identity;
- a generational lifecycle state;
- delegation, narrowing, revocation, or return rights;
- state-transition evidence and post-operation authority;
- future cleanup, release, flush, close, join, or cancellation obligations; and
- constraints on which handlers may realize it.

For example, a bounds capability can intercept an index operation, demand containment evidence,
emit lower range obligations, and return a narrowed element capability. A buffered logger also owns
buffer identity, memory, ordering state, a flush policy, failure disposition, and cleanup
obligations; describing it only as an interceptor would omit the authority that makes its behavior
sound.

## 4. Level-local operations and obligation languages

Each semantic level owns the obligation language it understands. A borrowing policy, moving
collector, ABI lowering, target profile, and ISA instruction family need not share constructors or
lifecycles.

```lean
-- Pseudo-Lean only.
class ObligationLanguage (Level : Type) where
  Obligation : Type
  State      : Type
  Satisfies  : State -> Obligation -> Prop

structure Operation (Level : Type) [ObligationLanguage Level] where
  Input       : Type
  Output      : Type
  pre         : ObligationLanguage.State Level -> Input -> Prop
  step        : ObligationLanguage.State Level -> Input ->
                  ObligationLanguage.State Level -> Output -> Prop
  generated   : Input -> List (ObligationLanguage.Obligation Level)
```

There is no universal obligation constructor registry. A generic envelope may package an
existential level-local obligation for orchestration, but it carries no authority and cannot
replace a translation theorem. A universal obligation type would become a god object: unrelated
policies would import one another, new policies would require central edits, opaque payloads would
hide semantics, and lowering could degenerate into retagging.

Every selected operation occurrence has one explicit **primary handler** at its owning stage.
Filtering, policy checks, resource governors, and other secondary interceptors compose around that
handler only through named selection and local proofs. This avoids two handlers each claiming to
have performed the same effect, while still allowing one handler to lower into further abstract
operations with their own primary handlers.

### 4.1 Small relational resource/scope schemas

The common resource/scope layer is deliberately small and relational. Effect/capability contracts
declare typed authority preconditions, results, transfers, and retained obligations. Domain policy
libraries supply their own carriers, operations, modality/alias laws, and obligation vocabularies.
The common layer supplies only parameterized schemas for:

- generative identity, parentage, freshness, and non-revival;
- request, reserve, grant, transfer, return, and typed disposition;
- cancellation authorization, request, delivery, observation, masking, unwind, cleanup, closure,
  terminal state, and join observation;
- race/linearization witnesses and exactly one selected winner;
- profile-defined scalar or vector capacity accounting and governors;
- failure-domain disposition and survivor/recovery ownership;
- causal edge kinds without identifying control causality with memory visibility; and
- conservation interfaces used by level-local lowering translations.

It defines no universal `Resource`, `Operation`, `Capability`, or `Obligation` sum and no fixed
scope-state encoding. Domain policies instantiate the schemas and prove their promised
authority/lifecycle consequences refine them.

Cross-domain laws required of every instantiation are:

- no fabrication and no stale-generation revival;
- balance plus cleanup conservation, with closure unable to erase or strand authority;
- cancellation is control causality, not visibility, rollback, or resource return;
- exactly one winner for each selected race/linearization point;
- irreversible commit is monotone and preserves the exact committed prefix;
- completion, notification, observation, resource return, reclamation, remote delivery, and
  persistence remain distinct consequences;
- forced failure-domain disposition names surviving, orphaned, quarantined, or recovery-owned
  resources explicitly;
- capacity counts committed and capacity-reserving in-flight resources while allowing potential
  overcommit under the selected profile;
- composition order and noninterference are explicit;
- selected handler/profile identity is artifact-recorded but not semantic authority; and
- applicability conservatively includes normal, failure, cancellation, cleanup, and terminal paths.

For every governed operation, each capability, constraint, and active obligation must be accounted
for by exactly one explicit semantic route, although one obligation may split and several may fuse:

- **preserve** it at the current level;
- **narrow or delegate** it, with the named recipient and retained remainder;
- **consume** it with a proof of its predicate and required state transition;
- **translate** it into lower-level obligations with a directional entailment theorem;
- **intercept** it with a named handler whose postcondition and generated obligations are proved;
- or **prove the governed operation absent** from all admitted reachable paths.

Silent substitution, discard, or a caller annotation saying “not applicable” is forbidden.
Applicability comes from sound coverage of the selected program and lowering.

## 5. Four orthogonal judgments

Memory safety exists at multiple levels. No high-level discipline exempts a concrete ISA access
from its architectural proof, and no architecturally valid access proves source authorization.

### 5.1 ISA-owned architectural definedness

```lean
-- Pseudo-Lean only.
ArchitecturalAccessDefined
  (execution : Execution)
  (occurrence : AccessOccurrence execution)
  (descriptorOrdinal : Fin occurrence.instruction.memAccesses.length)
  (preState : MachineState) : Prop
```

This judgment identifies the exact fetched production instruction and descriptor at an
execution-derived dynamic occurrence. It derives effective address, byte range, kind, width,
address-size and segment behavior, non-wrapping/canonical-address facts, and architectural
alignment or atomicity preconditions. It proves that the access follows the defined/non-faulting
architectural branch.

It does not define OS allocation provenance, program security policy, GC reachability, source
object identity, Rust borrowing, algorithm correctness, or output meaning. Race freedom is not
silently folded into access definedness; the ISA owns atomic and non-atomic semantics while the
selected concurrency policy proves any advertised race or ordering property.

### 5.2 Target-owned resource admission

```lean
-- Pseudo-Lean only.
TargetResourceAdmits
  (profile : TargetProfile)
  (context : ExecutionContext profile)
  (occurrence : AccessOccurrence context.execution)
  (descriptorOrdinal : Fin occurrence.instruction.memAccesses.length) : Prop
```

This judgment proves that the selected platform's current address domain, physical binding and
generation, lifecycle state, and permissions admit the exact range and access kind. Hosted targets
may derive it from loader, allocation, or mapping facts. Bare-metal targets derive it from their
memory map, privilege domain, MMU/device profile, or another target-owned grant; they do not invent
OS allocation provenance.

### 5.3 Policy-owned authorization

```lean
-- Pseudo-Lean only.
PolicyAuthorizes
  (policy : Policy)
  (sourceState : policy.State)
  (operation : policy.Operation) : Prop
```

This judgment states the selected source policy's rule: borrow exclusivity, GC liveness and
pinning, regional ownership, security domain, protocol state, or a bespoke invariant.

### 5.4 Behavioral refinement

```lean
-- Pseudo-Lean only.
BehavioralRefines
  (sourceContract : SourceContract)
  (selectedTargetBehavior : TargetBehavior) : Prop
```

This judgment proves that every admitted observable target behavior belongs to the independent
source contract. It owns functional results, logical events, permitted failure/cancellation
outcomes, and resource disposition. It is not derivable from access safety: a program may perform
only authorized, mapped, architecturally defined accesses while computing the wrong result or
writing to the wrong approved sink.

A verified access requires the first three judgments plus a lowering relation tying the same
source operation to the same target occurrence. Whole-program correctness additionally requires
behavioral refinement. Architectural validity alone does not establish program policy or behavior.
High-level authorization alone does not establish a valid machine access, live target mapping, or
correct observable result.

### 5.5 Ownership table

| Owner | Owns | Must not claim |
|---|---|---|
| Source/root specification | Observable behavior, permitted failures, logical effects and resource outcomes | Concrete registers, layouts, sink choice, or target authority |
| High-level policy | Authorization, invariants, policy lifecycle and policy obligations | ISA definedness or physical mapping |
| Handler/lowering | Explicit selection, translation, state relation, generated obligations and refinement | Authority not supplied by an owning layer |
| ISA/instruction family | Descriptor, address/range calculation, step semantics and architectural definedness | OS allocation, high-level authorization or provider behavior |
| Target/profile/platform | Live binding, generation, mapping, permission, provider/runtime realization and admission | Source meaning or self-selected specification |
| Linker/artifact producer | Exact bytes, layout, symbols, imports, slots and selected identity record | Runtime provider behavior or semantic authorization |
| Whole-program composition | Target-to-source behavior containment and complete obligation/resource disposition | New facts absent from its component certificates |

### 5.6 Platform/ISA memory consistency is a fundamental destination

The four judgments above are not an exhaustive concurrency stack. Whenever concurrent CPU,
device, or heterogeneous memory behavior is applicable, the selected platform/ISA memory model
additionally proves its fundamental consistency relations and permitted executions: for example
`rf`, `co`, `fr`, `po`, `sw`, `hb`, x86 TSO, AArch64 weak-memory, atomic/plain distinctions,
barriers, reservations, and target/device relations.

These laws are not lowering machinery and are not consequences of `ArchitecturalAccessDefined`.
The rebuilt lowering maps plural high-level policies into their required ISA access, target
admission, and selected platform memory-consistency obligations. `MEMORY_MODEL.md` is the current
authoritative destination for those platform/ISA memory semantics, not the owner of generic
handler selection, obligation transport, or staged lowering.

## 6. Target-to-source refinement, not “ISA-safe therefore source-safe”

A stale pointer after GC relocation may still address mapped writable memory. Therefore
`ArchitecturalAccessDefined` and `TargetResourceAdmits` can both hold while the source access is
invalid. Correctness flows from admitted target behavior back to an authorized source step.

```lean
-- Pseudo-Lean only.
theorem lowering_refines
    (rel : StateRel lowering sourceState targetPre)
    (step : SelectedLoweredStep block occurrence targetPre targetPost)
    (arch : ArchitecturalAccessDefined execution occurrence ordinal targetPre)
    (admit : TargetResourceAdmits profile context occurrence ordinal) :
    exists sourcePost,
      SourceStep operation sourceState sourcePost /\
      PolicyAuthorizes policy sourceState operation /\
      StateRel lowering sourcePost targetPost /\
      ObservablesRefine sourceState sourcePost targetPre targetPost
```

The policy proof comes from the source invariant and policy component carried by the lowering
certificate and state relation. It is not inferred from target safety.

A companion construction theorem shows implementability:

```lean
-- Pseudo-Lean only.
theorem lower_authorized
    (rel : StateRel lowering sourceState targetPre)
    (sourceStep : SourceStep operation sourceState sourcePost)
    (authorized : PolicyAuthorizes policy sourceState operation)
    (realization : RealizationWitnesses lowering operation targetPre) :
    exists selectedTargetExecution,
      ArchitecturalAccessDefined selectedTargetExecution.execution
        selectedTargetExecution.occurrence selectedTargetExecution.ordinal targetPre /\
      TargetResourceAdmits profile selectedTargetExecution.context
        selectedTargetExecution.occurrence selectedTargetExecution.ordinal /\
      SelectedExecutionRefines sourceStep selectedTargetExecution
```

Source-to-target construction does not replace target-to-source simulation. The final
`VerifiedProgram` direction remains containment: every admitted target behavior belongs to the
independent source contract. Full bisimulation is required only when a root contract separately
demands completeness of all permitted source behaviors.

## 7. Obligation conservation through lowering

Accounting covers both inherited source obligations and every obligation introduced by lowering or
an interceptor. For one lowering edge:

1. Every active source obligation is directly proved, translated into named target obligations, or
   transferred to a named interceptor with a proved postcondition and lifecycle result.
2. Every obligation introduced by the selected lowering is likewise proved, retained, translated,
   or transferred.
3. Every discharge contains a proof of the obligation predicate, not a status bit or renamed token.
4. Every translation proves that satisfaction below entails the required fact above.
5. Obligations generated by an interceptor's own effects enter the same accounting recursively.
6. The result is scoped to the exact operation occurrence and pre/post-state relation.

“Exactly once” is not the generic law: one obligation may split, several may fuse, and redundant
evidence is harmless. The law is semantic coverage with no zero branch.

```lean
-- Pseudo-Lean only.
structure Translation
    (High Low : Type)
    [ObligationLanguage High] [ObligationLanguage Low] where
  lower : ObligationLanguage.Obligation High ->
            List (ObligationLanguage.Obligation Low)
  sound : forall high lowState,
    SatisfiesAll lowState (lower high) ->
    ObligationLanguage.Satisfies (projectState lowState) high

inductive DischargeDerivation :
    (stage : Nat) -> (level : Type) ->
    [ObligationLanguage level] ->
    ObligationLanguage.Obligation level -> Type
  | direct : Satisfies state obligation -> DischargeDerivation stage level obligation
  | lower :
      (translated : List lowerLanguage.Obligation) ->
      (children : forall obligation in translated,
        DischargeDerivation lowerStage lowerLevel obligation) ->
      lowerStage < stage ->
      TranslationSound obligation translated ->
      DischargeDerivation stage level obligation
  | intercept :
      NamedInterceptorStep interceptor obligation post generated ->
      (children : forall obligation in generated,
        DischargeDerivation lowerStage lowerLevel obligation) ->
      lowerStage < stage ->
      PostconditionEntails post obligation ->
      DischargeDerivation stage level obligation
```

The exact Lean representation is undecided. The required property is a finite, local,
well-founded proof. Generation of a lower obligation is not evidence that it holds. Same-stage
cycles such as “`O` is `P`; `P` is `O`” are rejected, and production admission accepts no unresolved
obligation assumptions. This is deliberately not a global mutable ledger.

## 8. Capabilities and handlers compose conservatively

Independent handlers initially compose only by product/conjunction, with explicit proofs that:

- both policies authorize the selected operation;
- each selected transition preserves the other's invariant; and
- their generated obligations can be jointly satisfied.

If ordering matters, the composed capability or lowering exposes that order and supplies a bespoke
interaction or distributive-law theorem. There is initially no generic ordered handler stack.

For example, “borrow then pin” and “pin then borrow” are not silently interchangeable. A moving
collector can invalidate a concrete address exposed by a borrow unless their interaction proves a
pin/no-relocation rule through release. More generally, bespoke interaction is required when a
combined transition can alter another policy's address/range, alias set, liveness interval, write
set, event order, or obligation lifecycle.

Handlers may filter, enrich, duplicate, buffer, redirect, forbid, or lower an operation into more
abstract blocks. Each action remains explicit in selection data and proves its source semantics.
Duplication is not free: a logical event promised exactly once needs a root contract that permits
multiple physical emissions or a projection theorem coalescing them without inventing or losing
logical events.

## 9. Target profile candidates and explicit selection

Targets may offer convenient candidates:

- a bare-metal profile may offer serial logging;
- Windows may offer console output or a selected event-log/daemon adapter;
- Linux may offer terminal, syslog, or journaling adapters.

These are candidates or tooling recommendations, never semantic defaults. Even when tooling finds
one recommended candidate, final selection is explicit and recorded. A game may route logical logs
to a graphical window. A web server may route them to daemon logging. The artifact certificate
records the exact handler/dictionary, target, profile, and version identity so compilation is
explicit and reproducible.

Selection also proves every capability constraint. A target-provided buffered console candidate is
inadmissible under `NoAllocationHere` if its lowering allocates. A different fixed-buffer or direct
serial implementation may be selected, or the program is rejected. Convenience never overrides a
constraint.

## 10. Scoped cancellation, overcommit, and efficient unwinding

Cancellation is a first-class typed operation and outcome. It is not allocator failure, a Boolean
flag, an asynchronous exception with unspecified consequences, or cleanup prose.

### 10.1 Scope and cancellation protocol

Every cancellable request or task has a generative scope identity and generation, a typed parent
and propagation policy, a canonical environment, a lifecycle state, owned and borrowed resources,
children, and scoped obligations. Reuse of a numeric or platform identifier never recreates an old
scope.

```lean
-- Pseudo-Lean only.
inductive ScopeLifecycle
  | running
  | cancelRequested (epoch : CancelEpoch) (cause : CancelCause)
  | cancelPending (epoch : CancelEpoch) (delivery : DeliveryEvidence)
  | observedAtSafepoint (epoch : CancelEpoch) (point : SafePointId)
  | unwindBegun (epoch : CancelEpoch) (plan : CleanupPlan)
  | cleaning (epoch : CancelEpoch) (dispositions : CleanupDispositions)
  | cleanupComplete (epoch : CancelEpoch) (result : CleanupResult)
  | scopeClosed (epoch : CancelEpoch) (bundle : ClosedScopeBundle)
  | taskTerminal (outcome : TaskOutcome)

structure Scope where
  id          : ScopeId
  generation  : ScopeGeneration id
  parent      : Option ScopeId
  propagation : PropagationPolicy parent id
  environment : CanonicalEnvironment
  state       : ScopeLifecycle
  owned       : ScopedAuthority
  borrowed    : ScopedLoans
  children    : ChildScopes
  obligations : ScopedObligations

structure CancelRight (scope : ScopeId) where
  owner      : Principal
  causes     : Set CancelCause
  generation : ScopeGeneration scope

structure FailureEscalationRight (scope : ScopeId) (refusal : RefusalCause) where
  generation : ScopeGeneration scope
  allowed    : RefusalMayRequestCancellation rootContract refusal
```

`CancelRight` may be shareable and repeated requests may be idempotent. This is distinct from the
unique monotone scope transition and cancellation epoch. Cause arbitration for concurrent requests
belongs to the selected root/profile policy; it is not determined by duplicability of the request
right.

The protocol distinguishes these events and transitions:

1. **Request:** a holder of `CancelRight scope` requests an allowed cause.
2. **Delivery/visibility/pending:** the selected runtime makes the request pending for the task.
3. **Observation:** the selected execution observes the request at an admitted safepoint.
4. **Unwind start:** the normal continuation is replaced by the selected cancellation consequence.
5. **Individual cleanup dispositions:** every scoped obligation is released, returned, transferred,
   quarantined, made recovery-owned, explicitly leaked when the root permits that exact leak, or
   retained as outstanding.
6. **Cleanup complete and scope close:** cleanup results and the remaining bundle are sealed.
7. **Task terminal:** the task produces its phase-indexed terminal outcome.
8. **Parent/join observation:** an authorized observer consumes or inspects the promised terminal
   bundle under a separate join/observation rule.

Request, delivery, observation, result production, resource return, scope closure, task terminal,
and join observation are distinct. Acceptance of a cancellation request is not completion. Control
notification and cancellation causality are not memory synchronization or publication. Any memory
visibility claim requires the selected architecture/platform theorem.

Top-down cancellation begins only with explicit `CancelRight` authority. Parent propagation to a
child uses a selected typed propagate, shield, defer, or detach edge; parenthood alone does not
manufacture a child right. Successful child termination and join still account for the child's
terminal bundle, and cancellation never consumes `MustJoin`.

Spawn racing parent cancellation has an explicit linearization rule: either spawn is rejected and
no child exists, or the child is admitted into the cancelled subtree with its own unwind, cleanup,
terminal, and join obligations. There is no interval in which an unaccounted child exists.

Bottom-up cancellation begins with a typed lower-level result such as capacity/overload refusal.
Capacity refusal, policy denial, deadline/timeout, allocator/platform failure, and implementation
bug are distinct causes. A selected governor/handler may translate only a root-enumerated cause into
a cancel request, and only when:

- the precious root permits that exact cancellation cause and terminal outcome;
- the handler proves the failure-to-cancellation mapping;
- the current scope is cancellable and the handler possesses a generation-matched
  `FailureEscalationRight` for that exact scope and refusal cause;
- already committed external effects remain compatible with the proposed outcome; and
- all new cleanup, reporting, and parent/child obligations enter conservation.

A low-level failure cannot invent a source cancellation branch. An escalation right grants no
authority over a parent or sibling scope. Bottom-up propagation across such an edge requires
separate root permission and authority.

### 10.2 Overcommit

Overcommit permits aggregate potential demand to exceed physical capacity. It does not permit
unaccounted live resources or optimistic authority over nonexistent storage.

The admission invariant is:

- every acquisition either succeeds with exact identity, ownership, generation, live accounting,
  and cleanup obligation, or returns a root-permitted refusal/cancellation transition;
- admitted live resources never exceed actual capacity under the selected resource model;
- reserved versus committed capacity is explicit when the target distinguishes them;
- a partial acquisition returns its partial reservation/handle and cleanup obligation; it is never
  reported as “no resource”;
- capacity-reserving waiting, queued, reserved, or in-flight grants count against the applicable
  capacity even before a caller receives a handle;
- cancellation and reclamation return, transfer, retire, or preserve every scoped obligation; and
- a failed acquisition cannot be counted as progress toward resource cleanup or allocation.

Potential demand, cumulative allocation, peak live bytes, maximum single allocation, allocation
count, reserved address space, and committed physical storage are distinct quantities. A profile
must name which quantity it constrains. Resources may be scalar, vector-valued, or profile-defined,
and admission may block, queue, load-shed, or refuse according to the selected root/profile.

Acquisition exposes at least these phases: waiting, reservation, grant, refusal,
cancel-before-grant, grant-then-reclaimed, and return. The selected linearization theorem resolves
acquisition-versus-cancel races. If grant wins, authority and cleanup obligations exist even if the
caller never observes the returned handle. If cancellation wins before grant, no ownership is
invented. Persistence of an allocator or service capability does not make the reservations,
handles, sessions, or other resources it produces persistent.

### 10.3 Cooperative, forced, masked, and raced cancellation

A selected cancellation contract states:

- its cooperative protocol and any separately selected forced failure-domain transitions;
- where requests may be observed and which regions are masked/noncancellable;
- separate request-to-delivery, delivery-to-observation, observation-to-unwind,
  unwind-to-cleanup, and cleanup-to-terminal bounds or weaker progress/fairness claims;
- idempotence and the result of repeated or competing requests;
- the acquisition-versus-cancel linearization rule;
- nesting, child propagation, detach, and join consequences;
- treatment of already committed external effects;
- cleanup failure, retry, escalation, and terminal reporting;
- process, device, provider, or address-domain loss; and
- the exact root-visible terminal outcome.

Masking defers observation; it does not erase a request. A noncancellable critical region must be
bounded or carry the selected progress argument. In an acquisition race, the proof identifies
whether cancellation wins before ownership transfer or acquisition wins and installs a cleanup
obligation that unwinding must discharge.

Every latency or liveness claim names its scheduler, safepoint-frequency, interruptible-wait,
child-progress, and cleanup-progress assumptions. A masked blocking operation cannot claim an
unconditional cancellation bound unless the selected platform proves an interruptible wait or a
separate bound for leaving the masked region.

Forced thread/process/device death is a separate failure-domain transition, never “stronger
cooperative cancellation.” It does not magically make arbitrary instruction points safe or inherit
cooperative cleanup theorems. Its target profile must supply resumable/unwind state when any,
asynchronous-context admission, interruption invariants, survivor/orphan/owner-death recovery, and a
resource-specific reclamation theorem for every physical resource it claims to reclaim. Process or
device loss may make normal cleanup impossible; that is a separately selected disposition, not
ordinary cancellation discharge.

Every operation contract declares cancellation behavior, mask and observation points,
phase-indexed outcomes, introduced resources and children, and irreversible effects. Generated
failure, cancellation, and cleanup obligations follow the same local conservation and decreasing
rank. Applicability analysis conservatively covers failure, cancellation, and cleanup paths, not
only normal execution.

### 10.4 Conservation at cancellation

Cancellation may consume a normal-continuation obligation only through the specified cancellation
terminal consequence. Every resource, cleanup, child, join, pin, loan, handle, buffer, and provider
obligation is:

- released by its owning operation;
- returned to its source owner;
- transferred to an explicitly named live recipient;
- quarantined with a typed repair restriction;
- transferred to a named recovery owner;
- leaked only when the precious root explicitly permits that exact leak and consequence; or
- recorded as still outstanding in the sealed terminal bundle for a later owner.

There is no generic `cancel` disposition that empties a context. Cancellation handlers introduce
their own reporting, buffer-flush, close, and terminal-bundle obligations into the same local
well-founded conservation derivation. Cleanup's own effects, cancellation behavior, and progress
assumptions are modeled. Cleanup failure is recorded separately from the primary cancellation
cause; `cleanup failed` cannot be reported as `scope closed`.

Bulk arena release proves that no lease, borrow, child-owned allocation, or required destructor
escapes the arena. It separately disposes non-memory resources such as sockets, handles, provider
sessions, log buffers, and join rights. Releasing the backing bytes alone is not complete cleanup.

### 10.5 Terminal observability

Irreversible effects carry commit/linearization identity. For HTTP, the root distinguishes at least
pre-response, headers/status committed, partial body, complete logical response, flush completion,
and transport terminal. Remote observation is not local logical completion, and local completion is
not flush or transport disposition.

The root decides what cancellation means in each phase. Candidate contracts include:

- before response commit, resource-pressure cancellation refines to a typed `503`/retry response;
- after headers/status commit, only a root-permitted finish, abort, reset, or truncation applies—a
  fabricated replacement `503` is forbidden;
- after a partial body, retry is allowed only when the root proves it cannot duplicate an
  irreversible network, database, or other external effect;
- after an idempotent fully committed response, cancellation affects only local cleanup; or
- cancellation is masked through a bounded commit region.

These are different observable contracts. No handler or target profile chooses between them
silently. Craig/root-contract review must select the permitted causes, commit boundaries, and
outcomes for the rebuilt HTTP spike.

### 10.6 Efficient unwinding is an explicit constraint

Cancellation correctness does not imply efficient unwinding. A capability context may separately
require:

```text
MaxCancelLatency duration
MaxUnwindSteps steps
MaxUnwindWork cost
MaxCleanupDepth depth
BulkReleaseAllowed arena
SelectedUnwindStrategy profile strategy
```

A hand-crafted lowering may choose arena allocation and bulk release, structured cleanup blocks,
continuations, a bounded cleanup stack, fused finalizers, or target unwind tables. It proves the
selected cost/resource bound and behavioral equivalence. Moving an interceptor across a stage,
fusing cleanup with a terminal block, or replacing per-object cleanup with arena teardown requires
an explicit equivalence/refinement and conserved obligations. Optimization is never exemption from
proof, applicability, target admission, lifecycle, or authority.

### 10.7 Full web-request derivation

Consider a request scope with a logical response contract, resource-pressure cancellation cause,
typed `503` before commit, truncated-response/abort after commit, `MaxPeakLiveBytes`, and
`MaxCancelLatency`.

**Bottom-up path:**

1. The request enters with a fresh child `ScopeId`, scoped allocator/governor offer, cancellation
   runtime offer, and explicit root-permitted outcomes.
2. Parsing or response construction requests an optimistic allocation. Aggregate potential demand
   may exceed capacity because the selected governor permits overcommit.
3. The target allocator either succeeds with exact allocation identity, generation, ownership,
   peak-live accounting, and `MustRelease`, or returns typed refusal. It never grants ownership for
   unavailable capacity.
4. On refusal, the resource governor is the primary handler for that result. It uses its selected
   generation-matched `FailureEscalationRight` to request `resourcePressure` cancellation for this
   scope. The rule proves that the request contract permits the cause and the appropriate
   phase-indexed outcome.
5. The cancellation runtime separately records delivery/pending visibility. The running request
   then observes cancellation at a certified safepoint. Neither event is memory synchronization.
   If execution is in a bounded masked commit region, observation is deferred and the latency proof
   includes that bound.
6. Unwind begins. Before response commit, the selected handler may construct the typed `503`/retry
   response. After headers or partial body commit, it may only finish, abort, reset, or expose
   truncation according to the root contract; it cannot fabricate a replacement `503`.
7. A selected arena implementation may bulk-release all arena-owned allocations in one target
   operation. Its refinement proves the same ownership and cleanup consequence as the abstract
   per-resource plan and satisfies the unwind-work bound.
8. Remaining buffers, handles, child tasks, join rights, logical response completion, flush,
   transport disposition, logging events, and cleanup failures are separately discharged,
   transferred, quarantined, or recorded outstanding. Cleanup failure remains distinct from the
   primary resource-pressure cause.
9. Scope closure and task terminal are certified separately. The terminal request outcome is
   projected to the precious root and later observed/joined by the parent. Request acceptance,
   delivery, local result, resource return, remote observation, and join are never conflated.

**Top-down path:**

1. The parent or timeout governor holds `CancelRight requestScope` for an allowed cause.
2. It requests cancellation without needing an allocator failure.
3. The same observation, masking, unwind, cleanup, terminal, and join protocol runs. Reusing the
   protocol does not conflate the two causes; the root-visible outcome and reporting may differ.

**Source-independent facts** include scope lifecycle, allowed causes/outcomes, commit boundary,
logical response semantics, cancellation conservation, and selected latency/work constraints.
**Implementation-specific facts** include allocator algorithm, overcommit accounting, safepoint
placement, arena layout, target unwind tables, connection-abort primitive, and physical grants.

This case also pressures handler order. `allocator -> refusal governor -> cancellation request` is
not equivalent to `cancellation mask -> allocator`: masking can delay observation while allocation
still succeeds or fails, and an allocation that wins the race creates ownership that unwind must
release. The selected order and race theorem are explicit.

## 11. Worked design cases

These cases pressure-test the protocol before any public interface is implemented.

### 11.1 Allocator identity and allocation budgets

Consider a scope with:

```text
UseAllocator A
MaxPeakLiveBytes 4096
MaxSingleAllocationBytes 1024
MaxCumulativeAllocatedBytes 65536
MaxAllocationCount 128
```

An abstract `allocate n` is a join point. The selected handler must:

1. prove it invokes allocator identity `A`, not merely an ABI-compatible allocator;
2. check or prove that the request is at most 1024 bytes, the new peak-live total remains at most
   4096 bytes, cumulative allocation remains at most 65536 bytes, and the count remains at most
   128;
3. mint fresh allocation/binding identity and lifecycle generation through the owning policy and
   target adapter;
4. return the promised source allocation capability;
5. create the matching release obligation; and
6. lower any metadata access into separately checked memory operations.

`free` consumes the exact generation-matched allocation capability and release obligation, proves
the selected target deallocation, and reduces current live bytes. It does not reduce cumulative
allocated bytes or allocation count. Address reuse creates a new generation; stale authority cannot
cover the new allocation. A policy may constrain only a selected subset of these measures, but must
name them precisely.

Under `NoAllocationHere`, a direct allocation is absent only when selected-operation coverage
proves it unreachable. A handler may not hide allocation inside logging, formatting, exception
setup, or another lowering. If a fused block allocates, it must surface and reject the constraint.

The generic part may prove natural-number budget arithmetic and conservation across sequential
composition. Allocator identity, target allocation success/failure, physical binding, and cleanup
remain realization-specific.

### 11.2 Logical logging with four sinks

The logical contract is parameterized rather than represented by an undifferentiated `Log` token:

```lean
-- Pseudo-Lean only.
structure LogContract where
  ordering             : LogOrdering
  delivery             : DeliveryGuarantee
  refusalBackpressure  : RefusalBackpressurePolicy
  bufferingDurability  : BufferingDurability
  flush                 : FlushContract
  failureObservability : FailureObservation
  cleanup               : LogCleanupContract
```

Suppose the root promises ordered logical log events and permits a declared `LogFailure` outcome
under one selected value of this contract.
Four handlers are considered:

1. **Console:** formats and writes bytes to a console provider.
2. **Serial:** lowers to bounded polling or interrupt-driven UART blocks.
3. **Graphical:** appends a visual log entry to a game window.
4. **Daemon:** sends a structured event to the selected system logging service.

Each handler proves a projection from its physical effects to the selected logical event contract.
Sinks are interchangeable only relative to that contract; there is no theorem that all sinks
refine a generic log token. If the root promises literal console bytes instead, only the console
realization qualifies unless the root explicitly permits another sink.

A filtering handler must prove which root events may be omitted. Enrichment preserves the original
event fields and states the added fields. Duplication proves whether two emissions project to one
logical event or whether the root permits two. Redirection records the selected sink. A forbidding
handler proves the governed logging operation absent.

A buffering handler introduces allocator/memory capability demands and lifecycle obligations. It
must specify:

- event order while buffered;
- capacity and backpressure/failure behavior;
- whether partial sink writes expose prefixes;
- flush triggers and flush failure;
- buffer authority during callbacks or concurrency;
- cleanup on ordinary return, root exit, cancellation, and fatal disposition; and
- whether dropping buffered events is ever permitted by the root.

Handler ordering is observable. `filter -> enrich -> buffer -> sink` is not generally equivalent to
`enrich -> buffer -> filter -> sink`. The selected composition records the order and proves the
required interaction; the initial library does not infer a universal order.

### 11.3 Borrowed access

A mutable-borrow policy authorizes a logical field write using object identity, field range,
lifetime, and exclusivity. A generic layout-parametric adapter may prove field containment,
checked offset arithmetic, and preservation through a state relation.

The realization must still provide the chosen allocation/layout/base, address calculation,
register realization, exact dynamic occurrence and descriptor, current target binding/grant, and
equality between the logical field and concrete accessed range. Borrow exclusivity does not by
itself prove absence of all conflicting machine accesses; that requires a whole-access
correspondence theorem.

### 11.4 Moving-GC access across a safepoint

A moving collector authorizes an object-field access using reachability, object generation, root
state, and its relocation protocol. If a concrete address escapes across a safepoint, the selected
interaction must pin the object, refresh the address after relocation, or prove the safepoint
cannot collect or move it.

Architectural definedness and target admission can remain true for a stale address, so neither
proves GC authorization. The target-to-source simulation fails unless the occurrence corresponds to
the currently authorized object/binding and preserves the post-state relation. “Live GC object to
live fixed allocation” is not a generic adapter until relocation and pinning are modeled.

### 11.5 Literal buffer passed to `WriteFile`

The source operation promises a logical output event or literal bytes according to the precious
root. The lowering selects a literal layout, read-only memory binding, buffer length, output handle,
provider call, and failure semantics.

The buffer read needs policy authorization, target resource admission, and ISA-defined accesses in
the selected provider boundary model. The linker owns exact literal and import-slot identity; the
Windows profile owns provider realization. A provider certificate cannot manufacture the source
output meaning, and successful access to the buffer cannot prove that the correct logical bytes
were requested.

### 11.6 IAT memory and indirect-call validity

An import call combines distinct concerns:

- the linker proves the exact artifact's slot, symbol, and layout identity;
- the loader/profile proves a live generation-matched IAT binding and permitted read;
- the ISA proves the exact dynamic memory read and indirect-control transfer are architecturally
  defined;
- the provider/runtime certificate proves the resolved target realizes the selected service; and
- the source refinement proves the service call implements the independent logical operation.

Reading a mapped IAT slot is not provider authorization. Resolving a valid provider is not proof
that the emitted call uses the right slot. A static instruction index cannot identify a repeated
dynamic call.

## 12. Dynamic occurrence and replay-safe grants

Evidence is scoped to execution-derived occurrences, not caller-provided natural numbers.

```lean
-- Pseudo-Lean only.
structure AccessOccurrence (execution : Execution) where
  agent          : execution.AgentId
  step           : execution.CertifiedStep agent
  preState       : MachineState
  pc             : Address
  fetched        : Instruction
  fetchProof     : execution.fetch step preState pc = fetched

structure TargetGrant (context : ExecutionContext) where
  binding        : context.BindingId
  generation     : context.Generation binding
  range          : AddressRange
  permissions    : PermissionSet
  mintedByTarget : context.Mints binding generation range permissions

GrantCovers grant occurrence descriptorOrdinal preState : Prop
```

Where concurrency is selected, occurrence identity also contains the agent/thread and certified
event or partial-order position. Repeated loop iterations yield distinct occurrences even when
their PC and fetched instruction are identical.

Constructor privacy alone is insufficient for grants. A persistent grant is sealed and indexed by
execution context, binding identity, lifecycle generation, covered range, and permissions.
`GrantCovers` relates it to the exact occurrence, descriptor, current pre-state, resolved range, and
required access kind. Free, unmap, or rebind invalidates the current-state relation. Reuse mints a
new generation, so an old grant cannot cover the new state. A persistent grant may validly support
many occurrences; the derived coverage proof is occurrence-specific.

## 13. Candidate adapter and consumer matrix

“Candidate” means suitable for design review, not approved library work.

| Adapter or fact | Potential generic portion | Required specific portion | Pressure-test consumers |
|---|---|---|---|
| Interval access | Containment and non-wrap arithmetic parameterized by address width | Selected descriptor, effective address and target grant | Borrowed field, literal buffer, IAT |
| Field/array layout | Offset/scale arithmetic under an explicit layout | Chosen layout, base and register realization | Borrowed field, GC field, sort table |
| Obligation translation | Directional entailment and relational composition | Level-local predicates and state projection | Allocation, logging, borrow, GC |
| Independent composition | Product predicates and preservation skeleton | Noninterference theorem | Read-only log source plus budget constraint |
| Allocator budget | Live-byte arithmetic and sequential conservation | Allocator identity, failure, binding and cleanup | Logging buffer, Spike 3 storage |
| Logical logging | Event projection interface | Sink semantics, failure, order and cleanup | Console, serial, GUI, daemon |
| Stack slot | Possibly interval arithmetic | ABI growth, red zone, alignment, probing, frame lifetime and unwind | Checked store, output call frame |
| Borrow exclusivity | Policy-local exclusivity laws | Whole-machine access correspondence | Checked store, shared/concurrent buffer |
| Moving-GC liveness | Policy-local reachability laws | Relocation, safepoint, pinning and refreshed bindings | GC object field |
| Indirect call | Abstract selected-service refinement | Artifact slot, loader binding, control target, ABI/provider realization | `WriteFile`, process exit |

The first four arithmetic/relational rows may become small generic libraries only after their
consumers demonstrate identical theorem shapes and Craig approves implementation. Stack ownership,
borrow-to-machine nonconflict, and live-GC-to-fixed-allocation are specifically withheld from early
generalization.

## 14. Negative controls

The design is rejected if an implementation permits any of these:

- **Architectural-policy conflation:** a mapped, non-faulting stale pointer is accepted as source
  authorization.
- **Caller-minted admission:** public constructors or arbitrary host/mapping premises create a
  target grant.
- **Static replay:** evidence for one loop iteration is reused solely because the PC/instruction is
  equal.
- **Generation replay:** authority survives free/remap and authorizes a new object at the same
  address.
- **Dropped constraint:** `NoAllocationHere` succeeds while a selected handler allocates.
- **Circular discharge:** source obligation `O` lowers to `P`, while `P` is justified only by
  assuming `O`.
- **Retagging:** a string, Boolean, or constructor rename counts as proof of discharge.
- **Hidden weaving:** global instance priority or import order changes the selected sink, allocator,
  target, profile, failure semantics, or cleanup.
- **Order erasure:** noncommuting handlers compose without a selected order and interaction proof.
- **Silent sink substitution:** console-byte behavior is replaced by GUI or daemon logging under a
  root that did not permit it.
- **Run-derived meaning:** a generated execution, output, artifact, or evaluator defines the source
  specification it is supposed to implement.
- **Universal obligation authority:** an opaque payload or caller-forgeable universal obligation
  bypasses a level owner's predicate.
- **Cleanup disappearance:** buffering, allocation, handles, loans, pins, or provider state vanish
  on return, failure, cancellation, or root exit without a selected disposition theorem.

### 14.1 Mandatory cancellation and overcommit controls

The design must structurally reject all of these:

1. An acquisition grant wins its race and charges quota, the caller never observes the handle, and
   no cleanup obligation exists.
2. Reserved or in-flight capacity is omitted from admission accounting.
3. A stale cancel right affects a reused scope identifier or later generation.
4. A refusal handler cancels a parent or sibling without a matching escalation/propagation right.
5. Parent terminal state consumes `MustJoin` before child cleanup and terminal-bundle accounting.
6. Duplicate cancel requests run cleanup, resource return, or terminal publication twice.
7. Masked blocking I/O claims unconditional cancellation latency without interruptible-wait or
   scheduler/progress premises.
8. Committed HTTP headers are followed by a fabricated replacement `503` response.
9. Retry duplicates an irreversible partial network, database, or other external effect.
10. Forced thread/process/device death inherits cooperative lock release or cleanup claims.
11. Arena release succeeds despite an escaping borrow, child allocation, required destructor, or
    unclosed socket.
12. Cleanup failure is reported as successful scope closure.
13. A cancel request is treated as task completion, memory visibility, resource return, or join
    observation.
14. A child refusal bubbles to its parent without an explicit propagation edge and root permission.

Additional controls reject partial acquisition reported as “no resource,” spawn racing cancellation
and producing an unaccounted child, a persistent service capability making its produced handles
persistent, and a first implementation installing a simplified synchronous/noncancellable meaning
as if it were the general contract. An initial implementation may select an explicitly smaller
profile of the complete semantics; it may not redefine the complete semantic surface.

## 15. Hand-crafted lowering is a feature

The system should make bespoke lowerings cheap to generate, discard, and rebuild. “Cheap” never
means proof-free: every bespoke lowering retains behavioral refinement, applicability, target
authority, lifecycle, cleanup, and obligation-conservation proofs. It should not optimize for
retaining a conventional pass pipeline when a whole-program implementation benefits from fusion,
different allocation, target-specific operations, or a different effect route.

Optimization or fusion may move interception across stages only with an explicit
equivalence/refinement theorem and conserved inherited and introduced obligations.

Repeated motifs may become shared abstract operations only after they are independently specified
and materially different consumers exhibit the same proof boundary. What is reused is the highest
target-independent semantic fact that remains true, plus small routine proof adapters. Intermediate
representations, handler boundaries, and generated programs remain disposable.

## 16. Proposed amendments to `TRUST_REBUILD_PLAN.md`

This section proposes exact semantic changes. It does **not** edit or supersede the accepted plan in
this commit.

### 16.1 Replace the singular checked-access prerequisite

In §2 and §2.5, replace any implication that one checked-memory authority interface is the shared
high-level model with four orthogonal judgments:

1. ISA-owned `ArchitecturalAccessDefined` for every selected dynamic descriptor occurrence;
2. target/profile-owned `TargetResourceAdmits` using sealed binding- and generation-sensitive
   evidence; and
3. policy-owned `PolicyAuthorizes` for plural high-level disciplines.
4. whole-program `BehavioralRefines` against the source-owned independent root contract.

Require the selected lowering/state relation and target-to-source simulation to connect all four
without deriving behavior from access safety.

### 16.2 Add capability-directed effect selection

Extend §2.1 with the semantic polarities demand, constraint, offer, and authority without committing
to one Lean representation. State explicitly that algebraic effect handling is normative: typed
operations are join points, explicit implementation dictionaries/handlers are selected advice,
and staged proof-producing lowering is weaving. Require one primary handler per selected operation
occurrence. Artifact certificates record handler/dictionary/target/profile/version identity. Target
profiles may recommend candidates but final selection remains explicit and no global instance
chooses semantics.

### 16.3 Add obligation conservation to every lowering edge

Require every lowering edge to account for inherited and lowering-introduced obligations by proof,
translation, named interception, preservation/delegation, or sound absence. Require directional
semantic entailment and a finite well-founded local derivation; forbid a universal obligation
registry, global ledger, circular retagging, and silent discard.

### 16.4 Clarify capabilities and composition

Define interception as one capability role, while permitting persistent authority, resource
identity, lifecycle, delegation/revocation, state transitions, and future obligations. Initially
permit generic composition only by product plus explicit preservation/noninterference. Require
selected order and bespoke interaction/distributive-law proofs for noncommuting handlers. Do not
introduce a generic handler stack.

### 16.5 Replace Phase A's early dictionary/pathfinder step

Postpone implementation of the current smallest `CheckedMemoryOperations` dictionary, universal
high-level memory-authority record, and affected target lowering. Before shared interface approval,
review this design against:

- exclusive mutable borrowing/region ownership;
- a tracing moving collector with safepoints, relocation, and pinning;
- allocator identity plus distinct cumulative/peak-live/per-allocation/count and no-allocation
  constraints;
- logical logging through console, serial, graphical, and daemon sinks;
- scoped top-down and bottom-up cancellation, overcommit, acquisition races, masking, child
  propagation, irreversible commit phases, cleanup failure, and bounded unwind;
- checked stack/field access, literal-buffer output, and IAT/indirect calls.

Only after plural-policy and materially different consumer pressure tests should the smallest
shared/public interface be proposed for implementation.

### 16.6 Clarify what may proceed

Do not pause independent high-level specifications or pure algorithm proofs that satisfy the
two-realization-erasure test. Continue to treat `ClosedExecution` and `ProgramCertificates` as
backend leaves. Gate shared safety machinery, checked-memory pathfinder implementation, affected
target lowering, and template declaration on Craig's explicit approval.

### 16.7 Update ownership and review gates

Replace the singular checked-access ownership row with separate ISA, policy, lowering, and
target/profile seams. Add negative controls for caller-minted grants, stale-generation/static-PC
replay, circular obligation translation, hidden handler selection, noncommuting composition, and
silent sink substitution. Keep Trust Repair as integration owner only.

### 16.8 Add the complete cancellation design surface

Require the semantic model to accommodate generative scopes, canonical environments, typed
propagation, `CancelRight`, `FailureEscalationRight`, request/delivery/observation/unwind/cleanup/
closure/terminal/join separation, acquisition linearization and overcommit accounting, masking and
progress assumptions, irreversible commit phases, cleanup failure/disposition, and cooperative
versus target-owned forced failure-domain transitions. First implementations may select smaller
explicit profiles but may not install a temporary synchronous or noncancellable meaning as the
general contract.

## 17. Documentation consistency map

This proposal is not canonical while conflicts remain unresolved. Current file ownership does not
dictate the rebuilt destination: existing documents, APIs, stages, and datatypes are spare parts.
The first table is descriptive only.

`MEMORY_MODEL.md` is nevertheless authoritative for the platform/ISA memory, provenance, ordering,
device, and validation meanings it currently states until an accepted successor proves coverage.
That authority makes it a fundamental destination of lowering; it does not make it the owner of
the generic lowering architecture.

### 17.1 Current live-document conflict inventory

| Live document and exact surface | Conflict or freeze risk | Required audit disposition |
|---|---|---|
| `TRUST_REBUILD_PLAN.md` §§2.1–2.5 and Phase A | Names an abstract-block/dictionary seam, one checked-access contract, and pathfinder-first sequence before the replacement lowering is selected | Amend after design acceptance to semantic polarities, four judgments, full cancellation surface, and destination owners without freezing a representation |
| `MEMORY_MODEL.md` §§4–16 | Mixes durable authority/lifecycle/concurrency laws with staged implementation sequence, named index/ledger shapes, and candidate APIs | Remains the authoritative semantic baseline until an accepted successor proves §18 clause coverage; packaging is rebuildable, but no split/extraction or historical downgrade occurs before that review |
| `SYSTEM_EFFECTS.md` §§1.1, 2, 4, and 6 | Current typeclasses, “placement-free typed row,” and target matrix can freeze the effect/lowering representation or look like platform defaults | Keep useful source meanings and observation laws as spare parts; replace or split current APIs; call target rows explicit candidates and link the accepted lowering design |
| `ABI_CONTEXT.md` §§4–8 and 10 | §7 says “generational ledger”; §8's blanket “cancellation is cooperative” narrows the complete model | Replace ledger wording with imported schemas; normal observation may select a cooperative profile, while forced termination remains a distinct failure-domain outcome; keep ABI transport-only |
| `API_STATE_MODELS.md` §§1–5, especially §3 | `ComposedState` obligation list, `Callable` derivation, and ledger equations read as normative architecture | Historical/inventory downgrade; live semantics move to destination owners, with no compatibility requirement for current shapes |
| `OBLIGATIONS_AND_CAUSALITY.md` §§1–2.3 | Correctly calls itself inventory but still prescribes duplicate future obligation constructors | Keep inventory/orientation; turn prescriptions into examples and links to the accepted generic and domain-local semantics |
| `MEMORY_HOOK.md` §§3–4 and §§12.4–12.6 | Durable descriptor facts are mixed with one planned capability-authoring vocabulary | Keep descriptor/fidelity/ISA connection laws; historical-downgrade Layer A and link plural policies, lowering, and target admission |
| `PROOF_CARRYING_ASSEMBLY.md` §§1–2 | Narrow discrete-memory permissions can be mistaken for the universal capability ontology | Historical/orientation downgrade; keep only still-valid semantic examples and negative controls |
| `READ_BINDER_CONTRACT.md` §§2–5 and §9 | Universal binder semantics are durable, but §9 freezes landed implementations and `[]`/plain `Except` can erase a committed prefix | Preserve successful payload binding/chunking plus committed bytes and terminal EOF/would-block/error/cancel; make APIs rebuildable and consume new contracts |
| `FUTURE_PROCESS_MODEL.md` §§2–4 | Future process capability/cancellation material can compete with current semantics | Keep future-profile only, parameterized by the accepted generic resource/scope and effect contracts |
| `SPIKES/SPIKE3_SORT_LINES.md` §§2 and 4.1; `SPIKE4_HTTP_SERVER.md` §§1–2 and 4; `SPIKE5_GZIP.md` §§3–4 | Consumer-local resource, refusal, cancellation, and cleanup prose can become parallel global machinery | Keep only each precious root/profile choice and consumer instantiation; replace duplicate machinery with links |
| `SPIKES/SPIKE4_HTTP_SERVER.md` §§1–2 and 4 specifically | Conflates HTTP `414` policy rejection with allocation/admission overload and closes request/connection scope at parser completion | Separate parser-buffer release from transferred/live request and connection obligations; model uncommitted, committed-prefix, complete, cancellation, and cleanup-failure send phases |
| `EQUIVALENCE_PROOFS.md` §1.1 reactive-program discussion | Claims unconditional reactive liveness under finite capacity and unconstrained arrivals | Replace with admitted-scope safety/refinement, premise-indexed progress, and explicit overload/refusal/backpressure/cancellation behavior |
| `DECISIONS.md` ADR 0004 in §3 | “Attached, in-scope capability proof” risks freezing one evidence representation | Preserve the dynamic-access safety requirement; allow plural policy evidence transported through lowering into policy/ISA/target judgments |
| `ROADMAP.md` §§2–4, `ARCHITECTURE.md` §2, `VISION.md` §§1 and 4, and other `DECISIONS.md` summaries | Concise durable rules coexist with duplicate protocol detail | Keep durable principles, status, and links; no second protocol definition |
| `TARGETS/WASI.md` §§1–2, `TARGETS/LINUX.md` §§1–2.3, `TARGETS/WINDOWS.md` §1, and target examples in `SYSTEM_EFFECTS.md` §4 | Platform examples can silently select source meaning or cancellation policy | Targets own physical realization and profile outcomes only; every outcome refines explicitly selected source semantics |
| `COMPILER_PLAN.md` “Non-negotiable completion gate” and “Subsequent slices”; `STDLIB_FACILITIES_PLAN.md` §§2, 6, and 7 | Current staged slices/APIs can be mistaken for semantic owners; Stdlib's cancellation ownership is inconsistent with the clean destination | Mark implementation plans replaceable; carry selected effects/failures and consume destination contracts without compiler- or Stdlib-local semantics/ledgers |

### 17.2 Clean destination semantic ownership and migration

Even these file/module boundaries are rebuildable. What is canonical is the semantic responsibility
and theorem meaning, not a permanent filename, datatype, stage count, or API.

| Destination responsibility | Owns | Must not own | Migration from current documents |
|---|---|---|---|
| Precious root specification | Full admissible envelope: observables, safety/non-fabrication, causality, failures/partial effects, authority/provenance/cancellation/cleanup requirements, and adopted progress/resource/security claims | Handler choice, target layout, or run-derived meaning | Keep/rebuild per-spike roots; delete incidental intermediate contracts |
| Effect/capability contracts | Typed operation meaning plus typed authority preconditions, results, transfers and retained obligations across demand/constraint/offer/authority polarities | Physical grants, one global handler stack, universal operation registry, or concrete authority carrier | Split useful source vocabulary from `SYSTEM_EFFECTS.md`; replace representation-frozen typeclasses/rows as needed |
| Generic resource/scope semantics | Small parameterized schemas for generative identity/parentage/freshness, domain-supplied modality laws, lifecycle transitions, cancellation phases, races, typed dispositions, capacity accounting, causal edge kinds, terminal bundles, and conservation interfaces | Universal resource/obligation sum, domain operation constructors, fixed state encoding, global ledger, or memory-specific policy | Candidate extraction only: each schema must specialize back to every applicable `MEMORY_MODEL.md` rule under §18 before migration |
| Domain policy libraries | Borrowing, GC, regions, allocators, logging sinks, request policies, their carriers/local obligation languages, and explicit interaction/refinement laws | ISA definedness or target-minted admission | Keep only verified policy semantics from current memory/effect docs; add materially different policies without central datatype edits |
| Rebuilt memory semantics | Precious memory relation families such as `rf`, `co`, `fr`, `po`, `sw`, `hb`, and selected target/device relations, plus memory-specific authorization policies | Generic scope/cancellation ontology or lowering machinery | Proposed successor only after clause preservation; `MEMORY_MODEL.md` is not split or downgraded until Craig accepts every changed/deferred/no-successor row |
| Rebuilt lowering semantics | Explicit primary-handler selection; staged interpretation; local well-founded obligation translation/conservation; source-target relations; target-to-source simulation; behavioral refinement; ordered/fused composition proofs | Source meaning, physical authority, universal obligation constructors, or a permanent compiler pipeline | Replace current dictionary/row/ledger seams; mine them only for proof patterns and negative cases |
| ISA family | `ArchitecturalAccessDefined`, exact descriptor occurrence, instruction step/fault behavior | Policy authorization or platform allocation | Keep descriptor work from `MEMORY_HOOK.md` and ISA code; rebuild authoring connection |
| Target/profile/platform | `TargetResourceAdmits`; physical grants, mappings, generations, runtime/provider realization, and failure-domain transitions | Source semantics or implicit global defaults | Keep accepted target certificates and profile facts; require explicit selection and new lowering connection |
| ABI boundary | Transport/projection of logical context, machine conventions, physical boundary admission, frames, and unwind metadata | Another ownership, cancellation, cleanup, or obligation system | Reduce `ABI_CONTEXT.md` to transport/realization and links |
| Linker/artifact certificate | Exact selected handler/dictionary/target/profile/version structural identity and evidence closure | Behavioral meaning or authority; fingerprints as proof | Extend only after interface approval; fingerprints remain metadata |
| Governance/integration | Review gates, dependency order, current status, and atomic cutover | Semantic protocol duplication | Amend `TRUST_REBUILD_PLAN.md`; reduce summaries to links |

After acceptance, this proposal drives an atomic reconciliation of surrounding documents. It then
becomes either a link/index or the designated canonical design source, as Craig decides; it must
not coexist as a fourth competing owner.

### 17.3 Rebuild-resistance test

Review must answer yes to all five questions:

1. Can obligation datatypes, handler representation, lowering stages, scope-state encoding, and
   accounting structures all be deleted and rebuilt without changing source semantics?
2. Does every preserved claim point to a semantic theorem or negative control rather than a module,
   datatype, field, or constructor name?
3. Are current implementations explicitly evidence and spare parts rather than preservation
   obligations?
4. Can a novel GC, allocator, logger, cancellation runtime, or target be added through local policy
   plus translations/handlers without editing the precious root?
5. Is every compatibility requirement justified by external artifact/ABI semantics rather than
   internal history?

Failure means the documentation freezes the architecture and must be amended before design closure.
The proposal commit intentionally edits none of the audited surrounding documents.

## 18. `MEMORY_MODEL.md` semantic preservation appendix

`MEMORY_MODEL.md` is the authoritative semantic baseline until an accepted successor proves
coverage. Its file layout, sections, stage names, datatypes, and interfaces are replaceable; its
accepted meanings are not silently discardable. “No successor” is blocking absent Craig's explicit
approval.

This preservation rule protects the applicable platform/ISA memory, provenance, ordering, device,
validation, and other accepted semantic clauses. It does not assign generic handler selection,
obligation translation, or staged lowering to `MEMORY_MODEL.md`.

For a proposed extraction, the second column names the neutral law, its memory instantiation, and
the exact specialized consequence that must recover the existing rule. An extraction that requires
unstated assumptions or cannot recover the rule is **semantic weakening — BLOCKED**. The table is a
design obligation, not a claim that the successor theorems already exist.

| Existing section/claim/invariant/control/gate | Destination owner and exact successor clause, including specialization | Status | Rationale, affected profiles, counterexamples, and proof/validation consequence |
|---|---|---|---|
| §§3, 5.3, 6: authority/provenance is decided before ordering | Domain policy authorization plus §5.3 `PolicyAuthorizes`; memory instantiation requires live provenanced authority before consulting rebuilt memory relations; specialized consequence is the current “ordering cannot repair unauthorized access” rule | meaning-preserved | All CPU/device profiles. A fence around a stale pointer remains rejected. Successor proof orders authorization before consistency construction |
| §6.1.1: stored/raw bytes cannot mint provenance or authority | §4.1 no-fabrication schema instantiated by memory typed-view/binding policy; specialized consequence: integer/address bytes remain non-dereferenceable absent a live generation-matched imported binding | generalized (proposed) | x86, AArch64, hosted, bare-metal, external memory. Decode/cast counterexample remains rejected. Extraction is blocked until specialization proves the current typed-view rule |
| §§4, 6.1–6.2: generative identity and stale-generation rejection | §4.1 generative identity/freshness/non-revival plus §12 replay-safe grants; memory instantiation uses `RegionId`, binding/allocation generation and current-state liveness; consequence rejects free/rebind/ABA revival | generalized (proposed) | CPU, IAT, allocator, device/IOMMU. Same-address reuse is the negative control. Target grant and policy generation must agree at the occurrence |
| §§6.2–6.4, 7.3: loan and obligation conservation | §4.1 balance/cleanup conservation and §7 lowering conservation instantiated by memory loans, views, guards, `MustReturnLoan`, `MustRelease`, and terminal bundles; consequence recovers exact return/transfer/discharge before closure | generalized (proposed) | Borrowing, locks, spawn/join, root exit. Empty-ledger replacement and dead-thread stranded authority remain rejected |
| §§4, 8, 10.4, 11: ISA/program/scheduler/control/observable causality remain distinct | §4.1 causal-edge-kind schema and §10.1 cancellation distinction; memory instantiation retains typed `po`, scheduler, interrupt, device and projected-observable paths; consequence forbids one edge kind from manufacturing another | generalized (proposed) | Threads, futex, interrupts, device completion, traces. Notification/control delivery cannot imply publication or observable completion |
| §§3–5.3: architecture-neutral event vocabulary contains no hidden TSO | Rebuilt memory semantics in §17.2 retains normalized access/barrier/event vocabulary; x86 and AArch64 instantiations separately interpret it; consequence recovers no common FIFO/multi-copy-atomic assumption | meaning-preserved | x86/AArch64 and future ISA/device profiles. “AArch64 = TSO plus fences” remains a negative control |
| §5.1: x86 WB operational TSO, FIFO per-agent store buffers, forwarding, locked/fence rules | `MEMORY_MODEL.md` §5.1 remains owner until an exact rebuilt-memory successor clause is approved; no generic resource/scope extraction changes it | meaning-preserved | x86 WB only; UC/WC/MMIO excluded. Litmus/model-checking and Intel/AMD reference gates remain required. No successor currently proposed, so removal is blocking |
| §5.2: AArch64 weak memory, acquire/release/barriers, exclusives and local/global monitors | `MEMORY_MODEL.md` §5.2 remains owner until an exact successor; §4.1 race schemas may be consumed but do not define memory order | meaning-preserved | AArch64 only. Failed exclusive write, reservation granule, shareability and progress premises retained. No TSO leakage |
| §§5.1–5.2, 8: agent-local x86 store buffers and AArch64 reservations/monitors | Rebuilt memory semantics §17.2, specialized separately per ISA; consequence preserves per-agent buffering and reservation invalidation rather than a generic agent-local state field | meaning-preserved | x86 store-buffer and AArch64 exclusive-pair counterexamples. Generic scope identity supplies no ordering theorem |
| §§4, 6.2–6.3, 7: plain versus atomic access/authority distinction | Domain memory policy plus rebuilt memory relations; ISA §5.1 proves the selected instruction descriptor; specialized consequence forbids mixed plain/atomic access and rejects “atomic” as a relabelled ordinary access | meaning-preserved | x86 aligned `MOV` atomic profile, AArch64 atomics/exclusives, futex wait words. Width/alignment/single-copy-atomicity qualifiers retained |
| §§4, 7.1–7.2: synchronization witnesses name instance/generation and exact release/acquire events | Rebuilt memory semantics §17.2 with domain lock policy; §4.1 identity/race schema is only supporting structure; consequence recovers `SyncWitness`-style evidence without freezing that datatype | generalized (proposed) | Mutex and future synchronization policies. Wake or shared address alone cannot create `sw`; proof must name observed release under target memory rules |
| §§7.1–7.3, 9: result-indexed lock/wait authority | Domain lock/wait policy instantiates §4.1 request/reserve/grant/return/disposition; consequence returns guards/protected authority only on selected acquisition results and preserves pending/refusal resources otherwise | generalized (proposed) | Mutexes, futex, `WaitOnAddress`, timeouts/cancellation. Failed CAS, wake, or not-acquired result grants no ownership |
| §§7.1, 7.3: queue-node loans and deferred-withdrawal obligations | Domain queue-lock policy over §4.1 lifecycle/conservation; specialized consequence requires published node return or generation-matched outstanding withdrawal before reuse | generalized (proposed) | MCS/qspinlock-style candidates. Lazy withdrawal cannot disappear on cancellation; generic allocator cleanup is insufficient |
| §§3–4, 7–11: completion, notification, observation, return, reclamation, delivery and persistence are distinct | §4.1 consequence-distinction law plus root envelope §2; each domain policy instantiates exact event/result types; consequence preserves all current non-collapse rules | generalized (proposed) | CPU, scheduler, network, device, storage, remote delivery. One completion flag cannot prove resource return or persistence |
| §§6.4, 9: wake/runnable/signaled is not memory visibility | §4.1 causal-kind separation plus rebuilt memory `sw` rules; futex/parking instantiation proves release/acquire visibility separately; consequence recovers wake-only rejection | meaning-preserved | Linux futex, Windows address parking, task join. A wake count or successful wait cannot mint publication |
| §§4, 10.1–10.3: CPU barrier is not cache maintenance, DMA completion, or ownership transfer | Rebuilt memory/device policy §17.2; §4.1 consequence distinction is supporting only; specialization retains separate cache/IOMMU maintenance, completion, ownership and visibility effects | meaning-preserved | Bare-metal x86/AArch64, noncoherent DMA, devices. `DMB`/fence-only counterexamples remain rejected |
| §§4, 6.1.2, 10.3: DMA/device/IOMMU bindings are generational and address-domain specific | §4.1 generative identity instantiated by device policy plus target-owned §5.2 admission; consequence rejects stale IOVA/descriptor/rebind evidence and preserves logical-resource identity | generalized (proposed) | DMA, GPU, device, IOMMU/RDMA future profiles. CPU pointer or raw key bytes cannot mint device authority |
| §§6.4, 8.4: cancellation does not imply rollback, synchronization, cleanup, or terminality | §10 complete cancellation protocol and §4.1 causal/conservation schemas; memory/thread instantiation preserves live authority until explicit disposition; consequence rejects request-as-return/visibility | strengthened (proposed) | Cooperative task cancellation, locks, waits, HTTP. Strengthening adds missing phases without weakening existing no-collapse rules |
| §§8.4, 10.4: interrupt/control delivery, handler entry, device completion and scheduler wake are separate | Target failure/control profile plus ABI transport and §4.1 causal kinds; specialization recovers exact handler context, masking, nesting, callable surface and return/unwind obligations | meaning-preserved | IRQ/NMI/exception/signal/APC/trap and device paths. Entry cannot grant DMA visibility or ordinary-thread authority |
| §§6.4, 8.4, 10, 13: failure-domain termination is not normal cleanup | Target/profile failure-domain owner plus §10.3–10.4 typed disposition; memory instantiation names survivor/orphan/owner-death/quarantine consequences per resource | strengthened (proposed) | Forced thread/process/device loss, robust recovery, external resources. Forced kill cannot inherit cooperative unlock or reclaim devices without target theorem |
| §11 and §11.1: total non-inventing trace quotient with bidirectional fidelity to labelled source paths | Rebuilt observation/refinement owner plus root §2 and `BehavioralRefines` §5.4; successor must preserve node surjection, no invented edges, path witnesses, renaming/isomorphism and relation kinds | meaning-preserved | Concurrent CPU and heterogeneous target traces. A convenient linearization or transitive reduction cannot replace the quotient theorem |
| §§9, 9.1–9.2: bare address parking, futex and `WaitOnAddress` have narrow profile semantics | Domain wait policy over §4.1 lifecycle plus platform admission; specialization preserves wait-word lifetime/generation, errors, spurious returns, process-private scope and non-fence wake semantics | meaning-preserved | Linux x86/AArch64 futex and Windows parking. Parking is not join, ownership acquisition, composite wait, or publication |
| §§7, 9, 14–15: progress claims carry exact fairness/eligibility/interference and cleanup-liveness premises | Root envelope §2 plus domain policy progress clauses and §10.3 phase-specific latency; successor consequence preserves safety-only/system-progress/starvation-free distinctions | generalized (proposed) | Mutex, parking, cancellation, scheduler, bare-metal waits. Retry, wake, timeout, cleanup, or finite test cannot be promoted into progress |
| §§10.1–10.5: bare-metal x86/AArch64 SMP, device order, DMA and interrupt qualifiers | Rebuilt memory/device semantics §17.2 plus ISA/target owners; no neutral extraction replaces target rules; exact specialization retains startup, memory attributes, barriers, cache/DMA ownership and interrupt routes | meaning-preserved | Bare-metal profiles and hardware/QEMU harnesses. Hosted assumptions and coherent-memory defaults cannot leak in |
| §10.5 and §13: QEMU/hardware validation is bounded evidence, not architectural proof | Validation owner remains the selected target/profile matrix; successor clause must state emulator/hardware/vendor coverage and untested boundaries | meaning-preserved | All native/bare-metal profiles. Observed outcomes cannot prove completeness, exact equivalence, or unsupported vendors |
| §§14–15.1: stage gates and reference-intake gates precede normative implementation claims | Governance owner plus destination-specific review gates; semantic successor preserves “no downstream dependency before exit criterion” and authoritative pinned reference intake, while exact M1–M9 packaging may be rebuilt | generalized (Craig review required) | All profiles. Renaming/reordering stages is allowed; weakening exit criteria, skipping target references, or treating examples as completion is rejected |
| §16 requirement closure and negative-control matrix | Governance plus each destination semantic owner; every current row must map to an accepted successor theorem/control before deletion | meaning-preserved | Cross-cutting. Missing successor row blocks reconciliation; a smaller first implementation is an explicit profile, not a weakened universal model |

### 18.1 Extraction review rule

For every candidate move out of §§6–10, review must record:

1. the neutral general law;
2. the memory-domain instantiation;
3. the exact specialized theorem recovering the current claim;
4. all retained architecture/profile qualifiers and negative controls; and
5. the destination of validation and reference-intake gates.

Re-attack the result with x86, AArch64, bare-metal, futex/parking, GPU/DMA, asynchronous,
interrupt, trace-quotient, and validation counterexamples. Extra unstated assumptions, lost
qualifiers, or a missing specialization are **semantic weakening — BLOCKED**. Semantics are the
frozen baseline; packaging and Lean APIs are not.

## 19. Non-goals

This proposal does not seek:

- classic textual pointcuts or name-pattern matching;
- hidden global weaving or global semantic defaults;
- a universal ownership, capability, effect, or obligation god type;
- automatic universal handler composition or a generic ordered handler stack;
- a global mutable obligation ledger;
- one memory policy shared by borrowing, GC, region, target, and ISA layers;
- complete language memory safety from ISA fault freedom alone;
- automatic derivation of race freedom from ordinary access safety;
- preservation or compatibility of old spike proof APIs;
- a fixed general compiler pipeline; or
- any Lean implementation in this design commit.

## 20. Review checklist and next gate

Before implementation is proposed, reviewers should establish:

- the four judgments have non-overlapping ownership and connect through the selected lowering;
- target-to-source refinement cannot infer policy authorization from target access safety;
- obligation translations are directional, well-founded, and cover introduced obligations;
- grants cannot be caller-minted or replayed across free/remap generations;
- handler selection and ordering are explicit and artifact-reproducible;
- product composition requires preservation/noninterference;
- allocator constraints and logging failures/cleanup remain visible through lowering;
- the complete cancellation surface is available without forcing one global cancellation or HTTP
  policy;
- borrowing and moving-GC examples retain their distinct policy semantics;
- source contracts pass the two-realization-erasure test;
- every proposed generic adapter has at least two materially different immediate consumers; and
- the negative controls fail for structural reasons rather than repository policy or convention;
  and
- every documentation conflict in §17 has an approved amendment/link owner before this design is
  called closed.

After Craig, MP, and Reviewer accept the design, a separate plan amendment may select the smallest
public interface. Only Craig's explicit decision authorizes subsequent Lean implementation.
