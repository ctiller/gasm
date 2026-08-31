# Proof-lowering core design

**Status:** clean-slate design proposal. It authorizes no Lean implementation, public API,
migration, or integration. Craig owns semantic and architecture decisions; `trustplan` owns the
design plan; Trust Repair owns integration.

This document defines the semantic boundary for rebuilding proof-producing lowering. It replaces
the center of gravity of the historical capability/obligation lowering proposals without requiring
compatibility with their datatypes, stage names, ledgers, rows, or proof APIs. Those artifacts are
spare-parts evidence only.

## 1. Goal

Given a proved, result-indexed source program and explicit implementation choices, ordinary target
proof should be generated structurally. Instruction semantics, address arithmetic, descriptor
fidelity, control-flow topology, frames, ABI facts, segment composition, and routine obligation
transport belong in owner libraries. A program supplies its source proof, choices and parameters,
an unavoidable local representation relation when one genuinely exists, and the final connection
to its precious root.

The core is a proof-producing interpretation of typed source operations. It is not instructions
followed by a later attempt to reconstruct why they implement the program.

## 2. Semantic owners and disposable mechanisms

| Owner | Owns | Does not own |
|---|---|---|
| Precious root/specification package | Observable behavior, partial effects, result/failure/refusal/cancellation meaning, root-visible resource outcomes, selected progress and observable performance/security bounds | Registers, instruction schedules, provider identity, physical admission |
| Domain/API library | Operation contracts, state/resource relations, authority, capability and lifecycle meanings, conservation/discharge/persistence, implementation-independent constraints | ISA definedness, artifact identity, physical mapping |
| Proof-lowering core | Exact selected definition tree, typed derivation, coverage, structural proof transport/composition, source/target segment correspondence | Domain predicate meaning, source meaning, physical authority |
| ISA family | Result-indexed architectural action semantics and definedness; access-descriptor specialization | Source authorization, OS/provider admission |
| Platform/ISA memory model | Fundamental permitted executions and relations such as `rf`, `co`, `fr`, `po`, `sw`, `hb`, target/device relations and qualifiers | Generic lowering or high-level memory-safety ontology |
| Target/provider/platform | Physical mapping, live bindings and generations, provider/runtime results, lifecycle and failure behavior | Source meaning or policy authorization |
| ABI boundary | Exact entry/exit transport, registers, stack, clobbers, unwind and target convention | Domain lifecycle or authority semantics |
| Artifact/linker | Exact bytes, symbols, relocations, imports, selected implementation/profile identity and evidence closure | Behavioral meaning or authority |
| Whole-program refinement | Target behavior containment in the independent root and complete internal disposition | Facts absent from component certificates |

Every current lowering datatype, effect-row encoding, dictionary shape, compiler pass, ghost-world
record, obligation list, stage decomposition, and spike proof facade is disposable. Semantic owners
and directional recovery laws are not.

## 3. Independent roots and typed monadic contracts

A root is independent only if replacing the target, provider, memory-safety policy or lowering
strategy changes the refinement proof rather than the root definition. It states accepted outputs,
committed prefixes, failures, refusal, cancellation, cleanup, resource outcomes and only the
progress/performance/security claims actually required.

High-level APIs expose owner semantics through typed, result-indexed monadic contracts. An
operation contract names its logical input, precondition, possible results, postcondition per
result, events, resource transitions, retained domain duties and failure/cleanup behavior. It does
not expose target descriptors or prescribe a monad encoding. Free, Dijkstra, graded, indexed or
several composing domain monads are candidate techniques, not architecture.

The source contract is not defined by its interpreter. It admits at least two conceptually
different realizations, and its proof is usable without importing target code.

## 4. Selected proof-producing interpretation

Selection fixes an exact tree of source operations and chosen realizations, including reachable
callees, handlers, callbacks, dynamic targets, provider operations and lowering-internal actions.
The implementation universe remains open, but one proof concerns a closed selected tree and exact
artifact/profile.

Each realization rule connects one owner operation contract to:

1. an exact target segment and all possible result branches;
2. a source/target representation relation over actual pre/post states and events;
3. kernel-derived segment attributes;
4. generated owner-indexed lower obligations;
5. directional recovery of the source result and properties; and
6. exact target, ABI, memory-profile and artifact prerequisites.

An unmet implementation-specific prerequisite rejects that realization at proof time. Missing
provider/admission evidence is not a runtime event. Runtime refusal is permitted only when a
selected acquisition action has a proved refusal result admitted by the root. A realization may
not silently strengthen the public source API to make its own proof easier.

## 5. Structural laws over actual states and results

The whole-program theorem is induction over the typed lowering derivation. The design requires the
following semantic laws without freezing their Lean representation:

| Constructor | Required proof behavior |
|---|---|
| Pure | Relate the actual unchanged/logically changed state; any setup action is admitted stutter only when every branch has no source effect and cannot fault, trap, terminate or refuse |
| Bind | Use the actual intermediate source/target states and actual first result; thread committed prefixes, owner relations, retained obligations and constraints into the chosen continuation; never existentially reselect a convenient middle state |
| Branch/result | Cover every reachable result separately; success evidence cannot prove refusal, fault, cancellation or recovery branches |
| Finite loop/fold | Establish initialization, body preservation over actual iterations, exit and a fixed well-founded decrease only when termination is claimed; fallible loops preserve exact accepted prefix/first refusal |
| Reactive loop | Preserve a coinductive/domain invariant per admitted step; progress is conditional on named eligibility, capacity, fairness and environment premises |
| Call/handler | Close exact reachable implementation and indirect-target sets; connect caller/callee state, frame, ABI and return/failure/unwind branches |
| Failure/cancellation | Preserve committed effects and distinguish request, delivery, observation, masking, unwind, cleanup, terminality and failure-domain disposition |
| Async/deferred work | Extend coverage and constraint lifetime through spawned work, callbacks and post-return effects; relate enqueue, acceptance, completion, observation, return and cleanup separately |

Backward soundness is mandatory: every selected target execution is contained in an allowed source
execution. Conditional implementability is separate and optional: under explicit preconditions and
the selected profile/strategy, construct the root-required behaviors. It must distinguish existence
of one implementation, all eligible choices, and the one selected strategy; it never promises
completeness over an arbitrary source overapproximation.

## 6. Downward properties and upward owner obligations

Two proof directions meet at each rung.

- Downward demands are predicates from the root or a domain contract over the exact selected
  definitions, executions and results. Strongest mechanically derived facts flow toward leaves.
- Upward obligations are safety requirements generated by selected API, ISA, memory, target, ABI,
  provider and artifact leaves. Weakest-precondition-style requirements flow toward the owner able
  to prove, translate, delegate or retain them.

The common obligation facility is a representation-neutral routing protocol, not a universal
semantic datatype. An owner is a parameter/namespace, not a global enum. Each owner supplies a
sealed indexed requirement family and its generation and route laws. Routing evidence records:

- origin owner and exact opaque family;
- exact subject/definition/action, selected context, occurrence/segment and result;
- applicable scope, lifetime and resource/binding generations;
- selected profile/artifact identity;
- route: preserve, directional translate, named delegate/transfer, proved discharge, or explicit
  retention; and
- an optional owner-supplied fixed well-founded rank when finite discharge is promised.

The core cannot inspect predicate meaning. No constructor accepts a detached arbitrary proposition,
Boolean, unconstrained existential, empty admitted set, evaluator result or caller assertion. There
is no generic list, ledger, token rewrite or universal obligation enum. Transfer and discharge use
owner laws and total selected-tree coverage. Lower-owner safety cannot be discharged merely because
the source does not observe it; its final owner still validates it.

## 7. Machine-derived attributes and composition

Typed derivations or proved reflection generate exact owner-local attributes for selected rows,
definition/handler identity, occurrences, segments, topology, paths, footprints, frames, clobbers,
addresses, descriptors, effects, calls, result branches, provider leaves, ABI facts and artifact
connection. Mutation of code, selection, profile or artifact invalidates dependent evidence.

There is no universal attribute sum. Composition is property-specific:

- persistent prefix-closed safety such as exact `NoAlloc` or `OnlyAllocator A` composes by
  conjunction across compatible sequential segments;
- state, authority, ghost and obligation relations thread the actual intermediate state and match
  transfers;
- branches require all-reachable joins;
- loops require an invariant and, when promised, a fixed well-founded decrease;
- maximum, sum, cumulative, peak-live and lifetime bounds use different summaries;
- async properties close over pending/deferred effects for their entire scope; and
- parallel, fusion and split require owner-supplied interference, commutation or refinement laws.

Closed selected features remove irrelevant premises once. An absent memory-concurrency, allocation,
cancellation or device feature creates no per-program tax; a reachable feature brings its complete
transitive proof closure.

## 8. Universal admitted-implementation constraints

A universal constraint is a domain predicate over every implementation eligible under a named
interface/profile and every canonical environment and result branch. The final proof exhibits one
selected certified implementation. New admission or mutation requires re-proof.

For `NoAlloc`, the allocator domain fixes exact resource/effect classes and classifies direct body
and CFG actions, calls, dynamic targets, handlers, provider lazy initialization, error and cleanup
paths, unwind, callbacks, spawned/deferred work and lowering-internal helpers/spills for the full
constraint lifetime. Source syntax or a raw artifact scan is insufficient.

The taxonomy distinguishes allocator call, dynamic heap allocation, arena reservation, stack
growth, mapping, registration/metadata allocation, GPU/device allocation, physical reservation and
use of preallocated fixed storage. `OnlyAllocator A` classifies every allocation occurrence;
maximum single, cumulative, count and peak-live constraints use distinct composition laws.

Negative controls include hidden logger/error/cleanup allocation, open indirect targets, lazy
provider allocation, post-return async allocation, renamed reserve/register/grow, sample-only
absence, omitted helper/callback/spill, using absence as authority and adding an uncertified eligible
implementation. Constraints neither mint nor consume authority and prove no capacity, ownership,
physical admission or cleanup result beyond their exact predicate.

## 9. Open extensional realization contract

Reference implementations are preferential proof-producing constructors for the open realization
contract. They are not the definition of that contract. Any implementation may be selected when it
proves the same demanded semantic properties and exact target/artifact closure.

- Standard path: library construction derives routine attributes and discharges standard leaves.
- Hybrid path: standard construction derives common facts; a local theorem proves only the
  nonstandard residual.
- Novel path: a handcrafted/optimized implementation proves the same minimal extensional
  realization properties, all lower obligations, universal constraints and exact closure.

The abstract property must not embed reference bytes, exact register allocation, schedule or
algorithm unless the root truly requires it. Changing instruction topology is allowed. Changing the
source algorithm or observable contract requires a named source-level implementation/refinement
theorem before target proof; it cannot be hidden below the source.

“Property test” in the authority path means kernel theorem or proved reflection over production
semantics. Randomized/native tests are differential evidence only.

## 10. Architectural, target and artifact closure

`ArchitecturalActionDefined` covers exact result-indexed architectural actions; memory access is a
descriptor-specialized case. Every concrete access still proves architectural safety. High-level
GC/borrow/custom policy neither exempts it nor follows from it.

Platform/ISA memory consistency is an additional fundamental selected premise, not a consequence
of access definedness. The selected x86, AArch64, device or heterogeneous model owns its execution
relations. Concurrency-free selected trees discharge the premise once by irrelevance.

Source-corresponding actions prove exact operation correspondence plus domain authorization,
architectural definedness and target realization. Prologue, spill, loader, control, runtime and
cleanup actions may stutter only with selected-segment membership, architectural/target
definedness, frame/noninterference, generated-obligation accounting and no invented source
observable or authority. Fault, trap, termination, refusal or provider outcomes must be excluded or
refine an explicit source result; they are not stutter.

Target/provider admission, live binding, ABI transport and artifact identity remain orthogonal.
None is inferred from monad laws or source semantics. Exact physical evidence is an explicit sealed
owner premise.

## 11. Nonvacuity and falsifiers

Reject a design or proof when any of the following succeeds:

- the source contract is defined by the selected interpreter or is false/empty;
- a realization contains an arbitrary “sound handler” field;
- bind reselects an existential middle state or result;
- success evidence is reused on refusal/fault/cancellation;
- an internal helper, call, spill, failure, cleanup or callback escapes coverage;
- artifact identity, target success or monad law mints policy/physical authority;
- a missing admission proof becomes runtime refusal;
- ordinary straight-line instruction/frame/CFG/ABI proof needs repeated manual replay;
- a reference byte sequence, register schedule or constructor is the only eligible realization;
- a custom implementation bypasses closed-tree or obligation coverage;
- memory/device consistency is imposed on an unselected feature or omitted from a reachable one;
- a universal constraint proves only one execution or only source-level absence; or
- public source behavior is narrowed to satisfy one implementation.

## 12. Proof economy and validation boundary

For a fallback consumer far from roughly ten lines of genuinely program-specific proof per authored
assembly line, perform exactly one human specification-to-lowering feedback iteration. Decompose
burden into source semantics, reusable structural proof, semantic/domain transport, target/ABI
leaves and the irreducible local residual. Identify the proper owner and smallest candidate theorem.
Do not game the denominator by generated assembly, moved/relabelled lines, golfing or weakening the
claim. A shared implementation still requires Craig's approval and a materially different second
consumer; otherwise keep it local.

Routine selected straight-line/bounded structured programs should receive instruction semantics,
address/descriptor, frame, topology and obligation transport from libraries. Repeated manual proof
is a design failure that triggers rebuilding the boundary. Novel implementations may carry higher
burden proportional to their deviation without compatibility bias toward the reference lowering.

Proposal review authorizes only a later owner-approved experiment. An implemented interface is not
validated/frozen until two independently reviewed universal `VerifiedProgram` consumers—the
checked-access pathfinder and Spike 1—exercise it. The seven proof-architecture consumers are a
separate cross-domain pressure matrix.

## 13. Co-design skeleton: checked-access pathfinder

The pathfinder root is a tiny result-indexed read/write operation whose source contract fixes the
logical value/result and failure policy but not an address, instruction or platform mapping.

- Downward demand: exact logical access, bounds/range, permitted result and no invented effects.
- Selection: one policy authorization/representation relation, one ISA access realization, one
  target binding/profile and exact artifact.
- Derived attributes: address calculation, nonwrap/alignment, descriptor, occurrence/segment,
  frame/clobber, emitted bytes and result branch.
- Upward obligations: policy authority and generation, ISA architectural access definedness,
  selected memory consistency when applicable, target live mapping/permission, ABI and artifact
  connection.
- Residual: only the policy-owned relation from the logical location/value to the selected binding.
- Falsifiers: stale generation, raw integer provenance, wrong result branch, caller-minted grant,
  artifact mismatch, hidden helper access, access-safe but unauthorized target action.

The experiment must demonstrate that a standard access derives routine proof automatically and a
different policy or ISA realization changes owner leaves without changing the root.

## 14. Co-design skeleton: Spike 1

Spike 1's independent root is the exact hello-world logical output and selected termination/failure
semantics across Linux, Windows, Wasm and bare-metal profiles. The API operation is a result-indexed
write followed by a selected terminal operation; partial writes, refusal/failure and cleanup are
explicit where the profile admits them.

- Downward demand: literal bytes/event, result branches, committed prefix and terminal meaning.
- Selection: literal representation, provider/write strategy, retry/refusal policy, ABI/syscall or
  host-call path, termination strategy, target/profile and artifact.
- Derived attributes: literal layout, buffer read footprint, block/loop topology, call/ABI frame,
  provider result decoding, terminal segment and artifact links.
- Upward obligations: buffer provenance/authority, access definedness, provider admission, ABI,
  imports/linkage, lifecycle and exact terminal disposition.
- Composition: bind uses the actual write result and committed prefix to select retry, failure or
  termination; setup is stutter only on no-fault branches.
- Universal constraints: selected no-allocation/no-hidden-call properties include provider setup,
  failure and cleanup paths when demanded.
- Residual: the literal/source-event relation and chosen root result mapping; target leaf facts are
  reusable.
- Falsifiers: successful-write proof reused for short/failure result, hidden formatter allocation,
  termination treated as ordinary return, target success inferred from source, wrong literal or
  artifact/import closure.

Only after this and the pathfinder independently close universal `VerifiedProgram` roots may a
concrete core interface be proposed for freezing.

## 15. Historical and documentation disposition

`OBLIGATION_LOWERING_DESIGN.md`, its review commits, the earlier proposed proof architecture and all
current proof facades are historical evidence. They do not authorize compatibility work. This
document is the candidate core design; `MEMORY_MODEL_PRESERVATION_INVENTORY.md` is an independent
pass-one baseline; `PROPOSED_PROOF_ARCHITECTURE.md` pressure-tests all seven consumers.

`MEMORY_MODEL.md` remains authoritative for platform/ISA memory, provenance, synchronization,
lifecycle, device, trace, validation, reference and gate semantics until a second-pass mapping and
independent acceptance recover every applicable clause. No extraction, downgrade or replacement is
implied here.

## 16. Acceptance order

1. Accept this semantic boundary and the pass-one memory inventory as documentation only.
2. Accept the seven-consumer pressure test and unresolved owner-choice register.
3. Owner-authorize a minimal pathfinder/Spike-1 experiment; implement no broader framework.
4. Review two universal roots and mutation controls independently.
5. Only then propose a concrete interface and atomic surrounding-document reconciliation.
6. Implementation, migration and integration require separate authorization.
