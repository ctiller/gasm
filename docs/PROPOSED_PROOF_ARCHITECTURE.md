# Proposed proof architecture: seven-consumer pressure test

**Status:** design dossier set against `PROOF_LOWERING_CORE_DESIGN.md`. It authorizes no Lean,
public interface, migration or integration. Existing code is evidence, not proof that the proposed
edge already exists.

The seven consumers are Spikes 1–5, the graphics cube and the multithreading example. Checked
access is an additional pathfinder described in the core design; it is not one of the seven.

## 1. Common dossier rule

Every consumer must independently identify:

1. its precious root and unresolved owner choices;
2. source/specification-package proofs versus lowering delta;
3. high-level monadic operations and every result branch;
4. the exact selected implementation/call/handler/provider tree;
5. stage-by-stage target segments and artifacts;
6. machine-derived attributes at each rung;
7. bottom-up API/ISA/memory/target/ABI/provider/artifact obligations and their routes;
8. relational domain/ghost transfer;
9. failure, refusal, cancellation, partial effects, cleanup and progress;
10. standard versus hybrid/novel realization admission;
11. universal constraints and deceptive counterexamples;
12. irreducible program residual and expected proof-economy path;
13. exact current evidence versus required/hypothetical work; and
14. falsifiers and atomic cutover.

The root is independent of target code. A selected implementation tree is closed even though the
eligible implementation universe is open. “Machine-derived” means kernel construction or proved
reflection over production semantics, never caller metadata or a native test.

Unless a dossier states a different route, source/domain preconditions are discharged by the
source proof plus its exact representation relation; ISA, memory, target/provider, ABI and artifact
requirements are discharged by their sealed owner libraries; a cross-rung translation supplies a
directional recovery theorem; and cleanup, transfer or partial-effect duties remain explicitly
retained in the actual result continuation until their named owner closes them. No obligation is
discharged by root unobservability.

Default cutover is whole-spike atomic: the rebuilt universal `VerifiedProgram`, public emitter and
imports replace the old path together. A target-indexed canonical authority layer may land first
only when independently proved unique and unreachable from the old authority path.

## 2. Spike 1 — hello world

### Root and choices

The precious root is exact logical output plus selected partial-write, failure and terminal behavior
for Linux, Windows, Wasm and bare-metal profiles. Unresolved choices are whether each profile retries
short writes, exposes the committed prefix, how provider refusal/failure maps to the root, and which
terminal action is selected. The literal, not a target buffer address, is source meaning.

### Source package and monadic operations

The source package proves literal bytes/logical output-event correspondence. Its operations are
result-indexed `write bytes` and `terminate result`; selected profiles may expose accepted prefix,
short write, refusal/error and terminal/failure branches. Cleanup is explicit when the provider or
runtime acquires a resource.

### Selected tree and lowering stages

1. Source literal/write/terminate tree.
2. Selected write strategy: direct provider call, syscall/host call, bounded retry or bare-metal
   device loop.
3. Literal layout and buffer representation.
4. Exact call/syscall/device segments, result decoder and terminal segment.
5. ABI/import/link/artifact and selected target/profile closure.

Standard lowerings derive the literal layout, buffer footprint, address/range, frames, clobbers,
call topology, provider-result split and terminal connection. A novel direct-device implementation
is eligible by proving the same output/result contract and target-local device sequence properties.

### Attributes, obligations and relation

Derived attributes include exact literal bytes, segment/occurrence keys, buffer reads, descriptors,
control paths, call frames, imports and artifact bytes. Bottom-up obligations cover buffer
provenance/authority, architectural reads, provider admission/results, ABI, device order where
selected, lifecycle and terminal disposition. The local relation connects the logical literal/event
and committed prefix to the target buffer/provider state; target facts do not mint it.

Bind uses the actual write result: success, short prefix, refusal and fault choose different
continuations. Setup/prologue may stutter only on admitted no-fault branches. Termination is never
ordinary stutter.

### Constraints, economy, evidence and falsifiers

`NoAlloc` or `OnlyAllocator` covers provider initialization, error formatting, cleanup and deferred
callbacks as well as source-visible code. Hidden allocation, a success proof reused for short write,
wrong literal, target success inferred from the source, missing import, terminal-as-return, stale
artifact and unaccounted helper access are falsifiers.

Expected residual: literal/event relation and chosen root result mapping. Instruction, frame, ABI and
provider leaves are library-owned. Current evidence exists under `Spikes/Spike1Hello/` for multiple
targets, but the rebuilt typed interpretation and universal root closure are required. Cut over the
whole spike atomically.

## 3. Spike 2 — Fibonacci rows

### Root and unresolved outcomes

Commit `3b22faf6` is accepted source mathematics for recurrence, decimal schedule and row payload,
but it is not a complete precious root until output refusal, terminal result and cleanup are chosen.
Three legitimate roots remain:

- all 90 rows must be accepted or the program returns a failure carrying the exact committed
  prefix;
- emit the maximal accepted prefix and return success-with-prefix/refusal status; or
- require an infallible selected sink under an explicit environment premise.

Recommendation: choose all rows or first-refusal with the exact committed prefix and a distinct
terminal result. It exercises fallible composition without pretending the provider is infallible.

### Source package and monadic operations

The source package owns Fibonacci recurrence, decimal correctness, row construction, 90-step bound,
accepted-prefix meaning and refusal/terminal contract. Operations are `formatRow`, result-indexed
`emitRow`, bounded iteration and `terminate`; cleanup is explicit for any acquired output resource.

### Selected tree and lowering stages

1. Proven recurrence/decimal/row source schedule.
2. One selected row implementation: literal/sign/digit blocks and provider accept/refuse result.
3. Bounded 90-iteration plan with exact loop state.
4. Target decimal/block/frame certificates and provider/ABI leaves.
5. Accepted-prefix/first-refusal exit and terminal artifact.

### Attributes, obligations and relation

Machine-derived row attributes are exact block sequence, zero/one/many segment shape, topology,
frame/clobber, digit buffer ranges, provider occurrence/results and artifact identity. A bounded,
fallible iteration combinator lifts one proved row segment across the selected plan using the actual
row ghost and provider result. It derives the exact accepted prefix or first refusal and untouched
tail.

Bottom-up obligations cover arithmetic instruction/flag facts, buffer access, ABI/provider
admission, per-result retained output duties, terminal action and artifact link. The local relation
is only the source row/decimal schedule to selected row ghost and final root consequence.

### Constraints, economy, evidence and falsifiers

`NoAlloc`, bounded stack or `OnlyAllocator` constraints cover formatter/provider/error/terminal
paths and every loop iteration. A novel SIMD formatter or fused multirow write is admissible if it
proves the same row/prefix/refusal contract and exact target closure; changing output grouping is
not source-visible unless the root observes call boundaries.

Expected residual is one row relation plus root choice. Replaying 90 iterations, individual
instruction frames or decimal schedules manually is a design failure. Existing evidence includes
`Spikes/Rebuilt/Spike2Fibonacci/Spec.lean`, `Spikes/Spike2Fibonacci/` and the accepted source commit;
the proof-producing selected interpretation remains required.

Falsifiers: total-success theorem under a fallible provider, refusal dropping committed bytes,
existentially reselected loop state, output cleanup lost on refusal, generated assembly used as the
proof denominator, reference row schedule made the only implementation, or terminal result left
undefined. Atomic cutover follows root choice and universal VP closure.

## 4. Spike 3 — arbitrary finite byte-line sort

### Root and unresolved choices

The root sorts an arbitrary finite byte stream into lines with explicit stability policy, preserves
the chosen line/terminator semantics and emits an exact byte prefix under fallible output. It must
state whether equal keys are stable or unstable, how a final unterminated record is represented,
what preparation may fail, whether output retries, and how allocation/input/output resources are
cleaned on every result.

Recommended baseline: stable sort; final unterminated bytes form a final record; preparation failure
commits no output but returns exact input/allocation disposition; output uses an accepted-prefix or
first-refusal contract with no rollback; cleanup is attempted and its failure remains distinct.

### Source package and monadic operations

Source proofs own byte-stream ingestion, delimiter/final-record interpretation, stable permutation,
sortedness, exact serialized output and committed-prefix/refusal meaning. Monadic operations cover
read chunks/results, allocate/grow, parse/finalize, sort, write prefix/results and cleanup.

### Selected tree and lowering stages

1. Read binder and chunk/result interpretation.
2. Selected storage/allocator and descriptor/line-view representation.
3. Parse/final-record preparation.
4. Stable sorting implementation and representation proof.
5. Fallible serialized output loop.
6. Cleanup and terminal result.
7. Target/provider/ABI/artifact closure per Linux/Windows/Wasm profile.

### Attributes, obligations and relation

Derived attributes cover chunk binding, allocation occurrences, view/slot preservation, footprints,
sort-call tree, output segments, result paths, cleanup paths and artifact/import identity. Bottom-up
obligations include live generations, bounds/provenance, allocator/provider results, view/loan
destruction, ABI, target admission and terminal disposition. Domain relations transport raw buffer,
prepared records, views, sorted permutation, output prefix and live cleanup duties without a global
ghost world.

### Constraints, economy, evidence and falsifiers

Universal constraints distinguish heap allocation, stack growth, arena reserve and provider lazy
allocation. A deceptive allocator call in error logging, final-record handling or cleanup must fail
`NoAlloc`. Stable and unstable implementations are not interchangeable. A novel in-place sorter is
eligible only with the same stable root or a source-level theorem selecting a different root.

Expected residual: ingestion/record representation relation, selected sort representation theorem
and root result mapping. Current evidence is distributed across `Spikes/Spike3SortLines/` and
`docs/SPIKES/SPIKE3_SORT_LINES.md`; exact §§4.2, 5, 5.1 and 6 resource/refusal/terminal connections
remain design inputs, not universal closure.

Falsifiers: dropping the unterminated record, treating preparation failure as empty success,
unstable sort under stable root, byte-prefix refusal upgraded to record-only prefix, retry duplicating
bytes, cleanup erased by terminal failure, stored address bytes minting views, or target success
standing in for allocation authority. Cut over all phases together.

## 5. Spike 4 — reactive HTTP server

### Root and choices

The root describes an admitted sequence of request/response interactions, parser limits, exact
uncommitted/committed response prefixes, policy rejection, overload/backpressure, cancellation,
connection/request scope and cleanup. HTTP `414` policy rejection is distinct from allocation or
provider admission failure. Unresolved choices include keep-alive/pipelining subset, concurrency,
buffering, cancellation and send-retry policy.

### Source package and monadic operations

Source proofs own request-line parsing, method dispatch and response serialization. Monadic
operations are accept/read/parse/dispatch/write/close plus capacity grant, cancellation observation
and cleanup, each with explicit partial/failure results. Reactive progress depends on admitted
arrivals, capacity, fairness and peer behavior.

### Selected tree and lowering stages

1. Listener/connection admission and capacity policy.
2. Read chunks and parser state.
3. Request-line result: incomplete, complete, policy rejection or malformed.
4. Method/response construction.
5. Fallible send with committed prefix.
6. Request-buffer release, transferred request/connection duties and close/cleanup.
7. Scheduler/provider/ABI/target/artifact closure.

### Attributes, obligations and relation

Derived attributes close callbacks/dynamic dispatch, parser and buffer footprints, capacity events,
send segments and cleanup/async continuations. Bottom-up duties cover socket/handle generations,
buffer authority, allocator/capacity, provider results, cancellation registration, pending sends,
close and lifecycle. Relations remain domain-owned for parser, request, connection and output states.

### Constraints, economy, evidence and falsifiers

`NoAlloc` must include error responses, logging, TLS/runtime/provider lazy setup and post-return work.
`MaxPeakLiveBytes` composes across concurrent live requests, not per request by conjunction. A custom
zero-copy or fused parser is eligible with the same root and exact resource/async closure.

Expected residual: parser/request/response relation and selected server policy. Current evidence is
under `Spikes/Spike4HttpServer/` and `docs/SPIKES/SPIKE4_HTTP_SERVER.md`; reactive whole-program
closure is required.

Falsifiers: closing request/connection scope at parser completion, conflating `414` with overload,
rollback after committed send, cancellation as cleanup/visibility, unbounded arrivals used for
unconditional liveness, hidden callback/provider allocation or a dynamic handler outside the sealed
tree. Atomic cutover includes runtime, emitter and root.

## 6. Spike 5 — streaming gzip/gunzip

### Root and choices

The root relates an input byte stream to gzip/gunzip results, format errors, exact committed output
prefix, stream finalization, checksum/trailer behavior, resource cleanup and selected progress.
Choices include compression level/algorithm, buffering, concatenated-member policy, truncated input,
provider retry and allocation strategy.

### Source package and monadic operations

Source proofs own codec/format/checksum semantics and round-trip claims within the selected profile.
Operations read chunks, allocate/init codec state, step with input/output consumption counts,
finish/fail, write output and release resources. Every step is result-indexed for needs-input,
needs-output, produced prefix, stream-end and format/provider failure.

### Selected tree and lowering stages

1. Input binder/chunk acquisition.
2. Selected codec implementation and state representation.
3. Fallible streaming step loop with exact consumed/produced counts.
4. Output provider and committed-prefix loop.
5. Finish/trailer/checksum and cleanup.
6. Platform library/custom target, ABI and artifact closure.

### Attributes, obligations and relation

Derived attributes include buffer ranges, nonoverlap/alias policy, step result paths, loop progress
measure/invariant, provider calls, cleanup and exact library/artifact identity. Bottom-up obligations
cover codec state lifetime, buffer authority, allocation, target calls, provider admission, ABI,
cleanup and result decoding. The domain relation connects logical codec state to the selected native
or verified representation and threads actual consumption/production.

### Constraints, economy, evidence and falsifiers

Bounds distinguish peak codec state, output buffers and cumulative allocation. `NoAlloc` covers
lazy library initialization and failure cleanup. A different codec implementation is eligible with
the same format contract; an algorithm with observably different format/profile needs a source
implementation theorem.

Expected residual: codec representation relation and root output/result mapping. Current evidence
is under `Spikes/Spike5Gzip/` and `docs/SPIKES/SPIKE5_GZIP.md`; native/Wasm files do not establish
universal selected-tree closure.

Falsifiers: finish omitted, format error treated as EOF, consumed/produced counts reselected,
committed output rolled back, cleanup assumed from process exit, library call admitted by artifact
name alone, hidden allocation or one native round-trip test used as proof. Atomic cutover includes
codec/provider/artifact path.

## 7. Graphics cube — persistent CPU/GPU/WSI composition

### Root and choices

The root is a persistent presentation interaction: selected frames/cube state lead to specified
rendering/presentation observations under explicit device/surface-loss, resize, acquisition,
submission and teardown results. Acceptance, queue completion, fence/semaphore signal, image
availability, presentation acceptance and display visibility are distinct. Choices include API,
queue/device profile, shader, memory strategy, frame count and recovery policy.

### Source package and monadic operations

Source proofs own cube geometry/transforms and logical frame/presentation relation. Operations cover
instance/device/surface creation, resource allocation/binding, shader/pipeline setup, acquire,
record/submit/present, wait/recycle, resize/loss and cleanup with exact result branches.

### Selected tree and lowering stages

1. Logical frame/cube state.
2. Selected graphics API/profile and resource graph.
3. Shader/SPIR-V construction and validation.
4. Host/device memory binding, command recording and submission.
5. Synchronization/presentation loop and failure recovery.
6. Provider/loader/ABI/artifact and device-loss cleanup.

### Attributes, obligations and relation

Derived attributes close descriptor/resource identities, binding generations, command/shader
artifacts, queue scopes, submission paths, callbacks and teardown. Bottom-up duties cover device
admission, memory properties, host/device visibility, layout/ownership, semaphore/fence/image
lifecycle, provider results and exact SPIR-V/native artifacts. Relations are graphics-domain-owned;
CPU `sw` cannot replace Vulkan/SPIR-V/WSI relations.

### Constraints, economy, evidence and falsifiers

Universal constraints include device/host allocation kinds, no hidden provider allocation only when
the selected profile can prove it, bounded in-flight frames and async lifetime closure. A novel
shader/pipeline is eligible extensionally; a different visible image contract needs a source theorem.

Expected residual: cube-to-shader/resource relation and selected presentation observation mapping.
Current evidence is under `Spikes/GraphicsFoundation/`, `docs/GRAPHICS_FOUNDATION.md` and
`docs/GRAPHICS_ARCHITECTURE.md`; it is not yet a universal VP dossier closure.

Falsifiers: submission equals completion, present acceptance equals visibility, CPU fence equals
device flush, descriptor bytes mint binding authority, device-loss erases resources, shader test
output replaces formal semantics, or callback/loader actions escape the tree. Cut over the complete
graphics artifact/runtime path atomically.

## 8. Multithreading example / proposed Spike 8

### Root and choices

The root is a selected concurrent computation and exact observable result with explicit thread
lifecycle, lock/wait results, failure disposition and claimed progress. It does not assume one global
schedule, TSO, wake visibility or forced-termination cleanup. Choices include x86/AArch64,
Linux/Windows/bare metal, mutex implementation, wait adapter, fairness and async surface.

### Source package and monadic operations

Source proofs own the logical shared invariant and final counter/result. Operations spawn/donate,
acquire with result, update, release, park/wake, join/detach and root termination. Each carries
healthy/not-acquired/recovery/not-recoverable where selected and exact lifecycle results.

### Selected tree and lowering stages

1. Thread partition, authority and invariant.
2. Selected portable mutex contract and implementation.
3. x86 or AArch64 action/memory realization.
4. Linux futex, Windows address wait or bare-metal wait strategy.
5. Native lifecycle/ABI/boundary/artifact.
6. Concurrent trace/root result and validation matrix.

### Attributes, obligations and relation

Derived attributes include per-thread segments, exact action/event keys, descriptors, frames,
lock-result branches, wait registrations, lifecycle transitions and artifact identities. Bottom-up
duties include provenance/access modes, architecture consistency, synchronization witnesses,
guard/release/withdrawal/join duties, wait lifetime, provider/ABI and root disposition. Relations
separate logical thread from execution agent and preserve x86 buffers/AArch64 monitors in their
owners.

### Constraints, economy, evidence and falsifiers

No-allocation/no-blocking/async-safe constraints are profile-specific and cover every reachable
library/provider path. A different mutex is eligible through the extensional contract and exact
topology/progress proof; CPU mutex evidence grants nothing to shader/device agents.

Expected residual: program invariant and final counter/root mapping. ISA, mutex, wait/lifecycle,
memory relation and artifact leaves are libraries. Current design evidence is in
`docs/SPIKES/SPIKE8_MULTITHREADING.md` and `docs/MEMORY_MODEL.md`; the complete implementation is
staged/gated rather than current.

Falsifiers: wake as visibility, failed acquire as guard, scheduler nondeterminism replaced by one
trace, timeout/cancel as progress, store buffer migrated with thread, forced termination as unlock,
platform result count fabricated, or x86 proof reused on AArch64. Atomic cutover follows selected
M-stage/profile closure.

## 9. Cross-consumer matrix

| Pressure | S1 | S2 | S3 | S4 | S5 | Graphics | Multi |
|---|---:|---:|---:|---:|---:|---:|---:|
| Fallible committed prefix | yes | yes | yes | yes | yes | profile | no |
| Persistent/reactive lifetime | no | no | bounded phases | yes | streaming | yes | concurrent |
| Allocation/resource lifecycle | small | optional | central | central | central | GPU/device | guards/threads |
| Async/deferred closure | provider | no | cleanup/provider | central | provider | central | scheduler/interrupt |
| Platform/ISA memory model | access only | access only | access only | selected | selected | heterogeneous | fundamental |
| Novel implementation pressure | device output | formatter/fusion | sorter/storage | parser/server | codec | shader/pipeline | mutex/wait |
| Universal constraint falsifier | provider setup | formatter error | cleanup logger | callback/TLS | lazy codec | driver/provider | async library |

No single consumer may define the shared abstraction. Spike 2 tests bounded fallible lifting; Spike 3
tests phase/resource transfer; Spike 4 and graphics test async lifetime; multithreading tests native
memory and lifecycle ownership. A candidate common theorem must state the exact responsibility
shared by at least two materially different immediate consumers.

## 10. Proof-economy audit

For each consumer, one human feedback iteration records:

- source/specification burden excluded from lowering;
- reusable structural/semantic/transport/target facts already owned;
- exact missing owner delta;
- irreducible program relation/root closure; and
- smallest candidate theorem plus a materially different second consumer.

The exercise is a smell test only. It creates no CI ratio, waiver, counter or implementation
machinery. Manual replay of ordinary instruction/frame/CFG/ABI proof is itself evidence that the
design boundary is wrong; higher burden for a genuinely novel implementation is acceptable.

## 11. Decision register

| Decision | Current proposal | Owner status |
|---|---|---|
| Core direction | Property-directed monadic proof-producing interpretation with downward demands and upward sealed-owner routing | Proposed, not implemented |
| Obligation commonality | Representation-neutral routing protocol only; semantic family/lifecycle stays owner-local | Proposed, encoding disposable |
| Implementation admission | Open extensional contract; reference constructors preferred but not privileged | Proposed |
| Universal constraints | Interface-wide certified closure plus exact selected implementation | Proposed; deceptive controls mandatory |
| Spike 1 root | Exact output plus selected partial/failure/terminal profile | Owner must pin per profile before experiment |
| Spike 2 root | Recommend all rows or first refusal with exact committed prefix and distinct terminal result | Craig decision required |
| Spike 3 root | Recommend stable, final unterminated record, explicit preparation/output/cleanup results | Craig decision required |
| S4/S5/graphics/multi profiles | Narrow explicit first profiles, no completeness claim | Owner decisions required before implementation |
| Cutover | Whole-spike atomic by default | Accepted design rule; exception needs unique canonical authority theorem |
| Interface validation | Pathfinder plus Spike 1 universal VP roots before freeze | Proposed review gate, not implementation authority |

## 12. Validation and cutover gates

Any later implementation proposal must run at least:

- `python scripts/check_gates.py`;
- `lake exe check_gates_axioms`;
- focused rebuilt universal `VerifiedProgram` roots for the selected consumer/profile;
- public emitter and import resolution checks against the selected artifact; and
- a reachability audit proving no old declaration/authority path remains reachable from the public
  root.

Native, model and mutation validation supplements kernel proof. It never replaces source
independence, owner obligation discharge, architecture consistency, target admission or artifact
connection. Integration requires a separate exact-hash review and atomic cutover authorization.
