# Composable Boundary ABI Contexts

**Status (2026-08-29): reviewed design; enforcement incomplete.** `Gasm.Core.AbiContext` contains
placement-free requirement vocabulary, proof-indexed single-binding establishment, target-indexed
physical footprints, and a proposition-level resolved-boundary compatibility shape. It does **not**
yet implement heterogeneous rows, target argument classification, TLS/table/register lowering,
scope obligations, cancellation, adapters, or the whole-program connection theorem. None of its
current declarations is sufficient to construct or emit a `VerifiedProgram`.

This document owns context requirements at call boundaries. [The memory and concurrency model](MEMORY_MODEL.md)
owns authority, borrowing, atomic visibility, task/thread lifecycle, cancellation state, and
cross-worker transfer. Target documents own machine calling conventions and physical realization.
Library documents own their logical resource protocols.

## 1. Decision

Keep three concepts separate:

1. A **machine calling convention** classifies the complete function signature and assigns domain
   arguments, hidden arguments, results, saved state, stack layout, unwind behavior, and entry rules.
2. A **logical context contract** describes the resources a boundary requires, observes, mutates,
   consumes, or provides. It is independent of OS, ISA, and physical placement.
3. A **target realization** maps one fully classified boundary—including its logical context—to
   physical locations and proves that the complete physical footprints do not interfere.

The earlier design embedded placement in published requirements and compared abstract placements.
That composition rule is rejected. An abstract argument index, register name, TLS slot, or table
index is not a physical location and cannot establish non-interference.

## 2. Machine conventions remain per boundary

System V AMD64, Microsoft x64, AAPCS64, Wasm function types, syscalls, callbacks, signals, and
interrupts are different conventions or entry environments. The same ISA and OS may use several.
Interior library ABIs remain selectable independently of the process OS.

Signature classification happens before context placement. It includes by-value aggregate
classification, hidden result pointers, variadic register duplication/state, shadow space, stack
probing, red-zone availability, homogeneous aggregates, and unwind requirements. A context cannot
reserve `explicitArgument 5` and later assume that it means a stable register or stack slot.

Async entry is explicit. An ordinary call, callback, signal, and interrupt may have different saved
state, stack guarantees, permissible runtime services, and root contexts. A signal-safe subset is a
separate contract, not an ordinary-call row reused implicitly.

## 3. Placement-free logical contracts

A published logical requirement contains no register, argument number, TLS index, or Wasm table
index. Its identity includes Lean types for the resource and protocol; strings may be emitted as
diagnostic names but never confer compatibility or authority.

Each requirement declares these independent dimensions:

| Dimension | Initial vocabulary |
| --- | --- |
| Materiality | erased ghost, runtime |
| Access | observe, mutate, consume, provide |
| Extent | call, lexical, request, task, thread, process, object |
| Propagation | borrow, copy, move, inherit, do not propagate |
| Scheduling | pinned, migratable |
| Teardown | normal return, failure, cancellation, executor destruction, callback |

Extent is not storage. A task-scoped binding may currently be stored in thread-local storage only
when the task is pinned; a migratable task requires task/fiber-local storage or an explicit handle.
Windows TLS and FLS are therefore distinct realizations. Allocation of either storage mechanism is
fallible and belongs to the boundary outcome model.

Logical composition combines requirements by exact typed identity and protocol. It must eventually
produce a normalized heterogeneous row with an internal well-formedness proof. Composition with an
empty row may not make an internally conflicting row valid. Associativity and commutativity are
goals for this placement-free normalization and require Lean theorems; they are not claims about
adapter selection or physical code layout.

## 4. Establishment and satisfaction

A binding is usable only with proof that a modeled boundary transition established that exact
requirement and that its invariant holds in the resulting state. Public string records are not
provenance. Matching names, representations, or addresses never manufactures authority.

The proof shape is indexed by the complete requirement:

```text
requirement.establishes protocol before value after
requirement.valid protocol after value
----------------------------------------------------
EstablishedContextBinding requirement protocol before after
```

Because the requirement itself is an index, its resource representation, protocol, access mode,
extent, propagation, scheduling, and cleanup policy cannot be discarded by a later equality test.
The predicates must ultimately connect to the authority and obligation transitions in
`MEMORY_MODEL.md`; a trivially weak requirement proves only its own weak contract and cannot satisfy
a stronger typed requirement.

The eventual call rule consumes a normalized logical row of these bindings. No such row-level rule
is implemented today. The old `AbiContextCallable` string-equality witness has been deleted.

## 5. Target realization

A target realization receives all of the following together:

- the target architecture and execution environment;
- the selected convention and entry kind;
- the complete domain/result signature after target classification;
- the normalized logical context row;
- the address-space, TLS/FLS namespace, table/module instance, and allocation generations;
- setup, access, preservation, teardown, and unwind implementations.

It resolves these into target-owned physical locations. A physical location is typed by the target
and has a proved alias/overlap relation. It is not a string. Examples that must overlap include
x86-64 `rax`/`eax` and AArch64 `x19`/`w19`; examples that must remain distinct include slot zero in
different Wasm table instances or different TLS allocation generations.

The convention realization includes ordinary and hidden arguments. Thus Microsoft x64 argument
zero versus `rcx`, SysV argument five versus `r9`, variadic FP duplication, and signature-dependent
aggregate shifts are checked in one physical allocation problem.

## 6. Resolved footprints and conflicts

Every realized component publishes a physical footprint of reads, writes, and clobbers. The
convention footprint covers domain arguments, hidden parameters, results, saved/clobbered state,
stack/unwind machinery, and entry-environment effects. Each context footprint covers its setup,
lookup/access sequence, body preservation rule, teardown, and unwind path.

This captures interactions that constructor equality misses:

- a general-dynamic TLS lookup may call `__tls_get_addr` and clobber caller-saved registers;
- a library's private scratch register or TLS cell may collide with another component;
- a syscall adapter may clobber registers not clobbered by an ordinary function call;
- stack probing and unwind helpers have footprints even when the logical resource is disjoint.

Two physical accesses conflict when their target locations overlap and they are not both reads.
A resolved boundary carries proofs that:

1. every context footprint is compatible with the complete convention footprint;
2. context footprints are pairwise compatible;
3. the lowering really performs only accesses within the published footprints;
4. setup and teardown establish and restore the logical bindings they claim.

`Gasm.Core.AbiContext.RealizedBoundary` currently represents only the first two proposition-level
shapes. No target constructs one yet, and it is not wired to callability or emission. There is no
Boolean `firstConflict`; the rejected pairwise abstract-placement gate has been deleted.

## 7. Finite allocation and request accounting

Allocation, TLS/FLS allocation, table growth, and linear-memory growth are finite capabilities.
Their interfaces return explicit failure. No proof may assume that every finite request succeeds.
A caller specifies the meaning of exhaustion at its boundary.

A request allocation contract combines:

- a runtime allocator or growth handle whose authority comes from the memory model;
- finite peak-live and/or cumulative allocation limits;
- a ledger of live, peak-live, and cumulative bytes;
- typed provenance associating allocations and releases with the active scope;
- cleanup transitions for every declared exit.

Each successful allocation is charged before its result becomes usable. Release decreases live
bytes but not cumulative bytes. Charging arithmetic is non-wrapping, and no scoped allocation path
may bypass the ledger. Exhaustion is an explicit request outcome, so a server may clean up and fail
one request without terminating the process.

The logical allocator requirement is placement-free. A native realization may pass an explicit
handle, use a proved TLS/FLS lookup, or reserve an interior-ABI register. Wasm may use an explicit
parameter or instance-qualified capability table. These are different physical realizations of the
same logical resource.

A non-request path may require only the process allocator and omit the request ledger. The eventual
erasure/lowering theorem must prove that omitting accounting produces no request-entry or per-
allocation accounting instructions. This theorem is not implemented yet.

## 8. Scoped cleanup and cancellation

Scope entry and exit belong to the indexed authority/obligation transition system. Entry creates a
fresh scope generation and a `MustRestore`/`MustLeave`-shaped obligation. Exit requires the current
top generation and consumes it exactly once. Copying a scope witness, restoring it twice, restoring
an outer scope before an inner scope, or applying it to unrelated state must be unrepresentable.

The earlier copyable `AbiTlsScope` function model did not establish these properties and has been
deleted. Normal return, failure, cancellation, and unwind adapters must consume the same typed
cleanup obligation.

Cancellation state is owned by [the memory and concurrency model](MEMORY_MODEL.md), not this ABI
document. The required resource has a generative identity, caller-held signal authority, callee-held
read authority, monotonic state, atomic visibility, scheduler/blocking-operation integration, and
typed cleanup transitions. ABI context composition only passes or realizes an observation handle.
An immutable `active | cancelled` snapshot cannot model a later concurrent request and has been
deleted.

A cancellable logical contract declares safe points, permitted effect prefixes, cleanup behavior,
and a latency/progress condition such as one poll per bounded iteration or input chunk. Cancellation
is not an asynchronous jump into arbitrary instructions. A function omitting the cancellation
requirement contains no polling work; a caller cannot claim prompt cancellation while it executes.

## 9. Adapters and composition

Logical row normalization is separate from target realization. A verified adapter is an explicit
morphism between typed protocols or physical realizations. It declares its own footprint and proves:

1. source binding and protocol requirements;
2. destination establishment and validity;
3. preservation of unrelated logical resources;
4. translation of every success, failure, exhaustion, and cancellation outcome;
5. discharge of all scope and cleanup obligations;
6. physical-footprint compatibility after insertion.

Adapter search or selection may be order-dependent. Therefore no associativity/commutativity claim
is made for synthesized adapter plans. Coherence, if desired, requires a theorem that competing
plans are observationally equivalent.

## 10. Protocol evolution and linking

Changing a protocol creates a new Lean protocol identity. It cannot silently reuse a string key.
Old and new code compose only through an explicit refinement or adapter that proves validity and
outcome preservation. `ContextProtocolRefinement` records the minimum pure preservation shape;
stateful boundary refinement remains to be implemented.

External artifacts eventually need checked type/protocol fingerprints. Such a fingerprint is an
index for linker diagnostics, not proof by itself. The linker must connect it to a compiled,
kernel-checked theorem for the exact representation and protocol. Unknown versions, fingerprint
collisions, or missing refinement evidence fail closed.

## 11. Whole-program obligations

Before ABI contexts may participate in `VerifiedProgram`, the implementation must prove:

- typed row well-formedness, normalization, identity, associativity, and commutativity;
- exact establishment and satisfaction for every reachable direct and indirect call;
- full-signature target classification and physical placement correctness;
- alias-aware footprint compatibility, including setup/teardown/helper clobbers;
- footprint fidelity of emitted code;
- preservation of every logical and physical resource outside the declared frame;
- linear scoped cleanup on all outcomes and unwind paths;
- finite-resource success/failure totality and allocation-accounting completeness;
- cancellation authority, visibility, safe-point, effect-prefix, and cleanup properties through the
  memory/concurrency model;
- explicit protocol-refinement and adapter soundness;
- ghost erasure and zero runtime work for omitted runtime requirements;
- correct root-context establishment for ordinary, callback, signal, and interrupt entry kinds.

`VerifiedProgram` must carry these universal connection proofs for every admitted initial state and
environment behavior. No legacy constructor, compatibility escape hatch, allowlist, axiom, `sorry`,
or narrowed input domain may bypass them.

## 12. Current implementation boundary

Implemented in `Gasm.Core.AbiContext`:

- placement-free lifecycle/access vocabulary;
- requirements indexed by resource, protocol, key, and state types;
- proof-bearing establishment for one exact requirement;
- a pure protocol-refinement preservation shape;
- target-indexed physical locations and alias relation;
- physical read/write/clobber footprints and proposition-level compatibility;
- a resolved-boundary record requiring convention/context and pairwise context compatibility.

Not implemented:

- heterogeneous logical rows and their algebra;
- integration with `AbiDiscipline`, full signature classification, or any target `ABI.lean`;
- concrete TLS/FLS/register/argument/table realizations;
- footprint-fidelity proofs;
- indexed scope obligations;
- concurrency-model cancellation resources;
- verified adapters;
- integration with `Callable`, `VerifiedProgram`, linking, or emission.
