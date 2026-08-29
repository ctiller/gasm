# Composable Boundary ABI Contexts

**Status (2026-08-29): reviewed staging design; enforcement incomplete.**
`Gasm.Core.AbiContext` contains nominal, placement-free, argument/result/outcome-dependent context
contracts; explicit required and emitted obligation projections; stateful contract refinement; and a
target/environment realization interface. It does **not** implement heterogeneous rows, target
argument classification, concrete physical execution profiles, adapters, or the whole-program
connection theorem. None of its declarations is sufficient to construct or emit a
`VerifiedProgram`.

This document owns logical context requirements at call boundaries and their realization by calling
mechanisms. [The memory and concurrency model](MEMORY_MODEL.md) owns the common logical world,
authority/resource algebra, borrowing, obligations, cancellation state, lifecycle, synchronization,
and dynamic binding generations. ABI contexts project and transport those resources; they do not
define a second ownership or cleanup system. Target documents own machine conventions and physical
semantics. Library documents own their nominal logical protocols.

## 1. Decision and semantic layering

Keep three concepts separate:

1. A **machine calling convention** classifies the complete signature and assigns domain arguments,
   hidden arguments, results, saved state, stack layout, unwind behavior, and entry rules.
2. A **logical context contract** states a value-dependent transition over the common authority and
   obligation world. It is independent of ISA, OS, and physical placement.
3. A **target realization** proves that every admitted physical execution implements the logical
   transition while respecting the selected convention and environment.

This is the boundary-specific instance of `MEMORY_MODEL.md`'s demand/domain/target refinement. A
high-level contract says what authority and consequences are required. A library or platform
protocol supplies the domain plan. A target realization proves the register, stack, TLS/FLS, table,
runtime-call, unwind, and entry behavior.

The earlier designs embedded placement in published requirements or used a pairwise access matrix
as the composition gate. Both rules are rejected. Abstract argument indices are not physical
locations, and physical safety is a trace refinement problem rather than pairwise constructor
inequality.

## 2. Machine conventions remain per boundary

System V AMD64, Microsoft x64, AAPCS64, Wasm function types, syscalls, callbacks, signals,
interrupts, traps, coroutine resumes, and host/guest entries have distinct conventions or entry
environments. The same ISA and OS may use several. Interior library ABIs remain independently
selectable.

Signature classification happens before context placement. It includes by-value aggregate
classification, hidden result pointers, variadic state, shadow space, stack probing, red-zone
availability, homogeneous aggregates, unwind requirements, and control-flow protection. A context
cannot reserve `explicitArgument 5` and assume that it denotes a stable register or stack slot.

Entry and exit classes belong to the target/environment profile. There is no closed universal enum.
Signals, interrupts, callbacks, syscalls, thread/fiber starts, exception unwinds, Wasm traps, and
fatal aborts suspend, transfer, discharge, or invalidate different resources.

## 3. Nominal placement-free contracts

A published context has no register, argument number, TLS index, or Wasm table index. Strings may be
diagnostic labels but never establish identity, compatibility, or authority.

`BoundaryContextSpec World Key` makes the `(World, Key)` pair select one canonical contract with
associated argument, binding, result, outcome, and obligation-fragment types. Rows contain nominal
keys rather than freely constructed predicate-bearing records. The admitted row implementation must
enforce instance coherence: two different contracts cannot silently inhabit the same nominal key.
Protocol evolution creates a new key.

The remaining descriptive policy is deliberately small:

| Dimension | Initial vocabulary |
| --- | --- |
| Materiality | erased ghost, runtime |
| Extent | call, lexical, request, task, thread, process, object |
| Propagation | borrow, copy, move, inherit, do not propagate |
| Scheduling | pinned, migratable |

There is no standalone `observe | mutate | consume | provide` field. Those are projections of the
pre/post transition and may differ by result. Likewise, there is no `ContextTeardown` list. Cleanup
is transfer or discharge of an ordinary typed obligation in the common world.

Extent is not storage. A task-scoped binding may use TLS only while the task is pinned; a migratable
task requires task/fiber-local storage or an explicit handle. Windows TLS and FLS are distinct
realizations. Allocation of either mechanism is fallible and belongs to the outcome model.

## 4. Dependent obligation transitions

A context contract is dependent on arguments, concrete results, and semantic outcomes:

```text
requires(args, binding, beforeWorld)
transitions(args, binding, result, outcome, beforeWorld, afterWorld)
```

`requiredObligations(args, binding)` and
`emittedObligations(args, binding, result, outcome)` expose caller-facing obligation fragments.
Their presence in the pre- and post-world is proved by the contract. The transition remains the
authoritative account of obligations and authority that are preserved, discharged, transferred,
created, restricted, poisoned, or retained in a continuation or returned handle.

This permits contracts such as:

```text
(return_value & 1) = 1  ->  the mutex-release obligation was discharged
(return_value & 1) = 0  ->  the obligation is returned or transferred as declared
```

It also expresses argument-dependent authority: `(pointer, length)` requires authority over exactly
that byte range, and an operation tag may select read, write, or ownership-transfer authority.
Results may select only transitions declared in advance; they cannot retroactively manufacture
capabilities.

A call-lifetime loan is ordinary obligation transfer. The caller lends authority and emits a
must-return obligation to the callee. Every reachable ordinary result returns it; suspension may
transfer it into an explicitly returned continuation; a declared abort may invalidate the world but
does not pretend cleanup occurred.

Logical row composition operates over one `World`. It uses the memory model's resource algebra,
not independent products of per-context state. Sequential composition may use the obligations
emitted by one boundary to satisfy those required by the next. Unmatched resources remain in a
proved frame. Controlled sharing requires an explicit protocol law; it is not inferred from two
requirements mentioning the same storage.

Normalized heterogeneous rows and their identity, associativity, commutativity, framing, and
controlled-sharing laws are not implemented yet. Their representation must be benchmarked before it
becomes a public elaboration bottleneck.

## 5. Target realization interface

`TargetBoundarySemantics Target` makes the selected target/environment profile provide its own:

- classified signature type;
- entry and exit kinds;
- physical state and execution types;
- execution relation; and
- complete physical-admissibility predicate.

`ContextBoundaryRealization World Key Target` then proves two things for **every** physical execution
of the selected boundary:

1. the execution satisfies the target profile's physical-admissibility predicate; and
2. its projected arguments, binding, result, outcome, and pre/post worlds satisfy the nominal
   context transition.

The interface is intentionally relational. It does not assume deterministic execution, one ISA,
one OS, one ABI, one result path, or unlimited resources.

## 6. Required physical admissibility

Each closed target/environment profile must define physical admissibility strongly enough to cover:

- phases, control-flow paths, live ranges, setup, body, teardown, unwind, and helper calls;
- byte-range and register-alias overlap, including subregisters and stack ranges;
- complete signature classification, including ordinary and hidden arguments and results;
- intended producer/consumer handoffs and the values or refinement relations they carry;
- agreement for shared reads rather than an assumption that all read/read overlap is safe;
- call-transitive clobbers such as TLS resolver calls, stack probes, syscalls, and runtime helpers;
- root-state and entry-environment guarantees;
- preservation of every physical resource outside the declared frame; and
- fidelity between the emitted execution and the accesses/effects used by its proof.

Simple disjointness may be a sufficient lemma for unrelated live accesses. It is not the general
composition law. The deleted `PhysicalFootprint.Compatible` both rejected valid write-to-read
handoffs and accepted read/read overlap without value agreement. Optional or incomplete footprints
could also evade the gate. No replacement pairwise matrix is present.

Concrete target profiles must additionally cover applicable security/control-flow mechanisms such
as pointer authentication, BTI, and CET. A future Wasm component-model profile must pin and model
the Canonical ABI rather than treating it as a Core Wasm function convention.

## 7. Finite allocation and request accounting

Allocation, TLS/FLS allocation, table growth, and linear-memory growth are finite capabilities.
Their interfaces return explicit failure. No proof may assume every finite request succeeds. A
caller specifies the meaning of exhaustion at its boundary.

A request allocation protocol combines a runtime allocator/growth authority, peak-live and/or
cumulative limits, a generational ledger, and typed allocation/release obligations. Charging occurs
before a result becomes usable. Release decreases live bytes but not cumulative bytes. Accounting
arithmetic is non-wrapping, and no scoped allocation path may bypass the ledger.

Exhaustion is a result-dependent transition. A server may discharge or transfer the request's live
obligations and fail only that request. Process-owned allocator authority remains in the surrounding
frame. A path outside a request need not carry the request-accounting capability; the eventual
erasure theorem must prove that omission adds no runtime accounting work.

The logical allocator protocol is placement-free. Native realizations may use an explicit handle,
proved TLS/FLS lookup, or an interior-ABI register. Wasm may use an explicit parameter or an
instance-qualified capability table. These are distinct physical refinements of one logical demand.

## 8. Scope, cancellation, and asynchronous control

Scope entry emits an ordinary typed leave/restore obligation in the common world. Normal return,
failure, unwind, cancellation, suspension, worker transfer, and executor destruction each select a
declared transition that discharges or transfers it. There is no ABI-specific cleanup ledger.

Cancellation ownership and visibility remain in `MEMORY_MODEL.md`. ABI composition merely realizes
the callee's observation authority through a selected calling mechanism. A cancellable contract
declares its safe points, permitted effect prefixes, obligation transitions, and latency/progress
condition. Cancellation is cooperative, not an asynchronous jump into arbitrary instructions.

Interrupt and exception entry suspend rather than silently transfer the interrupted context's
authority. Handler authority is separately established. Fatal process/world invalidation is an
explicit abort outcome, never evidence that outstanding obligations were normally discharged.

## 9. Protocol evolution and linking

Changing a protocol creates a new nominal key. `ContextContractRefinement` relates old and new
worlds and explicitly maps arguments, bindings, results, outcomes, and obligation fragments. It
must preserve required obligations, emitted obligations, preconditions, and every stateful
result-dependent transition.

A verified adapter is such a logical refinement plus a target realization of the adapter's own
execution. Adapter planning may be order-dependent. Therefore associativity and commutativity of
logical row normalization do not imply coherence of synthesized adapter plans; competing plans need
an observational-equivalence theorem.

External artifacts eventually need checked nominal protocol and representation fingerprints. A
fingerprint supports linker lookup and diagnostics; it is not proof. The linker must connect it to a
kernel-checked theorem for the exact contract and realization. Unknown versions, collisions, and
missing refinements fail closed.

## 10. Whole-program connection obligations

Before ABI contexts may participate in `VerifiedProgram`, the implementation must prove:

- coherent nominal-key registration and heterogeneous row well-formedness;
- normalization, framing, identity, associativity, commutativity, and controlled-sharing laws;
- exact argument/result/outcome-dependent obligation conservation for every call;
- full-signature target classification and physical realization correctness;
- target-profile physical admissibility and emitted-execution fidelity;
- finite-resource success/failure totality and accounting completeness;
- cancellation and asynchronous-entry rules through the memory/concurrency model;
- adapter/refinement soundness and protocol-version fidelity;
- ghost erasure and zero runtime work for omitted runtime requirements; and
- correct root-context establishment for every admitted entry environment.

`VerifiedProgram` must carry universal connection proofs for every admitted initial state and
environment behavior. No legacy constructor, compatibility API, allowlist, axiom, `sorry`, or
narrowed input domain may bypass them.

## 11. Current implementation boundary

Implemented in `Gasm.Core.AbiContext`:

- nominal placement-free context specifications over a shared world;
- argument-, result-, and outcome-dependent transitions;
- explicit required/emitted obligation projections and presence laws;
- proof-bearing evidence for one boundary transition;
- stateful nominal contract refinement;
- target/environment-indexed entry, exit, signature, state, and execution types; and
- a staged realization requiring physical admissibility and logical refinement for every execution.

Not implemented:

- the M1 indexed authority/obligation world and resource algebra described by `MEMORY_MODEL.md`;
- coherent heterogeneous rows and their normalization/composition proofs;
- concrete target boundary semantics or physical-admissibility definitions;
- integration with `AbiDiscipline`, target `ABI.lean` files, or signature classification;
- concrete TLS/FLS/register/argument/table realizations;
- verified adapters or artifact protocol fingerprints; or
- integration with `Callable`, `VerifiedProgram`, linking, or emission.
