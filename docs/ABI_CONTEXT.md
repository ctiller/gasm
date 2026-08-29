# Composable Boundary ABI Contexts

**Status:** design for review. The typed requirement, placement, conflict detection, scoped TLS,
and cancellation foundations exist in `Gasm.Core.AbiContext`. Finite WASI allocation and
request-accounting models exist for the current Spike 3 and Spike 5 work. The row-level call rule,
verified adapters, and target-specific lowering remain integration work.

This document is the canonical definition of context carried across a call boundary. Target
documents define machine calling conventions and the concrete realization of placements; library
documents define the resources they require. Neither may invent a second context-composition rule.

## 1. Three concepts called "ABI"

They are related, but must remain distinct:

1. A **machine calling convention** assigns arguments, results, saved registers, stack layout, and
   unwind behavior. System V AMD64, Microsoft x64, and an interior library convention are examples.
2. A **context requirement** says which capabilities or ambient values a callee needs. An
   allocator, request budget, cancellation token, Vulkan dispatch table, and Winsock state are
   examples.
3. A **placement** says how one concrete context binding crosses one boundary: explicit argument,
   TLS slot, dedicated register, or capability-table slot. A proof-only binding has erased
   placement.

The operating system does not own the logical context ABI. A library may select its own interior
calling convention and context requirements. A complete platform supplies the instruction-set and
host semantics needed to realize them.

## 2. Requirements, bindings, and satisfaction

A context requirement contains:

- a stable resource identity and Lean resource type;
- whether the binding is erased or concrete;
- its placement;
- its lifetime, initially `perCall` or `requestScoped`;
- the protocol governing its use, ownership, propagation, and cleanup.

A binding contains a value and, for concrete values, provenance identifying the boundary that
established it. A call is well-formed only when every callee requirement has a satisfying binding.
Matching a register number or TLS index is insufficient: resource identity, representation,
lifetime, provenance, and protocol must also agree.

This is the intended call rule:

```text
caller context C satisfies callee requirements R
machine state satisfies the selected calling convention
callee preserves its framed capabilities and discharges its exit obligations
--------------------------------------------------------------------------
the call is admissible and returns one of the callee's declared outcomes
```

`VerifiedProgram` is not allowed to assume this premise. Its construction and emission path must
contain the universal proofs that every reachable boundary satisfies it for every admitted initial
condition.

## 3. Ghost and concrete context

An **erased ghost binding** may carry propositions, ownership witnesses, budgets used only in
proofs, or relations tying concrete state to a specification. It cannot affect emitted behavior and
requires no runtime setup.

A **concrete binding** is used when execution must discover a value: for example an allocator,
request ledger, host dispatch table, or cancellation flag. Every concrete binding is paired with a
ghost invariant relating its representation to its logical capability. Code reasons through that
invariant rather than treating TLS, a register, or a table entry as intrinsically trustworthy.

Erasure has two obligations:

- changing only ghost bindings cannot change emitted bytes or execution observations;
- a routine requiring no concrete context receives no context setup, lookup, accounting, or
  cancellation-polling instructions.

The second obligation is the zero-overhead rule. It is a property to prove of lowering, not merely
an optimization intention.

## 4. Concrete placements

The core placements are:

| Placement | Appropriate use | Boundary obligation |
| --- | --- | --- |
| Erased ghost | proof witnesses and logical budgets | prove erasure/non-interference |
| Explicit argument | ordinary values and uncommon capabilities | reserve argument location and prove representation |
| TLS slot | dynamically scoped request/thread context | establish, save, restore, and prove thread ownership |
| Dedicated register | hot interior ABI with a reserved context register | prove reservation and preservation across every call |
| Capability-table slot | Wasm imports/tables and host dispatch | prove index identity, table provenance, and entry type |

Placement is selected per boundary. The same logical capability may use TLS in a native server,
an explicit argument in a test harness, and a capability-table slot in Wasm. This requires a
verified adapter; it is not definitional equality.

## 5. Composition law

Requirements compose as a typed row. Composition is associative and commutative up to row
normalization, with the empty row as identity. Disjoint physical placements compose directly.
Overlapping concrete placements compose only when resource identity, representation, lifetime,
and protocol agree.

A mismatch is a link-time proof obligation, never a last-writer-wins choice. It may be resolved by
a verified adapter that:

1. requires the source binding;
2. establishes the destination binding and its provenance;
3. preserves all unrelated bindings;
4. translates success and every declared failure outcome;
5. restores scoped state on every exit.

Libraries publish their requirement row alongside their function convention. A program requiring
Vulkan and Winsock therefore carries the composition of those library rows; neither feature is a
global boolean embedded in `VerifiedProgram`.

## 6. Dynamic scopes and TLS

A scoped binding is installed with `enter`, which saves the immediately prior value. Every exit
uses `leave`, including normal return, allocation failure, cancellation, trap translation, and
language-level error propagation. `leave` restores the saved value, so nested request or subsystem
scopes restore their parent rather than clearing the slot.

The proof rule is bracket-shaped:

```text
prior --enter(value)--> active --body/outcome--> active' --leave--> prior
```

The body may mutate the resource according to its protocol, but it cannot acquire ownership of the
caller's saved binding. Unwinding code is part of the verified boundary implementation. A platform
whose native unwinder participates must prove that its unwind path implements the same `leave`.

## 7. Finite allocation and request accounting

Allocation and memory growth are finite capabilities. Their interfaces return an explicit failure;
no proof may assume that every finite request succeeds. A caller must specify what allocation
failure means at its boundary.

A request-scoped allocation capability combines:

- an allocator or memory-growth provider;
- a finite limit;
- a ledger of current live bytes, peak live bytes, and cumulative allocated bytes;
- provenance tying allocations and releases to the active scope;
- a cleanup policy for all exits.

Each successful allocation is charged before its result becomes usable. Release reduces live bytes
but not cumulative bytes. Growth fails if the provider cannot satisfy it or the chosen request
metric would cross its limit. The ledger must prove that no allocation path bypasses charging and
that arithmetic cannot wrap.

The limit policy is boundary-selected. Peak-live protects resident resource use; cumulative bytes
also limits churn. A server may enforce either or both. Exhaustion is an explicit request outcome,
so a request handler can clean up and reject that request while keeping the process alive. Process
termination is permitted only when the caller's declared policy chooses it.

Paths outside request handling do not install a request ledger. They may bind directly to a
process allocator and therefore pay neither request-entry nor per-allocation accounting overhead.
A library that allocates requires an allocation capability; it does not discover one through an
unmodeled global.

## 8. Cooperative cancellation

Cancellation is a caller-owned, monotonic capability. The caller may change `active` to
`cancelled`; a callee may observe but cannot clear it. A cancellable function declares the token in
its requirement row and declares safe points at which it may return `cancelled`.

Cancellation is not an asynchronous jump into arbitrary instructions. At a safe point the callee:

1. observes the token;
2. restores invariants needed by its public boundary;
3. releases or transfers outstanding linear resources according to its contract;
4. leaves every installed context scope;
5. returns an explicit cancellation outcome.

A contract must state cancellation latency or progress: for example, a safe point per input chunk
or per bounded loop iteration. It must also state which prefix of external effects may already be
observable. Operations needing all-or-nothing behavior require a separate transaction protocol.

Functions without a cancellation requirement contain no cancellation lookup or poll. A
non-cooperating function remains callable, but its caller cannot claim prompt cancellation across
that call.

## 9. Proof obligations

The eventual row-level implementation must establish:

- **Satisfaction:** each reachable call has every required binding with valid provenance.
- **Preservation:** a callee preserves bindings and capabilities outside its declared frame.
- **Composition:** normalized compatible rows compose; conflicts cannot construct callability.
- **Adapter soundness:** placement changes preserve the logical resource protocol and outcomes.
- **Scope restoration:** every exit restores the prior scoped binding.
- **Finite-resource totality:** allocation/growth success and failure are both modeled.
- **Accounting completeness:** every successful scoped allocation is charged exactly once and every
  release follows the ledger protocol.
- **Cancellation safety:** cancellation is observed only at declared safe points and all exit
  obligations are discharged.
- **Erasure:** ghost-only and omitted requirements add no emitted runtime work.
- **Indirect-call safety:** function values carry or imply the same convention and requirement row
  checked for direct calls.

These obligations extend the callability theorem; they do not replace functional equivalence or
memory-safety theorems.

## 10. Target realization

Target documents own only the mapping from abstract placement to executable mechanism:

- native targets may use explicit arguments, reserved registers, and a platform TLS mechanism;
- Wasm/WASI may use parameters, mutable globals where isolation permits, or typed
  capability/import-table entries;
- a future multiprocessing runtime establishes a distinct root context for each worker and proves
  which bindings may be shared, copied, or transferred.

OS APIs, instruction sets, calling conventions, and libraries remain independent axes. A concrete
artifact selects compatible members of each axis and proves their composition.

## 11. Review questions

The following choices remain deliberately open for review:

1. whether lifetime needs a third task/fiber-local constructor before multiprocessing;
2. whether allocation limits standardize peak-live, cumulative, or a product policy in core;
3. how cancellation latency is represented so it composes through library calls;
4. whether provenance identity is structural, nominal, or linker-issued in emitted artifacts;
5. which native TLS and Wasm table realizations become the first fully proved adapters.
