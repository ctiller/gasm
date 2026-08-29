# Boundary ABI Contexts

## 1. Requirements and placements

An ABI context is a capability demanded by a particular call boundary, not an operating-system or
process-wide ABI.  A requirement names its resource and lifecycle, then declares one placement:
an erased proof-only binding, an explicit argument, a TLS slot, a dedicated register, or a
capability-table slot.  Non-users have no requirement and therefore pay no setup or accounting
cost.

## 2. Binding, provenance, and composition

Concrete bindings carry provenance from the boundary that established them.  Callability requires
the concrete placement and provenance to satisfy the callee's requirement.  Requirements compose
only when overlapping physical placements have matching resource identity, layout, and lifecycle;
otherwise composition reports a conflict requiring an adapter.

## 3. Scoped TLS and recovery

TLS entry saves the prior binding, installs the new one, and restores the saved value on every
normal, failure, or cancellation exit.  Nested scopes therefore restore their immediate parent.
Allocation exhaustion and cancellation are request outcomes, not implicit process termination.

## 4. Cancellation

Cancellation is caller-owned and monotonic.  A cooperative callee may observe it only at a
declared safe point and returns an explicit cancelled outcome after scope cleanup.  Nested callees
cannot clear a parent token.  Non-cancellable callees declare no cancellation requirement.
