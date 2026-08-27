# 0004. Adopt Core Capability Machinery for Memory Safety

## Status

Accepted, 2026-08-27. (PLAN.md D3.)

## Context

The repository's deep review found the `Core` capability machinery
(`MemoryPermissions`/`BlockM`/obligation ledgers) fully designed but dormant: zero call
sites in shipped code (PLAN.md Findings ledger, 2026-08-27). Meanwhile no memory-touching
instruction anywhere in the codebase carries a checked capability proof — memory safety
exists only as an unenforced design intention. Under [`0001`](0001-vision-and-insights.md)'s
premise that untrusted generation must be caught by construction, an authoring surface
that merely permits correct capability use (rather than requiring it) will eventually be
bypassed by a generated program that doesn't bother.

## Decision

Adopt the dormant Core capability machinery as the *mandated* authoring surface for
memory-touching programs, per
[Law 11](../REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble):
memory access without an attached, in-scope capability proof must fail to assemble — the
artifact must be unbuildable, not merely flagged. Capabilities double as frame
conditions for the modular proof composition of [`0003`](0003-universal-equivalence-via-modular-decomposition.md).

## Consequences

Every module built on the raw symbolic-memory-operand bypass path is now tracked as
critical migration backlog (Phase 2 capability adoption/migration plan, TASKS.md PA4);
new programs must not be authored on the bypass path starting now. `Stdlib/Zlib/Windows.lean`
— flagged in the Findings ledger as the most fragile code in the repository (hand-computed
stack offsets, fixed 8MB/8MB `VirtualAlloc` split, no bounds checks) — is explicitly
scheduled last/biggest in the migration order precisely because it is the module this
decision most needs to reach. Bounds on fixed-size regions (arenas, I/O buffers, scratch
spaces) become contracts under this decision: overrun becomes unrepresentable, not merely
untested.

## Provenance

Mixed. The requirement itself is owner-stated, from the founding vision message: "we're
growing a functional problem in that memory safety is not considered; it was supposed to
be foundational and so something's missing -- really the instructions should be
validating they have access to an address and failing to assemble if that proof doesn't
carry." The specific mechanism adopted to satisfy it — the dormant Core capability
machinery (`MemoryPermissions`/`BlockM`/obligation ledgers) as the mandated authoring
surface, and its framing as Law 11 — is the coordinator's design choice, not named by the
owner.
