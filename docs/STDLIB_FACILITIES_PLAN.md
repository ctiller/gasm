# Standard library facilities plan

## 1. Purpose and status discipline

This document plans the growth and factoring of the Gasm standard library. It is
not an assertion that every named facility exists. Each item is marked with one of
these states:

- **Present**: implemented and described by its facility-specific document.
- **Next**: justified by an active consumer or build-health request and ready for a
  small reviewed slice.
- **Candidate**: supported by repeated code shapes, but its contract still needs
  consumer validation.
- **Deferred**: deliberately held until its semantic prerequisites exist.

`docs/STDLIB_CONTAINERS.md` remains the honest description of the container API
that is currently implemented. This document describes intended factoring and
landing order. Trust/build-health requests take priority over this roadmap; they
may advance, split, or defer a slice without changing the architectural boundary.

## 2. Design rule: contract, realization, executable use

Every representation-bearing facility should be factored into three distinguishable
layers:

1. A representation-independent semantic contract, stated through observations
   such as lookup, enumeration, membership, ordering, traces, or resource counts.
2. One or more concrete representations with proofs that their observations meet
   the contract.
3. Executable operations that programs can call without exposing representation
   fields or making clients repeat refinement proofs.

The separation need not imply three files for a tiny facility. It does require a
stable proof boundary. For example, clients of a finite map should prove against
lookup and finite-domain laws rather than a B-tree node layout. An association-list
reference implementation and a later B-tree implementation should be substitutable
at that boundary.

Theorem and algebra libraries do not need to invent a representation merely to fit
this pattern. Their corresponding boundary is a canonical definition, exact minimal
hypotheses, reusable behavior laws, and connection theorems to existing spellings.

Specifications may describe behavior and proved implementations may produce
certificates. They do not mint final program, ABI, target-admissibility, artifact,
or emission authority. Those authorities remain in Gasm Core and target layers.

## 3. Dependency and ownership boundaries

There are two foundational dependency lanes, joined only by explicitly effectful
algorithms:

```text
Lean / Init -> pure Stdlib contracts, algebras, and realizations

foundational Gasm Core -> Gasm.Effects contracts and observations

pure Stdlib + abstract capability/effect contracts
    -> effectful portable algorithms in Gasm.Effects or a lower Gasm utility namespace
    -> target adapters
    -> verified programs and artifacts
```

Pure containers, relations, bytes, arithmetic, and algorithms must not import a
target, host runtime, artifact format, or final verification authority. Fine-grained
imports are preferred over a growing umbrella dependency so that focused builds do
not inherit unrelated formats or targets.

In particular, pure Stdlib modules do not import `Gasm.Effects`. A reusable algorithm
which consumes Gasm's accepted effect or cancellation semantics belongs on the Gasm
lane. Stdlib may contain a purely parameterized transition algebra which assigns no
meaning or authority to its parameters; Gasm supplies the accepted interpretation.

Ownership is divided as follows:

- Pure value semantics, reusable algorithms, and representation refinements belong
  in `Stdlib`.
- Format grammars, format-specific errors, and format roundtrips remain in their
  domain libraries such as Fmt, HTTP, PNG, and Zlib.
- Observable console, filesystem, network, process, clock, and cancellation meaning
  remains in `Gasm.Effects`.
- ISA, ABI, object-format, syscall, and machine refinements remain target-owned.
- `VerifiedProgram`, export-set, artifact-identity, and emission authority remain in
  Gasm Core and its established realization path.

New namespace names in this plan are descriptive, not permission for a repository-
wide rename. Existing namespaces should move only as part of a small extraction with
real consumers.

## 4. Container and pure-algorithm program

### 4.1 Sequences and finite tables

- **Present:** representation-independent `Vec` model, Array-backed realization,
  `ByteVec` bridge, executable operations, and reference insertion sort.
- **Next:** complete append lookup laws, stable key-based sorting over a lawful total
  preorder, and preservation of relative order within comparator-equivalent values.
  For the current non-strict relation, keys are equivalent when precedence holds in
  both directions; stability preserves original tagged order inside that class.
- **Next:** a dependent finite-table contract with semantic model
  `(i : Fin n) -> F i`, extensionality, tabulation, dependent mapping, reindexing by
  finite equivalences, and append/split roundtrips.
- **Candidate:** slices or spans with exact take/drop/append and bounds laws. Their
  semantic contract should not force copying or aliasing behavior.

The dependent table is preferred to exposing casts from a heterogeneous storage
representation. A function-backed executable reference is acceptable until a
consumer demonstrates that a denser realization is needed.

### 4.2 Finite sets, maps, and persistent collections

- **Candidate:** `FinSet n` and `FinMap n A` contracts for compiler roles, worklists,
  liveness sets, clobber sets, and changed-block masks. A later bitset realization
  should refine the same membership and enumeration model. Promotion requires a
  named first migration in addition to the currently prospective uses.
- **Candidate:** a representation-independent finite `Map K V` contract with
  extensional lookup, unique enumeration, separate replace and fresh-or-reject
  operations, and fold laws.
- **Candidate:** an association-list reference map, followed by an ordered-tree
  realization and then a B-tree realization when balancing and occupancy laws have
  consumers.
- **Candidate:** persistent FIFO queue/deque with a list observation and push/pop
  order laws. A two-list queue is an appropriate first realization.
- **Candidate:** priority queue and union-find, after compiler or graph consumers
  establish the exact contracts.

There is no planned universal container inheritance hierarchy. Small semantic
interfaces and connection theorems are preferred to an abstraction lattice.

### 4.3 Generic algorithms

- **Candidate:** a finite worklist kernel with explicit seen set, termination measure,
  soundness, completeness under finite adjacency hypotheses, and `Nodup` output.
- **Candidate:** reachability, DFS postorder, and topological sort returning either a
  proved order or a concrete cycle witness.
- **Candidate:** strongly connected components after reachability and traversal
  interfaces settle.
- **Candidate:** stable merge, partition, grouping, deduplication, and binary search
  over ordered vectors.
- **Candidate:** generic dataflow iteration; domain-specific CFG semantics and final
  graph authority remain outside the algorithm.

A fuel-bounded search may intentionally omit completeness. Its API and theorem
names must not imply complete exploration.

## 5. Bytes, formatting, and parsing

The first extractions should be driven by concrete duplication:

- **Next:** move generic `ByteArray` lemmas out of the Zlib namespace and update PNG
  and Zlib atomically.
- **Next:** neutral alignment arithmetic such as `Nat.alignUp`, with exact divisibility
  and bound laws, extracted from multiple emitters. The existing behavior at zero
  alignment is preserved (`alignUp value 0 = value`); divisibility and round-up laws
  require positive alignment, and power-of-two laws state that stronger hypothesis
  separately.
- **Present:** Fmt's bounded UInt64 decimal contract, executable writer, digit-count
  and capacity bounds, together with the canonical decimal parse/format roundtrip
  foundation.
- **Next:** prove a connection theorem from HTTP's retained decimal spelling to the
  canonical Fmt behavior, then migrate the HTTP consumer without changing accepted
  syntax or output. Add a finer UInt64 digit-partition theorem only if that migration
  identifies a proof gap. Ownership and overlapping edits must be re-checked with
  Trust immediately before starting this slice.
- **Candidate:** `ByteCursor` with bounded endian reads, monotone position, no
  overread, and exact consumed-slice laws. ELF parsing and x86 decoding are initial
  consumers.
- **Candidate:** endian read/write primitives with roundtrip theorems. ELF, x86, and
  PNG provide consumer pressure without transferring their format semantics.
- **Candidate:** exact byte-chunk split/join/cap algebra shared by Effects, PNG, and
  Zlib. Environment queue/requeue policy remains effect-owned.
- **Candidate:** a byte builder exposing append, push, finalize, content, and length
  laws. It should land only after measurements confirm at least two consumers.
A general parser-combinator framework is not currently planned. Cursor and progress
laws should be extracted first. Higher-level parsing control belongs in Stdlib only
if two consumers retain the same control and error algebra afterward.

`Vec Byte n` is the preferred high-level byte sequence model when length belongs in
the contract. Dynamically sized buffers should use an existential sequence model or
retain `ByteArray` as a concrete realization behind a proved observation. Migration
must not force downstream `HEq` or cast plumbing merely to hide a runtime length.
Every bridge preserves exact output bytes; specialized byte storage may remain a
concrete realization where it is useful.

## 6. Fallible streaming and base I/O

This program is split into a pure finite-input fold and effectful source/sink I/O.
The highest-priority **Next** primitive requested by Trust is the pure fold. Before
implementation its step algebra must fix these semantics:

- acceptance commits exactly one input unit and returns the next fold state;
- refusal is atomic with respect to fold state and ownership accounting;
- the refused unit is retained as the head of the returned remainder and may be
  retried by the caller;
- the result returns the committed state, accepted prefix, exact remainder, stop
  reason, and resource-accounting witness.

Its conservation law partitions the original input into:

```text
accepted prefix ++ refused input ++ unconsumed tail
```

If the stop reason is refusal, the remainder is `refused :: unconsumedTail`; no state
or ownership delta from that refused step is committed. Resource counts use one
named unit per algebra. Required invariants are: live equals acquired minus reclaimed
without underflow; peak is the maximum live count over all committed prefixes;
refusal fabricates no ownership; reclamation is unique; and a terminal result names
any unreclaimed resources rather than silently treating them as cleaned up.

Effectful source/sink I/O remains **Candidate** and lives on the Gasm Effects lane,
not in pure Stdlib. Its separate outcome algebra must define partial commit, EOF,
the cancellation observation point, cleanup after partial progress, and precedence
when operation and cleanup both fail. After two accepted consumers exist, candidate
algorithms include bounded read-all, write-all with short writes, buffered source/
sink loops, flush, and finalization. They must not silently retry forever, discard a
remainder, or conflate console, file, and socket semantics.

## 7. Async facilities

Async is **Deferred** until the effect, obligation, cancellation, and resource-
reclamation algebras have an accepted profile and consumer. The first artifact
should be a pure lifecycle specification, not an executor or a conventional
`Future A` facade.

Pure Stdlib may define only a transition algebra parameterized by cancellation and
observation types. Accepted cancellation meaning, applicability to a profile,
observable traces, and adapter refinement remain owned by `Gasm.Effects` and target
layers.

The lifecycle must keep distinct:

- nominal request and task identity;
- submit, accept, complete, publish, notify, resource-return, and reclamation;
- pending, completed, cancelled, and reclaimed states;
- single completion and structured child ownership;
- cancellation propagation and cleanup;
- completion-versus-cancellation races and late notification;
- a unique owner for reclamation;
- nondeterministic scheduler order unless a target profile guarantees more;
- trace refinement from a target adapter to the portable model.

Only after this model is validated should the library consider join, race, timeout,
stream, or channel combinators. Lean's runtime `Task` implementation is not itself
a verified realization.

## 8. Inspiration and deliberate differences

The plan borrows useful boundaries rather than copying APIs:

- Rust: slice/owned-vector separation, explicit fallibility, byte-oriented I/O, and
  builders; without importing a borrow-checker-shaped API into Lean proofs.
- ML and Haskell: persistent maps/sets, folds/traversals, algebraic models, and laws;
  without a large hierarchy of collection typeclasses.
- OCaml: comparator-sensitive ordered containers; with the comparator contract made
  explicit in refinement proofs.
- Go and conventional systems libraries: small Reader/Writer-shaped streaming
  surfaces; with partial progress, refusal, cleanup, and conservation formalized.
- proof-oriented languages: semantic models, executable refinements, finite indices,
  and erased proofs; while retaining Gasm's stricter final program authority.

## 9. Landing sequence

Subject to higher-priority Trust/build repairs, the current sequence is:

1. Complete Vec laws and lawful stable key sorting.
2. Add the generic fallible streaming fold and resource-accounting lemmas requested
   by Trust.
3. Land dependent finite tables; separately promote `FinSet`/`FinMap` only when a
   named compiler migration is accepted.
4. Promote persistent FIFO and finite worklist facilities independently when their
   first integrations meet the admission gate.
5. Move neutral ByteArray lemmas atomically across their PNG/Zlib consumers.
6. Promote alignment, cursor, endian, chunk, and decimal facilities as independent
   librarian-reviewed slices; none is a prerequisite for landing the others.
7. Establish the abstract finite-map contract and association-list reference before
   tree and B-tree realizations.
8. Add bounded source/sink algorithms after two real streaming consumers agree on
   the outcome algebra.
9. Specify async lifecycles only after cancellation and effect prerequisites settle.

## 10. Admission and review gate

A representation-bearing facility is ready to land when its slice has:

1. At least two real consumers, or an explicit Trust/build-health request.
2. A semantic model and named observations independent of representation.
3. Executable operations and universal refinement/behavior theorems.
4. Explicit failure, duplicate, bounds, fuel, or capacity policy as applicable.
5. Negative controls for claims that would otherwise be easy to overstate.
6. No `sorry`, new axioms, or inappropriate decision-procedure authority.
7. Focused builds and the repository gates appropriate to its dependency closure.
8. Documentation that distinguishes present behavior from backlog.
9. Librarian review for ownership and duplicate extraction, MASM review when the
   compiler is a consumer, and Trust review for landing/build-health impact.

A theorem/algebra extraction instead requires a canonical definition, minimal named
hypotheses, universal behavior laws, connection theorems to retained spellings, the
same consumer/ownership/negative-control checks, and a focused build. It does not
need a fabricated representation or executable wrapper.

Every promoted slice records its dependency/import-closure and build-cost delta in
addition to before/after proof burden. Speculative generalization is removed when
that evidence is absent.

## 11. Working extraction inventory

This table is the initial inventory, not a claim of completeness. Candidate-to-Next
promotion requires filling any missing consumer, bound, and cost evidence.

| Facility | Current spellings | Consumers / pressure | Required law or boundary | State |
| --- | --- | --- | --- | --- |
| Vec and stable key sort | `Stdlib/Containers/*` | Spike 3 and MASM record sorting | tagged-input stability within mutual-preorder equivalence `beforeKey a b = true` and `beforeKey b a = true` | Next |
| Dependent finite table | function tables in RecursiveCFGBuilder and TypedCFG | compiler role and definition tables | extensionality, dependent get/map, reindex, append/split | Next |
| Generic ByteArray lemmas | `Stdlib/Zlib/ByteArrayBridge.lean` | Zlib and PNG | exact list/array observation bridges; no Zlib dependency | Next |
| `Nat.alignUp` | Linux ELF and Windows PE emitters | two linker/emitter paths | preserve zero policy; positive-alignment divisibility and minimality | Next |
| UInt64 decimal bridge | present Fmt UInt64 writer/bounds and HTTP decimal handling | Fmt, HTTP, Spike 2 | connection theorem and behavior-preserving HTTP migration; add only a demonstrated missing partition lemma | Next bridge; re-check ownership |
| Fallible finite fold | Trust streaming/accounting request | first integrations to be selected with Trust | atomic refusal, retained remainder, prefix conservation, live/peak/reclaim laws | Next by Trust request |
| Byte cursor | ELF parser and x86 decoding | two parsing paths | no overread, monotone cursor, exact consumed slice | Candidate |
| Endian primitives | ELF, x86 encoding, PNG big-endian emission | multiple byte formats | read/write roundtrip under exact width bounds | Candidate |
| Byte chunks | Effects splitting and PNG/Zlib streaming | effect and codec paths | split/join reconstruction and cap; no environment requeue policy | Candidate |
| `FinSet` / `FinMap` | Lists and function tables with differing local roles | prospective compiler analyses | membership/lookup, unequal-key preservation, exact unique enumeration | Candidate; integration required |
| FIFO / worklist | local traversal/search shapes | prospective graph and compiler use | FIFO observation; reachability soundness/completeness separated from fuel-bounded search | Candidate; integration required |

The implemented container status is sourced from `docs/STDLIB_CONTAINERS.md`; this
roadmap should not duplicate finer-grained present-state API claims as that surface
evolves.
