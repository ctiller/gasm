# Gasm standard containers and algorithms

## 1. Purpose and proof boundary

The container layer supplies small executable data structures together with pure
models. Programs use executable operations; proofs are phrased over
`toList`, lookup results, ordering, and representation invariants.  This keeps a
future storage or balancing change from leaking into downstream specifications.

## 2. Generic sorting

`Stdlib.Sort` provides insertion sort parameterized by a Boolean comparison.
`LawfulTotalRelation` carries exactly the transitivity and totality used by the
orderedness proof. The optional stronger `LawfulOrder` adds reflexivity and
antisymmetry for consumers that need equality reasoning. `StableOn` observes each
mutual-preorder key class by filtering the full records; `insertionSort_stableOn`
proves that every such class retains its exact input sequence, including distinct
records with equivalent keys. The central sorting contract therefore separates three
universal facts: pairwise ordering, permutation, and stability. The implementation is
deliberately simple: it is a reference algorithm and proof boundary, not a claim of
asymptotically optimal runtime.

## 3. Vector model

`Stdlib.VecSpec.Model` is the representation-free finite-index semantic layer. It
defines map, set, swap, append, and push without selecting storage and proves their
index observations. `Stdlib.Vec` is the currently selected contiguous `Array`
realization. Its `toModel_map`, `toModel_set`, `toModel_swap`, `toModel_append`, and
`toModel_push` theorems prove that the executable operations implement those exact
semantics. Bounds-sensitive successful access uses `Fin`; `get?` exposes failure
explicitly, including lookup laws on both sides of append.

`ByteArray.toVec` relates Lean's specialized byte storage to the same model through
size, `get`, `get?`, and list observations. Converting an appended byte vector back
to `ByteArray` agrees exactly with specialized ByteArray append, without requiring
clients to use the reverse heterogeneous-equality theorem.

The standalone `test_stdlib_vec` executable exercises append-boundary observations,
set, swap, push, semantic-model agreement, and ByteArray conversion. This proves that
the facilities execute together, but it is not an end-to-end program-consumer claim.
During the VerifiedProgram proof-template reset, no new code is attached to the old
Spike 3 proof tree. A rebuilt Spike consumer remains the completion gate, and no
target decoder currently depends on the ByteVec bridge.

The Array representation is certified but not opaque: Lean exposes the structure
constructor even though its fields have private names. Clients should use the public
operations and model laws as an API discipline, not rely on enforced abstraction.

## 4. Umbrella API and evolution

`Stdlib.Containers` is the supported umbrella import, and the repository-level
`Stdlib` facade re-exports it.  New container operations should ship with model laws,
invariant preservation where applicable, and executable regression guards.  Clients
should avoid matching on representation fields unless they are proving a new bridge
lemma inside the container layer.
