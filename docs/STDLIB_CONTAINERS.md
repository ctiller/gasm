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

`Stdlib.VecSpec.Model` is the representation-free semantic layer. `Stdlib.Vec` is the
currently selected contiguous `Array` realization, and `ByteArray.toVec` relates
Lean's specialized byte storage to the same model. Construction, indexing, update,
append, mapping, swapping, and folds expose laws connecting execution to the model.
Bounds-sensitive successful access uses `Fin`; `get?` exposes failure explicitly.

The Array representation is certified but not opaque: Lean exposes the structure
constructor even though its fields have private names. Clients should use the public
operations and model laws as an API discipline, not rely on enforced abstraction.

## 4. Umbrella API and evolution

`Stdlib.Containers` is the supported umbrella import, and the repository-level
`Stdlib` facade re-exports it.  New container operations should ship with model laws,
invariant preservation where applicable, and executable regression guards.  Clients
should avoid matching on representation fields unless they are proving a new bridge
lemma inside the container layer.
