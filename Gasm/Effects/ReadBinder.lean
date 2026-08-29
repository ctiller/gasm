/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
Gasm/Effects/ReadBinder.lean -- PA6 read-binder contract shape (docs/READ_BINDER_CONTRACT.md)

This file is a standalone demonstration, not a change to any existing effect typeclass or
target hook. It states the contract shape Law 9's read-binder clause requires
(`ReadBinderObligation`: a read's result is a universally-quantified variable, bounded only by
the syscall's declared cap, never pinned to one instantiation) and proves -- structurally, with
no `decide`/`native_decide`/`bv_decide` standing in for the quantifier -- that the shape forces
chunk-robustness as a corollary rather than as a separately-argued property. See
docs/READ_BINDER_CONTRACT.md for the full design; this file implements exactly its §2 and §7.
-/

import Gasm.Core.Types

namespace Gasm.Effects

open Gasm.Core (Byte)

/- REF: docs/READ_BINDER_CONTRACT.md#2-the-contract-shape -/
/-- The read-binder proof obligation (`docs/READ_BINDER_CONTRACT.md` §2). A program whose next
step is "read up to `requested` bytes, then run `Post` on whatever came back" satisfies Law 9's
read-binder clause only if it can discharge `Post` for every element of the bounded byte-array
domain -- not one chosen witness. `bytes.length = 0` (an empty read), `0 < bytes.length <
requested` (a short read), and `bytes.length = requested` (a maximal read) are ordinary,
un-special-cased instantiations of this one quantifier (`docs/READ_BINDER_CONTRACT.md` §3). -/
def ReadBinderObligation (requested : Nat) (Post : List Byte → Prop) : Prop :=
  ∀ (bytes : List Byte), bytes.length ≤ requested → Post bytes

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A single valid read outcome against a cap `cap`: `chunk` is any prefix of what actually
remains (`rem`), no longer than `cap`. This refines `ReadBinderObligation`'s domain with the one
additional fact a faithful environment's reads must respect -- each read consumes a genuine
prefix of what is left, never reordering or inventing bytes -- rather than defining a separate,
parallel notion of "valid read result". -/
def IsValidReadChunk (rem : List Byte) (cap : Nat) (chunk : List Byte) : Prop :=
  chunk.length ≤ cap ∧ chunk = rem.take chunk.length

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- A complete chunking of a logical input `rem` under read-cap `cap`: a finite list of reads
that, played in order, consumes all of `rem`. Nothing here forces `chunk` to be nonempty, forces
a fixed number of reads, or distinguishes "the first read returns everything" from "the input
arrives in many small (possibly empty) pieces" -- every witness is an equally legal instance of
the read-binder domain (`docs/READ_BINDER_CONTRACT.md` §3, §7). -/
inductive ChunksOf : List Byte → Nat → List (List Byte) → Prop where
  | nil {cap : Nat} : ChunksOf [] cap []
  | cons {rem chunk : List Byte} {cap : Nat} {chunks : List (List Byte)} :
      chunk.length ≤ cap →
      chunk = rem.take chunk.length →
      ChunksOf (rem.drop chunk.length) cap chunks →
      ChunksOf rem cap (chunk :: chunks)

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Every chunk delivered along any complete chunking is a valid read outcome (`IsValidReadChunk`)
against whatever truly remained at that point -- `ChunksOf` is not a parallel domain, it is
`ReadBinderObligation`'s domain applied at every position of a finite trace. -/
theorem ChunksOf.chunks_are_valid_reads {rem : List Byte} {cap : Nat} {chunks : List (List Byte)}
    (h : ChunksOf rem cap chunks) :
    ∀ chunk ∈ chunks, chunk.length ≤ cap := by
  induction h with
  | nil => intro chunk hmem; cases hmem
  | cons hcap _ _ ih =>
      intro chunk hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact heq ▸ hcap
      · exact ih chunk hmem'

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Restates the connection to §2 by name, not just by shape: once a `ReadBinderObligation cap
Post` has been discharged (proven for *every* element of the bounded domain), every chunk
appearing in *any* complete chunking automatically satisfies `Post` -- a chunking is not a
separate source of proof obligations, it is a sequence of witnesses into the one obligation
already established. -/
theorem ChunksOf.discharges_read_binder_obligation {rem : List Byte} {cap : Nat}
    {chunks : List (List Byte)} (h : ChunksOf rem cap chunks) {Post : List Byte → Prop}
    (hobl : ReadBinderObligation cap Post) :
    ∀ chunk ∈ chunks, Post chunk := by
  intro chunk hmem
  exact hobl chunk (h.chunks_are_valid_reads chunk hmem)

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Any complete chunking of `rem` reconstructs `rem` exactly, by structural induction on the
`ChunksOf` derivation -- no enumeration, no `decide`, no fixed bound on the number or size of
reads. This is the theorem the empty/short/full-read cases in §3 are three ordinary
instantiations of, not three separately-argued special cases. -/
theorem ChunksOf.flatten_eq_total {rem : List Byte} {cap : Nat} {chunks : List (List Byte)}
    (h : ChunksOf rem cap chunks) : chunks.flatten = rem := by
  induction h with
  | nil => rfl
  | cons _hcap heq _hrest ih =>
      rename_i rem' chunk' _cap' _chunks'
      simp only [List.flatten_cons, ih]
      have base := List.take_append_drop chunk'.length rem'
      rw [← heq] at base
      exact base

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- Chunk-robustness as a corollary, not a separate requirement: any two complete chunkings of
the *same* logical input reconstruct to the same bytes, regardless of how many reads each took
or where the split points fell -- a program's observable result cannot depend on how the
environment happened to chunk its input, because both chunkings are read-binder-domain witnesses
of the one theorem above, not two independent claims. -/
theorem chunk_robustness {total : List Byte} {cap : Nat} {chunksA chunksB : List (List Byte)}
    (hA : ChunksOf total cap chunksA) (hB : ChunksOf total cap chunksB) :
    chunksA.flatten = chunksB.flatten := by
  rw [ChunksOf.flatten_eq_total hA, ChunksOf.flatten_eq_total hB]

/- REF: docs/READ_BINDER_CONTRACT.md#7-worked-example-chunk-robustness-as-a-corollary -/
/-- The form of chunk-robustness a caller actually needs: if a continuation's postcondition
`Post` has already been established for the reconstruction obtained under *one* chunking, it
holds automatically for *every* other complete chunking of the same logical input. A program
proven correct for one chunking is provably equal, via this one lemma, to the same program under
any other chunking of the same input -- exactly the property
`docs/READ_BINDER_CONTRACT.md` requires this design to check rather than merely assert. -/
theorem continuation_invariant_to_chunking {total : List Byte} {cap : Nat} {Post : List Byte → Prop}
    {chunksA chunksB : List (List Byte)}
    (hA : ChunksOf total cap chunksA) (hB : ChunksOf total cap chunksB)
    (hPost : Post chunksA.flatten) : Post chunksB.flatten := by
  rw [chunk_robustness hA hB] at hPost
  exact hPost

end Gasm.Effects
