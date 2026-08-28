# BORROW_MODEL: Borrowing as Obligation Dispatch

- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/REVIEW.md#law-5-the-stop-and-design-invariant
- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity--anti-facade-law-no-dead-abstractions-or-mock-verification
- REF: docs/REVIEW.md#law-12-connection-theorem-mandate-no-unlinked-twins
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#11-capability-splitting-and-joining-laws
- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm
- REF: docs/MEMORY_HOOK.md#4-layer-a-assemble-time-capability-enforcement
- REF: docs/X86_MEMORY_MODEL.md#23-the-shape-mt1mt2-build-this-documents-structural-decisions
- REF: docs/VISION.md#4-tractability-modular-contracts-composed-proofs
- REF: docs/TARGETS/ARM64.md#7-what-is-settled-for-x86-only-versus-what-arm-must-decide

## 1. Status and scope

**Status**: this is a design document, not a report of built machinery. **No borrow
mechanism exists in the tree.** Everything described as existing was verified by reading
the tree or running commands at commit `ef5407e` (2026-08-28); everything proposed carries
its own `**Status**:` line. The one thing this document reports as *measured* rather than
proposed is the Lean-4 feasibility spike of §5, which was compiled at this repository's
pinned toolchain (`lean-toolchain`: `leanprover/lean4:v4.33.1`) in a scratch directory and
is deliberately **not** in the tree; its source is reproduced inline so it can be re-run.

**The owner's directive**, verbatim, in four fragments:

> *"do the memory hooks distinguish read and writeability? (and can we delegate readability
> when we have writeability safely?) -- my target is to not need rust"*

> *"i'm wondering about a borrow model being an obligation dispatch / the owner starts out
> with capability write / if it lends a read, then it loses the write capability (but retains
> read) / only when all reads are discharged does it regain write / and it can donate write"*

> *"on lean not being linear: yes, and that's why the intent for obligations is to flow
> through a monad"*

> *"can we make our own dsl shape for weaving these monads, since we know their shape?"*

And the Law 5 demand trigger, verbatim:

> *"isa scale up: we need multithreading and borrowing resolved"*

### 1.1 The direct answer to the first question

**No.** The vocabulary distinguishes read from write; nothing enforces the distinction, and
nothing delegates. Verified:

| Fact | Evidence |
| :-- | :-- |
| The share vocabulary exists | `PermissionShare := ReadOnly \| Exclusive \| Locked` (`Gasm/Core/Permissions.lean:24-28`) |
| Capability tokens exist | `MemoryPerm base len share`, carrying `validRange`/`nonEmpty` (`Gasm/Core/Permissions.lean:32-34`) |
| Splitting is **spatial only** | `MemoryPerm.split` cuts `[base, base+len)` at `k` and carries *the same* `share` into both halves (`Gasm/Core/Permissions.lean:38-49`, return type at line 41). There is no `Exclusive → ReadOnly ⊗ ReadOnly` operation anywhere. **That is the missing primitive, and it is the whole of the owner's rules 2 and 3.** |
| Disjointness is stated | `DisjointRanges` (`:53-54`), `DisjointTokens` (`:58-62`), the invariant field of `MemoryPermissions` (`:66-68`) |
| The permission container has exactly one consumer | `ComposedState.perms : MemoryPermissions Arch` (`Gasm/Core/State.lean:31`). A tree-wide grep for `MemoryPerm`/`PermissionShare`/`MemoryPermissions` over `Gasm/`, `Stdlib/`, `Spikes/`, `Tools/` returns that line, plus one doc-comment mention in `Gasm/Targets/X86_64/MemoryCell.lean:175`. Nothing else. |
| No theorem connects a store to `Exclusive` | No occurrence of either name in any theorem statement in the tree |
| An indexed typestate monad **already exists and is dormant** | `BlockM Arch S₁ S₂ α` with `pure`/`bind`/`get`/`set` (`Gasm/Core/BlockM.lean:25`, `:32`, `:37`, `:47`, `:52`). Its only tree-wide occurrence outside its own file is the `import` on `Gasm/Core/CFG.lean:20`. It is Atkey's parameterized monad, written in 2026, used by nothing. |
| The access-descriptor layer *does* exist and is live | `MemAccessKind := load \| store` (`Gasm/Targets/X86_64/MemoryCell.lean:41-43`); `MemAccessSpec` (kind, width, ref) (`Gasm/Targets/X86_64/Memory.lean:81-84`); `memAccesses : ι → List MemAccessSpec`, defaultless, on the instruction class (`Gasm/Targets/X86_64/Instructions/Base.lean:66`); `storeFootprint`/`loadFootprint` (`Gasm/Targets/X86_64/Memory.lean:99-105`); `WritesWithin`/`ReadsWithin` frame obligations discharged for all 14 memory forms (`Gasm/Targets/X86_64/MemoryFrame/Common.lean:39-52` plus the six per-family shards) |
| Machine memory is sealed | `X86_64Memory` with `private mk ::` / `private raw` (`Gasm/Targets/X86_64/MemoryCell.lean:54-56`); `X86_64Mem.read`/`write` (`:75`, `:100`) are the only functions in the tree that can touch bytes |
| **A loan counter already exists, live and used** | `ArenaPageToken.activeBorrows : Nat` with `isSafeToRelease t := t.activeBorrows == 0` (`Gasm/Core/Obligations.lean:43-53`), designed in `docs/MEMORY_PROVENANCE.md` §1.2, and actually incremented and decremented by the allocator spec (`Stdlib/SmolAlloc/Spec.lean:46`, `:101`, `:126`, `:149`). It is a *different subject* from this design's loans and it is instructive — see §3.2 |

Two corrections to the framing this document was commissioned with, recorded because they
matter downstream. `perms` sits on `ComposedState`, not on `MachineState`
(`Gasm/Core/State.lean:31`) — the machine state proper has no permission field, so a
borrow index cannot be threaded through the *machine* without either using `ComposedState`
or keeping the index outside the state entirely (this design does the latter, §4).
And `Gasm/Targets/X86_64/MemoryCell.lean` is no longer merely a "consumer of the permission
model" — it is the landed MH1 hook, and it does not mention permissions at all except in a
doc comment.

**So the honest starting position is better than it looks.** The hard, boring half — one
chokepoint for every byte access, a declarative per-instruction access descriptor with no
default, and frame lemmas connecting descriptor to behaviour — landed with MH1 (ADR-0040).
What is missing is the *authority* half: which accesses are permitted, and how permission
moves. That is what this document designs.

## 2. The model

### 2.1 The four rules, stated as a capability state

**Status**: proposed; nothing below exists. The names in this section are design names.

Per region, one ghost capability state:

```
Cap  ::=  write            -- owner holds write and read
       |  read n           -- n read loans outstanding: read allowed, write refused
```

The owner's four rules become four total functions on `Cap`:

| Owner's rule | Operation | Effect |
| :-- | :-- | :-- |
| "the owner starts out with capability write" | initial state | `write` |
| "if it lends a read, then it loses the write capability (but retains read)" | `lend` | `write ↦ read 1`; `read n ↦ read (n+1)` |
| "only when all reads are discharged does it regain write" | `reclaim` | `read 1 ↦ write`; `read (n+1) ↦ read n` |
| "and it can donate write" | `donate` | the region leaves this context entirely and appears in the donee's |

A borrow context is a list of such states, one per granted region: `Ctx := List Cap`,
positionally indexed. Two decidable predicates over it are the entire authority check —
`canStore Γ i` holds exactly when `Γ`'s `i`-th region is `write`; `canLoad Γ i` holds for
`write` and for `read _` alike. Shared-XOR-mutable is that one line: no `Cap` admits a
store while a loan is outstanding, and `lend` is the only way to create a second reader.

Note what `read n` is doing: it is a **ghost loan counter**, one of the three candidate
mechanisms this document was asked to weigh. It is not the recommendation on its own —
counters as free-standing data are re-derivable and forgeable — but as the *index* of a
monad (§4) it is exactly the right representation, because the index is the one thing in
Lean that cannot be duplicated by a proof. The counter is data; the discipline is typing.

### 2.2 Does `Locked` fit the same lattice? — a different axis, and then a third point

**Status**: this section is analysis of landed vocabulary plus proposed design; the
`Locked` constructor exists (`Gasm/Core/Permissions.lean:27`), nothing consumes it.

Two axes are being conflated in the current three-constructor enum.

**Axis 1 — authority**: who may load, who may store. `ReadOnly` admits loads only;
`Exclusive` admits both. This is the axis borrowing moves along, and it is the axis this
document is about.

**Axis 2 — atomicity and ordering**: how an access is performed and how it is ordered
against other accesses. `docs/X86_MEMORY_MODEL.md` §2.3 Decision 1 already settled where
this axis lives: on `MemAccessKind`, as a third constructor `rmw` — one indivisible
read-modify-write per descriptor entry — and §8 of that document explicitly rejected a
parallel per-access ordering field as duplicating a distinction the kind already draws.

`Locked` as written sits on **axis 2 wearing axis 1's clothes**. On the authority axis it
is indistinguishable from `Exclusive`: the in-flight MH3 surface spells this out, its
`shareAllows` mapping `.Locked` to `true` for both `.load` and `.store`, identically to
`.Exclusive`. A `PermissionShare` value that admits exactly what `Exclusive` admits is not
a third point on the authority lattice; it is an annotation about *how* the access is
performed, and that annotation now has a better home.

**But there is a genuine third authority point, and `Locked` is the right name for it.**
It is not a level between `ReadOnly` and `Exclusive`. It is the top of a second, parallel
branch: a share held by **many** holders **simultaneously**, all of which may store, whose
race-freedom is discharged **dynamically by atomicity** rather than statically by
exclusion. That is `AtomicU64`, `Mutex`, and `RefCell` in Rust's terms — the escape hatch
that exists precisely because the static discipline is not complete. Under the borrow
model:

- `Exclusive` and `ReadOnly` form the borrow lattice proper. Loans move between them.
- `Locked` is **not reachable by lending**. A region is `Locked` because it was created
  that way (shared state established at spawn, or handed over by a synchronization
  primitive), and a `Locked` region admits stores from any number of holders.
- Every access to a `Locked` region must be an `.rmw`-kind access or otherwise
  synchronization-ordered. That is the *obligation* `Locked` carries, and it is what makes
  it safe rather than merely permitted.

The recommendation is therefore: **keep three constructors, but re-read the third.** `Locked`
stops meaning "exclusive, but atomic" and starts meaning "shared-mutable, safety discharged
by atomicity". It is a different axis *only* if you read it as an ordering annotation; read
as an authority mode it is a real third point, and it is the point where the static
discipline hands off to a dynamic protocol. **Status**: this re-reading is proposed, not
ratified; it is Owner Question Q2 (§13). It has a concrete consequence for the in-flight
MH3 surface (§6) and a concrete consequence for the no-data-race theorem (§8), and it is
the single place where ARM's memory model bites (§9).

### 2.3 What a loan is, concretely — and when it is discharged (the crux)

This is the question most likely to sink the design, and it was posed correctly: Rust knows
when a borrow ends from lexical scope, tightened by NLL's liveness dataflow. Straight-line
assembly has no scopes.

**A loan is a ghost index transition. It emits no bytes.** `lend`/`reclaim` are operations
in the authoring monad whose *value* is `()` and whose *effect* is entirely on the type
index. This was measured, not assumed: in the §5 spike, a program containing `lendRead 0`
and `endRead 0` emitted the instruction list `[st 0, ld 0, st 0]` — the two ghost
operations contributed nothing (`#eval` output, §5.3). A loan costs zero instructions and
zero runtime state.

**Discharge is forced at four places, none of which is a scope:**

1. **The routine's declared post-index.** A routine whose type says `Asm Γ Γ α` — the
   contract "I give back what I was given" — cannot elaborate with an undischarged loan,
   because the computed final index is `read 1` where the declared one is `write`. This
   is the primary forcing function and it is exactly the ABI-style contract the tree
   already states elsewhere (`ObligationLedger.isValidAtReturn`,
   `Gasm/Core/Obligations.lean:79`). **Measured**: the omission is an elaboration error
   (§5.4, control NEG-2) — but with a poor message, which is a real finding, recorded in
   §5.5.
2. **Branch joins.** Both arms of a conditional must arrive at the same index. This is an
   equality obligation `Γ_then = Γ_else`, decidable by `decide` when both are literal.
   The tree's control-flow vocabulary already has this shape: `CpuTerminator.jcc` demands
   `h_true : S = TrueIn` and `h_false : S = FalseIn` (`docs/API_STATE_MODELS.md` §4).
   Rust computes this join by dataflow; here it is a proof obligation that the fast path
   closes by `decide` and the slow path closes by a written proof. That substitution — a
   dataflow *decision* becomes a dispatched *obligation* — is the whole design thesis in
   one instance.
3. **Loop bodies.** A loop body must be index-preserving (`Asm Γ Γ`): a loan opened in an
   iteration must close in that iteration. This is a genuine restriction, and it is
   honestly weaker than NLL, which can carry a borrow across a back edge when liveness
   permits. Stated as a limit, not papered over (§11).
4. **Call boundaries.** A callee's index contract is part of its type, so lending across a
   call is representable (`donate` transfers, `lend` splits) and the caller's index reflects
   it. **Status**: proposed; the call-boundary form has not been spiked.

**So discharge is neither an instruction nor a block boundary nor a runtime check.** It is
an explicitly-written ghost operation whose omission is caught by an index mismatch at a
*declared contract*. The monad answers the crux for free, exactly as the coordinator
suspected: the index knows when the last loan is gone, because `reclaim` on `read 1` is the
only transition back to `write`.

## 3. Confronting linearity directly

Lean is not linear. A `MemoryPerm` token is an ordinary value; `let p := tok; f p p`
duplicates it and no typing rule objects. Any design that says "lending consumes the write
token" and means it literally is wrong in Lean.

The resolution the owner named is right, and it is worth stating precisely *why* it works:
**the resource that must not be duplicated is moved out of value position and into type
position.** A Lean value can be used twice; a type index cannot be "used" at all — it is
threaded by `bind`'s typing rule, which is the only way to sequence, and which mentions each
intermediate index exactly once:

```
bind : Asm Γ₁ Γ₂ α → (α → Asm Γ₂ Γ₃ β) → Asm Γ₁ Γ₃ β
```

Duplicating a value of type `Asm Γ₁ Γ₂ Unit` is harmless — running the same lend twice from
`Γ₁` still starts at `Γ₁`, and sequencing the duplicate forces `Γ₂ = Γ₁`, which fails. The
substructural content lives in the *shape of composition*, not in the *uniqueness of a
value*. This is Atkey's parameterized monad and it is how Ynot and Idris's `ST` handle the
identical problem; the coordinator's framing is correct.

**And the tree already contains it.** `BlockM Arch S₁ S₂ α` (`Gasm/Core/BlockM.lean:25`)
is exactly this signature, with `bind` at `:37` composing `S₁ → S₂` with `S₂ → S₃`. It has
been dormant since it was written, with no consumer. The borrow model is not a new
structural commitment; it is the first consumer of a structure already ratified in
`docs/API_STATE_MODELS.md` §2 and sitting unused — which materially changes the Law 8
calculus (§10).

### 3.1 The alternatives, weighed

**Typestate over an explicit map** — thread `ComposedState.perms` as ordinary data and make
each declared access carry an obligation that the map grants the needed share at that
footprint. Rejected as the recommendation, per the owner's ruling, and independently
correct to reject: because the map is a value, nothing forces the *author* to thread the
updated map rather than the original. Every `lend` produces a new map, and reusing the old
one is a well-typed program that has forgotten the loan. It requires a discipline the type
system does not check, which is the exact failure mode Law 13 tier 1 exists to eliminate.
Its one real advantage — `do`-notation works — is answered by §5.

**Ghost loan counters as free-standing data**, with the reclaim rule proven as a theorem
rather than enforced by typing. Rejected as a standalone mechanism for the same reason:
the counter can be re-derived, ignored, or reset by a well-typed program. It survives *as
the content of the index* (§2.1), where it is not forgeable, and the reclaim rule is then a
lemma about the index rather than a hope about a value.

**Indexed monad.** Recommended. Costs: `do` does not work (§5), and index unification has
to reduce computed contexts during elaboration (measured to work, §5.3).

### 3.2 Prior art in the tree: `activeBorrows`, and what it demonstrates

The tree already contains a loan counter, and it is not dormant. `docs/MEMORY_PROVENANCE.md`
§1.2 specifies that a backing arena tracks `activeBorrows : Nat`, incremented by
sub-allocation and decremented by free, with page release gated on the count reaching zero.
That is realized as `ArenaPageToken.activeBorrows` / `isSafeToRelease`
(`Gasm/Core/Obligations.lean:43-53`) and genuinely exercised by the allocator spec, which
increments it at `Stdlib/SmolAlloc/Spec.lean:101` and `:126` and decrements at `:149`.

**It is the same shape on a different subject.** Both are "a resource whose reclamation is
gated on outstanding loans reaching zero". But `activeBorrows` gates *lifetime* — do not
release the page while children are alive — where this design gates *authority* — do not
store while readers are alive. They answer different questions and neither subsumes the
other, so they are not Law 12 twins of the same model-level fact. They are, however, two
instances of one abstraction, and Law 12's stated preference order puts "a single source of
truth from which other forms are derived" above two parallel encodings. Whether to factor a
generic counted-loan abstraction with two instances, or to leave them separate on the
grounds that lifetime and authority genuinely differ, is Owner Question Q4 (§13). It is not
urgent and it should not be resolved by accident.

**What it demonstrates is the sharper point, and it is evidence rather than argument.**
`activeBorrows` is a value-level counter threaded through an ordinary state record. Nothing
in its type prevents a spec transition from constructing the successor state with the
*old* count, or with no increment at all — the increments at `:101` and `:126` are correct
because they were written correctly, not because anything checks them. That is precisely the
objection §3.1 raises against value-level typestate and ghost counters, stated here against
a real, working, in-tree instance rather than against a hypothetical. It is also the reason
the borrow model's counter belongs in an index: the arena counter can afford this because a
mis-threaded count causes a leak, while a mis-threaded borrow count causes a data race.

## 4. What the index is, and what it is not

**Status**: proposed; nothing in this section exists.

The index is a **static, syntactic** borrow context: a list of region states, where a region
is identified by its position and described by a `RegionSpec`-shaped record (anchor register,
length, share) — the shape MH3 is landing (§6). The index is **not** the machine state, and
**not** `ComposedState.perms`. Three consequences, all load-bearing:

- **It erases completely.** The index is a type argument; nothing about it survives to
  `SymbolicInstr`, encoding, or bytes. This is the zero-cost-proof-erasure shape
  `docs/API_STATE_MODELS.md` §1 already establishes, and it is why a loan costs zero
  instructions (measured, §5.3).
- **It is decidable.** Every index transition is a total function on a finite structure of
  literals, so `canStore`/`canLoad`/index equality all close by `decide` — Law 10 rung 2,
  kernel-checked, no allowlist entry. This is the "Rust's borrow checker as the fast path"
  claim made concrete: the fast path is `decide` on the index.
- **It says nothing about aliasing.** Two regions with distinct indices may denote the same
  bytes at runtime. The index tracks *authority bookkeeping*; whether the bookkeeping
  corresponds to reality is a separate obligation (`DisjointTokens`,
  `Gasm/Core/Permissions.lean:58-62`) discharged semantically against the routine's
  precondition. **This is the sharpest limit of the whole design and §11 states it in full.**

The connection between the index and the machine is therefore a theorem, not a definition:
the index-tracked context must be shown to grant the footprints the descriptors declare.
That theorem is MH3's `MemSafe` shape (`docs/MEMORY_HOOK.md` §4.4), unchanged.

## 5. The weaving DSL — measured, not asserted

**Status**: measured feasibility spike, compiled at `leanprover/lean4:v4.33.1`; **not in
the tree and not proposed for the tree in this form**. The code below is reproduced so the
measurement can be re-run and audited. Real region identifiers, widths, `MemRef`s, and
`MemoryPerm` backing are all abstracted away — this measures *syntax and elaboration
behaviour*, nothing else.

### 5.1 Does Lean's `do` work? No, and the failure is clean

Lean's `do` requires a `Monad m` instance with `m : Type u → Type v`. An indexed monad is
`Ctx → Ctx → Type → Type` and cannot instantiate it. Measured error, on a `do` block over
the indexed monad:

```
error: failed to synthesize instance of type class
  Pure (Asm [Cap.write] [Cap.write])
```

Unambiguous and immediate — not a subtle mis-elaboration. Confirms the coordinator's
flag.

### 5.2 The DSL: Lean's own `do` *syntax*, elaborated to indexed binds

The measured answer to "can we make our own DSL shape for weaving these monads" is **yes,
and it is about thirty lines, because Lean's `doSeq` parser can be reused verbatim.** The
DSL declares a term-level `asm` prefix over `Lean.Parser.Term.doSeq`, then walks the parsed
sequence and folds it into `bind` applications:

```lean
syntax (name := asmStx) "asm " Lean.Parser.Term.doSeq : term

private def seqItems (s : Syntax) : Array Syntax :=
  let inner := if s.getKind == ``Lean.Parser.Term.doSeqBracketed then s[1] else s[0]
  inner.getArgs.filter (·.getKind == ``Lean.Parser.Term.doSeqItem)

private partial def asmSeq (items : Array Syntax) (i : Nat) : MacroM (TSyntax `term) := do
  if h : i < items.size then
    let el := items[i][0]; let isLast := i + 1 == items.size
    if el.getKind == ``Lean.Parser.Term.doExpr then
      let e : TSyntax `term := ⟨el[0]⟩
      if isLast then return e else `(Asm.bind $e (fun _ => $(← asmSeq items (i+1))))
    else if el.getKind == ``Lean.Parser.Term.doLetArrow then
      let decl := el[3]
      let x : TSyntax `ident := ⟨decl[0]⟩
      let e : TSyntax `term := ⟨decl[3][0]⟩
      `(Asm.bind $e (fun $x => $(← asmSeq items (i+1))))
    else Macro.throwError s!"asm: unsupported step of kind {el.getKind}"
  else Macro.throwError "asm: empty block"

@[macro asmStx] def expandAsm : Macro := fun stx => do
  return (← asmSeq (seqItems stx[1]) 0).raw
```

That is the entire weaving mechanism. It supports statement sequencing and `let x ← e`
binding; it reuses Lean's indentation-sensitive layout, so authoring looks like `do` and is
formatted like `do` by every existing tool.

### 5.3 What authoring actually looks like

All five programs below compiled with exit code 0.

```lean
/-- Both indices INFERRED: the author writes no context annotation at all. -/
def ownerWritesThenLends := asm
  store (Γ := [Cap.write]) 0
  lendRead 0
  load 0
  endRead 0
  store 0

/-- Contract stated explicitly (write in, write out) — the routine-signature shape. -/
def roundTrip : Asm [Cap.write] [Cap.write] Unit := asm
  lendRead 0
  load 0
  endRead 0
  store 0

/-- Donating the write away: the post-index records it. -/
def donate : Asm [Cap.write] [Cap.read 1] Unit := asm
  store 0
  lendRead 0
  load 0

/-- Nested loans, partial discharge: write returns only after the LAST discharge. -/
def twoLoans : Asm [Cap.write] [Cap.write] Unit := asm
  lendRead 0
  lendRead 0
  load 0
  endRead 0     -- one loan still outstanding: a `store 0` here would not elaborate
  load 0
  endRead 0
  store 0

/-- Independent regions do not interfere. -/
def twoRegions : Asm [Cap.write, Cap.write] [Cap.write, Cap.write] Unit := asm
  lendRead 0
  store 1
  load 0
  endRead 0
  store 0
```

Three measured facts about this, each of which was a live risk:

1. **Indices are inferred when not annotated.** `#check` on the un-annotated program
   reports `Asm [Cap.write] (discharge (lend [Cap.write] 0) 0) Unit` — Lean propagated the
   index through five binds with no annotation from the author. Authors write the contract
   at routine boundaries and nothing in between.
2. **Computed indices unify.** The post-index of `lendRead` is the *application* `lend Γ i`,
   and the next step's obligation is `canStore (lend [Cap.write] 0) 0 = true`. Elaboration
   reduces these without help. This was the risk most likely to make the approach miserable
   in practice and it did not materialise at this scale. It is *not* established at
   realistic scale (§5.5).
3. **Ghost operations emit nothing.** `#eval (ownerWritesThenLends []).2` printed
   `[Instr.st 0, Instr.ld 0, Instr.st 0]` — the two lend/discharge steps contributed zero
   instructions.

### 5.4 Obligation dispatch at the bind — the centre of the design, measured

Each access operation takes its authority obligation as an auto-param whose tactic is the
dispatcher:

```lean
macro "borrow_auto" : tactic => `(tactic| first | decide | omega | skip)

def store (i : Nat) {Γ : Ctx} (_h : canStore Γ i = true := by borrow_auto) : Asm Γ Γ Unit
def load  (i : Nat) {Γ : Ctx} (_h : canLoad  Γ i = true := by borrow_auto) : Asm Γ Γ Unit
```

`first | decide | omega | skip` is the fast path followed by a deliberate fall-through: when
neither tactic closes the goal, `skip` leaves it open, and Lean reports it. Four measured
outcomes:

| Control | Program | Measured result |
| :-- | :-- | :-- |
| NEG-1 | `lendRead 0` then `store 0` | `error: could not synthesize default value for parameter '_h' using tactics` + `error: unsolved goals ⊢ canStore (lend [Cap.write] 0) 0 = true` |
| NEG-2 | `lendRead 0; load 0` against a declared `Asm [write] [write]` | error, but the goal reads `⊢ canLoad (?m.18 x✝) 0 = true` — a metavariable, not the real problem |
| NEG-4 | `store 0` with `Γ` an opaque variable | `error: unsolved goals  G : Ctx ⊢ canStore G 0 = true` |
| POS-5 | same, with the author passing a proof: `store 0 h` where `h : canStore G 0 = true` | compiles |

NEG-1 and NEG-4 together are the design's thesis, demonstrated. **The same mechanism does
both jobs**: where the borrow structure is statically known, `decide` closes it silently and
the author sees nothing (this is Rust's borrow checker, as the fast path); where it is not,
the author is handed the exact proposition at the exact source position and supplies a proof
(POS-5). There is no third outcome, no `unsafe`, and no escape hatch — because the fallback
is not an escape, it is work.

This is also the concrete answer to why an elaborator beats `do`: `do` has nowhere to put a
failed side condition except a type error. A dispatching elaborator has somewhere to put it —
a goal.

### 5.5 What the measurement did **not** establish

Stated plainly, because a spike that only reports its successes is worthless:

- **Scale.** The largest program measured is seven steps over two regions with literal
  indices. Elaboration cost of index reduction over a realistic routine — `Stdlib/Zlib/X86_64.lean`
  is 2,245 lines — is unmeasured. If index normalization is quadratic in program length, the
  approach fails on exactly the modules that need it most. **This is the first thing an
  implementing task must measure, before anything else is built.**
- **Error quality on index mismatch is poor.** NEG-2 — the *most common* author mistake,
  forgetting to discharge — produced a goal mentioning a metavariable rather than "region 0
  still has 1 outstanding loan". Usable errors here need either a custom elaborator that
  checks the index before elaborating the obligations, or a post-hoc index-diff reporter.
  Unbudgeted and non-trivial.
- **No real instruction, no real address, no `MemoryPerm`.** The spike's `store`/`load` take
  a region *number*. Real accesses take a `MemRef`, evaluate to an address, and must be tied
  to a `MemoryPerm` at that address. That connection is MH3's `AccessOK`, and it is where the
  actual difficulty lives — the spike measured the weaving, not the checking.
- **No control flow.** Straight-line only. §2.3's joins and loops are unmeasured.

## 6. Relationship to MH3 — this subsumes it, and that is a finding, not a collision

**Status**: MH3 (`docs/tasks/MH3-capability-authoring-surface.md`) is `ready` and **in
flight in an agent worktree at the time of writing**, uncommitted: `Gasm/Targets/X86_64/CheckedAsm.lean`
(497 lines), `Stdlib/SmolAlloc/MemSafety.lean`, `Tools/CheckMemBypass.lean`, and
`scripts/mem_bypass_allowlist.txt`. None of it is on `main` (verified: no occurrence of
`CheckedAsm`, `RegionSpec`, `AccessOK`, or `MemSafe` in any `.lean` file in the main tree).
Line references below are to that uncommitted file and will move.

Read directly, MH3's shape is:

```
CheckedInstr   (Γ : Frame) (Inv : X86_64MachineState → Prop)   -- one instruction, fixed Γ
CheckedProgram (Γ : Frame) (Inv : ...) := List (CheckedInstr Γ Inv)
```

with `RegionSpec` (anchor, len, share), `Frame := List RegionSpec`, `shareAllows`,
`AccessOK`, a decidable `literalAccessOK` with an `AccessOK.ofLiteral` soundness theorem, a
`mem_bounds`-style auto-param, `erase`, `grantedFootprint`, and `MemSafeStatement`.

**The verdict: the borrow monad is MH3's `CheckedProgram` with `Γ` promoted from a parameter
to an index. They are the same artifact.** `List (CheckedInstr Γ Inv)` is precisely the
index-preserving special case `Asm Γ Γ`, which is what a *non*-flow-sensitive frame means.
Concretely, of MH3's surface:

- `RegionSpec`, `Frame`, `AccessOK`, `literalAccessOK`, `AccessOK.ofLiteral`, the auto-param,
  `erase`, `grantedFootprint`, `MemSafeStatement`, the bypass ledger and its gate: **all
  carry over unchanged.** The borrow model adds nothing to and removes nothing from any of
  them.
- `CheckedProgram Γ Inv := List (CheckedInstr Γ Inv)` becomes `Asm Γ₁ Γ₂ α`, with the old
  type recovered at `Γ₁ = Γ₂`.
- `shareAllows` needs one change under §2.2's re-reading: `.Locked` currently maps to `true`
  for both kinds, which is right for authority and silent about the atomicity obligation. It
  would additionally demand that the access kind be `.rmw`.

This is **not** a Law 12 unlinked twin, and it must not be allowed to become one. The
correct sequencing, recommended: **let MH3 land as designed and approved.** It is the
approved v1 line (ADR-0040 Q1), it is being built now, and every piece of it except the
`CheckedProgram` type constructor survives the upgrade verbatim. The borrow model is then a
follow-on that replaces one type and keeps the rest — the "nothing in v1's shape is discarded
by the upgrade" contract `docs/MEMORY_HOOK.md` §4.3 already committed to, honoured. Stopping
MH3 to rebuild it as an indexed monad would discard four working pieces to change one.

The one coordination item that cannot wait: **MH3's `shareAllows` treatment of `.Locked`, and
whether MH3's `CheckedProgram` is named in a way that survives becoming an index.** Both are
one-line concerns and both should be raised with the MH3 agent rather than resolved by a
later rewrite.

## 7. Does the DSL make ill-formed programs *unwritable*?

The claim to test: if the DSL is the sole authoring surface, a malformed chain is not merely
unprovable but unwritable, because generated syntax cannot be mis-indexed the way a
hand-written `bind` chain can.

**Partly. The strong reading does not hold; a weaker and still valuable one does.**

What the DSL genuinely prevents is *mis-weaving*: an author cannot write `Asm.bind` with
mismatched intermediate indices, because they never write `Asm.bind` at all — the macro
generates every one, and each is generated from adjacent steps, so the intermediate index is
by construction the previous step's post-index. Mis-sequencing is unrepresentable in the
surface syntax. That is real.

What it does not prevent is **writing a step whose obligation is false**, because the
obligation is not a syntax error — it is a goal. NEG-1 is not "unwritable"; it is written,
and then rejected at elaboration. The distinction matters because it is the distinction
between a *parser* and a *checker*, and the whole design's value is that it is a checker
with a proof-shaped fallback. A surface in which the bad program could not be typed at all
would also be a surface in which the *hard* program could not be typed at all — and the hard
program is the one we need (POS-5).

So: Law 11's "fails to assemble" is satisfied at elaboration, not at parse. That is the same
bar `docs/MEMORY_HOOK.md` §4.2 already sets and ADR-0040 accepted. It is not weaker for being
at elaboration: no bytes are emitted, the artifact is unbuildable, and the build is red.

**Cost of making the DSL the only surface.** The mechanism already exists in MH3's design and
is being built: the ratcheted bypass ledger (`scripts/mem_bypass_allowlist.txt`) plus a gate
that fails CI when a memory-operand smart constructor is used outside the ledger. Sole-surface
status is then "ledger empty", which is monotone, measured, and defined — `docs/MEMORY_HOOK.md`
§4.5. The cost is not the mechanism; it is the migration, and PA4 already owns it with a
ratified ordering (new/small modules first, `Stdlib/Zlib/X86_64.lean` last). Nothing in the
borrow model changes that cost. **Status**: ledger and gate are MH3 deliverables, unbuilt on
`main`.

### 7.1 Emit directly, or produce a term? — produce a term

Recommended: the DSL produces a value in the indexed monad, which carries the emission; it
does not emit bytes at elaboration.

The dichotomy as posed is false, and that is the reason: **the obligations are elaborated at
term-construction time either way.** Every auto-param in §5.4 runs when the term elaborates,
whether or not that term's *value* is a byte string. Emitting directly buys no additional
checking and costs composition — a routine that cannot be named as a value cannot be called,
inlined, or given a contract, and `erase : CheckedProgram → List SymbolicInstr`
(`docs/MEMORY_HOOK.md` §4.5) is precisely the seam that keeps the assembler, linker, decoder,
and fuzzers untouched. The spike's `Asm` is a writer monad over an instruction list for
exactly this reason, and it cost nothing.

### 7.2 What a failed obligation looks like to the author

An **error**, carrying the goal, at the failing step's source position (measured, §5.4). Not
a `sorry`, not a marker, not a warning. This is the right answer on gate grounds as well as
ergonomic ones: a marker would need a new gate to catch it, whereas an error is caught by
`lake build`, which every gate already depends on. The `sorry` route is worse still — it
would be caught by the axiom gate, but only after producing a *buildable* artifact, which is
precisely what Law 11 forbids.

The one refinement worth designing in: the DSL should accept an explicit per-step proof
escape (`store 0 h`, measured working in POS-5) so that the fallback is always "supply the
proof here", never "restructure the block to make `decide` work".

## 8. Shared-XOR-mutable and data races

**Status**: proposed theorem shape; no multi-thread machine exists. `docs/X86_MEMORY_MODEL.md`
§2.3 Decision 3's store-buffer machine is MT2's deliverable and is unbuilt, as is every
`MT` task.

Does shared-XOR-mutable make a data race unrepresentable? **For non-`Locked` regions, yes,
and the theorem has a clean shape.** For `Locked` regions, deliberately no — and that is the
correct outcome, not a gap.

Define a conflict in the standard way: two accesses from *different* threads whose footprints
overlap, at least one a store, not ordered by happens-before. The needed global invariant is
a partition of authority across threads, which is `DisjointTokens`
(`Gasm/Core/Permissions.lean:58-62`) lifted from one context to a family of them:

```
GlobalWF Θ  :=  for every address a,
                  at most one thread's context grants `write` over a, and
                  if any thread's context grants `write` over a, no other grants any share over a
```

The theorem shape:

```
theorem no_unsynchronized_race
    (Θ : ThreadId → Ctx) (h : GlobalWF Θ)
    (t₁ t₂ : ThreadId) (ht : t₁ ≠ t₂)
    (a₁ : MemAccessSpec) (h₁ : AuthorizedBy (Θ t₁) a₁)
    (a₂ : MemAccessSpec) (h₂ : AuthorizedBy (Θ t₂) a₂)
    (hover : Overlaps a₁ a₂)
    (hstore : a₁.kind = .store ∨ a₂.kind = .store)
    (hplain : ¬ IsSynchronized a₁ ∧ ¬ IsSynchronized a₂) :
    False
```

The proof is short and structural: a store is authorized only from `write`; `GlobalWF` says
no other thread holds any share over the same address; so `a₂` is unauthorized, contradicting
`h₂`. It needs no ordering reasoning whatsoever — **which is the point**. The races are
excluded by authority, before the memory model is consulted.

`IsSynchronized` is where `Locked` lives and where the theorem deliberately stops. A `Locked`
region admits concurrent stores from multiple threads; those accesses *are* conflicting in
the footprint sense, and they are safe because they are `.rmw`-kind — indivisible by
construction, per `docs/X86_MEMORY_MODEL.md` §2.3 Decision 1. So `Locked` accesses are
excluded from the conflict relation by hypothesis, and their safety is discharged by
atomicity rather than by this theorem. A borrow model that claimed to exclude *all* races
would have to exclude spinlocks, and Spike 8's whole verified computation is a spinlock
(`docs/SPIKES/SPIKE8_MULTITHREADING.md` §3).

**If this lands, the borrow model and the memory model discharge one obligation together**,
and the division is exact: the borrow model establishes that authored programs are
data-race-free on plain accesses; the memory model then only has to state *ordering* for the
synchronized ones. That is the difference between TSO mattering for safety and TSO mattering
only for ordering — the coordinator's read is correct. Two honest caveats. First, it requires
cross-thread capability transfer to be modelled at all (spawn hands regions to a child; join
returns them; a lock acquire dynamically grants), and none of that exists — it is MT2-shaped
work with no task. Second, `GlobalWF` is an invariant over *concrete addresses*, so it
inherits §11's aliasing gap in full: if two threads' region specs alias without the model
knowing, `GlobalWF` is false and the theorem says nothing.

## 9. Architecture neutrality — the ARM question

**Status**: analysis; `docs/TARGETS/ARM64.md` is reconnaissance, and no ARM target exists.

The vocabulary is neutral: `MemoryPermissions Arch` is already arch-parameterized
(`Gasm/Core/Permissions.lean:66`), and `MemoryPerm`/`DisjointRanges`/`DisjointTokens` mention
no architecture. The *authority* semantics of §2.1 are neutral too — "who may store" is not a
memory-model question, and the four rules contain no ordering claim. §8's race theorem is
likewise ordering-free by construction, which is the strongest neutrality result here: it
holds on any architecture, because it never mentions one.

**Two places where an x86 assumption would enter if this design were written carelessly, both
on the `Locked` axis:**

1. **"Atomic = one indivisible access" is a TSO-shaped assumption.**
   `docs/X86_MEMORY_MODEL.md` §2.3 Decision 1 makes a locked RMW exactly one
   `MemAccessSpec` with `kind := .rmw`, so that interleaving between its read and write
   halves is unrepresentable. That is right for x86, where `LOCK`-prefixed RMW and memory-operand
   `XCHG` are single indivisible actions. It is **wrong for AArch64**, whose exclusive
   monitor is `LDXR`/`STXR` — a *pair* of instructions that can fail and must be retried.
   An ARM atomic increment is not one access; it is a loop. If `Locked`'s meaning is defined
   as "declares one `.rmw` entry", ARM cannot express its own atomics.
   The fix is available and cheap if taken now: define `Locked` by its **obligation** — "every
   access to this region is synchronization-ordered" — and let each target discharge that
   obligation its own way (x86: one `.rmw` entry; ARM: an exclusive-monitor pair with a
   retry-loop contract). §2.2's re-reading is written this way deliberately.
2. **Per-access ordering annotations.** `docs/X86_MEMORY_MODEL.md` §8 rejected a `MemOrder`
   field alongside the kind, correctly, because x86-TSO has no third value to express — and
   said explicitly that it "might" be needed for ARM. AArch64's `LDAR`/`STLR` carry
   acquire/release *per access*, which is exactly that third value. This is not a borrow-model
   decision, but the borrow model is the first design that would consume it (via
   `IsSynchronized`), so it is worth recording here that the rejection is x86-scoped and that
   `docs/TARGETS/ARM64.md` §7 independently reached the same conclusion from the other
   direction.

**Verdict: the borrow model is architecture-neutral, and the one place an x86 assumption
could enter — the definition of `Locked` — is defined obligationally in §2.2 precisely to
keep it out.** That framing was chosen with ARM in view and is worth stating explicitly so an
ARM implementor is not left inheriting an unstated assumption, which is the specific harm
`docs/TARGETS/ARM64.md` §7 warns about.

## 10. Demand, staging, and honest cost

### 10.1 The trigger

Named by the owner: *"isa scale up: we need multithreading and borrowing resolved."* This is
Law 5 demand, stated, not inferred. It extends the prerequisite set ADR-0039 ratified (P2
memory hook — landed as MH1; P3 decoder modularization; P4/P5 the unified
validation-and-calibration gate) with a fourth and fifth item, and it sits consistently with
ADR-0040's deferral: ADR-0040 accepted a bounded v1 line *with flow-sensitive typestate
deferred to PA2/PA3*, and this document is that deferred item arriving under its own demand.

**So the answer to "does the borrow model subsume ADR-0040's deferral or sit beside it" is:
it is the deferral, arriving.** It subsumes it (§6): MH3's v1 is the index-preserving special
case, and the upgrade discards nothing.

### 10.2 What actually blocks what

The demand is real, but it is not uniform across the expansion, and conflating the stages
would overstate the gate:

| Expansion stage | What it needs | State |
| :-- | :-- | :-- |
| Wave A — GPR-only ALU forms, no memory operands | Nothing from this document. `memAccesses _ := []` is their honest descriptor. | Unblocked today |
| Wave B — memory-operand forms | MH1 (landed) + MH3's checked authoring surface. Straight-line borrow index is a strict improvement but not a hard gate. | MH3 in flight |
| Memory forms authored inside loops over buffers | The straight-line borrow index, plus §2.3 item 3's loop rule | Unbuilt |
| Atomics, fences, anything multi-threaded | MT1 + MT2 + §8's cross-thread transfer | MT1/MT2 blocked; §8's transfer has no task |
| Branch-heavy authored routines | §2.3 item 2's join obligations — this is PA2/PA3 | Unstarted |

### 10.3 Cost, stated as a large honest number rather than a small optimistic one

Estimates are in agent-days of focused work, and they are estimates, not measurements. The
uncertainty is dominated by two unmeasured things (§5.5's scale question and the error-message
work), and both could double their line items.

| Piece | Estimate | Confidence |
| :-- | :-- | :-- |
| Borrow context type, four operations, decidable predicates, index lemmas | 3–5 days | Reasonable — the spike is most of the shape |
| The weaving DSL macro, hardened (positions, escapes, error messages) | 4–8 days | Low. The spike's 30 lines took under an hour; usable *errors* (§5.5) are the real cost and are unmeasured |
| Elaboration-cost measurement at realistic scale, and remediation if it is bad | 2 days to measure, unbounded to fix | **Lowest confidence item in the table.** If index normalization is superlinear this is a redesign, not a fix |
| Promoting MH3's `CheckedProgram` to the index; everything else of MH3 unchanged | 3–5 days, *after* MH3 lands | Reasonable — one type constructor |
| `MemSafe` re-proof over the indexed form for the pathfinder routine | 5–10 days | Moderate |
| Joins and loops (§2.3 items 2–3) | This is PA2/PA3's scope, not a line item here | — |
| Cross-thread transfer + §8's theorem | Blocked on MT2, which is blocked on XM1 | — |

**The honest headline: straight-line borrow-checked authoring is weeks, not months — call it
three to five weeks of agent-time on top of MH3, with one item (elaboration scale) capable of
turning that into a redesign. The complete borrow model, including control flow and threads,
is months, and most of that time is PA2/PA3 and MT2 — work that is already queued for other
reasons and is not made longer by this design.** Gating *all* ISA expansion on the complete
model would be a mistake; gating Wave B on MH3, and loop/branch-heavy memory authoring on the
straight-line index, matches the actual dependencies.

### 10.4 Law 8, confronted rather than managed

The risk is building an elaborator ahead of a program that needs it. Three facts bear on it,
and the third is the one that actually settles it:

- The demand is named by the owner (§10.1). That removes the "speculative" charge but not the
  "premature" one.
- Instructions are already authored in Lean, so this replaces an authoring surface rather than
  inventing one. **This mitigation is weaker than it sounds and should not be leaned on**: what
  exists today is `Stdlib/Zlib/X86_64.lean`-style raw `SymbolicInstr` lists, and the surface
  being replaced is *MH3's*, which does not exist on `main` yet either. Replacing an
  unbuilt surface with a different unbuilt surface is not the same as replacing a used one.
- **The decisive fact is different: the structural commitment was already made and is
  dormant.** `BlockM` (`Gasm/Core/BlockM.lean:25`) is the indexed monad, ratified in
  `docs/API_STATE_MODELS.md` §2, with zero consumers since it was written. Under Law 8 that
  is *already* a dead abstraction — an inert typeclass-shaped commitment with no operational
  path. The borrow model does not add speculative structure; it is the first thing that would
  make an existing piece of speculative structure real, or prove it should be deleted. That
  is the opposite of the wsc failure mode: wsc built ISA breadth on an unvalidated model,
  whereas this validates a model already in the tree before breadth is built on it.

Against that, the Law 8 charge that *does* stick and should be answered by sequencing rather
than argument: **the DSL should not be built before §5.5's scale question is measured.** A
weaving elaborator that cannot elaborate `Stdlib/Zlib/X86_64.lean` in reasonable time is a
facade regardless of how sound it is.

### 10.5 The VISION §4 DSL claim, checked rather than inherited

`docs/VISION.md` §4 states the rule: *"anywhere there is a population of artifacts — even a
closed population, even a population of one — reach for a DSL"*, with a closed population
earning exhaustive language-level theorems and the instruction registry's roundtrip gate named
as the exemplar.

Checked, and it holds — with one qualification that matters. The operation population *is*
closed and small: lend, reclaim, donate, split, load, store, and (for `Locked`) a synchronized
access. Seven constructors, and the closure argument is not merely an assertion — it is forced,
because `MemAccessKind` is `load | store` (`Gasm/Targets/X86_64/MemoryCell.lean:41-43`) plus
`docs/X86_MEMORY_MODEL.md` §2.3's proposed `.rmw`, and `memAccesses` is defaultless, so no
instruction can introduce an eighth access shape without a compile error. The index shape is
likewise known and finite. So language-level theorems — "every well-typed `Asm` program's
dynamic footprint lies inside its entry frame", "no two authorized concurrent plain accesses
conflict" — are proven once about the language and apply to every program written in it. That
is the sublinear-cost mechanism applied to the safety layer, and it is the strongest form of
the VISION §4 argument.

**The qualification**: the theorems that are cheap this way are the ones about *authority
bookkeeping*, which is the decidable part. The obligations that remain per-program are the
aliasing and dynamic-bounds ones (§11), and those do not become language-level theorems — they
become per-routine proof obligations, one per non-literal access. So the leverage is real but
partial: the DSL makes the *borrow* reasoning free and leaves the *pointer* reasoning
per-program. Claiming otherwise would be the overclaim this project's Law 8 exists to catch.

## 11. What this cannot catch

Stated in full, because the recommendation is worthless without it.

1. **Aliasing between regions — the fundamental gap.** The index tracks region *identifiers*.
   Two regions may denote the same bytes at runtime, and no amount of index discipline detects
   it. Rust does not have this problem because ownership provenance is carried by the type
   system from allocation onward; assembly has no such provenance — a register is a 64-bit
   number. The obligation is `DisjointTokens` over concrete addresses, discharged against a
   routine's precondition, per program. **This is the one place where "not needing Rust" is
   strictly false: Rust gets disjointness free from provenance, and this design must prove it.**
2. **Register-to-register copies create untracked anchors.** `mov rbx, rax` makes `rbx` a second
   name for a region anchored at `rax`. Region identity must therefore *not* be the anchor
   register; the anchor belongs in the routine's invariant `Inv`, related to region identity by
   an author-stated fact — which is MH3's existing entry-anchored design and inherits its
   limitation exactly (`docs/MEMORY_HOOK.md` §4.3).
3. **Dynamic bounds.** Whether a loop index is within a region is not decidable and never was;
   it is discharged by the loop invariant. Unchanged from ADR-0040's accepted line.
4. **Loans across loop back-edges** (§2.3 item 3). Strictly weaker than NLL.
5. **Anything about `Locked` regions' actual safety.** §8's theorem excludes them by
   hypothesis; their safety rests on atomicity, which is the memory model's obligation, not
   this one's.
6. **Self-modifying code, and the loader.** `X86_64Mem.initRegion`
   (`Gasm/Targets/X86_64/MemoryCell.lean:132`) installs an image wholesale, outside any
   borrow context. Legitimate, and outside the model.

## 12. Rejected alternatives

- **A decidable borrow-check pass over an ordinary-monad program** — author in `StateM Ctx`
  where `do` works, emit a program, then gate on `borrowCheck prog = .ok` by `decide`. This is
  genuinely attractive and nearly made it to the recommendation: it costs zero ergonomics, and
  "obligation dispatch" is arguably more literal in it. Rejected because the check is
  *whole-program and posterior*: a failure reports at the end of a routine rather than at the
  offending step, the fast/slow-path split disappears (a `decide` over the whole program either
  closes or does not, with nothing to hand the author), and it cannot express a routine whose
  *contract* is index-changing — which is what donation and cross-call lending are. It remains
  the right fallback if §5.5's scale measurement kills the indexed approach, and is recorded
  here for that reason.
- **A capability value with a phantom region tag, rank-2-quantified (`runST`-style)** — keeps
  an ordinary `Monad`, so `do` works. Rejected on the linearity argument of §3: the capability
  is still a value, so `let c := cap; use c; use c` duplicates it, and phantom tags prevent
  region confusion without preventing reuse. It solves a different problem.
- **Enforcing linearity via a linear-types elaborator extension.** Out of scope by an order of
  magnitude, and unnecessary once the index carries the discipline.
- **Making `Locked` a level between `ReadOnly` and `Exclusive`.** It admits stores, so it is not
  below `Exclusive`; it admits multiple holders, so it is not above `ReadOnly` in the lattice's
  own order. Forcing it into a total order loses exactly the property that distinguishes it
  (§2.2).
- **Building this instead of MH3, or beside MH3.** §6. Beside is a Law 12 twin; instead
  discards four working pieces to change one.
- **Waiting for PA2/PA3 before any of it.** Same argument ADR-0040 already accepted and for the
  same reason: it sequences all enforcement behind unstarted work.

## 13. Questions for the owner

1. **Q1 — sequencing against MH3.** Recommended: MH3 lands as approved; the borrow model is a
   follow-on that promotes `CheckedProgram`'s `Γ` to an index and keeps everything else (§6).
   The alternative — redirect the in-flight MH3 agent now — discards working parts. Confirm the
   follow-on sequencing, or rule the other way before MH3 completes.
2. **Q2 — the `Locked` re-reading (§2.2).** Recommended: `Locked` stops meaning "exclusive but
   atomic" and starts meaning "shared-mutable, safety discharged by atomicity", defined by its
   obligation rather than by x86's one-`.rmw`-entry mechanism so AArch64's `LDXR`/`STXR` pair
   can satisfy it (§9). This is a semantic change to a landed constructor and needs a ruling.
3. **Q3 — the measurement gate.** Recommended: no DSL is built until elaboration cost at
   realistic program length is measured (§5.5, §10.4). This makes the first task a measurement
   task with an explicit kill criterion, and delays usable output by a few days. Confirm that
   trade.
4. **Q4 — one counted-loan abstraction, or two (§3.2).** The tree's `activeBorrows`
   (`Gasm/Core/Obligations.lean:43-53`) gates arena *lifetime* on outstanding sub-allocations;
   this design gates *authority* on outstanding readers. Same shape, different subject.
   Factoring them into one abstraction with two instances is Law 12's stated preference; leaving
   them separate is defensible because lifetime and authority genuinely differ. No recommendation
   is offered — this is a judgement call about how much generality is worth its cost, and it is
   not on any critical path. Worth a ruling only so that it is decided rather than drifted into.

## 14. Tracking

**Status**: the tasks below are filed with this design and are unstarted.

| Task | Track | Content | After |
| :-- | :-- | :-- | :-- |
| `docs/tasks/BR1-borrow-index-feasibility.md` | proof-arch | §5.5's kill-criterion measurement, then the borrow context, four operations, and the weaving DSL | MH1 |
| `docs/tasks/BR2-borrow-authoring-upgrade.md` | proof-arch | §6's promotion of MH3's `CheckedProgram` to an index; `MemSafe` re-proof on the pathfinder | BR1, MH3 |
| `docs/tasks/BR3-cross-thread-capability-partition.md` | concurrency | §8's `GlobalWF` and the no-unsynchronized-race theorem shape | BR1, MT2 |

PA2 (`docs/tasks/PA2-step-lemma-composition-design.md`) owns §2.3's joins and loops and should
treat the index-equality-at-join obligation as a candidate building block. PA4
(`docs/tasks/PA4-capability-adoption.md`) remains the migration epic and is unaffected in
ordering. MT1/MT2 (`docs/tasks/MT1-atomic-primitives.md`,
`docs/tasks/MT2-multithreaded-machine-state.md`) own the atomicity axis; §2.2's re-reading of
`Locked` is a coordination item with them, not a competing design.
