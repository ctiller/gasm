# BORROW_MODEL: Provenance, Borrowing, and Obligation Dispatch

- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/REVIEW.md#law-5-the-stop-and-design-invariant
- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity--anti-facade-law-no-dead-abstractions-or-mock-verification
- REF: docs/REVIEW.md#law-12-connection-theorem-mandate-no-unlinked-twins
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#11-capability-splitting-and-joining-laws
- REF: docs/API_STATE_MODELS.md#2-the-indexed-typestate-monad-blockm
- REF: docs/MEMORY_HOOK.md#4-layer-a-assemble-time-capability-enforcement
- REF: docs/MEMORY_PROVENANCE.md#12-hierarchical-provenance--active-borrows
- REF: docs/X86_MEMORY_MODEL.md#23-the-shape-mt1mt2-build-this-documents-structural-decisions
- REF: docs/SPIKES/SPIKE8_MULTITHREADING.md
- REF: docs/VISION.md#4-tractability-modular-contracts-composed-proofs
- REF: docs/TARGETS/ARM64.md#7-what-is-settled-for-x86-only-versus-what-arm-must-decide

## 1. Status and scope

**Status**: this is a design document, not a report of built machinery. **No borrow mechanism,
pointer type, transmogrification operation, or lock invariant exists in the tree.** Everything
described as existing was verified by reading the tree or running commands at commit `46b3a60`
(2026-08-28); everything proposed carries its own `**Status**:` line. Two things are reported as
*measured* — the indexed-monad authoring spike (§6) and the pointer-forgeability spike (§2.3).
Both were compiled at this repository's pinned toolchain (`leanprover/lean4:v4.33.1`) in a
scratch directory, are deliberately **not** in the tree, and have their sources reproduced inline.

**§9's mutex is the sharpest place to state what is and is not built**: it depends on three
mechanisms, and **all three are absent from the tree today**. Nothing here should be read as
saying a lock has been verified.

**The owner's directives**, verbatim:

> *"do the memory hooks distinguish read and writeability? (and can we delegate readability when
> we have writeability safely?) -- my target is to not need rust"*

> *"i'm wondering about a borrow model being an obligation dispatch / the owner starts out with
> capability write / if it lends a read, then it loses the write capability (but retains read) /
> only when all reads are discharged does it regain write / and it can donate write"*

> *"on lean not being linear: yes, and that's why the intent for obligations is to flow through a
> monad"*

> *"can we make our own dsl shape for weaving these monads, since we know their shape?"*

> *"regarding memory safety - my assumption is that we'd have a typed/provenanced pointer type
> that's required to read to/from at all, correct?"*

> *"transmogrification -- how can i turn provenance in one system to provenance in another (we
> have this instance: smol allocates from virtual alloc blocks), and how can i declare a bundle of
> bytes to now have a type -- the latter gets us to proof carrying memory addresses"*

> *"i think the shape of it is a special kind of borrow with an obligation that discharges the
> hold on the underlying memory (and maybe forces a destruction operation)"*

> *"by proof carrying memory addresses i'm thinking of 'when this atomic word is 1 the thread that
> set it has the mutex'"*

And the Law 5 demand trigger:

> *"isa scale up: we need multithreading and borrowing resolved"*

### 1.1 The direct answer to the first question

**No.** The vocabulary distinguishes read from write; nothing enforces the distinction, and
nothing delegates. Verified:

| Fact | Evidence |
| :-- | :-- |
| The share vocabulary exists | `PermissionShare := ReadOnly \| Exclusive \| Locked` (`Gasm/Core/Permissions.lean:24-28`) |
| Capability tokens exist | `MemoryPerm base len share` (`Gasm/Core/Permissions.lean:32-34`) |
| Splitting is **spatial only** | `MemoryPerm.split` cuts `[base, base+len)` at `k` and carries *the same* `share` into both halves (`Gasm/Core/Permissions.lean:38-49`, return type at line 41). There is no `Exclusive → ReadOnly ⊗ ReadOnly` operation anywhere. **That is the missing primitive, and it is the whole of the owner's rules 2 and 3** |
| `split` does not *return* disjointness, though it is derivable | The result type records both ranges, so `DisjointRanges` follows by `omega` from the indices plus the existing `h_wrap` — but no disjointness proof is among the returned components. §7.3 needs one; adding it is small |
| Disjointness is stated | `DisjointRanges` (`:53-54`), `DisjointTokens` (`:58-62`), the invariant field of `MemoryPermissions` (`:66-68`) |
| The permission container has exactly one consumer | `ComposedState.perms` (`Gasm/Core/State.lean:31`). A tree-wide grep over `Gasm/`, `Stdlib/`, `Spikes/`, `Tools/` returns that line and one doc comment |
| No theorem connects a store to `Exclusive` | No occurrence of either name in any theorem statement in the tree |
| An indexed typestate monad **already exists and is dormant** | `BlockM Arch S₁ S₂ α` with `pure`/`bind`/`get`/`set` (`Gasm/Core/BlockM.lean:25,32,37,47,52`). Its only occurrence outside its own file is the `import` at `Gasm/Core/CFG.lean:20`. Atkey's parameterized monad, written in 2026, used by nothing |
| The access-descriptor layer exists and is live | `MemAccessKind := load \| store` (`MemoryCell.lean:41-43`); `MemAccessSpec` (`Memory.lean:81-84`); `memAccesses`, defaultless (`Instructions/Base.lean:66`); `storeFootprint`/`loadFootprint` (`Memory.lean:99-105`) |
| **Frame lemmas: 30 theorems, not 176** | `MemoryFrame/` holds 35 theorems, of which 5 are in `NegativeControl.lean`. The 30 are 28 covering the 14 memory forms (Mov 18, Call 4, Push 2, Pop 2, Ret 2) plus the 2 shared batch lemmas in `Common.lean`. **The 74 register-only forms declare `memAccesses _ := []` and are covered *in principle* by the batch lemmas, not individually instantiated** |
| `ReadsWithin` pins the whole post-state, and all 14 forms close | It carries a second conjunct, `StoreAgreeOn` (`MemoryFrame/Common.lean:56-59`, used at `:73-78`): two pre-states agreeing outside memory and on the declared load footprint write *identical bytes into* the declared store footprint. With `WritesWithin` bounding *where* `step` writes, the pair pins the post-state completely — outside the store footprint nothing changes; inside it the bytes are a function of the pre-state's non-memory fields plus the declared load footprint. **§7's typed views depend on exactly this strength**: a typed view's invariant is stable only if the bytes under it are determined by declared inputs |
| **`bv_decide` is at zero tree-wide** | All 20 remaining occurrences across four files are prose documenting its *absence*; no tactic invocation survives (`X86_64Mem.read64_write64_same` is now closed structurally), and `scripts/gate_allowlist.txt`'s `bv_decide` lines are comments, not live entries. Relevant here because §5's fast path is `decide` at Law 10 rung 2 — kernel-checked, no allowlist entry — and the tree's posture is that rung 4 has been paid down to nothing rather than accumulated |
| **`MemRef` is not a typed pointer, not even in embryo** | A public record of `base : Option Reg64`, `index`, `disp`, with default field values and no proof component (`Memory.lean:49-52`). Anyone can build any `MemRef`. What carries a citation is MH3's constructor — §10 |
| **The memory seal is tier 3, and the reason is measured** | `private mk ::` does not privatize auto-generated eliminators: `X86_64Memory.casesOn`/`.rec`/`.recOn` stay public and `m.casesOn (fun f => f)` yields the raw `Address → Byte` from any module. **But that leak is semantically empty**: `readByte` is public and total, so `fun a => X86_64Mem.readByte m a` is `rfl`-equal to the very same function — the bytes were never confidential, and hiding them was never the point. Tier 1 would have cost real axioms, since `opaque` has no definitional unfolding. What the seal buys is that every memory touch goes through a **named** function, making access sites enumerable — an auditable chokepoint, enforced by `Gasm/Targets/X86_64/MemoryFrameAudit.lean` (`MemoryCell.lean:52-71`). §2.3 holds the pointer type to that same standard |
| **A discharge check already exists, live and used** | `ArenaPageToken.activeBorrows : Nat` with `isSafeToRelease t := t.activeBorrows == 0` (`Gasm/Core/Obligations.lean:43-53`), designed in `docs/MEMORY_PROVENANCE.md` §1.2, exercised at `Stdlib/SmolAlloc/Spec.lean:46,101,126,149`. §7.2 argues this **is** §7's discharge check, written before the pattern was named |
| Zero atomics, zero memory model | `docs/X86_MEMORY_MODEL.md` §1.1: no `LOCK`, no `CMPXCHG`, no `XADD`, no fences; the only `XCHG` is register-register with `memAccesses _ := []`; **the document states plainly that nothing it specifies exists in Lean** |

Two corrections to earlier framing: `perms` sits on `ComposedState`, not `MachineState`; and
`MemoryCell.lean` is the landed MH1 hook, not a permission consumer.

---

## 2. The provenanced pointer — what is borrowed

### 2.1 Why this layer, and a correction to this document's own earlier verdict

An earlier revision concluded that the aliasing half of memory safety was **"strictly not
reachable, and that gap is fundamental"**, because assembly has no provenance: a register is a
64-bit number, and `mov rbx, rax` silently creates a second anchor.

**That argument was about the wrong layer and the conclusion was wrong.** It is true of *emitted
assembly* and false of the *authoring surface*. Emitted bytes have no provenance; the Lean term
that produced them can have as much as we give it. If a memory operand accepts only a `Ptr r`
value — if there is no way to dereference a bare 64-bit quantity at all — provenance is carried
in the Lean type and erased at emission, exactly as ghost tokens and the borrow index are. The
`mov rbx, rax` objection dissolves for a reason worth stating plainly: **under this design the
author never names a register as a pointer.** Register assignment is chosen at lowering, so no
authoring-level operation copies a pointer into an untracked second name.

What changes is *what the obligation is about*. Without typed pointers you must answer "do these
two 64-bit numbers alias", undecidable in general. With them you answer "are these two declared
regions disjoint", and regions are a closed, declared population — the condition `docs/VISION.md`
§4 names for language-level theorems.

### 2.2 The type

**Status**: proposed; nothing in this section exists.

```lean
/-- Unforgeable region identity. Created only by frame entry, by `split`, and by §7. -/
structure RegionId where
  private mk ::
  private ident : Nat        -- GENERATIVE, not address-derived: see §7.5
  private len   : Nat

def RegionId.length (r : RegionId) : Nat        -- lengths are public; creation is not

/-- Offset term: a literal displacement, or a register holding a runtime value. -/
inductive Ofs
  | lit (n : Nat)
  | dyn (reg : Reg64)

/-- A provenanced pointer: a region tag and an offset term, and NO ADDRESS. -/
structure Ptr (r : RegionId) where
  private mk ::
  ofs : Ofs
```

**The load-bearing decision is that `Ptr` carries no address at all.** It is not "an address plus
a tag"; it is a provenance and a displacement, and the concrete address is `anchor(r) + offset`,
computed at lowering from the frame's anchor register. Two consequences:

- **There is no `ofNat : UInt64 → Ptr r` to remember to leave out, because there is no `UInt64` in
  the type.** A design that stores an address and then declines to expose a constructor is one
  careless helper away from reopening; a design with no field of that type is not. Scope this
  precisely, though: it closes the *address-injection* hole by shape, and says nothing about
  conjuring a **region**, which is a different hole closed a different way — §2.3.
- **Lowering is a per-target detail rather than a commitment** (§13).

| Operation | Signature (sketch) | Note |
| :-- | :-- | :-- |
| grant | `basePtr : (r : RegionId) → Ptr r` | from a frame entry or §7 |
| offset | `Ptr.add : Ptr r → Nat → Ptr r` | **unchecked**, provenance-preserving |
| dynamic offset | `Ptr.addReg : Ptr r → Reg64 → Ptr r` | **unchecked**, provenance-preserving |
| dereference | `load/store : (p : Ptr r) → (w : MemWidth) → (h : inBounds r p w := by …) → …` | **checked here** |

Offsetting being unchecked preserves a ruling already made: `docs/MEMORY_HOOK.md` §2 boundary
decision 1 states address computation is free and the obligation attaches at dereference, because
`LEA` forms addresses without accessing memory. Nothing here narrows that.

### 2.3 What it must refuse — measured, and held to the chokepoint standard

**Status**: measured. Two files across a real module boundary at v4.33.1; the sealed module built
to `.olean`, the attacks compiled against it via `LEAN_PATH`.

**The standard is not "unrepresentable".** The `X86_64Memory` seal settled that question on
measured grounds (§1.1): its `casesOn` leak turned out to be *semantically empty*, because the
blessed API is public and total and returns the same function by `rfl`; and tier 1 would have cost
real axioms, because `opaque` has no definitional unfolding. What a seal in this codebase buys is
that the thing **cannot be reached without going through a named, audited operation**. That is the
bar applied below.

Twelve attacks:

| # | Attack | Result |
| :-- | :-- | :-- |
| A1 | `Ptr.mk (.lit 0)` from another module | **Rejected** — `Unknown constant PtrSpike.Ptr.mk` |
| A2 | anonymous constructor `(⟨.lit 0⟩ : Ptr r)` | **Rejected** — `Constructor for Ptr is marked as private` |
| A3 | `p.casesOn (fun o => o)` to **observe** the offset | **Compiles** — the same eliminator leak; harmless |
| A4 | `Ptr.rec` to **construct** a `Ptr` | **Rejected** — the motive must supply a `Ptr`, needing the private constructor |
| A5 | `(default : Ptr r)` | **Rejected** — `failed to synthesize Inhabited (Ptr r)` |
| A6 | `Classical.ofNonempty`; `Nonempty (Ptr r)` by `infer_instance` | **Rejected** — Lean does **not** auto-generate one |
| A7 | `RegionId.mk 0 999` — forging a region | **Rejected** — `Unknown constant PtrSpike.RegionId.mk` |
| A8 | `(h : r₁ = r₂) → Ptr r₁ → Ptr r₂` via `h ▸ p` | **Compiles** — correct: it demands a proof the regions are equal |
| A9 | the same structure `deriving Inhabited`, then `default` | **Compiles** — forges a pointer into *any* region |
| A10 | `r.casesOn (fun _ l => l)` — observing a region's private length | **Compiles** — harmless; lengths are public |
| A11 | `(basePtr r).add 9999` — forming an out-of-bounds pointer | **Compiles** — deliberate |
| A12 | dereferencing that pointer | **Rejected** — `could not synthesize default value for parameter '_h'` + unsolved goal |

**The decisive result is the A3/A4 pair.** `casesOn` is an *eliminator*: it observes. The memory
seal's property was about observation, so the leak hit it squarely. A provenance tag's property is
about **creation**, and no eliminator creates. The two seals face opposite directions, which is why
the same attack lands on one and not the other. That is structural, not luck — but it was measured,
because the memory seal's authors reasoned too.

#### The self-check the memory seal's resolution demands — and it changes the claim

The memory seal was not defeated by `casesOn` so much as revealed to have been protecting nothing,
because a public total operation already yielded the same thing. **Applying that test here changes
what this section can claim.**

**`Ptr r`'s constructor seal is semantically empty in exactly the same sense.**
`basePtr : (r : RegionId) → Ptr r` is public and total, so anyone holding `r` can already produce a
`Ptr r`; A1/A2/A4's rejections block nothing that `basePtr` does not hand over. **And that is
correct by design**: a pointer is not the capability, it is a cursor. Holding the *region identity*
is what authorizes. Reading the attack table as though `Ptr`'s privacy were load-bearing would
repeat the memory seal's original error one level up.

**The load-bearing seal is on `RegionId`, and its property is reachability, not unforgeability.**
The claim that survives is: *a `RegionId` cannot be obtained except through a named creation
operation* — frame entry, `split`, `alloc` (§7.3), or the environment axiom (§7.6) — **and every one
of those consumes a capability it already had.** Region identity is inhabited only relative to
something already granted; the chain bottoms out at the environment, where it is stated once and
audited. That is the same auditable-chokepoint property MH1 has, one level up: MH1's chokepoint
enumerates every memory *touch*, this one enumerates every provenance *creation*.

The audit predicate is correspondingly precise, and it is what the tier-3 lint checks: **no
declaration whose result mentions `RegionId` or `Ptr` positively without a `RegionId` among its
arguments.** That single predicate subsumes all three realistic regressions — a public constructor,
a `UInt64 → Ptr r` helper, and A9's `deriving Inhabited` (which is exactly such a nullary producer,
and the sharpest of the three, since this codebase derives `Inhabited` liberally: `MemWidth`,
`MemAccessKind`, `MemRef`, `SmolBlockHeader`, `SmolAllocState`).

**Tier 1 here would be worse than expensive; it would be self-defeating.** Making `RegionId`
`opaque` to force absolute unforgeability would remove definitional unfolding — and §6.3's measured
result that computed indices unify, and §5's whole `decide` fast path, *depend* on `r.length` and
the index transitions reducing. Sealing them opaquely would turn every obligation into an author
proof and destroy the fast path the design exists to provide. So tier 3 is not a grudging fallback
here: it is the only tier compatible with the mechanism.

**Retracting an earlier claim in this document**: a previous revision asserted "tier 1 against
forging, plus a tier-3 audit". That was wrong on both halves — the `Ptr` seal it credited is empty,
and the property that matters is a reachability property enforced by lint. **The correct claim is
tier 3, on the same measured grounds as the memory seal**, with the audit predicate above as its
content.

### 2.4 The residue — where free ends and per-program begins

- **Free by construction.** Distinct regions are disjoint: regions come only from frame entry
  (declared disjoint once via `DisjointTokens`), from `split` (disjoint by index arithmetic), and
  from §7. Every pointer operation preserves provenance.
- **Free by `decide`/`omega`.** Literal-offset bounds — MH3's landed special case, generalized past
  literal displacements by carrying the length in `RegionId`.
- **Per-access `omega`, against a number in the type.** A `dyn` offset owes
  `value(reg) + width ≤ r.length`, from the loop invariant. One local goal per dynamic access.
- **Per-routine, at the boundary.** That the anchors a routine is *handed* are disjoint is
  discharged by its caller; at the top, by the loader or allocator.
- **Genuinely residual.** Provenance introduced from outside: bytes from the OS, a device, or a
  parse — §7, where it can be named and gated rather than diffused.

**Revised verdict on aliasing**: it does not vanish, and calling it fundamental was wrong. It
collapses from an unbounded, undecidable, per-access question into a bounded per-routine boundary
condition plus per-dynamic-access arithmetic.

---

## 3. The borrow model — authority over time

### 3.1 The four rules

**Status**: proposed; nothing below exists.

Per region, one ghost capability state:

```
Cap  ::=  write            -- owner holds write and read
       |  read n           -- n read loans outstanding: read allowed, write refused
```

| Owner's rule | Operation | Effect |
| :-- | :-- | :-- |
| "the owner starts out with capability write" | initial state | `write` |
| "if it lends a read, then it loses the write capability (but retains read)" | `lend` | `write ↦ read 1`; `read n ↦ read (n+1)` |
| "only when all reads are discharged does it regain write" | `reclaim` | `read 1 ↦ write`; `read (n+1) ↦ read n` |
| "and it can donate write" | `donate` | the region leaves this context and appears in the donee's |

A borrow context is a list of such states keyed by the `RegionId` identity of §2.2. Two decidable
predicates are the entire authority check: a store is admitted exactly when the region is `write`;
a load for `write` and `read _` alike. Shared-XOR-mutable is that one line.

**§7.2 generalizes `read n` from a counter to a ledger of outstanding *views*, of which read loans
are the degenerate case.** That generalization is forced by transmogrification and it is the same
finding SmolAlloc's two ledgers produce independently; §3 is stated in the simple form first
because the four rules are the specification and they read better without it.

### 3.2 Does `Locked` fit the same lattice? — a different axis, and then a third point

**Status**: analysis of landed vocabulary plus proposed design; the constructor exists
(`Gasm/Core/Permissions.lean:27`), nothing consumes it.

**Axis 1 — authority**: who may load, who may store. The axis borrowing moves along.
**Axis 2 — atomicity and ordering**: `docs/X86_MEMORY_MODEL.md` §2.3 Decision 1 settled this on
`MemAccessKind` as a third constructor `rmw`; its §8 rejected a parallel ordering field.

`Locked` as written sits on **axis 2 wearing axis 1's clothes**: on authority it admits exactly
what `Exclusive` admits, so it is not a third point on that lattice.

**But there is a genuine third authority point, and `Locked` is the right name.** Not a level
between `ReadOnly` and `Exclusive` — the top of a second branch: a share held by **many** holders
**simultaneously**, all of which may store, whose race-freedom is discharged **dynamically by
atomicity** rather than statically by exclusion. `Locked` is not reachable by lending; a region is
`Locked` because it was created that way or handed over by a synchronization primitive; and every
access to it owes an atomicity obligation.

**§9 is where this definition is tested, and it needs one extension.** A mutex word is `Locked`,
but its *point* is a claim about a **different** region. Nothing in the definition above carries
that link. §9.2 supplies it.

### 3.3 What a loan is, and when it is discharged (the crux)

Rust knows when a borrow ends from lexical scope, tightened by NLL liveness. Straight-line assembly
has no scopes.

**A loan is a ghost index transition. It emits no bytes.** Measured: a program containing a lend and
a discharge emitted `[st 0, ld 0, st 0]` — the ghost operations contributed nothing.

**Discharge is forced at four places, none a scope:**

1. **The routine's declared post-index.** A routine typed "I give back what I was given" cannot
   elaborate with an outstanding loan — the shape the tree already states as
   `ObligationLedger.isValidAtReturn` (`Gasm/Core/Obligations.lean:79`). **Measured** (§6.4, NEG-2),
   with a poor message (§6.5). **§8 shows this is also what makes leaks compile errors.**
2. **Branch joins.** Both arms must arrive at the same index: an equality obligation, decidable when
   both are literal. The tree's control-flow vocabulary has this shape already
   (`CpuTerminator.jcc`, `docs/API_STATE_MODELS.md` §4). Rust computes this join by dataflow; here it
   is an obligation the fast path closes by `decide`. **That substitution is the design thesis in one
   instance.**
3. **Loops.** An earlier revision said loop bodies must be *index-preserving*. **That was too weak a
   rule and §8.1 corrects it**: the general rule is index-*parametric* over the iteration count.
4. **Call boundaries.** A callee's index contract is part of its type. **Status**: proposed; not
   spiked.

---

## 4. Confronting linearity directly

Lean is not linear. A `MemoryPerm` token is an ordinary value; `let p := tok; f p p` duplicates it
and no typing rule objects.

The resolution the owner named is right, and *why* is worth stating: **the resource that must not be
duplicated is moved out of value position into type position.** A value can be used twice; a type
index cannot be "used" at all — it is threaded by `bind`'s typing rule, the only way to sequence,
which mentions each intermediate exactly once:

```
bind : Asm Γ₁ Γ₂ α → (α → Asm Γ₂ Γ₃ β) → Asm Γ₁ Γ₃ β
```

Duplicating a value of type `Asm Γ₁ Γ₂ Unit` is harmless — sequencing the duplicate forces
`Γ₂ = Γ₁`, which fails. The substructural content lives in the *shape of composition*, not the
*uniqueness of a value*. This is Atkey's parameterized monad, as Ynot and Idris's `ST` use it.

**And the tree already contains it.** `BlockM` (`Gasm/Core/BlockM.lean:25`) is exactly this
signature, dormant since written. The borrow model is not a new structural commitment; it is the
first consumer of a structure already ratified in `docs/API_STATE_MODELS.md` §2 and sitting
unused — which materially changes the Law 8 calculus (§14.3).

**This is also what makes §7's handles safe without linearity** (§7.5): a duplicated handle does not
help, because authority is checked against the index, not the handle.

### 4.1 The alternatives, weighed

**Typestate over an explicit map.** Rejected: because the map is a value, nothing forces the author
to thread the *updated* map. Reusing the old one is a well-typed program that has forgotten the loan.

**Ghost loan counters as free-standing data.** Rejected as standalone: the counter can be
re-derived, ignored, or reset. It survives *as the content of the index*.

**Indexed monad.** Recommended. Costs: `do` does not work (§6), and index unification must reduce
computed contexts (measured at small scale, §6.3; unmeasured at realistic scale, §6.5).

### 4.2 Prior art in the tree: `activeBorrows`

`docs/MEMORY_PROVENANCE.md` §1.2 specifies an arena tracking `activeBorrows : Nat`, gated on zero
for release; realized at `Gasm/Core/Obligations.lean:43-53` and exercised at
`Stdlib/SmolAlloc/Spec.lean:101,126,149`.

**What it demonstrates is evidence rather than argument.** It is a value-level counter threaded
through an ordinary state record. Nothing in its type prevents a transition from constructing the
successor with the old count, or with no increment — the increments are correct because they were
written correctly, not because anything checks them. That is §4.1's objection stated against a real,
working, in-tree instance, and it is why the borrow model's counter belongs in an index: a
mis-threaded arena count leaks; a mis-threaded borrow count races.

§7.2 revisits it now that the allocator is a *consumer* rather than an analogue.

---

## 5. What the index is, and what it is not

**Status**: proposed.

The index is a **static, syntactic** borrow context keyed by the `RegionId` identity §2.2 defines.
It is **not** the machine state and **not** `ComposedState.perms`.

- **It erases completely** — the zero-cost-proof-erasure shape `docs/API_STATE_MODELS.md` §1
  establishes, and why a loan costs zero instructions (measured, §6.3).
- **It is decidable.** Every transition is a total function on a finite structure of literals, so
  authority predicates and index equality close by `decide` — Law 10 rung 2, kernel-checked, no
  allowlist entry. "Rust's borrow checker as the fast path" made concrete.
- **It says nothing about aliasing on its own.** §2 is what makes region identities mean something.

The connection to the machine is a theorem: the index-tracked context must grant the footprints the
descriptors declare — MH3's `MemSafe` shape (`docs/MEMORY_HOOK.md` §4.4), unchanged.

---

## 6. The weaving DSL — measured, not asserted

**Status**: measured spike; **not in the tree and not proposed for the tree in this form**. Real
region identifiers, widths, `MemRef`s and `MemoryPerm` backing are abstracted away.

### 6.1 Does Lean's `do` work? No, and the failure is clean

`do` requires `Monad m` with `m : Type u → Type v`. An indexed monad is `Ctx → Ctx → Type → Type`.
Measured: `failed to synthesize instance of type class Pure (Asm [Cap.write] [Cap.write])` —
unambiguous and immediate, not a subtle mis-elaboration.

### 6.2 The DSL: Lean's own `do` *syntax*, elaborated to indexed binds

**Yes, and it is about thirty lines, because Lean's `doSeq` parser can be reused verbatim.**

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

It reuses Lean's indentation-sensitive layout, so authoring looks like `do` and is formatted like
`do` by every existing tool.

### 6.3 What authoring actually looks like

All compiled with exit code 0.

```lean
/-- Both indices INFERRED: the author writes no context annotation at all. -/
def ownerWritesThenLends := asm
  store (Γ := [Cap.write]) 0
  lendRead 0
  load 0
  endRead 0
  store 0

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

1. **Indices are inferred when not annotated** — `#check` reports
   `Asm [Cap.write] (discharge (lend [Cap.write] 0) 0) Unit`, propagated through five binds.
2. **Computed indices unify** — the obligation `canStore (lend [Cap.write] 0) 0 = true` reduces
   without help. The risk most likely to make this miserable did not materialise *at this scale*.
3. **Ghost operations emit nothing** — `[Instr.st 0, Instr.ld 0, Instr.st 0]`.

### 6.4 Obligation dispatch at the bind — the centre of the design, measured

```lean
macro "borrow_auto" : tactic => `(tactic| first | decide | omega | skip)
def store (i : Nat) {Γ : Ctx} (_h : canStore Γ i = true := by borrow_auto) : Asm Γ Γ Unit
```

`skip` is a deliberate fall-through: when neither tactic closes the goal, Lean reports it.

| Control | Program | Measured result |
| :-- | :-- | :-- |
| NEG-1 | lend then store | `unsolved goals ⊢ canStore (lend [Cap.write] 0) 0 = true` |
| NEG-2 | lend, load, against a write-in/write-out contract | error, but the goal reads `⊢ canLoad (?m.18 x✝) 0 = true` — a metavariable |
| NEG-4 | store with an opaque context | `unsolved goals  G : Ctx ⊢ canStore G 0 = true` |
| POS-5 | the same, author passing `h : canStore G 0 = true` | compiles |

NEG-1 and NEG-4 together are the thesis. **The same mechanism does both jobs**: where the structure
is statically known, `decide` closes it silently; where it is not, the author gets the exact
proposition at the exact position and supplies a proof. No third outcome, no `unsafe` — the fallback
is not an escape, it is work.

This is why an elaborator beats `do`: `do` has nowhere to put a failed side condition except a type
error. A dispatching elaborator has somewhere to put it — a goal.

### 6.5 What the measurement did **not** establish

- **Scale.** Seven steps, two regions, literal indices. Cost over a realistic routine
  (`Stdlib/Zlib/X86_64.lean` is 2,245 lines) is unmeasured. If index normalization is superlinear
  the approach fails on exactly the modules that need it. **First thing an implementing task must
  measure.**
- **Error quality on index mismatch is poor** (NEG-2) — the *most common* author mistake.
- **No real instruction, address, or `MemoryPerm`.** Connecting §2 to §6 is unmeasured.
- **No control flow.** Straight-line only.

---

## 7. Transmogrification — one mechanism

**Status**: proposed; nothing in this section exists.

### 7.1 The shape: a borrow with a transformation, discharged by an inverse

The owner's shape — *"a special kind of borrow with an obligation that discharges the hold on the
underlying memory (and maybe forces a destruction operation)"* — unifies what were two operations:

| | Sub-allocation | Byte typing |
| :-- | :-- | :-- |
| What is transformed | the **region** (narrowed) | the **type** (refined) |
| Loan | `Exclusive S` for `S ⊂ R` | `Typed T R` |
| Parent's hold while outstanding | suspended over `S`'s extent | suspended over the typed extent |
| Discharge | `free` | `destruct` |

**`malloc`/`free` and construct/destruct are the same operation at different granularity.** One
mechanism:

```lean
inductive View | sub (extent : Extent) | typed (T : Type) (extent : Extent)

/-- Suspend the parent's hold over `view`'s extent, yielding a handle. -/
def lendAs (parent : RegionId) (v : View) : Asm Γ (suspend Γ parent v) (Handle v)

/-- The inverse. Restores the parent's hold; for a typed view this is the destructor. -/
def discharge (parent : RegionId) (v : View) : Asm Γ (restore Γ parent v) Unit
```

This is a strictly better design than two parallel mechanisms, and it collapses two would-be Law 12
twins before they are written.

### 7.2 The view ledger — and why two independent routes reach it

The unified operation forces a generalization of §3.1: a region's capability state is not a scalar
but a **ledger of outstanding views**.

```
Cap ::= owned (outstanding : List View)
```

- `write` is `owned []`
- `read n` is `owned` with `n` whole-region read views
- sub-allocation is `owned` with the carved extents outstanding
- a typed view is `owned` with a `typed` entry

`canStore` becomes "no outstanding view covers this extent"; reclaim is "the ledger is empty".

**The same generalization is forced independently by SmolAlloc, and that convergence is the
finding.** The allocator keeps *two* ledgers:

- `activeBorrows : Nat` (`Spec.lean:46`) is a **count**. It answers "is the arena safe to release"
  (`isSafeToRelease`) correctly, and can answer nothing about disjointness, because a count has no
  identity.
- `obligations : List ObligationToken` with `mkFreeObligation payloadAddr` (`Spec.lean:56-58`, pushed
  at `:100`, `:125`) is a **named multiset**. It carries identity.

**The named list is the view ledger; the counter is its cardinality.** And `isSafeToRelease`
(`activeBorrows == 0`) **is** §7.1's discharge check — written before anyone named the pattern.
Treating SmolAlloc as the existing worked instance rather than an analogy is correct.

**Two observations about the current implementation** that the indexed form makes unrepresentable.
Stated as observations against the spec as written, not proven defects, and worth confirming with
whoever owns SmolAlloc:

1. `free` decrements saturatingly — `if s.activeBorrows > 0 then s.activeBorrows - 1 else 0`
   (`Spec.lean:149`). An unbalanced free is absorbed rather than rejected.
2. `free` discharges by `s.obligations.filter (fun o => o != targetObligation)` (`Spec.lean:145-146`),
   removing *all* matching entries, and `mkFreeObligation` is keyed on the **address alone**. Two
   obligations for the same address are indistinguishable. `eraseAllChecked`
   (`Gasm/Core/Obligations.lean:62`), which returns `Option` and would catch discharging something
   not present, exists and is unused here.

Observation 2 is the same defect §7.5 identifies from the pointer side.

### 7.3 Sub-allocation, concretely

`MemoryPerm.split` is the primitive step; an allocator is its closure over a free list.

```lean
structure AllocState (R : RegionId) where
  outstanding : List RegionId
  freeList    : List RegionId
  partition   : Partitions R (outstanding ++ freeList)   -- pairwise disjoint, covering R

def alloc (s : AllocState R) (n : Nat) : Option (Σ S : RegionId, Ptr S × AllocState R)
def free  (s : AllocState R) (S : RegionId) (p : Ptr S) : Option (AllocState R)
```

The invariant carries disjointness: every region handed out is disjoint from every other outstanding
one *because the partition says so*, not because each call site proves it. That is what makes §2.4's
"free by construction" true across an allocator, not only across a static frame. `free` returns
`Option` deliberately — returning a region that is not outstanding is a failure, not a no-op.

**Needs**: the disjointness component `split` does not currently return (§1.1). Small, self-contained.

### 7.4 Byte typing, and the roundtrip convergence — checked

Two regimes, kept apart because only one is free.

**Checked.** Parse and obtain `Except err T`. Safe; costs a parse. In tree: `Stdlib/Http11/Parser.lean`,
`Stdlib/Png/Spec.lean`.

**Asserted.** Claim the bytes satisfy `T`'s invariant because of *how they got there*:

```lean
structure Typed (T : Type) (r : RegionId) where
  private mk ::
  ptr : Ptr r
  inv : Invariant T r          -- a Prop; erased

def typeAfterWrite (t : T) (p : Ptr r) (h : fits T r) : Typed T r
```

**The roundtrip theorem *is* the introduction rule for the asserted regime.** If a `T` was just
written, `parse (write t) = .ok t` is exactly the obligation `typeAfterWrite` needs, and nothing else
will do. That reframes a set of parser efforts that look independent as instances of one mechanism,
and gives them a shared reason to be ∀-quantified — Law 9 pressure they would otherwise each take
individually.

**The evidence is thinner than it appears, in three specific ways:**

- **Http11 — holds, strongest case.** `request_roundtrip (r : Request) : parseRequest (writeRequest r) = .ok r`
  (`Stdlib/Http11/Roundtrip.lean:304`) and `response_roundtrip` (`:444`) are ∀-quantified and landed.
- **Zlib — holds, fixed branch.** `lz77_roundtrip_soundness (data : ByteArray)`
  (`Stdlib/Zlib/Equivalence.lean:363`), `emitFixedBlock_roundtrip_soundness` (`:1875`),
  `compress_roundtrip_of_fixed_choice` (`:1884`) — ∀-quantified over `ByteArray`, landed.
- **PNG — does not hold yet.** `png_roundtrip_soundness_inst` and
  `png_idempotent_canonical_roundtrip_inst` (`Stdlib/Png/Equivalence.lean:367,380`) carry `_inst`,
  which under Law 8 and Law 10 marks them ground-instance regression tests explicitly *not* presented
  as general theorems. A candidate for the mechanism, not an instance; making it one is PA8 work this
  design gives a second motive for.
- **ELF — not on `main`.** `Gasm/Targets/ELF/` holds `Format.lean` and `Notes.lean` and no parser. A
  checked parser exists in an agent worktree, uncommitted, carrying no roundtrip theorem.

Two landed instances, one candidate, one in flight: enough to make the convergence real, not enough
to call it a settled pattern.

### 7.5 Why destruction is load-bearing, and why region identity must be generative

**Destruction is not optional.** If bytes typed as `T` could silently revert to raw while a
`Typed T r` might still exist, the invariant is stale and the type is a lie. The destructor is the
proof that no typed view survives. **A transmogrify dischargeable without it is unsound.**

**But Lean is not linear, so the handle cannot be what enforces this** — a `Handle` value can be
duplicated. It does not need to be: **authority is checked against the index, not the handle**
(§4). After `discharge`, the view is gone from the index, so a dereference through a duplicated
handle fails the authority check. Use-after-free is caught the same way stale borrows are.

**This forces one design constraint that is easy to miss.** If `RegionId` were address-derived, a
block freed and reallocated at the same address would produce a region *equal* to the stale one, and
a duplicated stale `Ptr` would type-check against the new grant. **`RegionId.ident` must therefore be
generative** — a fresh identity per allocation, monotone in the index — not the address. This is the
same defect as §7.2 observation 2 (`mkFreeObligation` keyed on address alone), seen from the pointer
side, and it is the strongest argument that the two ledgers should be unified.

### 7.6 The danger: unchecked transmogrify

An unchecked transmogrify — asserting `T` of arbitrary bytes with no proof — is the single hole
through which all memory safety leaks.

**Recommendation: demand a proof; it must not be ledgerable.** `docs/MEMORY_HOOK.md` §4.5's bypass
ledger exists for *authoring paths not yet migrated* — a migration state with a defined end ("ledger
empty"), monotone and measured. An unchecked transmogrify is not a migration state; it is a permanent
semantic assertion. Ledgering it would make the ledger un-emptiable by construction and park a
soundness hole behind a counter — precisely the confidence-manufacturing shape Law 8 and the TC21
linter exist to catch.

**There is one legitimate case, and it is not this operation.** The initial frame's regions come from
outside the model: the OS mapped an image, `VirtualAlloc` returned a block. That is an **axiom of the
environment**, belonging where other environment axioms live — stated once at the boundary in the
target's OS model, not as a general operation available to any author. Naming it separately keeps the
general operation honest.

**If ruled the other way**, the ledger entry must record the module; the exact region and byte range;
the type asserted; the invariant *not* proven, written as a proposition rather than a description;
why a parse is not viable; and a review sign-off — and it must introduce an axiom so
`lake exe check_gates_axioms` sees it. A bypass the axiom gate cannot see is worse than one it can.

### 7.7 The typing rule under the `casesOn` attack

`Typed T r` has `Ptr r`'s shape: private constructor, one data field, one `Prop` field. Applying
§2.3's measured result: `casesOn` **observes** (harmless — the pointer is already held, the proof is
of a true proposition) and **cannot construct** (the motive must supply a `Typed`, needing the private
constructor). The same three regressions apply, and the §2.3 audit must cover `Typed` and `Handle` as
well as `Ptr` and `RegionId`.

**Honest labelling**: this is *inference* from the measured `Ptr` result on an identically-shaped
type, not a separate measurement. It must be re-measured when `Typed` is written — that is exactly the
assumption that failed for `X86_64Memory`.

---

## 8. Leak-freedom — verified, with three conditions

The claim: a forgotten `free` is a loan never discharged, so the post-index does not match the
declared contract and the program does not compile. **Memory leaks become compile errors, by the same
mechanism that makes use-after-free unrepresentable.**

**The reasoning holds, and it is strictly stronger than Rust**, where leaking is *safe*:
`mem::forget` is a safe function, `Rc` cycles leak by design, and the language explicitly declines to
guarantee leak-freedom because ownership cannot force a destructor to run. An obligation that must be
discharged before a routine typechecks does have that power. **Status**: unbuilt; this is a property
of the proposed design, not a measured one — §6 measured discharge-forcing on read loans (NEG-2), not
on allocations.

Three conditions, two named by the coordinator and one found here.

### 8.1 Loops — the index-preserving rule was too weak; index-parametric is correct

§3.3's earlier "loop bodies must be index-preserving" would force every allocation to be freed within
its own iteration, blocking legitimate patterns like building a list. **The correct rule is
index-parametric**: a body of type `∀ i, Asm (Γ i) (Γ (i+1))` composes to `Asm (Γ 0) (Γ n)`, which is
an ordinary dependent fold. Allocation across iterations is then expressible, at the cost of an
author-stated invariant `Γ`.

**One honest degradation.** When the iteration count is a runtime value, the index cannot be a
statically-known list — it becomes a symbolic count, and the exit obligation becomes the arithmetic
goal "outstanding = 0" rather than a structural index match. **Leak-freedom survives** — an
undischarged obligation is still a compile error — but for runtime-bounded allocation it is an
arithmetic obligation the author discharges, not a free structural one.

### 8.2 Escaping allocations — transfer is the owner's fourth rule

A routine that allocates and returns the pointer has not leaked; it transferred. The post-index must
distinguish this, and it does: **transfer is `donate`**. The routine's type *exports* the region —
`Asm Γ (Γ ++ [S]) (Ptr S)` — and the caller's index gains it. Discharge *removes* a view and restores
the parent; transfer *moves* it to the caller. Both are index operations, neither is a leak, and the
fourth rule is what makes the distinction expressible. No narrowing of the claim is needed here.

### 8.3 Pointers stored in memory — the real limit, and it is the strongest one

A routine that allocates and stores the pointer *into a data structure in memory* — a linked-list
node's `next` field — has moved the region's ownership into the heap. **The index tracks capabilities
held at a program point, not capabilities held by data.** A static index cannot follow ownership that
lives in bytes.

This is where separation logic reaches for recursive predicates and Rust reaches for ownership-in-fields
(`Box<T>`). Under this design the mechanism is available in principle — a `typed` view whose invariant
*is* "this field owns region S" makes the container's destructor obligated to discharge the contained
pointer, and §7.1's unification is exactly what makes that compose recursively. But it is unbuilt and
not cheap.

**So v1 should forbid pointer-valued fields**, and the leak-freedom claim should be stated as holding
for programs whose ownership graph is a tree the index can see. That is a real restriction — it
excludes linked lists, trees with parent pointers, and most interesting heap structures — and it is
the largest gap between this claim and a general leak-freedom guarantee.

**Net verdict**: leak-freedom is real, is stronger than Rust, and holds *for straight-line and looping
code whose allocations are either discharged or donated, with no pointers stored in memory*. Stated
without those conditions it would be an overclaim.

---

## 9. Proof-carrying addresses: lock invariants

**Status**: proposed. **All three mechanisms this depends on are absent from the tree**; see §9.3.
Nothing here should be read as saying a lock has been verified.

### 9.1 The shape

*"when this atomic word is 1 the thread that set it has the mutex"* is **not a claim about the word's
own bytes**. The lock word holds no data; its *value* licenses a claim about memory **elsewhere**.

```lean
/-- The word at `lockRegion` guards `protected`. Ghost state attached to a physical location. -/
structure LockInv (lockRegion protected : RegionId) where
  private mk ::
  inv : LockInvariant lockRegion protected

/-- A successful acquire MOVES the protected region's capability into this context. -/
def acquire (l : LockInv w p) : Asm Γ (Γ ++ [p ↦ owned []]) Bool
def release (l : LockInv w p) : Asm (Γ ++ [p ↦ owned []]) Γ Unit
```

The physical value and the logical permission move together, **and indivisibly** — which is exactly
why only an atomic RMW can move them. If the read of the lock word and the acquisition of the
permission could be separated, two threads could both observe 0 and both acquire.

### 9.2 `Locked` earns its place — and needs one extension

§3.2 defined `Locked` as shared-mutable with safety discharged by atomicity, and called it "the point
where static discipline hands off to a dynamic protocol". A mutex is that handoff made concrete: **the
word is `Locked`; the protected region transitions from unowned to `Exclusive`-held-by-the-acquirer.**

**§3.2's definition supports the first half and not the second.** It describes the word correctly and
says nothing about a *linked* region. The extension: `Locked` carries an associated ghost claim naming
the region it guards, and the atomicity obligation on its accesses is strengthened to "this access
transfers the named capability". That is genuinely new vocabulary, not a re-reading of what §3.2
already said, and it is the concrete payoff for keeping `Locked` as a third authority mode rather than
folding it into `Exclusive`.

### 9.3 The three-way dependency — none of which exists

Spike 8's verified computation is an XCHG test-and-set spinlock whose **unlock is a plain `MOV`**
(`docs/SPIKES/SPIKE8_MULTITHREADING.md` §3, and §2.1's "the critical section is a deliberate
load/add/store"). A plain-store unlock is correct **only under TSO**, relying on store-store and
load-store preservation. So:

| Layer | Supplies | State in tree |
| :-- | :-- | :-- |
| Borrow model (this document) | *what moves* — the protected region's capability | Unbuilt |
| Atomics (MT1) | *indivisibility* — the transfer cannot be torn | Unbuilt; zero atomic forms exist |
| Memory model (XM1/MT2) | *visibility* — prior writes are seen by the next acquirer | Unbuilt; `docs/X86_MEMORY_MODEL.md` states it has zero Lean |

**If any of the three is missing, the mutex is unsound.** And under one thread any ordering theorem is
vacuous — `docs/X86_MEMORY_MODEL.md` §8 explicitly rejects stating one now for that reason. This
document therefore claims a *shape* and a *dependency*, and claims nothing about a verified lock.

### 9.4 Is byte typing a special case? — one mechanism, one real difference

Both attach a logical claim to a physical location. Byte typing's claim is about *the same bytes*
("these bytes satisfy `T`"); the lock invariant's claim is about *other* bytes ("the value here
licenses ownership of that region").

**One mechanism — a ghost claim indexed by a physical location — with byte typing the reflexive case
and lock invariants the cross-region case.** The cross-region indirection is the real difference, and
it has one consequence that byte typing does not carry: the claim must be **transferable between
threads**, which is why it needs atomicity and the memory model and byte typing does not. So they are
the same mechanism with genuinely different obligations attached, and giving the mechanism once while
stating the two obligation sets separately is the right factoring.

---

## 10. Relationship to MH3 — this subsumes it, and that is a finding

**Status**: MH3 is `ready` and **in flight in an agent worktree**, uncommitted
(`Gasm/Targets/X86_64/CheckedAsm.lean`, `Stdlib/SmolAlloc/MemSafety.lean`, `Tools/CheckMemBypass.lean`,
`scripts/mem_bypass_allowlist.txt`). None is on `main`.

MH3's shape is a list of checked instructions under a frame fixed for the whole routine, with a region
record, a per-access obligation, a decidable literal case with a soundness theorem, an auto-param,
erasure, and a `MemSafe` shape.

**The borrow monad is MH3's checked program with the frame promoted from a parameter to an index. They
are the same artifact** — a list of instructions sharing one frame is precisely the index-preserving
special case. Everything except the program type constructor carries over unchanged.

**MH3 is also where the typed pointer is closest to existing.** `MemRef` is *not* a typed pointer in
embryo: it is a public record with default field values and no proof component (`Memory.lean:49-52`);
anyone can build any `MemRef` naming any register. What carries a citation is MH3's memory-instruction
constructor. §2 generalizes that in two directions: past literal displacements, and from "this access
is authorized" to "this *value* is authorized to be dereferenced".

**Recommended: let MH3 land as designed and approved.** It is the ADR-0040 Q1 line, being built now,
and the upgrade discards nothing — honouring `docs/MEMORY_HOOK.md` §4.3's "nothing in v1's shape is
discarded". Two coordination items for the MH3 agent: its `Locked` admission row (§3.2, §9.2), and
whether its program type is named in a way that survives becoming an index.

---

## 11. Does the DSL make ill-formed programs *unwritable*?

**Partly.** The DSL prevents *mis-weaving*: authors never write binds, so each intermediate index is
by construction the previous step's post-index. It does not prevent **writing a step whose obligation
is false**, because that is a goal, not a syntax error. The distinction is between a *parser* and a
*checker*, and the value is that it is a checker with a proof-shaped fallback: a surface in which the
bad program could not be typed would also be one in which the *hard* program could not be typed
(POS-5).

Law 11's "fails to assemble" is satisfied at elaboration, not at parse — the bar
`docs/MEMORY_HOOK.md` §4.2 sets and ADR-0040 accepted. No bytes are emitted; the build is red.

**Sole-surface cost** is not the mechanism — the ratcheted bypass ledger and gate are MH3
deliverables — it is the migration, which PA4 owns. §14.5 records the one way the pointer type
*reduces* it.

### 11.1 Emit directly, or produce a term? — produce a term

The dichotomy is false: **obligations are elaborated at term-construction time either way.** Emitting
directly buys no additional checking and costs composition — a routine that cannot be named as a value
cannot be called, inlined, or given a contract, and erasure to `SymbolicInstr` is the seam that keeps
the assembler, linker, decoder and fuzzers untouched.

### 11.2 What a failed obligation looks like

An **error** carrying the goal, at the failing step's position (measured). Not a `sorry`, not a marker
— an error is caught by `lake build`, which every gate depends on, whereas a `sorry` would produce a
*buildable* artifact, which Law 11 forbids. The DSL should accept an explicit per-step proof escape
(measured, POS-5).

---

## 12. Shared-XOR-mutable and data races

**Status**: proposed theorem shape; no multi-thread machine exists.

```
GlobalWF Θ  :=  for every address a,
                  at most one thread's context grants `write` over a, and
                  if any thread's context grants `write` over a, no other grants any share over a
```

```lean
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

The proof is short and structural: a store is authorized only from `write`; `GlobalWF` says no other
thread holds any share over that address; so `a₂` is unauthorized. It needs no ordering reasoning —
**races are excluded by authority, before the memory model is consulted.**

`IsSynchronized` is where `Locked` lives and where the theorem stops. A `Locked` region admits
concurrent stores; those accesses *are* conflicting in the footprint sense and are safe because they
are indivisible. A model that excluded all races would exclude spinlocks, and Spike 8's verified
computation is a spinlock.

**If this lands, the borrow model and the memory model discharge one obligation together**: the borrow
model establishes data-race-freedom on plain accesses; the memory model then only states *ordering*
for the synchronized ones — which is precisely §9's mutex. Caveats: cross-thread transfer does not
exist and has no task; and `GlobalWF` rests on §2's provenance discipline, since with typed pointers
the premise is establishable at spawn from §7.3's partition and without them it is not.

---

## 13. Architecture neutrality

**Status**: analysis; no ARM target exists.

Authority semantics are neutral — "who may store" is not a memory-model question — and §12's theorem
is ordering-free by construction, so it holds on any architecture because it never mentions one.

**The pointer type is *more* portable than what exists.** `MemRef` is explicitly x86-shaped
(`base + index*scale + disp` derives from the SIB byte), and `docs/TARGETS/ARM64.md` §7 flags it will
not fit AArch64 without modification. §2.2's `Ptr` carries **no addressing mode at all**: a provenance
and a displacement, lowered per target — x86 to `MemRef`, AArch64 to `[Xn, #imm]`, `[Xn, Xm, LSL #k]`,
or a literal-pool form. `Ofs.lit`/`Ofs.dyn` covers AArch64's immediate and register-offset shapes
unchanged.

**Three concrete ARM findings, cheap now and expensive to discover late:**

1. **Writeback mutates the pointer.** AArch64 pre/post-indexed forms (`STR X0, [X1], #16`) update the
   base register *as part of the access*. That single instruction is a store **and** a pointer update:
   the descriptor must declare both, and the borrow index must account for the offset changing at that
   step. x86-64 has no such form, so neither this design nor MH1's descriptor anticipates it. An ARM
   team should decide early whether writeback forms are modelled as one descriptor with a declared
   register effect, or excluded from the first cut.
2. **"Atomic = one indivisible access" is TSO-shaped.** `docs/X86_MEMORY_MODEL.md` §2.3 Decision 1
   makes a locked RMW one descriptor entry — right for x86, **wrong for AArch64**, whose exclusive
   monitor is `LDXR`/`STXR`: a *pair* that can fail and must be retried. An ARM atomic increment is a
   loop. §3.2 therefore defines `Locked` by its **obligation**, leaving each target to discharge it.
3. **§9's mutex is the hardest test of neutrality, and it passes — obligationally.** x86's release is a
   plain `MOV`, correct under TSO. AArch64's is not: it needs `STLR` or an explicit barrier. **The
   permission transfer §9.1 describes is identical across targets; only the discharge instruction
   differs.** The obligation — "the release must make prior writes visible before the lock word's
   release is observable" — stays constant, and each target's memory model discharges it its own way.
   That is the strongest available form of the neutrality claim, and it survives precisely because §3.2
   and §9.2 are framed as obligations rather than as instruction choices. Had `Locked` been defined as
   "one `.rmw` entry, released by a plain store", ARM could not have satisfied it.

Related: `docs/X86_MEMORY_MODEL.md` §8 rejected a per-access ordering field because x86-TSO has no
third value, and said it might be needed for ARM. AArch64's `LDAR`/`STLR` carry acquire/release per
access, which is that third value; §9 is its first consumer.

---

## 14. Demand, staging, and honest cost

### 14.1 The trigger

*"isa scale up: we need multithreading and borrowing resolved"*, and for §7, `smol_malloc` carving
from `VirtualAlloc` blocks — **in-tree code, not a projection** (`Stdlib/SmolAlloc/Spec.lean`). Law 5
demand, stated. This document is ADR-0040's deferred flow-sensitive typestate arriving under its own
demand, and it **subsumes** that deferral (§10) rather than sitting beside it.

### 14.2 What actually blocks what

| Expansion stage | Needs | State |
| :-- | :-- | :-- |
| Wave A — GPR-only ALU forms | Nothing here | Unblocked today |
| Wave B — memory-operand forms | MH1 (landed) + MH3 | MH3 in flight |
| Memory forms in loops over buffers | Straight-line borrow index + §2's pointer | Unbuilt |
| Allocator-backed routines | §7.3 | Unbuilt; consumer exists today |
| Atomics, threads, any lock | §9's three layers | All unbuilt |
| Branch-heavy routines | §3.3 item 2 — PA2/PA3 | Unstarted |

### 14.3 Law 8, confronted rather than managed

- The demand is named by the owner, and §7's is in-tree code.
- **Decisive: the structural commitment was already made and is dormant.** `BlockM` is the indexed
  monad, ratified in `docs/API_STATE_MODELS.md` §2, with zero consumers — under Law 8 *already* a dead
  abstraction. This design does not add speculative structure; it is the first thing that would make
  existing speculative structure real, or prove it should be deleted.

The charge that **does** stick, answered by sequencing: the DSL must not be built before §6.5's scale
question is measured. An elaborator that cannot elaborate `Stdlib/Zlib/X86_64.lean` in reasonable time
is a facade regardless of soundness.

### 14.4 The VISION §4 DSL claim, checked

The operation population is closed and small — lend, reclaim, donate, `lendAs`, discharge, load,
store, synchronized access — and closure is *forced*, because `MemAccessKind` is `load | store` plus
the proposed `.rmw` and `memAccesses` is defaultless, so no instruction can introduce an eighth access
shape without a compile error.

**The qualification**: the cheap theorems are about *authority bookkeeping*, the decidable part. What
remains per-program is dynamic bounds and §7's introduction rules. The leverage is real but partial —
and §2's pointer type is what makes it *large* rather than marginal, because without it the residue
was unbounded aliasing and with it the residue is arithmetic.

### 14.5 Cost, rechecked

Agent-days of focused work; uncertainty dominated by §6.5 and the error-message work.

| Piece | Estimate | Change |
| :-- | :-- | :-- |
| Elaboration-cost measurement, remediation if bad | 2 days to measure, unbounded to fix | Unchanged. **Lowest confidence, and it dominates** |
| Borrow context, four operations, decidable predicates | 3–5 days | Unchanged |
| Weaving DSL, hardened | 4–8 days | Unchanged |
| §2 pointer type, region identity, tier-3 audit | **+4–7 days** | New |
| Promoting MH3's program type to the index | 3–5 days, after MH3 | Unchanged |
| `MemSafe` re-proof for the pathfinder | 3–7 days | **Reduced** from 5–10: disjointness stops being a per-routine discharge over concrete addresses |
| §7 unified transmogrify + `split` disjointness + SmolAlloc as first instance | **+6–10 days** | New; **cheaper than the two-mechanism version** it replaces, and it has an existing consumer |
| §7.4 asserted typing glue | **+2–3 days** | New; checked regime is free, roundtrip theorems land anyway |
| §8.3 recursive typed views (pointers in memory) | **not estimated** | Deliberately out of v1 |
| §9 lock invariants | **not estimated** | Blocked on all three layers of §9.3 |

**The headline changes in a way that matters to the ISA decision.** The up-front bill grows to roughly
**five to eight weeks on top of MH3** (from three to five before the pointer type and transmogrification).
But it *shrinks* the marginal cost of every migrated routine, removing an unbounded per-routine aliasing
obligation from PA4's long tail and replacing it with a boundary condition plus arithmetic. **Since
PA4's tail is the large number and the up-front work is the small one, this makes the whole programme
cheaper — it moves cost earlier and makes it visible.** The owner's unification of §7 is itself a cost
reduction against the two-mechanism design it replaces.

Unchanged: the complete model including control flow and threads is months, most of it PA2/PA3 and MT2
— work already queued for other reasons.

---

## 15. What this cannot catch

1. **Dynamic bounds.** One local `omega`-shaped goal per dynamic access, against a length in the type.
2. **Entry disjointness.** One obligation per routine boundary, discharged by the caller.
3. **Pointers stored in memory** (§8.3). The largest limit: v1 forbids pointer-valued fields, which
   excludes linked lists and most heap structures. Recursive typed views are the route, unbuilt.
4. **Runtime-bounded allocation counts** (§8.1): leak-freedom becomes an arithmetic obligation rather
   than a structural one. Still a compile error; not free.
5. **Loans across loop back-edges** without a stated invariant. Weaker than NLL.
6. **`Locked` regions' actual safety.** §12 excludes them by hypothesis; safety rests on §9's three
   layers, none of which exists.
7. **Whatever the environment asserts** (§7.6): that the OS really mapped the bytes it says it did.
   Irreducible, and correctly located at one boundary.
8. **Provenance creation is audited, not unrepresentable** (§2.3). Region identity is reachable only
   through named operations, and that property is enforced by a tier-3 lint — the same tier and the
   same measured reasoning as the memory seal, and deliberately so, because tier-1 opacity would
   destroy the `decide` fast path. A lapsed audit reopens it; the predicate to enforce is "no
   declaration produces a `RegionId` or `Ptr` without one among its arguments".

**No longer listed, because §2 removes them**: aliasing as an unbounded per-access problem, and
`mov rbx, rax` creating an untracked anchor.

---

## 16. Rejected alternatives

- **Two parallel transmogrification mechanisms** (sub-allocation and byte typing designed separately).
  Rejected on the owner's unification: they are one borrow-with-transformation at different
  granularity, and separating them would have produced a Law 12 twin plus a duplicated discharge rule.
- **A decidable borrow-check pass over an ordinary-monad program.** Nearly made it: zero ergonomic
  cost. Rejected because the check is whole-program and posterior — failures report at the end of a
  routine, the fast/slow-path split disappears, and it cannot express a routine whose *contract* is
  index-changing, which is what donation and transfer are. Remains the fallback if §6.5 kills the
  indexed approach.
- **A pointer type storing an address behind a private constructor.** Weaker than address-free: it has
  a field of the dangerous type, so safety depends on never adding a helper that fills it.
- **Handles enforcing discharge by linearity.** Impossible in Lean, and unnecessary: the index does it
  (§7.5).
- **A capability value with a phantom region tag (`runST`-style).** Keeps `do` working; rejected on
  §4's argument — the capability is still a value, so it can be reused.
- **Ledgering unchecked transmogrify** (§7.6). Makes the ledger un-emptiable and parks a soundness hole
  behind a counter.
- **Making `Locked` a level between `ReadOnly` and `Exclusive`.** It admits stores and multiple
  holders; a total order loses the property that distinguishes it — and §9 is what that property buys.
- **Building this instead of, or beside, MH3** (§10).
- **Stating a lock invariant now as though it were sound** (§9.3). All three supporting layers are
  absent; claiming otherwise is the facade shape this codebase keeps catching.

---

## 17. Questions for the owner

1. **Q1 — sequencing against MH3.** Recommended: MH3 lands as approved; the borrow model is a follow-on
   promoting its frame to an index (§10).
2. **Q2 — the `Locked` re-reading and its §9.2 extension.** Recommended: `Locked` means
   "shared-mutable, safety discharged by atomicity", defined by obligation so AArch64's `LDXR`/`STXR`
   can satisfy it (§13), **and** carries an associated ghost claim naming the region it guards. The
   second half is new vocabulary, not a re-reading.
3. **Q3 — the measurement gate.** Recommended: no DSL before elaboration cost is measured at realistic
   length, with an explicit kill criterion (§6.5, §14.3).
4. **Q4 — one counted-loan abstraction, or two (§4.2, §7.2).** §7.2 now answers most of this: the
   allocator's **named** obligation list *is* the view ledger and `isSafeToRelease` *is* the discharge
   check, so unification is recommended rather than merely possible. What remains for a ruling is
   whether `docs/MEMORY_PROVENANCE.md`'s allocation model is refactored onto it now or later.
5. **Q5 — unchecked transmogrify (§7.6).** Recommended: demand a proof; make it un-ledgerable; locate
   the environment's assertions at one named boundary.
6. **Q6 — v1's ownership-graph restriction (§8.3).** Recommended: v1 forbids pointer-valued fields,
   making leak-freedom hold for tree-shaped ownership only. This excludes linked lists. Confirm that is
   an acceptable v1 line, or fund recursive typed views up front.

---

## 18. Document boundaries — a Law 12 note, and a split I am not proposing

This document now covers what a pointer is (§2), who may use it over time (§3–§6), how values enter and
leave (§7–§8), and how a claim at one address licenses ownership of another (§9).

**Recommended: do not split it, and the reason is a finding rather than a preference.** The first
revision treated authority and provenance as separate concerns, and that separation is exactly what
produced its wrong verdict — it reasoned about borrowing without reasoning about what was borrowed. A
reader given §3 without §2 will make the same mistake, and a reader given §7 without §3 will not see
that transmogrification *is* a borrow. The owner's two unifications both cut against splitting.

**There is a real Law 12 overlap that does need resolving.** `docs/MEMORY_PROVENANCE.md` already owns
provenance identity — `ProvenanceId`, `ProvenanceBlock`, `ArenaPageToken`, §1.2's active-borrow
discipline — and §7 here designs the same allocator from the authority side. Proposed division, for a
ruling rather than unilateral edit:

- `docs/MEMORY_PROVENANCE.md` keeps the **allocator and lifetime** model: allocation identity, arena
  retention, Spike 3's lifecycle.
- This document keeps **authority, the authoring type, and the transformation rules**.
- §7.2 is the explicit bridge; `Ptr`/`RegionId`/`View` are named in one place only.

Left unresolved, the two will drift into describing the same allocator twice — the unlinked-twin shape
Law 12 prohibits, at document level.

---

## 19. Tracking

**Status**: unstarted.

| Task | Track | Content | After |
| :-- | :-- | :-- | :-- |
| `docs/tasks/BR1-borrow-index-feasibility.md` | proof-arch | §6.5's kill-criterion measurement, then the borrow context, four operations, and the weaving DSL | MH1 |
| `docs/tasks/BR2-borrow-authoring-upgrade.md` | proof-arch | §10's promotion of MH3's program type to an index; `MemSafe` re-proof | BR1, MH3 |
| `docs/tasks/BR3-cross-thread-capability-partition.md` | concurrency | §12's `GlobalWF` and the no-unsynchronized-race theorem | BR1, MT2 |
| `docs/tasks/BR4-provenanced-pointer.md` | proof-arch | §2's address-free pointer type, generative region identity, and the tier-3 provenance-creation audit | MH1 |
| `docs/tasks/BR5-transmogrification.md` | proof-arch | §7's single mechanism, the view ledger, `split`'s disjointness component, SmolAlloc as first instance, §8's leak-freedom statement | BR4 |
| `docs/tasks/BR6-lock-invariants.md` | concurrency | §9's cross-region capability transfer | BR5, MT1, MT2 |

PA2 owns §3.3's joins and loops, and §8.1's index-parametric loop rule is an input to it. PA4 remains
the migration epic; §14.5 records that the pointer type reduces its per-routine cost. PA8 gains a
second motive for PNG's roundtrip (§7.4). MT1/MT2 own the atomicity and visibility layers §9.3 depends
on.
