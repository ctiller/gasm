# MEMORY_HOOK: The Memory Access Contract (x86-64, AArch64, and the Wasm cross-target note)

- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/REVIEW.md#law-14-calibration-data-governance-the-third-reference-class
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions
- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate
- REF: docs/VISION.md#5-performance-modeling-agents-as-the-optimizing-compiler
- REF: docs/TECHNICAL_NOTES.md (§2)
- REF: docs/MEMORY_MODEL.md (§§4–7, §14)
- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p2-blocking-the-memory-operand-contract-law-11-pa4-at-least-at-the-instruction-layer

## 1. Status and scope

**Status** (revised 2026-08-29): this was written as a pure design document, and **Layers S
and P have since been built**. The sealed
memory cell, the width-indexed read/write API, `MemRef`, `fault : Option X86_64Fault`, the
defaultless `memAccesses` field and the frame-lemma set all exist in the tree today (§3's
Status line enumerates them with file evidence). `MemCostModel`, the registered forms'
`memUops` derivation, and the registry audit also exist (§5). **Layer A (capability authoring) remains
unbuilt** — `CheckedAsm` has no declaration anywhere in `Gasm/`, `Stdlib/` or `Spikes/`.

Read the **per-section `**Status**:` lines as authoritative**, not this preamble: each was
re-verified against the tree on 2026-08-29, and they now differ from one another by design
(§§3 and 5 landed; §4 did not). Every mechanism still proposed-but-unbuilt carries its own
`**Status**:` line per the repository's design-only convention, and every fenced Lean block under a
section marked unbuilt is a design sketch, not tree contents. The §1.1 evidence table below
is a **snapshot of the pre-MH1 tree at commit `0d5c6a9` (2026-08-27)**, retained because it
is the motivating measurement this design was derived from; it describes the state MH1
changed, not the state today. The remaining capability work is consolidated in
`docs/MEMORY_MODEL.md` stages M1/M4; performance-hook work remains architectural debt in
`docs/TECHNICAL_NOTES.md`.

Consumers depend on this being right in both directions.
`Gasm/Targets/X86_64/Instructions/Base.lean:40` cites §3.3 by name as the reason
`memAccesses` carries no default; a reader trusting the retired "none of this exists"
markers would have concluded that citation pointed at nothing, and — because contributors
are expected to trust `**Status**:` markers —
rebuilt what was already there.

**The directive** (owner, verbatim): *"memory contracts — let's plan out a memory hook —
apis every instruction needs to go through to access memory, so we can do the perf and
permissions in one place."* And, for the permissions half: *"the instructions should be
validating they have access to an address and failing to assemble if that proof doesn't
carry"* — Law 11's fail-to-assemble bar, not a runtime check.

This document designs that hook: what instructions call, how the capability proof is
carried and enforced at assemble time, what the perf side records and how it stays
falsifiable, the migration path for the existing 88 instruction forms, the effect on
existing proofs, and how faults become distinguishable observations. Counts in the baseline below
are explicitly historical measurements, not a live registry census.

### 1.1 Verified pre-MH1 baseline (the evidence this design is grounded in)

| Fact | Evidence |
| :-- | :-- |
| 14 of 88 instruction forms touch memory | `MovRspDispByte`, `MovRspDispImm32`, `MovRspDispImm64`, `MovMem8Reg8`, `MovMem64DispReg64`, `MovMem64DispImm32`, `MovReg64Mem64Disp`, `MovzxR64Mem8`, `MovReg32RspDisp32`, `PushR64`, `PopR64`, `CallRipRel`, `CallRel32`, `RetOp` — enumerated from `Gasm/Targets/X86_64/Registry.lean` + each `step`'s body |
| The machine model's only memory primitives are five helpers + raw field access | `X86_64MachineState.read64`/`write8`/`write64`/`push64`/`pop64` (`Gasm/Targets/X86_64/Registers.lean:226-265`); the field itself is `memory : Address → Byte`, total, public |
| Instruction steps already bypass even those helpers | `MovRspDispImm32.step` inlined a raw 4-byte store lambda (no `write32` helper existed); `MovzxR64Mem8.step` and the former RSP-specific W32 MOV load read raw memory bytes inline. The missing widths already caused the exact per-instruction re-implementation this hook exists to end |
| Non-instruction code also writes memory raw | `Gasm/Targets/Windows/Win32API.lean` hooks (`readFileHook`/`recvHook` write destination buffers via raw `memory := fun a => ...` lambdas, lines 112–136, 214–217); the linkers' `loadMemory` installs the image raw |
| Zero capability call sites | Law 11's own Status line; `MemoryPerm`/`MemoryPermissions`/`BlockM` have no call sites outside `Gasm/Core` |
| Memory cost is 14 sets of inline, uncited literals | every load is flat `latencyCycles := 4`, every store `1`, duplicated per instance; 0 of 88 forms cite any calibrated or vendored source (`docs/TECHNICAL_NOTES.md` §2) |
| Stop reason was one undifferentiated bit | `faulted : Bool`; DIV/IDIV, HLT, Linux `sysExitHook`, and bare-metal HLT/debug-exit paths all wrote `true`. `runProgramTraceWithLoops` returned `[]` for fuel-out, no-instruction-at-rip, CPU fault, and clean halt alike (the historical stop-reason T12 finding) |
| Existing proofs that touch memory semantics | `step_ret_op` (`Stdlib/Zlib/CRC32Equivalence.lean:652`, `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean:139`, both `rfl`); `LoopInvariant.lean:598` (`simp [X86_64MachineState.read64, ...]`); `Stdlib/SmolAlloc/Equivalence.lean:42-45,140-142` (`read64` as observation). **No step lemma exists for any store form** — the read-over-write theory this design centralizes does not exist anywhere today |

## 2. The design in one page

One module family, `Gasm/Targets/X86_64/Memory*.lean`, exposing three coupled surfaces.
**Status** (corrected 2026-08-29): this line previously read "none of the three exists;
MH1/MH2/MH3 respectively." **Layers S and P exist** — Layer S landed as
`Gasm/Targets/X86_64/MemoryCell.lean` (the sealed cell), `Memory.lean` (`MemRef`, the
width-indexed API), `MemoryFrame/` (the frame-lemma set) and `MemoryFrameAudit.lean` (the
seal audit); Layer P landed as `MemCostModel.lean`, the registered instruction-family
derivations, and the memory-cost/provenance checks in `Tools/CheckX86Obligations.lean`. Layer A does
**not** exist and is superseded by the cross-architecture authoring design in
`docs/MEMORY_MODEL.md` §§6–7.

- **Layer S — the semantic hook.** Width-indexed `read`/`write` as the *only* functions
  that can touch machine memory bytes (the raw `memory` field is sealed behind a private
  projection), a canonical effective-address term (`MemRef`), and a new mandatory
  typeclass field `memAccesses : ι → List MemAccessSpec` — a **declarative access
  descriptor** stating, per instruction form, exactly which (kind, width, address)
  accesses its `step` performs. The descriptor is the load-bearing novelty: permissions,
  faults, perf, and measurement all read this one source (§3.3).
- **Layer A — the capability authoring surface.** A checked program type whose
  memory-operand constructors demand a capability citation plus an in-bounds proof, and
  which erases to today's `SymbolicInstr` list before encoding. Omitting the proof is a
  Lean elaboration failure — the artifact is unbuildable, which is Law 11's bar (§4).
- **Layer P — the memory cost table.** All memory-class uops are constructed by hook
  functions from one small coefficient table with Law-14 provenance marks. Per-form
  memory cost becomes *computed from the descriptor*, not hand-written 14 times; the
  falsifiable surface shrinks from "14 duplicated memory-cost blocks" to "one table of ~8
  named coefficients, each citing a calibration artifact or marked model-internal" (§5).

Two boundary decisions, argued rather than assumed:

1. **Address computation is exposed by the hook but the obligation attaches at
   dereference, not at address formation.** `MemRef.effectiveAddress` is one shared
   definition with one lemma set (today every memory `step` re-computes
   `s.gprs base + signExtend8To64 disp` inline). But LEA computes an effective address
   and performs no access — forming an out-of-bounds pointer is legal and useful x86;
   dereferencing one is not. So LEA carries no capability obligation, and the capability
   check quantifies over the hook's *access descriptors*, not over address arithmetic.
   This matches the capability-machine precedent (pointer arithmetic free, dereference
   checked) and keeps the obligation set exactly equal to the set of real accesses.
2. **Encodable instruction structures stay proof-free data; the capability proof lives
   one layer up and is erased.** The decoder, the differential fuzzers, and the
   roundtrip gate must construct arbitrary instruction instances from arbitrary bytes —
   a proof-carrying field on `MovMem64DispReg64` would make decoding impossible.
   Law 11's proof is therefore carried by the *authoring* term (Layer A) and erased
   before encoding — the zero-cost-proof-erasure shape `docs/API_STATE_MODELS.md`
   already establishes for `ComposedState`. The bypass this leaves open (authoring raw
   `SymbolicInstr` directly) is closed mechanically by a ratcheted ledger gate (§4.5),
   exactly as Law 11's text requires ("prohibited in migrated modules; unmigrated
   modules are tracked as critical backlog").

## 3. Layer S: the semantic hook

**Status** (corrected 2026-08-28): this line previously read "unbuilt; MH1. Sketches below
are design, not existing code." **Layer S is built.** The implementation and its enforcement
landed together. What exists in the tree:

| Design element | Landed as |
| :-- | :-- |
| Sealed memory cell (`private mk ::` + `private raw`) | `Gasm/Targets/X86_64/MemoryCell.lean` — split out of `Memory.lean` for an import-cycle reason recorded in that file's header |
| Width-indexed `read`/`write`, `readByte`/`writeByte`/`writeBytes`, `initRegion` | `Gasm/Targets/X86_64/MemoryCell.lean:79`–`:156` |
| `MemRef` | `Gasm/Targets/X86_64/Memory.lean:49` |
| `fault : Option X86_64Fault` (`.divideError | .memFault | .halted`) replacing `faulted : Bool` | `Gasm/Targets/X86_64/Registers.lean:84`; `X86_64Fault` at `:66` |
| The §3.4 lemma set | `Gasm/Targets/X86_64/MemoryFrame/` — per-family frame proofs, shared register-only and exact singleton store/load derivations, plus a Law-13 negative control |
| Seal audit (the §3.2 tier-3 fallback) | `Gasm/Targets/X86_64/MemoryFrameAudit.lean` |
| `memAccesses`, defaultless | `Gasm/Targets/X86_64/Instructions/Base.lean:66`, cited from `:40` as the reason it has no default |

The fenced blocks in §3.1–§3.4 below are still the **design sketches as written**; they are
not transcriptions of the landed code and names and signatures differ in places. Read the
tree, not the sketch, for the current API — and see §3.2's CORRECTION block for the two
sealing claims this section got wrong.

### 3.1 Types and API

```lean
inductive MemWidth | w8 | w16 | w32 | w64          -- 1/2/4/8 bytes
def MemWidth.bytes : MemWidth → Nat

/-- Canonical x86-64 effective-address term: base + index*scale + disp.
    The original MH1 forms use only base+disp8/disp32; index is the forward slot ISA
    expansion fills without a new address representation. -/
structure MemRef where
  base  : Reg64
  index : Option (Reg64 × Nat) := none   -- scale ∈ {1,2,4,8}
  disp  : Int := 0

def MemRef.effectiveAddress (m : MemRef) (s : X86_64MachineState) : Address

inductive MemAccessKind | load | store

/-- One declared access: static shape (kind, width, addressing term), dynamic address
    obtained by evaluating `ref` against the pre-step machine state. -/
structure MemAccessSpec where
  kind  : MemAccessKind
  width : MemWidth
  ref   : MemRef

-- The data path: the ONLY readers/writers of machine memory bytes.
def X86_64Mem.read  (w : MemWidth) (a : Address) (s : X86_64MachineState) : UInt64
def X86_64Mem.write (w : MemWidth) (a : Address) (v : UInt64) (s : X86_64MachineState) : X86_64MachineState
-- Derived: push64/pop64 (RSP adjust + write/read), initRegion (loader image install).
```

`read64`/`write64`/`write8`/`push64`/`pop64` survive as `abbrev`s delegating to the hook
(definitionally equal to today's byte ladders), so every existing `rfl` step lemma keeps
closing — see §7. The missing widths (`read8`, `read32`, `write32`) exist from day one,
retiring the three inline raw-lambda re-implementations in `Mov.lean`.

### 3.2 Sealing the raw field (what makes the chokepoint mechanical, not conventional)

The `memory` function moves behind a wrapper whose projection is `private` to the hook
module:

```lean
structure X86_64Memory where
  private mk ::
  private raw : Address → Byte
```

`private mk ::` + `private raw` elaborate at this repo's pinned toolchain (v4.33.1), and
`private` is module-scoped in Lean 4: outside the defining module (which landed as
`Gasm/Targets/X86_64/MemoryCell.lean`, not `Memory.lean` — see that file's header for the
import-cycle reason), the names `X86_64Memory.mk` and `X86_64Memory.raw` do not resolve,
`⟨f⟩` and `{ raw := f }` are rejected, and `m.raw`/`m.1` are rejected.

> **CORRECTION (2026-08-28, adversarial review).** This paragraph previously claimed that
> "neither constructing an `X86_64Memory` from a raw function nor projecting one out
> elaborates", and called the result "Law 13 preference-tier 1 — the bypass is
> *unrepresentable*, not linted". Both halves were wrong, and the negative control that
> was said to have verified them only exercised `mk` and `raw` directly.
>
> 1. **Projection is not sealed.** `private mk ::` does not privatize the auto-generated
>    eliminators. `X86_64Memory.casesOn`, `.rec` and `.recOn` are public, and
>    `m.casesOn (fun f => f)` returns the raw `Address → Byte` from any module — it
>    elaborates, compiles, and runs.
> 2. **Construction was never sealed, by design.** `X86_64Mem.initRegion` is public and
>    takes an arbitrary `Address → Byte`; that is exactly "constructing an `X86_64Memory`
>    from a raw function", and the very next sentence of this section describes it as
>    intentional. The mechanism is right; the sentence denying it was wrong.
> 3. **The leak is semantically empty**, which is why (1) is a lint issue and not a
>    soundness one: `X86_64Mem.readByte` is public and total, so
>    `fun a => X86_64Mem.readByte m a` is the raw function too, and is `rfl`-equal to the
>    `casesOn` term. Byte-level observation is deliberately available.
>
> So the property the seal actually buys is **not** confidentiality of the bytes. It is
> that every memory touch goes through a *named* function in the hook module, keeping the
> set of access sites enumerable so that fault checks, Law 11 permission checks and cost
> accounting have one place to land. That is an auditable-chokepoint property, and it is
> enforced at **preference-tier 3** by the seal audit in
> `Gasm/Targets/X86_64/MemoryFrameAudit.lean` (the fallback this section's Status
> paragraph already anticipated), which fails the build if any declaration outside the
> hook module names one of the three eliminators. Tier 1 was considered and rejected on
> the merits: making the type genuinely opaque removes definitional unfolding, so
> `X86_64Mem.read`/`write` could no longer be *defined* over it without an axiomatized
> API — trading a semantically empty lint gap for real non-standard axioms in a tree whose
> trust story is axiom-gated.

Instruction steps, Win32 interceptor hooks, and loaders all route through the hook's API;
the loaders get a dedicated `initRegion`/`initImage` entry point (installing an executable
image is a legitimate bulk write, and giving it a named API keeps it inside the chokepoint
rather than allowlisted around it). Spec/proof-side *observation*
(`SmolAlloc/Equivalence`'s `read64` assertions) uses the read API and is unaffected.

**Status** (corrected 2026-08-28): this line previously said the sealed wrapper and the
migration of all raw access sites "are MH1's deliverable" — future tense. **They landed.**
The sealed wrapper is `Gasm/Targets/X86_64/MemoryCell.lean`; the five helper definitions,
the three inline instruction lambdas, the Win32 hook lambdas and `loadMemory` all route
through the hook's API. The contingency this line described — "if the hook module must
later split, the fallback is a compiled-environment audit … tier 3, only if tier 1 proves
untenable" — is **what actually happened, for a different reason**: tier 1 turned out not
to be reachable at all (see the CORRECTION block above), so the audit is not a contingency
but the live enforcement, and it exists as `Gasm/Targets/X86_64/MemoryFrameAudit.lean`.

### 3.3 The declarative access descriptor — the one source four consumers read

`X86_64Instruction` gains one field, **with no default** (the same forcing-function
choice `roundtripCases` made, and the opposite of the choice that let `canFuzzHardware`
opt-outs go silent — `docs/X86_ISA_EXPANSION_PREREQUISITES.md` P4):

```lean
class X86_64Instruction (ι : Type u) where
  ...
  memAccesses : ι → List MemAccessSpec   -- NO default: omission is a compile error
```

Register-only forms write `memAccesses _ := []` — one explicit line, 74 instances.
Memory forms declare their accesses: `PushR64` declares
`[⟨.store, .w64, ⟨.rsp, none, -8⟩⟩]`; `MovReg64Mem64Disp` declares
`[⟨.load, .w64, ⟨basePtr, none, disp⟩⟩]`. Addresses are evaluated against the
**pre-step** state, uniformly.

The descriptor is *data about* the step function, so it is a Law-12 twin of the step's
actual behavior and must be linked by a connection obligation, per family:

```lean
-- WritesWithin: step never writes outside its declared store footprint.
theorem Foo.writesWithin : ∀ (i : Foo) (s : X86_64MachineState) (a : Address),
    a ∉ storeFootprint (memAccesses i) s → (step i s).memory a = s.memory a
-- ReadsWithin: step's result depends on memory only through its declared load footprint.
theorem Foo.readsWithin : ∀ (i : Foo) (s₁ s₂), agreeOutsideRegs s₁ s₂ →
    agreeOn (loadFootprint (memAccesses i) s₁) s₁ s₂ → step i s₁ ≈ step i s₂
```

The memory-form obligations are discharged either directly from the corresponding hook calls or
through exact shared derivations whose premises bind the descriptor to the semantic step. The first
singleton-store consumers are `MovMem32DispReg32` and `MovMem64DispReg64`; register-only forms use
the shared memory-preservation derivation. The first singleton-load consumers are
`MovReg32Mem32Disp` and `MovReg64Mem64Disp`. The W32 family now subsumes the former
RSP-specific identity. The proofs live in the
`RoundtripGate/*`-style per-family shard convention so a new memory form cannot land
without them. **Status** (corrected 2026-08-28): this line previously read "unbuilt; MH1
(field + 14 real descriptors + frame lemmas for the memory families), with the
register-form batch lemma in the same change." **It is built.** `memAccesses` is a field
with **no default** at `Gasm/Targets/X86_64/Instructions/Base.lean:66` — so omitting it is
a compile error, exactly the gate §8's H1 row names — and `:40` cites this section by name
as the reason. The frame lemmas live in `Gasm/Targets/X86_64/MemoryFrame/` under the
per-family shard convention described above.

Why the descriptor rather than just centralized read/write calls — four consumers read
this one source:

1. **Permissions (§4).** The Law-11 obligation is stated as: every element of
   `memAccesses i` falls inside a granted capability. Quantifying over a small static
   list of `MemAccessSpec`s is tractable at assemble time; quantifying over "whatever
   the step body happens to do" is not.
2. **Faults (§6).** When a memory map lands, the *interpreter* — not each instruction —
   checks the descriptor before applying `step`: on violation it stops with the
   **pre-step** state plus a structured fault. This is hardware-faithful (`#PF` leaves
   the instruction's register writes unperformed), and it is impossible to get right
   inside a `step` body that has already half-executed. Fault semantics land by editing
   the interpreter + hook only; zero instruction edits.
3. **Perf (§5).** An access's static shape (kind, width, addressing form) determines its
   uops and cost; the hook derives memory uops from the descriptor, so per-form cost is
   computed, not transcribed.
4. **Measurement.** The address stream of a run is `memAccesses` evaluated along the
   trace — exactly what a future cache/locality model (`docs/TECHNICAL_NOTES.md` §2) and the
   hardware timing harness's containment checks consume, obtained without instrumenting the
   interpreter.

Known limit, stated now: a static `List MemAccessSpec` cannot express
state-*dependent access counts* (REP-class string ops, masked SIMD stores). The
extension slot is a second constructor (`.dynamic : (X86_64MachineState → List ...)`)
added when a spike demands such an instruction (Law 5); the 88 current forms and the
expansion's Wave A/B (`docs/X86_ISA_EXPANSION_PREREQUISITES.md` §6) are all static.

### 3.4 The lemma set (what "one place" buys proofs)

The hook module hosts, once, the theory every future memory proof needs and which today
exists nowhere (no store-form step lemma exists in the tree):

- **Read-over-write**: `read w a (write w a v s) = truncate w v`;
  `read w₁ a₁ (write w₂ a₂ v s) = read w₁ a₁ s` when `[a₁,a₁+w₁) ∩ [a₂,a₂+w₂) = ∅`.
- **Width decomposition**: `read64` as the composition of byte reads (today implicit in
  the ladder definitions, needed explicitly by every buffer proof).
- **Push/pop roundtrip**, `initRegion` read-back, and footprint algebra
  (`storeFootprint`/`loadFootprint` union/disjointness lemmas).
- The per-family `writesWithin`/`readsWithin` frame lemmas of §3.3 — candidate building
  blocks for the canonical M1 indexed authoring surface's routine frame conditions
  (`docs/VISION.md` §4: "capability tokens … are also the frame conditions").

**Status** (corrected 2026-08-28): this line previously read "unbuilt; MH1". **The lemma
set is built** across `Gasm/Targets/X86_64/MemoryFrame/`, with byte-granular read-over-write,
exact singleton store/load derivations, and `initRegion` read-back proved in shared modules and a
Law-13 negative control in `MemoryFrame/NegativeControl.lean`. The W32/W64 register-to-memory
stores above are the first singleton-store consumers; `MovReg32Mem32Disp` and
`MovReg64Mem64Disp` are the first singleton-load consumers.
The disjointness lemmas are `omega`-class arithmetic over
`UInt64` intervals; wraparound at 2⁶⁴ is handled the way `MemoryPerm.validRange`
already does (a no-overflow side condition carried by the capability, not re-proven per
access).

## 4. Layer A: assemble-time capability enforcement

**Status**: historical design input, unbuilt, and **superseded**. The retired MH3/PA4
sequence below is not an active implementation plan. `docs/MEMORY_MODEL.md` M1 now owns
the checked indexed authoring surface, provenance, typed views, canonical state forms, and
elaboration budget; M4 owns cross-thread authority transfer. The sketches in this section
remain useful requirements and examples only where they agree with that canonical design.

### 4.1 The problem Law 11 actually poses

At authoring time addresses are symbolic: whether `mov qword [rbx+8], rax` is in bounds
depends on what `rbx` holds at that program point. A capability over a *concrete* range
cannot be checked against a register-relative operand without a statement about the
register. The capability must therefore be **register-anchored**: "at this routine's
entry, register R points at the base of a region of `len` bytes held with share S."
That is the frame condition the retired PA1/PA4 analysis identified for upgrade into a
real capability obligation; M1 decides its current representation and enforcement shape.

### 4.2 The obligation shape

```lean
/-- One entry of a routine's memory frame: at entry, `anchor` holds the base address of
    a region of `len` bytes, granted with `share`. Backed by a `MemoryPerm` at the
    concrete address the caller proves in scope (Gasm/Core/Permissions.lean). -/
structure RegionSpec where
  anchor : Reg64
  len    : Nat
  share  : PermissionShare

abbrev Frame := List RegionSpec   -- pairwise-disjointness via DisjointTokens (Core)

/-- The per-access obligation: under frame Γ and the author-stated program-point
    precondition `Inv` (an invariant relating current register values to the entry
    anchors), every declared access of instruction `i` lands inside a region of Γ whose
    share admits the access kind. -/
def AccessOK (Γ : Frame) (Inv : X86_64MachineState → Prop)
    (acc : MemAccessSpec) : Prop := ...
```

A checked program is a term whose memory-instruction constructors demand this proof:

```lean
-- What an author writes, static-offset case (the RSP-frame / header-field pattern that
-- dominates Stdlib/Zlib/X86_64.lean):
CheckedAsm.store64 (frame := Γ) ⟨.rsp, none, 0x28⟩ .rax
    (h := by mem_bounds)   -- auto-param; discharges 0x28 + 8 ≤ Γ's rsp-region length by decide/omega

-- The dynamic case (loop over a buffer): the proof term cites the loop invariant.
CheckedAsm.load8 ⟨.rsi, none, 0⟩ .r9 (h := inv_implies_rsi_in_input_region ...)
```

Omit `h` where no auto-param can discharge it and the term **does not elaborate** — the
program is unbuildable, which is Law 11's bar. The proof is *carried* by the program
term; for literal-displacement accesses against declared regions it is discharged
automatically (a `decide`/`omega` auto-param over literals — Law 10 rung 2, no axiom);
for computed addresses the author supplies an invariant-derived proof term, reusing the
existing loop-invariant machinery where M1's indexed surface and automation admit it.

### 4.3 What v1 does and does not make unrepresentable (the honest line)

v1's frame is **entry-anchored, not flow-sensitive**: `Γ` binds anchors at routine
entry, and the connection between "current register values" and "entry anchors" is the
author-stated invariant `Inv`, discharged semantically (in the routine's safety proof),
not tracked in the type system through every `add rsi, 1`. Consequences, stated
plainly:

- **Unrepresentable in v1**: a memory access with *no* capability citation at all (the
  Spike-4/Zlib class where nothing anywhere says which region an access belongs to);
  any literal-offset overrun of a declared region (`mov [rsp+4096], x` against a
  4096-byte frame fails `decide` — undischargeable, at elaboration time); a write
  citing a `ReadOnly` region.
- **Carried-but-semantically-discharged in v1**: dynamic in-boundedness (loop index
  < length). The obligation cannot be omitted — the constructor demands the proof term
  — but its truth rests on the stated invariant, proven in the routine's `MemSafe`
  theorem (§4.4), not by the elaborator alone.
- **Historically deferred to PA2/PA3**: flow-sensitive capability transfer (register copied
  to register, region split across a call, `BlockM`-indexed frames). That sequencing is
  superseded. The canonical M1 entry gate now requires the indexed authoring surface,
  canonical state forms, automation, and an elaboration budget before normative capability
  implementation starts. This entry-anchored `Frame` sketch may be reused only if M1 proves
  it is a sound component of that accepted surface; it is not a separately landable v1.

### 4.4 The soundness theorem (what the carried proofs *mean*)

Per checked routine, the DSL's obligations compose into one statement:

```lean
theorem MemSafe : ∀ s₀, Pre Γ s₀ →
    dynamicFootprint (run (erase prog) s₀) ⊆ grantedFootprint Γ s₀
```

where `dynamicFootprint` is the union of `memAccesses` along the trace (§3.3 makes this
definable without interpreter instrumentation, and the frame lemmas make it provable).
This is what turns the carried tokens into Law 11's "capabilities double as frame
conditions": a caller composes with a checked routine knowing its entire memory effect
is inside `Γ`, with no global reasoning. **Historical status**: this was MH3's proposed
theorem shape and one-routine acceptance bar. Current acceptance is `docs/MEMORY_MODEL.md`
M1's indexed-authoring exit criterion, followed by M4 for cross-thread transfer.

### 4.5 Erasure, coexistence, and unconditional admission

`CheckedAsm.erase : CheckedProgram Γ → List SymbolicInstr` — proofs erased, encoding
unchanged, so the assembler/linker/emitter pipeline is untouched. Old and new authoring
coexist mechanically:

- A gate rejects raw memory-operand `SymbolicInstr` construction outside designated
  infrastructure modules (erasure, decoder, fuzzers, and roundtrip machinery). The
  covered constructor set is derived from the registry rather than hand-maintained.
- **"Does not need the discipline" is mechanical, not declared**: a module with no
  memory-operand constructors acquires no proof burden. A module that selects such a
  constructor must use the checked authoring path; there is no bypass ledger.

**Historical status**: the earlier MH3 draft proposed a migration ledger, but it was never
built and exception ledgers are now forbidden. M1 must gate the accepted authoring boundary
directly and add the Law-13 negative control described above.

### 4.6 Relation to the read-binder contract (deliberately not unified)

`docs/READ_BINDER_CONTRACT.md` §5's conclusion is preserved verbatim by this design:
the read-binder's quantifier ranges over the **syscall's declared cap** and must not be
capped by the destination buffer's capacity — the gap between the two *is* Spike 4's
bug. The hook sits on the other side of that composition: it bounds **writes** by the
**destination capability**. The two meet at exactly one point: a syscall interceptor
that delivers read bytes into program memory (`readFileHook`, `recvHook`) performs its
writes through `X86_64Mem.write` like any instruction (§3.2), and in a checked program
the continuation's write-safety obligation sits *inside* the read's universal
quantifier, exactly as §5 of that document specifies. With `requested = 128` against a
16-byte region, `AccessOK` is undischargeable for the quantified lengths 17–128 — the
overflow is a proof failure at authoring time rather than an invisible scribble.
Nothing here narrows the read quantifier; nothing there weakens the write bound.

## 5. Layer P: the perf side, and how it stays falsifiable

**Status** (corrected 2026-08-29): built. `Gasm/Targets/X86_64/MemCostModel.lean` owns the
provenance-marked coefficient table and `memUops`; the registered memory-touching forms derive
their memory uops through it; `Tools/CheckX86Obligations.lean` audits the derivation and reports
provenance. Calibration remains incomplete exactly as §5.2 states.

### 5.1 One table, provenance-marked, instead of 14 sets of inline literals

```lean
/-- Every memory-cost coefficient in the model, in one place, each carrying Law 14
    provenance. Initial contents are today's de-facto values (load-to-use 4, store 1),
    relabeled honestly as model-internal rather than left implicit in 14 instances. -/
structure MemCostModel where
  loadToUseL1     : Cited Nat      -- cycles, L1 hit
  storeAddrCost   : Cited Nat
  storeDataCost   : Cited Nat
  loadPorts       : Cited (List PortId)
  storeAddrPorts  : Cited (List PortId)
  storeDataPorts  : Cited (List PortId)
  -- per-width / indexed-addressing deltas as they become measurable (F1)

inductive Provenance
  | modelInternal                    -- uncalibrated; counted and printed by the gate
  | calibrated (artifact : String)   -- cites a Law-14 calibration file (F2's format)

structure Cited (α : Type) where value : α ; source : Provenance
```

The hook exposes the only constructors of memory-class uops —
`memUops : MemAccessSpec → MemCostModel → List X86_64Uop` — and MH2 replaces the 14
forms' duplicated inline uop blocks (a Law-12 unlinked-twin population: the identical
`MOV.storeAddr`/`MOV.storeData` literal block is hand-copied across every store form
today) with `memAccesses i |>.flatMap (memUops · costModel)`. Construction of a uop
with `uopClass ∈ {.load, .storeAddr, .storeData}` outside the hook is closed off the
same way §3.2 seals memory (a private-constructor cost tag on memory uops, with a
source-linter fallback), so a new instruction *cannot* introduce a fresh invented
memory latency — the coefficient set is closed under the table.

### 5.2 Why this is falsifiable where today's numbers are not

Today's memory cost claims are unfalsifiable for a structural reason: they are 14
scattered literals with no stated measurement that could contradict them
(`docs/TECHNICAL_NOTES.md` §2: the coefficients lack calibrated sources). The hook changes the
*shape* of the claim:

1. **The coefficient set is finite, enumerable, and small** (~8 named fields), because
   every per-form number is derived. Calibrating a coefficient recalibrates every form
   at once; a coefficient the harness cannot measure stays `modelInternal` and is
   *counted* — "N of M memory coefficients calibrated" in gate output (Law 14's
   honesty-in-output clause), instead of invisible.
2. **Each coefficient names its future refuting experiment.** The landed table documents,
   per field, the microbenchmark shape needed to measure it (load-to-use: dependent
   pointer-chase resident in L1; store costs: store/reload chains). The existing
   RDTSC/RDTSCP harness measures whole repeated instruction streams and cycles only; its
   containment and rank-order checks are per instruction, not per memory coefficient, and
   cannot isolate these table fields or validate uop decomposition. Dedicated coefficient
   kernels (and any PMU-backed evidence required by those recipes) remain future work. No
   result is accepted and bound to the six fields; every field remains `modelInternal`.
3. **The derivation itself is checkable.** "Every memory uop in every form equals
   `memUops` of its descriptor" is decidable over the registry's witness population
   (`allEncodableInstructions`) and belongs in the registry audit — so the gate can
   verify no form bypasses the table, mechanically.

What Layer P deliberately does **not** build now: an address-dependent cost model
(cache hierarchy, A0). The seam is designed — the descriptor stream of §3.3 is the
address trace a cache model consumes, and `memUops` is the single site where cost
would become locality-dependent — but building the hierarchy model is demand-driven
(Law 5; the forcing function is the zlib epic's ranking needs, F6). Designing the seam
without the model is the point of a hook.

### 5.3 What the hook hands the per-instruction validation-and-calibration gate

The landed registry gate gets from this design: (a) a mechanical
memory-touching predicate per form (`memAccesses ≠ []` — no heuristics, no silent
opt-out, because the field has no default); (b) the closed coefficient table with
per-field provenance status to count and print; (c) the derivation invariant of
§5.2(3) to check against the registry; (d) per-coefficient measurement recipes to
drive hardware containment checks; (e) the descriptor-vs-step frame lemmas (§3.3) as the
per-family proof obligation whose absence the gate flags. Items (a)–(c) are enforced now;
their enforcement does not imply that any calibration result has been accepted.

## 6. Faults and observability

Two changes, deliberately staged:

1. **Fault/stop plumbing now** (MH1, cheap): `faulted : Bool` on `X86_64MachineState` is
   replaced by `fault : Option X86_64Fault := none` with
   `def X86_64MachineState.faulted (s) : Bool := s.fault.isSome` — every existing
   *reader* (`if s'.faulted then …` in the interpreters) compiles unchanged. DIV/IDIV write
   `.divideError`; HLT, Linux process exit, and bare-metal exit paths write `.halted` so a clean
   termination is not mislabeled as a CPU exception.

   ```lean
   inductive X86_64Fault
     | divideError                                              -- #DE
     | memFault (kind : MemAccessKind) (width : MemWidth) (addr : Address)
     | halted                                                   -- HLT / platform exit signal
   ```

   A memory fault is thereby a *distinguishable, data-carrying* outcome from the day
   the type exists — never a third indistinguishable `[]`. This composes with (does
   not duplicate) the future `Except`-shaped stop-reason result, which
   distinguishes fuel-out / no-instruction / fault as stop *reasons*; this design
   supplies the fault reason's *payload*, so the combined outcome type is
   `fuelExhausted | noInstructionAtRip | faulted (f : X86_64Fault) | completed`, with
   no two outcomes sharing a representation. Whichever half lands second must preserve both
   the outer stop-reason distinction and the fault payload.
2. **Fault semantics on demand** (deliberately not now): making `memFault` *reachable*
   requires a memory map / granted-region model in the machine state — machine-state
   surface the owner has ruled expands demand-driven, spike-forced (Law 5; the P1
   ruling). When that spike arrives, the implementation site is already fixed by §3.3:
   the interpreter checks the instruction's descriptor against the map *before*
   applying `step`, and faults with the pre-step state — hardware-faithful, zero
   instruction edits. Until then, this document does not claim the model can produce a
   memory fault: it cannot, and saying otherwise would be the exact overclaim
   `docs/TECHNICAL_NOTES.md` §2 catalogs. **Status**: `X86_64Fault` and the field change were
   built in MH1; the map and the interpreter pre-check have no task yet and are named as
   future, spike-forced work.

Law 11 enforcement does not depend on stage 2: the assemble-time obligation (§4) is
the enforcement mechanism; the runtime fault model is model-fidelity work (B3) and
belt-and-braces observability, not the gate.

## 7. Effect on existing proofs

Inventoried against every memory-semantics-touching proof in the tree (§1.1's last
row):

- **`step_ret_op` (two copies, `rfl`)**: unchanged. `read64` remains definitionally the
  same byte ladder (an `abbrev` into the hook); `pop64` likewise. `rfl` still closes.
- **`LoopInvariant.lean:598`** (`simp [X86_64MachineState.read64, hmem2]`): the unfold
  target gains one definitional layer. Mitigation: the hook ships an `@[simp]`
  unfolding set, and MH1's acceptance criterion is that this file (and
  `CRC32Equivalence.lean`, `SmolAlloc/Equivalence.lean`) build with at most
  simp-set-name adjustments — measured, not hoped.
- **`SmolAlloc/Equivalence.lean`** (`read64` as observation): unchanged (abbrev).
- **Fetch/`decide` facts** (`instructionAtRip` over encodings): untouched — the hook
  does not alter `encode`, so every encoding-derived `decide` fact and the entire
  roundtrip gate are outside the blast radius.

Net assessment, stated as the design input it is: **the hook makes memory proofs
easier, and the honest reason is that today there is almost nothing to break** — no
store-form step lemma exists anywhere, so every future memory proof (including the M1/M4
capability migration through Zlib) would otherwise re-derive read-over-write and byte-decomposition
facts ad hoc, per width pair, per file. Centralizing the theory before that population
exists is the cheap moment. The two real risks on the other side of the ledger:

- **Opacity risk**: if hook definitions were made `irreducible` or the lemma set is
  incomplete, `rfl`/`simp`-style proofs stall against the extra layer. Mitigation:
  definitions stay reducible; the §3.4 lemma set is part of MH1's definition of done,
  and the three existing proof files are its regression suite.
- **Cascade risk**: the hook module sits below `Instructions/*`, so a cost-table edit
  rebuilds the same ~39-module cascade B3 measures for any instruction-layer edit. The
  table therefore lives in its own leaf module so *semantic* hook changes and *cost*
  changes cascade independently — but the structural fix is B3 itself, and this design
  inherits (does not worsen or fix) that dependency. Recorded as a known cost.

## 8. Migration

Phased so that each phase is independently landable, `rfl`-preserving where it touches
proofs, and gated. Counts are from §1.1 (14 memory forms of 88; 74 register-only).

**Status**: historical landing sequence. H0–H2 landed. H3/H4 never landed and their
MH3/PA4 sequencing is retired; current checked-authoring work enters through
`docs/MEMORY_MODEL.md` M1, while cross-thread transfer enters through M4.

| Phase | Task | Content | Size | Gate that makes it stick |
| :-- | :-- | :-- | :-- | :-- |
| H0 | MH1 | Hook module: sealed memory field, width-indexed read/write, `MemRef`, missing widths; migrate 5 helpers, 3 inline instruction lambdas, Win32 hook writes, loader `initRegion`; `fault : Option X86_64Fault`; §3.4 lemma set | ~1 module + ~20 call sites | `private` field: raw access fails to elaborate (mutation-verified) |
| H1 | MH1 | `memAccesses` field, **no default** → all 88 instances (74 × `[]`, 14 real); frame lemmas for the 14 + batch lemma for the 74 | 88 one-liners + 14 lemma pairs | Compile error on omission (no default); shard convention for the lemmas |
| H2 | MH2 | `MemCostModel` + `memUops`; delete 14 forms' inline memory-uop literals; provenance counting in gate output; derivation-invariant check in the registry audit | 14 forms + 1 table | Private cost tag / linter: memory uops constructible only via hook |
| H3 (retired) | MH3 | Historical `CheckedAsm` v1 + erasure + `MemSafe` proposal; superseded by M1 | DSL + 1 routine | Historical ledger proposal; M1 must select the actual gate |
| H4+ (retired) | PA4 | Historical module-by-module migration ordering; superseded by M1/M4 | the long tail | Historical ledger-zero target; current exit criteria live in `MEMORY_MODEL.md` |

H0–H2 are complete and remain reusable infrastructure. The old H3/H4 coexistence and
ledger story is not active: mass memory-operand authoring waits for M1's accepted checked
authoring surface and bypass gate, and cross-thread authority transfer waits for M4.

**Current ordering.** M0 fixes the common event surface; M1 then fixes the indexed authoring
surface, normal forms, automation, and elaboration budget. M4 adds cross-thread authority
partition and lifecycle transfer after M1 and M3. A standalone entry-frame DSL must not land
ahead of those gates merely because the historical H3 proposal allowed that sequencing.

## 9. What this design rejects, and why

- **Runtime permission checks as the enforcement mechanism** — Law 11 mandates
  fail-to-assemble; a model-level check catches at simulation what the type system
  should have refused at construction. (Model-level checking still arrives later as
  fault *semantics*, §6 stage 2 — fidelity, not enforcement.)
- **Proof fields on encodable instruction structures** — kills the decoder and every
  differential fuzzer (§2 boundary 2).
- **Unifying the hook's capability bound with the read-binder's quantifier bound** —
  would make Spike 4's overflow provable-safe by construction
  (`docs/READ_BINDER_CONTRACT.md` §5); the two bounds stay distinct and compose (§4.6).
- **Treating the historical entry-anchored v1 carrier as the current sequence** — the
  canonical plan now gates normative capability implementation on M1's indexed authoring
  surface, normal forms, automation, and elaboration budget (§4.3 and
  `docs/MEMORY_MODEL.md` §§14–15).
- **Building the cache-hierarchy cost model now** — Law 5; the hook designs the seam
  (descriptor stream + single cost site) and stops (§5.2).
- **An arch-generic Core hook typeclass now** — Wasm's memory already has its own
  bounds-checked, trapping access path (post-B7); abstracting over two targets with
  one instance each is speculative structure (Law 8 risk). The x86-64 hook's shapes
  (`MemWidth`, descriptor, cost table) are written to generalize, and Core already owns
  the capability vocabulary; the typeclass gets extracted when a third target demands
  it.

## 10. Historical owner questions and dispositions

1. **Q1 — v1 obligation strength (§4.3): superseded.** The owner no longer needs to choose
   between an entry-only carrier and later typestate. `docs/MEMORY_MODEL.md` M1 requires the
   indexed authoring surface up front, with canonical normal forms, automation, and an
   elaboration budget; M4 adds cross-thread transfer.
2. **Q2 — `MemRef` as the expansion's operand convention: still a target-level design
   question, not a competing memory-model plan.** Resolve it in the x86 target/expansion work
   after M1 fixes the capability-bearing authoring boundary. It must not change the canonical
   cross-architecture authority model or bypass M1's stage-entry gate.
3. **Q3 — the `memAccesses` mandatory field: resolved.** The no-default field requires every
   registered form to declare its accesses explicitly; omission is a compile error and the
   frame/registry audits are built (§3).

## 11. Follow-on work

| Work item | Track | Content | Status / dependency |
| :-- | :-- | :-- | :-- |
| Semantic x86 memory hook | proof-arch | §3 + §6 stage 1 | complete |
| Memory-uop centralization | perf | §5 | complete; coefficients remain uncalibrated |
| Indexed capability authoring | proof-arch | §4, revised by `docs/MEMORY_MODEL.md` §§6–7 | stages M1/M4 after M0 |

The capability migration must consume §4 as historical input but use the resource algebra,
typed obligations, and exit criteria in `docs/MEMORY_MODEL.md` §§6–7 and 14. Frame lemmas and
§4.4's `MemSafe` shape remain candidate building blocks, consistent with
`docs/READ_BINDER_CONTRACT.md` §9 item 4. Fault/stop-reason work coordinates with §6;
future calibration work must replace §5's placeholder cost table with sourced data.

## 12. Cross-target note: Wasm

The owner asked directly whether anything here needs to generalize to the Wasm target.
**Status**: §12.3's seal is implemented and verified in the tree (below); §12.1, §12.2,
§12.4, §12.5, and §12.6 are analysis, not new machinery — each says explicitly which of
its claims were checked by reading code/running gates versus recommended for later.
Verified against `main` at `27ab4ed` and later rechecked after the x86-64 seal-audit
correction cited in §12.3 by reading `Gasm/Targets/X86_64/MemoryCell.lean`,
`Gasm/Targets/X86_64/Memory.lean`, `Gasm/Targets/X86_64/MemoryFrameAudit.lean`,
`Gasm/Core/Permissions.lean`, `Gasm/Core/State.lean`, `Gasm/Targets/Wasm/Semantics.lean`,
`Gasm/Targets/WASI/ABI.lean`, and the authority design now consolidated in
`docs/MEMORY_MODEL.md` §6, and by `grep`-confirming
call-site counts asserted below.

### 12.1 The asymmetry, verified

§9's rejected-idea list already asserts the shape of the argument ("Wasm's memory already
has its own bounds-checked, trapping access path"); this subsection checks it against the
tree rather than repeating it.

- **x86-64 has no runtime bounds check anywhere in the model.** `X86_64Mem.read`/`write`
  (`MemoryCell.lean`) are total over all of `Address`; nothing in the machine state or the
  interpreter can refuse an access. The *only* place an out-of-range access can be refused
  is before the fact, at authoring/assembly time — which is exactly Law 11's mandate and
  exactly why it is phrased as fail-to-assemble: there is no other stage at which "this
  access is illegal" can be observed at all, runtime included.
- **Wasm's specification mandates a runtime bounds check on every memory access**, and the
  model now honors it: `wasm-exec-instructions#memory-instructions`'s reduction rule for
  `t.load`/`t.store` ("If `i + ao.offset + N/8 > |mems[x].bytes|`, then: Trap.") is
  implemented in `evalLeafInstr`'s six memory-instruction cases
  (`Gasm/Targets/Wasm/Semantics.lean`) and confirmed by the differential fuzzer's
  nine out-of-bounds/memory-limit cases against a real host engine (Node/V8) — not merely
  asserted by the Lean model in isolation. A Wasm program is therefore memory-safe at
  *runtime*, by the interpreter's own construction, independent of anything the program's
  author did or didn't prove.
- **The asymmetry holds, and it is not a matter of degree.** x86-64 needs a carried
  capability proof because nothing else will ever refuse a bad access; Wasm needs no such
  proof for memory-safety-in-the-narrow-sense (no OOB read/write can occur, full stop —
  every access either lands in bounds or the whole instruction traps) because the
  interpreter itself refuses it, every time, mechanically, before the access happens.

**What this means for Law 11's scope.** Law 11's text ("every instruction that reads or
writes memory MUST carry proof of a valid, in-scope capability... Program construction
MUST fail... when that proof is absent") is written in x86-64's vocabulary
(`MemoryPerm`, fail-to-*assemble*) and does not transfer to Wasm by substituting a
different capability type — there is nothing for a Wasm capability to *buy* that the
interpreter does not already guarantee unconditionally. The obligation that *does*
transfer is the goal one level up: "establish that a memory access is legal before it
executes." For x86-64 that goal is discharged at assembly time (no other option exists).
For Wasm it is discharged at run time by the interpreter, per access, automatically — so
the Wasm-shaped version of Law 11's goal is not "prove you may access this address," it
is **"prove this program does not trap"** (a liveness/functional-correctness property of
the *program*, not a memory-safety property of the *access*) — and that property is
already exactly what the WASI platform's `VerifiedProgram.traceEquivalence`
(`Gasm/Targets/WASI/ABI.lean`) plus each spike's own `#guard
!(runWasiTraceState ...).isError` check are in the business of proving: a spike's
`traceEquivalence` theorem is false if the modeled run ever traps somewhere the spec
doesn't say it should, because a trapped run's event trace stops short of the
spec's. **Recommendation, not a ruling**: Law 11 should not be reworded to cover Wasm; a
future Wasm-specific law/clause (if one is ever warranted) would read "every
The WASI `VerifiedProgram` MUST prove its complete execution outcome never traps outside the cases its
`spec` models," which is a restatement of the existing equivalence-proof obligation, not
a new mechanism. No such clause is proposed here — Law 5: nothing currently demands it,
`traceEquivalence` already carries the weight, and writing a law around one restated
sentence is exactly the kind of premature structure Law 8 warns against.

### 12.2 What generalizes and what is target-specific

Assessed against the "what else plausibly generalizes" list, each checked rather than
assumed:

- **`MemWidth`/`MemAccessKind` (the atomic enums, `X86_64/MemoryCell.lean`) carry zero
  x86-specific content** — `w8`/`w16`/`w32`/`w64` and `load`/`store` are meaningful for any
  byte-addressed target, Wasm included. They are the one piece of this design that
  genuinely could move to `Gasm/Core` today without misrepresenting either target.
  **Recommendation: do not move them yet.** Two independent reasons, not one: (1) no Wasm
  consumer needs them — this change's sealed `WasmMem` accessors are written as separate,
  concretely-typed functions (`read8`/`read32`/`read64`/`write8`/`write32`/`write64`; only
  three of the four widths exist in Wasm's current instruction set, and none of the
  differential fuzzer's, spikes', or WASI's code dispatches on a shared width tag), so
  there is no live duplication to unify yet — moving the enums now would be relocating
  code to satisfy a future consumer that does not exist, which is the Law 5 mistake in
  miniature; (2) MH2 and MH3 are concurrently editing the exact x86-64 files that define
  and consume these enums (`MemoryCell.lean`'s `MemAccessSpec`, the forthcoming
  `MemCostModel`/`memUops`) — relocating their definitions out from under that work risks
  a collision for zero present benefit. Revisit when a second consumer exists (a Wasm perf
  model wanting shared width vocabulary, or MH2/MH3 landing and freeing the file up).
- **`MemAccessSpec`/`MemRef` (the x86-64 *descriptor*) do NOT generalize as currently
  shaped, and the claim that they do is optimistic.** `MemRef` is register-relative
  addressing evaluated against `X86_64MachineState.gprs` — a *symbolic* address
  expression, evaluated against the pre-step state, that is what makes Layer A's
  assemble-time capability discharge possible at all (`decide`/`omega` over a literal
  displacement against a named register). Wasm has no analogue: by the time
  `evalLeafInstr` reaches a `.i32_load`/`.i32_store` case, the base address has already
  been popped off the operand stack as a *concrete* `UInt32` — there is no register-named,
  symbolic operand for a descriptor to point at. A Wasm access descriptor, if one is ever
  built, would need `MemAccessSpec`'s §3.3 "Known limit" `.dynamic` extension slot
  (state-dependent address, not a static `MemRef`) for *every* Wasm memory instruction,
  not as an edge case — which inverts the design's premise that static descriptors are the
  common case and dynamic ones are rare. Forcing Wasm through the existing `MemAccessSpec`
  shape would therefore misrepresent Wasm's addressing model exactly as this task's brief
  warned against; a Wasm descriptor, if the measurement consumer (below) ever demands one,
  is a new, small, address-already-concrete shape (`kind`, `width`, `addr : Nat`), not a
  reuse of `MemRef`.
- **The measurement/perf consumer (§3.3 item 3–4) is the one place a shared descriptor
  shape has real pull**: memory latency is target-independent, and a future Wasm cost
  model would want the same `(kind, width, address)` triple a cache/locality model
  consumes for x86. **Status**: no Wasm perf/cost model exists or is proposed by this
  change — MH2 is x86-only and out of this change's scope by the owner's own instruction.
  Recorded here so the eventual Wasm cost-model task starts from "reuse the atomic enums,
  build a Wasm-shaped concrete-address descriptor" rather than re-deriving the question.
- **The capability-authoring surface (Layer A: `RegionSpec`, `Frame`, `CheckedAsm`,
  the bypass ledger) is irreducibly x86-64.** §12.1 already establishes there is nothing
  for a Wasm capability to buy; building `WasmCheckedAsm` would be capability machinery
  with no obligation for it to discharge, i.e. exactly the "false unification" this task's
  brief warned against forcing.

### 12.3 The concrete gap: sealing Wasm's memory (closed)

**Status**: implemented and verified in this change (not proposed — built).

`Gasm/Targets/WASI/ABI.lean`'s `wasiHostCall` called the pre-seal `readMem32`/`writeMem32`
helpers directly, and two of its cases (`fd_read`, `sock_recv`) called `ByteArray.set!` on
`s.memory` in a raw per-byte loop — bypassing `evalInstr`'s B7 trap check entirely, since
  host calls are never dispatched through `.i32_load`/`.i32_store`. This was recorded as a
  pre-existing, separate gap for the WASI execution harness. It is the same defect
class MH1's x86-64 seal makes unrepresentable (§3.2): a memory-touching function existing
outside the chokepoint that a caller can reach without going through the checked path.

The fix mirrors MH1's mechanism, adapted to Wasm's asymmetry (§12.1: a per-access
Option/trap outcome, not a capability proof).

> **Correction, made against this file rather than repeated (2026-08-28, prompted by the
> same adversarial-review finding §3.2's own CORRECTION block records for x86-64, read
> during a rebase onto the commit that added it).** An earlier draft of this bullet claimed
> `private mk`/`private raw` made `WasmMemory` "no term outside this file can construct
> one from an arbitrary `ByteArray` or project one back out" — the exact overclaim §3.2
> names for `X86_64Memory`, and false for the identical reason: `private mk ::` does not
> privatize the auto-generated `WasmMemory.casesOn`/`.rec`/`.recOn`, so
> `m.casesOn (fun f => f)` returns the raw `ByteArray` from any module. §3.2's
> "semantically empty" argument applies here at least as strongly, because unlike x86-64
> (which had no public total-observation function before its audit named one), this
> design's `toBytes` is *already* the public, total, unrestricted read API — the `casesOn`
> leak reveals nothing `toBytes` does not. Construction was likewise never sealed **by
> design**: `ofBytes` is public and unrestricted, mirroring `X86_64Mem.initRegion`,
> exactly as §3.2 (post-correction) says `initRegion` itself was never sealed.
>
> What the seal buys is the same property §3.2 lands on for x86-64: every memory touch
> goes through a *named* function in `MemoryCell.lean`, keeping access sites enumerable —
> **not** confidentiality or immutability of the bytes. `Gasm/Targets/X86_64/
> MemoryFrameAudit.lean`'s tier-3 seal-audit (which fails the build if a declaration
> outside `MemoryCell.lean` names an `X86_64Memory` eliminator) is hardcoded to
> `X86_64Memory`'s three eliminator names (verified by reading `sealOwningModule`/
> `sealedEliminators` in that file) and does **not** cover `WasmMemory`. **Status**: no
> equivalent audit exists for the Wasm seal — recommended follow-up, not built here (scope:
> the concrete gap this section closes is the OOB-trap bypass named below, which the seal
> closes regardless of eliminator-leak enumerability; extending the tier-3 audit pattern
> to `WasmMemory` is separable work, and touching `MemoryFrameAudit.lean` itself was
> avoided here as x86-64/MH-team territory per this task's own instruction to stay out of
> concurrently-edited files).
>
> **A second, Wasm-specific residual worth naming precisely because x86-64 has no
> analogue of it**: `toBytes` and `ofBytes` round-trip freely (by design, for the loader/
> test-harness use case), and x86-64's unstructured address space has no size invariant
> for that round-trip to violate — but Wasm's `memory.grow` DOES enforce one (`memMax`/the
> hard ceiling, B8). Code that fetched `toBytes`, grew or shrank the `ByteArray` with
> ordinary (unchecked) `ByteArray` operations, and re-wrapped the result via `ofBytes`
> would change linear-memory size without going through `evalLeafInstr`'s
> `.memory_grow` case at all — bypassing the max-size/hard-ceiling check, not the
> OOB-access trap check this section's gap is about. **Checked, not assumed to be safe**:
> `grep`-confirmed zero call sites do this anywhere in the tree today (`toBytes`'s one
> caller is `SemanticsFuzzer.lean`'s host-module serialization, which does not
> round-trip through `ofBytes`; every `ofBytes` call site constructs from a freshly-built
> image, never from a `toBytes` result) — not a live bug, same category as the WASI gap
> this section closes was before this change. Named here rather than left implicit,
> per this project's own standard for such findings (Law 13): the mechanical prevention
> (a growth-invariant check inside `ofBytes`, or narrowing what `toBytes`/`ofBytes` can
> compose into) is future work, not claimed as done.

- `Gasm/Targets/Wasm/MemoryCell.lean` (new) defines `WasmMemory`, a sealed wrapper
  (`private mk`, `private raw : ByteArray`) structurally identical to `X86_64Memory`.
  `WasmMachineState.memory` (`Gasm/Targets/Wasm/Semantics.lean`) is now typed
  `WasmMemory`, not `ByteArray`.
- The module exposes exactly: bulk construction/observation (`ofBytes`, `zero`, `empty`,
  `toBytes`, `grow` — the legitimate loader/test-harness/serialization operations, mirroring
  `X86_64Mem.initRegion`/`zero`), and checked, `Option`-returning, width-indexed
  read/write (`read8`/`read32`/`read64`/`write8`/`write32`/`write64`) plus bulk
  `readBytes`/`writeBytes` for the WASI iovec-buffer case. `none` means out of bounds; the
  caller decides what that means (every current caller traps), but the *decision* to
  observe the failure is now structurally forced at every access site this section audits
  below — a caller cannot silently drop it the way a total, silently-permissive helper
  function let it before.
- `evalLeafInstr`'s six memory-instruction cases (`Semantics.lean`) now call these checked
  accessors instead of re-deriving the bounds inequality inline; `wasiHostCall`'s
  `fd_read`/`fd_write`/`sock_recv`/`sock_send` cases (`ABI.lean`) do the same, and now set
  `trapped := true` (leaving the pre-call state otherwise unmutated) on any out-of-bounds
  access instead of the previous silent clip/no-op/panic-risking raw access. This is a new
  behavior on a path the B7 task note confirms is currently unreachable (no WASI execution
  harness exists yet) — there is no regression to preserve, and choosing "trap" keeps the
  interpreter's one safety story (every OOB access anywhere traps) uniform rather than
  inventing a second, WASI-specific outcome (e.g. a host errno) with no present consumer
  to justify it (Law 5).
- Every free-standing raw-`ByteArray` construction of a `WasmMachineState.memory` field
  across the tree (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`,
  `Gasm/Targets/Wasm/Fuzzable.lean`'s differential-fuzzer test fixtures) now goes through
  `WasmMem.ofBytes`, so the field's sealed type is enforced everywhere it is constructed,
  not just at the two call sites the bug report named.

**Verification**: `lake build` of `Gasm.Targets.Wasm.MemoryCell`,
`Gasm.Targets.Wasm.Semantics`, `Gasm.Targets.WASI.ABI`, `Gasm.Targets.Wasm.Fuzzable`,
`Gasm.Targets.Wasm.SemanticsFuzzer`, `Gasm.Targets.Wasm.HostOracle`, `wasm_fuzzer`,
`validate_spike_wasm`, and `test_spike1_wasm` all succeed (0 errors); every Wasm spike's
`Equivalence.lean` (Spike1/2/3/4/5) rebuilds unchanged, since none constructs a
`WasmMachineState` directly (spikes emit real `.wasm` binaries and run them through
`runWasiTraceState`/a real host engine). Before/after behavior of `lake exe wasm_fuzzer`
and `lake exe validate_spike_wasm` is recorded in this task's closing report, not
duplicated here.

### 12.4 The capability-vocabulary question (`MemoryPermissions Arch`)

`Gasm/Core/State.lean`'s `ComposedState Arch ApiStateType` carries `perms :
MemoryPermissions Arch` (`Gasm/Core/Permissions.lean`), and that container is generic over
`Arch` — so in the abstract, instantiating `ComposedState WasmArch _` would give Wasm a
`perms` field for free. Checked, not assumed, before concluding anything from this:

- **Nothing wires `WasmArch` into `ComposedState` anywhere in the tree**
  (`grep -rn "ComposedState" | grep -i wasm` — zero hits). Wasm's `TargetArch WasmArch`
  instance (`Semantics.lean`) is consumed directly by `stepWasm`/`runWasiTraceState`;
  `ComposedState`/`BlockM`/`CFG`/`Callable`/`ABI.lean` (Core) are x86-64-only in practice
  today, not merely in this design's aspiration.
- **The `perms` field itself is inert for every target that does use `ComposedState`,
  x86-64 included**: `grep -rn "\.perms\b"` across all `.lean` sources returns zero hits;
  `grep -rln "MemoryPerm\b"` across `.lean` sources returns only `Permissions.lean`'s own
  definition and `MemoryCell.lean`'s citation comment. This matches §1.1's own "Zero
  capability call sites" finding for x86-64 — the slot is unpopulated architecture-wide,
  not specifically un-adopted by Wasm.
- **`Address` (`Gasm/Core/Types.lean`) is hardcoded `UInt64`**, and `MemoryPerm`'s
  `validRange` bound is hardcoded against `2^64`. Wasm32 addresses a 4 GiB (`2^32`) space;
  a `UInt64`-typed capability is a permissive superset (not unsound) but is not the tight
  bound Wasm's own address space has, another small tell that this vocabulary was shaped
  for x86-64 and not yet exercised against a second target.
- **`Arch` is a phantom parameter of `MemoryPermissions`, not a real index**: re-reading
  `Gasm/Core/Permissions.lean`'s definition — `structure MemoryPermissions (Arch : Type)
  where tokens : List (Address × Nat × PermissionShare); disjoint : DisjointTokens
  tokens` — `Arch` appears nowhere in either field's type. `docs/MEMORY_MODEL.md` §6 treats
  architecture-neutral authority vocabulary as a requirement, but replaces the current
  pairwise-disjoint list with a real resource algebra. The existing shape never depended on
  `x86-64` in the first place; from this section's angle that is a caution, not a
  feature: "arch-parameterized" is doing no real work today. `ComposedState WasmArch _`
  would type-check and would carry a *phantom-tagged* `MemoryPermissions WasmArch`, but
  its `tokens`/`disjoint` fields would be bit-for-bit the same shape as x86-64's — the
  parameter exists to keep two architectures' capabilities from being mixed at the type
  level, not to encode anything architecture-specific about what a capability *is*. Both
  readings are correct; this document's is the one relevant to "does Wasm already have a
  usable slot," and the answer stays no.

**Conclusion: there is no populated slot to reuse, for any target — "Wasm already has a
permissions slot it isn't using" overstates what exists; the accurate statement is "Core
has a generic container that nothing populates yet, and Wasm additionally does not
participate in the wrapper that holds it."** Populating it for Wasm now would mean
inventing real capability tokens and a granting/checking discipline for a target whose own
memory-safety story (§12.1) does not need one — capability machinery with no obligation to
discharge, same objection as Layer A above. **Recommendation**: leave `MemoryPermissions`
unpopulated for Wasm; if a future Wasm need for capability-shaped reasoning emerges (e.g.
reasoning about which WASI-granted file/socket handles a routine may touch — a genuinely
different resource class than linear memory), design it against that concrete need rather
than pre-filling this slot speculatively.

### 12.5 Fault/trap distinguishability, x86 vs Wasm

Checked for the historical T12 failure class: a stop reason must
never be conflatable with another (x86-64's `runProgramTraceWithLoops` returns `[]` for
fuel-out, no-instruction-at-rip, *and* a clean fault alike).

- **x86-64, today**: `X86_64Fault` (`divideError | memFault ... | halted`) and
  `fault : Option X86_64Fault` are built; DIV/IDIV write `.divideError`, HLT/platform exits write
  `.halted`, and the derived `faulted` projection remains for compatibility. The `memFault`
  payload is present but remains unreachable until memory-fault semantics are implemented.
  TC18's stop-reason `Except` shape is
  likewise **Status: unbuilt**, so the outer trace runner still conflates fault, fuel exhaustion,
  and no-instruction-at-RIP as `[]`. The payload migration fixed fault-kind representation, not
  whole-program stop-reason distinguishability.
- **Wasm is already better-separated on the fuel-exhaustion axis, independent of this
  change**: `WasmRunResult := Except WasmMachineState (WasmMachineState × ControlSignal)`
  (`Semantics.lean`) makes fuel exhaustion a structurally distinct outcome (`.error`) from
  every genuine stopping point (`.ok`) — the fuel-conversion work that predates this task
  already closed Wasm's version of that stop-reason gap; `runWasiTraceState`
  (`Gasm/Targets/WASI/ABI.lean`) is the whole-program entry point that returns this
  un-collapsed, and every load-bearing spike equivalence theorem is paired with a
  `#guard !(... ).isError` check proving it never hits `.error`.
- **Wasm's `trapped : Bool` is one bit, the same shape as x86-64's pre-payload `faulted`
  field** — it distinguishes "trapped" from "not trapped" but not *why* (OOB
  load/store/`unreachable`/integer-divide-by-zero/`i32.div_u` etc. all set the same bit).
  It is therefore behind x86-64's current fault-kind representation, even though x86-64's outer
  trace runner still conflates stop classes as described above.
  **Recommendation, not built here**: if a future consumer needs to distinguish trap
  *reasons* (e.g. a differential harness wanting to assert "trapped, and specifically on
  the OOB path, not `unreachable`"), the natural shape is a Wasm-side enum
  paralleling `X86_64Fault`'s — `WasmTrap.oob (kind : MemAccessKind) (width) (addr) |
  .unreachable | .divByZero | ...` — replacing the bare `Bool` the way `X86_64Fault` replaced
  the x86-64 field. No such consumer exists today (every current check is
  "trapped or not"), so this is named as a parallel future step, not built now (Law 5).

### 12.6 Relationship to the canonical borrowing model

`docs/MEMORY_MODEL.md` §6 consolidates the indexed authority and obligation design that
supersedes this document's planned x86-64 capability-authoring layer. The direct question
is whether that common model should also subsume the Wasm memory-safety story in
§§12.1–12.3.

**No.** Native checked authoring proves that a symbolic access lands inside a granted
region because the x86/AArch64 machine model otherwise has no point at which to reject an
unauthorized address. Wasm's interpreter already establishes in-bounds linear-memory access
at runtime for every load and store. Routing Wasm linear memory through the native indexed
authoring surface would therefore add machinery without a corresponding safety obligation.

The designs can still share typed resource-lifecycle machinery. If a genuine Wasm/WASI
capability need appears—such as borrowed file or socket handles—the common obligation
algebra is the mechanism to extend, rather than inventing a target-local duplicate.

**Status**: analysis only. The common borrowing design is specified but unimplemented; the
Wasm bounds-checking path is implemented independently.

### 12.7 What this section rejects, and why

- **An arch-generic Core hook typeclass** — already rejected in §9 for Wasm-as-second-
  target under Law 5/Law 8; §12.1–§12.4 add the concrete evidence (the asymmetry is real
  and load-bearing, not cosmetic; the shared vocabulary that exists carries no present
  consumer; the one arch-generic container already in Core is unpopulated for every
  target) rather than repeating the assertion.
- **Reusing `MemAccessSpec`/`MemRef` for Wasm** — §12.2: Wasm's addresses are concrete by
  the time any access executes, not symbolic; forcing them through a register-relative
  descriptor shape would misdescribe the target, not generalize over it.
- **A `WasmCheckedAsm` capability-authoring surface, whether built directly or via the
  borrow model's `BlockM`/weaving-DSL machinery** — §12.1/§12.2/§12.6: there is no
  assemble-time obligation for it to carry: the interpreter already guarantees every
  memory access is in-bounds or the program traps, unconditionally, in every build. The
  borrow model does not change this answer; it only makes the rejected surface cheaper to
  build, which is not the same as making it needed (§12.6).
- **Populating `MemoryPermissions` for Wasm now** — §12.4: the slot is unpopulated
  architecture-wide, not Wasm-specifically neglected, and its `Arch` parameter is phantom
  (carries no architecture-specific content today); inventing tokens for it ahead of any
  concrete need is speculative structure, same objection as the two items above.
- **Moving `MemWidth`/`MemAccessKind` to `Gasm/Core` in this change** — §12.2: the move
  would be correct in principle (the types carry no x86-specific content) but has no
  present consumer on the Wasm side and collides with MH2/MH3's concurrent edits to the
  x86-64 files that define and will consume them; revisit when either condition changes.
