# MEMORY_HOOK: The Memory Access Contract (x86-64)

- REF: docs/REVIEW.md#law-11-memory-access-capability-mandate-fail-to-assemble
- REF: docs/REVIEW.md#law-14-calibration-data-governance-the-third-reference-class
- REF: docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions
- REF: docs/READ_BINDER_CONTRACT.md#5-integration-with-law-11s-capability-mandate
- REF: docs/VISION.md#5-performance-modeling-agents-as-the-optimizing-compiler
- REF: MODEL_DEBT.md (§A0, §A8, §B3)
- REF: docs/X86_ISA_EXPANSION_PREREQUISITES.md#p2--blocking-the-memory-operand-contract-law-11--pa4-at-least-at-the-instruction-layer

## 1. Status and scope

**Status**: this is a design document, not a report of built machinery. Nothing specified
here exists in the tree unless a sentence explicitly says it was verified there; every
proposed-but-unbuilt mechanism carries its own `**Status**:` line per `CONTRIBUTING.md`'s
convention. Everything described as existing was verified by reading the tree or running
commands at commit `0d5c6a9` (2026-08-27). Implementation is tracked as MH1–MH3
(`docs/tasks/MH1-semantic-memory-hook.md`, `docs/tasks/MH2-memory-uop-centralization.md`,
`docs/tasks/MH3-capability-authoring-surface.md`).

**The directive** (owner, verbatim): *"memory contracts — let's plan out a memory hook —
apis every instruction needs to go through to access memory, so we can do the perf and
permissions in one place."* And, for the permissions half: *"the instructions should be
validating they have access to an address and failing to assemble if that proof doesn't
carry"* — Law 11's fail-to-assemble bar, not a runtime check.

This document designs that hook: what instructions call, how the capability proof is
carried and enforced at assemble time, what the perf side records and how it stays
falsifiable, the migration path for the existing 88 instruction forms, the effect on
existing proofs, and how faults become distinguishable observations.

### 1.1 Verified current state (the evidence this design is grounded in)

| Fact | Evidence |
| :-- | :-- |
| 14 of 88 instruction forms touch memory | `MovRspDispByte`, `MovRspDispImm32`, `MovRspDispImm64`, `MovMem8Reg8`, `MovMem64DispReg64`, `MovMem64DispImm32`, `MovReg64Mem64Disp`, `MovzxR64Mem8`, `MovReg32RspDisp32`, `PushR64`, `PopR64`, `CallRipRel`, `CallRel32`, `RetOp` — enumerated from `Gasm/Targets/X86_64/Registry.lean` + each `step`'s body |
| The machine model's only memory primitives are five helpers + raw field access | `X86_64MachineState.read64`/`write8`/`write64`/`push64`/`pop64` (`Gasm/Targets/X86_64/Registers.lean:226-265`); the field itself is `memory : Address → Byte`, total, public |
| Instruction steps already bypass even those helpers | `MovRspDispImm32.step` inlines a raw 4-byte store lambda (`Mov.lean:166-173` — no `write32` helper exists so it was re-implemented inline); `MovzxR64Mem8.step` and `MovReg32RspDisp32.step` read raw `s.memory addr` bytes inline. The missing widths already caused the exact per-instruction re-implementation this hook exists to end |
| Non-instruction code also writes memory raw | `Gasm/Targets/Windows/Win32API.lean` hooks (`readFileHook`/`recvHook` write destination buffers via raw `memory := fun a => ...` lambdas, lines 112–136, 214–217); the linkers' `loadMemory` installs the image raw |
| Zero capability call sites | Law 11's own Status line; `MemoryPerm`/`MemoryPermissions`/`BlockM` have no call sites outside `Gasm/Core` |
| Memory cost is 14 sets of inline, uncited literals | every load is flat `latencyCycles := 4`, every store `1`, duplicated per instance; 0 of 88 forms cite any calibrated or vendored source (`MODEL_DEBT.md` §A0/§A8) |
| Fault model is one bit, two sites | `faulted : Bool`; only `Div.lean` sets it (`#DE`); `runProgramTraceWithLoops` returns `[]` for fuel-out, no-instruction-at-rip, and fault alike (`TCB.md` T12) |
| Existing proofs that touch memory semantics | `step_ret_op` (`Stdlib/Zlib/CRC32Equivalence.lean:652`, `Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean:139`, both `rfl`); `LoopInvariant.lean:598` (`simp [X86_64MachineState.read64, ...]`); `Stdlib/SmolAlloc/Equivalence.lean:42-45,140-142` (`read64` as observation). **No step lemma exists for any store form** — the read-over-write theory this design centralizes does not exist anywhere today |

## 2. The design in one page

One module family, `Gasm/Targets/X86_64/Memory*.lean`, exposing three coupled surfaces.
**Status**: none of the three exists; MH1/MH2/MH3 respectively.

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
  falsifiable surface shrinks from "88 forms of inline literals" to "one table of ~8
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

**Status**: unbuilt; MH1. Sketches below are design, not existing code.

### 3.1 Types and API

```lean
inductive MemWidth | w8 | w16 | w32 | w64          -- 1/2/4/8 bytes
def MemWidth.bytes : MemWidth → Nat

/-- Canonical x86-64 effective-address term: base + index*scale + disp.
    Today's 14 forms use only base+disp8/disp32; index is the forward slot the ISA
    expansion's SIB-indexed forms fill without a new address representation. -/
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

`private mk ::` + `private raw` elaborate at this repo's pinned toolchain (v4.33.1 —
verified by compiling exactly this shape during this design pass), and `private` is
module-scoped in Lean 4: outside `Gasm/Targets/X86_64/Memory.lean`, neither constructing
an `X86_64Memory` from a raw function nor projecting one out elaborates. This is Law 13
preference-tier 1 — the bypass is *unrepresentable*, not linted. Instruction steps,
Win32 interceptor hooks, and loaders all route through the hook's API; the loaders get a
dedicated `initRegion`/`initImage` entry point (installing an executable image is a
legitimate bulk write, and giving it a named API keeps it inside the chokepoint rather
than allowlisted around it). Spec/proof-side *observation* (`SmolAlloc/Equivalence`'s
`read64` assertions) uses the read API and is unaffected.

**Status**: the sealed wrapper and the migration of all raw access sites (5 helper
definitions, 3 inline instruction lambdas, the Win32 hook lambdas, `loadMemory`) are
MH1's deliverable. The single-module `private` scope is deliberately strict; if the hook
module must later split, the fallback is a compiled-environment audit in the
`Registry.lean`/`check_refs_coverage` style — tier 3, only if tier 1 proves untenable.

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

These are provable by unfolding for the 14 memory forms (their steps are literally
hook calls at the declared addresses once migrated), and by a shared batch lemma for
the 74 `[]` forms (their steps never mention memory). They live in the
`RoundtripGate/*`-style per-family shard convention so a new memory form cannot land
without them. **Status**: unbuilt; MH1 (field + 14 real descriptors + frame lemmas for
the memory families), with the register-form batch lemma in the same change.

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
   trace — exactly what a future cache/locality model (MODEL_DEBT §A0) and F1's
   containment checks consume, obtained without instrumenting the interpreter.

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
- The per-family `writesWithin`/`readsWithin` frame lemmas of §3.3 — which are exactly
  the frame conditions PA2's composition calculus needs routine contracts to carry
  (`docs/VISION.md` §4: "capability tokens … are also the frame conditions").

**Status**: unbuilt; MH1. The disjointness lemmas are `omega`-class arithmetic over
`UInt64` intervals; wraparound at 2⁶⁴ is handled the way `MemoryPerm.validRange`
already does (a no-overflow side condition carried by the capability, not re-proven per
access).

## 4. Layer A: assemble-time capability enforcement

**Status**: unbuilt; MH3 (shape + one pathfinder routine); PA4 remains the migration
epic that carries it across the tree. This section is the "instruction-level obligation
shape" `docs/X86_ISA_EXPANSION_PREREQUISITES.md` P2 requires before memory-form
instructions are mass-authored.

### 4.1 The problem Law 11 actually poses

At authoring time addresses are symbolic: whether `mov qword [rbx+8], rax` is in bounds
depends on what `rbx` holds at that program point. A capability over a *concrete* range
cannot be checked against a register-relative operand without a statement about the
register. The capability must therefore be **register-anchored**: "at this routine's
entry, register R points at the base of a region of `len` bytes held with share S."
That is precisely the frame condition PA1's Theorem 3 stated informally and PA4's task
file says to upgrade "into a real capability obligation."

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
for computed addresses the author supplies an invariant-derived proof term, which is
exactly the loop-invariant machinery PA15 demonstrated and PA2's calculus will make
cheap.

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
- **Deferred to the PA2/PA3 typestate upgrade**: flow-sensitive capability transfer
  (register copied to register, region split across a call, `BlockM`-indexed frames).
  `Frame` is designed to become `BlockM`'s index when that lands; nothing in v1's shape
  is discarded by the upgrade.

The alternative — requiring full flow-sensitive typestate before any migration — is
rejected on cost: it is PA2+PA3's whole program of work, and gating every memory
instruction on it would leave Law 11 unenforced for months while `Stdlib/Zlib` keeps
growing hand-offset scratch arithmetic. This is Owner Question Q1 (§10).

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
is inside `Γ`, with no global reasoning. **Status**: the theorem shape and the DSL
machinery that discharges it are MH3; the first end-to-end instance (one real routine)
is MH3's acceptance bar, per P2's "exercised on at least one real instruction family
end-to-end."

### 4.5 Erasure, coexistence, and the bypass gate

`CheckedAsm.erase : CheckedProgram Γ → List SymbolicInstr` — proofs erased, encoding
unchanged, so the assembler/linker/emitter pipeline is untouched. Old and new authoring
coexist mechanically:

- A ratcheted ledger, `scripts/mem_bypass_allowlist.txt` (the established 5-field
  `::`-format), lists every module currently authoring memory-operand `SymbolicInstr`s
  raw — seeded with today's full population (`Stdlib/Zlib/X86_64.lean`,
  `Stdlib/SmolAlloc/Program.lean`, the spike `Program.lean`s). A gate script fails CI
  if a memory-operand smart constructor (`mov_mem64_disp`, `movzx_r64_mem8`, `push_r64`,
  …, enumerated from the registry's 14 memory forms, not hand-listed) is used outside
  the ledger + the designated infrastructure modules (erasure, decoder, fuzzers,
  roundtrip). Entries are counted and printed every gate run, may only be removed
  (migration) — adding one requires the same justified-entry discipline as every other
  allowlist, and review policy per Law 11 is that new entries are rejected.
- **"Not yet migrated" vs "does not need it" is mechanical, not declared**: a module
  with no memory-operand constructors never trips the gate and never appears in the
  ledger. The ledger *is* the migration backlog; empty ledger = migration finished.
  A migration that cannot be finished is thereby avoided: the end state is defined
  (ledger empty), monotone (ratchet), and measured (count in gate output).

**Status**: gate script and ledger are MH3 deliverables, with a Law-13 negative
control: a mutation adding a raw memory-operand use to an unledgered module must fail
the gate before the gate counts as delivered.

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

**Status**: unbuilt; MH2. Coordinates with the concurrently-dispatched per-instruction
validation-and-calibration gate task (P4/P5 of the expansion prerequisites) — §5.3
states exactly what this design hands that gate.

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
(`MODEL_DEBT.md` §A8: 0 of 88 coefficients cite any source). The hook changes the
*shape* of the claim:

1. **The coefficient set is finite, enumerable, and small** (~8 named fields), because
   every per-form number is derived. Calibrating a coefficient recalibrates every form
   at once; a coefficient the harness cannot measure stays `modelInternal` and is
   *counted* — "N of M memory coefficients calibrated" in gate output (Law 14's
   honesty-in-output clause), instead of invisible.
2. **Each coefficient names its refuting experiment.** MH2's table documents, per
   field, the F1 microbenchmark shape that measures it (load-to-use: dependent
   pointer-chase resident in L1; store costs: store/reload chains) — so F1's
   containment criterion (`real ∈ [min, max]`) and rank-order checks apply
   per-coefficient, not per-form. `**Status**`: F1's harness is `ready`, unstarted;
   until it lands these are named recipes, not performed measurements, and every field
   is `modelInternal`.
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

The sibling gate task, when it lands, gets from this design: (a) a mechanical
memory-touching predicate per form (`memAccesses ≠ []` — no heuristics, no silent
opt-out, because the field has no default); (b) the closed coefficient table with
per-field provenance status to count and print; (c) the derivation invariant of
§5.2(3) to check against the registry; (d) per-coefficient measurement recipes to
drive F1 containment checks; (e) the descriptor-vs-step frame lemmas (§3.3) as the
per-family proof obligation whose absence the gate flags. Items (a)–(c) are
enforceable the day MH1+MH2 land, before any calibration exists.

## 6. Faults and observability

Two changes, deliberately staged:

1. **Fault plumbing now** (MH1, cheap): `faulted : Bool` on `X86_64MachineState` is
   replaced by `fault : Option X86_64Fault := none` with
   `def X86_64MachineState.faulted (s) : Bool := s.fault.isSome` — every existing
   *reader* (`if s'.faulted then …` in the interpreters) compiles unchanged; the two
   writer sites in `Div.lean` become `fault := some .divideError`.

   ```lean
   inductive X86_64Fault
     | divideError                                              -- #DE, today's only fault
     | memFault (kind : MemAccessKind) (width : MemWidth) (addr : Address)
   ```

   A memory fault is thereby a *distinguishable, data-carrying* outcome from the day
   the type exists — never a third indistinguishable `[]`. This composes with (does
   not duplicate) TC18's trace-type fix: TC18's `Except`-shaped run result
   distinguishes fuel-out / no-instruction / fault as stop *reasons*; this design
   supplies the fault reason's *payload*, so the combined outcome type is
   `fuelExhausted | noInstructionAtRip | faulted (f : X86_64Fault) | completed`, with
   no two outcomes sharing a representation. MH1's task file records the coordination
   note for whichever of MH1/TC18 lands second.
2. **Fault semantics on demand** (deliberately not now): making `memFault` *reachable*
   requires a memory map / granted-region model in the machine state — machine-state
   surface the owner has ruled expands demand-driven, spike-forced (Law 5; the P1
   ruling). When that spike arrives, the implementation site is already fixed by §3.3:
   the interpreter checks the instruction's descriptor against the map *before*
   applying `step`, and faults with the pre-step state — hardware-faithful, zero
   instruction edits. Until then, this document does not claim the model can produce a
   memory fault: it cannot, and saying otherwise would be the exact overclaim
   `MODEL_DEBT.md` §B1 catalogs. **Status**: `X86_64Fault` and the field change are
   MH1; the map and the interpreter pre-check have no task yet and are named as
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
store-form step lemma exists anywhere, so every future memory proof (the entire
PA4/Zlib program) would otherwise re-derive read-over-write and byte-decomposition
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

| Phase | Task | Content | Size | Gate that makes it stick |
| :-- | :-- | :-- | :-- | :-- |
| M0 | MH1 | Hook module: sealed memory field, width-indexed read/write, `MemRef`, missing widths; migrate 5 helpers, 3 inline instruction lambdas, Win32 hook writes, loader `initRegion`; `fault : Option X86_64Fault`; §3.4 lemma set | ~1 module + ~20 call sites | `private` field: raw access fails to elaborate (mutation-verified) |
| M1 | MH1 | `memAccesses` field, **no default** → all 88 instances (74 × `[]`, 14 real); frame lemmas for the 14 + batch lemma for the 74 | 88 one-liners + 14 lemma pairs | Compile error on omission (no default); shard convention for the lemmas |
| M2 | MH2 | `MemCostModel` + `memUops`; delete 14 forms' inline memory-uop literals; provenance counting in gate output; derivation-invariant check in the registry audit | 14 forms + 1 table | Private cost tag / linter: memory uops constructible only via hook |
| M3 | MH3 | `CheckedAsm` v1 + erasure + `MemSafe` shape; bypass ledger seeded with the full current authoring population; **one real routine migrated end-to-end** (pathfinder: a small `SmolAlloc` or the `crc32SymbolicProgram` frame PA1 already characterized) | DSL + 1 routine | Ledger gate with negative control; ledger only shrinks |
| M4+ | PA4 | Module-by-module authoring migration, new/small first, `Stdlib/Zlib/X86_64.lean` (2,245 lines) last per PA4's ratified ordering | the long tail | Ledger count → 0 |

Old and new coexist at every phase: unmigrated modules keep building (their raw
authoring is ledgered, counted, and frozen — no new entries), migrated modules cannot
regress (their constructors demand proofs), and the semantic hook (M0–M2) is invisible
to authoring entirely. The expansion's Wave B (memory-operand mass authoring) requires
M0–M3 done — that is P2's blocking condition made concrete.

**Ordering note.** M0–M2 precede and do not depend on PA2's composition-calculus
design; M3's *shape* is PA2-compatible by construction (§4.3) but does not wait for
it. If PA2's design lands first, M3 adopts its frame representation directly; the
reverse order costs one representation-alignment pass on a single pathfinder routine.

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
- **Requiring full flow-sensitive typestate (BlockM) before any enforcement** — right
  destination, wrong sequencing (§4.3); v1's entry-anchored frames enforce the
  no-citation and literal-overrun classes now and upgrade without rework.
- **Building the cache-hierarchy cost model now** — Law 5; the hook designs the seam
  (descriptor stream + single cost site) and stops (§5.2).
- **An arch-generic Core hook typeclass now** — Wasm's memory already has its own
  bounds-checked, trapping access path (post-B7); abstracting over two targets with
  one instance each is speculative structure (Law 8 risk). The x86-64 hook's shapes
  (`MemWidth`, descriptor, cost table) are written to generalize, and Core already owns
  the capability vocabulary; the typeclass gets extracted when a third target demands
  it.

## 10. Questions for the owner

1. **Q1 — v1 obligation strength (§4.3).** Entry-anchored frames with
   invariant-discharged dynamic bounds are recommended as the Law-11 carrier until
   PA2/PA3's typestate upgrade. The alternative (flow-sensitive capability tracking
   from day one) is stronger but sequences all enforcement behind PA2+PA3. Is v1's
   line — omission and literal overruns unrepresentable now, dynamic bounds carried
   but semantically discharged — acceptable as Law 11 compliance for migrated modules?
2. **Q2 — `MemRef` as the expansion's operand convention.** New memory-operand
   instruction forms should take a `MemRef` operand (one form per operation × width,
   addressing folded into the term) rather than one struct per addressing mode —
   collapsing the form count the ISA expansion would otherwise multiply, at the cost of
   changing the roundtrip-case enumeration convention and interacting with B3's decoder
   modularization. Recommended yes, for new forms only (the existing 14 stay as-is
   until B3-era normalization). Needs a ruling before Wave B is scoped.
3. **Q3 — the `memAccesses` mandatory field.** It is the one structural change with a
   per-form cost (88 one-line edits now; one line forever after per new form) and the
   design's keystone (§3.3). The no-default choice is deliberate P4 medicine — silent
   opt-out impossible. Confirm the cost is accepted; the fallback (a linter inferring
   memory-touchingness from step bodies) is strictly weaker and reviewable on request.

## 11. Follow-on tasks filed with this design

| Task | Track | Content | After |
| :-- | :-- | :-- | :-- |
| `docs/tasks/MH1-semantic-memory-hook.md` | proof-arch | §3 + §6 stage 1 (M0+M1) | — |
| `docs/tasks/MH2-memory-uop-centralization.md` | perf | §5 (M2) | MH1 |
| `docs/tasks/MH3-capability-authoring-surface.md` | proof-arch | §4 (M3): shape, erasure, ledger gate, pathfinder routine | MH1 |

PA4 (`docs/tasks/PA4-capability-adoption.md`) remains the migration epic and consumes
§4 as the "instruction-level obligation shape" its design deliverable calls for; PA2's
design should treat §3.3's frame lemmas and §4.4's `MemSafe` shape as candidate
building blocks, per the same relationship `docs/READ_BINDER_CONTRACT.md` §9 item 4
establishes. TC18 coordinates on the fault/stop-reason outcome type (§6). F1/F2
calibrate §5's table when they land.
