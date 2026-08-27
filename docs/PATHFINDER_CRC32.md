# PATHFINDER_CRC32: Design for `crc32SymbolicProgram`'s Contract, Proof, and Composition Sketch

- REF: docs/VISION.md#4-tractability-modular-contracts-composed-proofs
- REF: docs/EQUIVALENCE_PROOFS.md#4-the-three-independent-split-theorems
- REF: docs/REVIEW.md#law-7-target-separation--equivalence-proof-purity-the-authoring-ergonomics-mandate
- REF: docs/REVIEW.md#law-9-universal-quantification--input-completeness-mandate-the-anti-pointwise-law
- REF: docs/REVIEW.md#law-10-kernel-checked-gates--the-native_decide-restriction-exhaustive-finite-domains-only
- REF: docs/REVIEW.md#law-12-connection-theorem-mandate-no-unlinked-twins
- REF: docs/STDLIB_ZLIB.md#22-crc-32-iso-3309-ieee-8023
- REF: docs/STDLIB_ZLIB.md#61-checksum-invariance-theorems
- REF: docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model
- REF: docs/STDLIB_SMOLALLOC.md#4-linear-obligations-memory-invariants
- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention

This design's task brief (`PA1: crc32 pathfinder`) and the DSL/composition ADRs it tests are
tracked in the integration branch's `docs/tasks/` and `docs/adr/` directories, which are not yet
committed to any shared branch this worktree can resolve a path against (verified: no commit on
any local branch touches `docs/adr/` or `docs/tasks/`). Those citations are therefore given as
prose pointers below, not as `REF:` links, to avoid asserting a resolvable in-tree path that does
not exist. `MODEL_DEBT.md`, `TASKS.md`, and `PLAN.md` **do** exist on this branch (this document
was rebased onto `claude/codebase-review-sonnet-4fe3c4` specifically to make those citations
resolve) and are cited directly.

## 0. Status and Revision Log

**v2 — responding to design review (APPROVE-WITH-CHANGES, 12 mandatory items).** The review
independently re-derived the 61-instruction census in v1 and found it exactly correct, called the
document "unusually honest" about composition being unexercised, and then did empirical Lean work
(a working `bv_decide` proof of the connection theorem, confirmed axiom-gate behavior on the
actual toolchain, confirmed two real assembly defects at their real call sites) that materially
changes the plan below. This revision is a substantial rewrite, not a patch: the contract (§2),
step-lemma strategy (§3), composition story (§4), and tactic strategy (§5) are all changed from
v1, not merely annotated. Sections not carried over from v1 without change: none — even the
mostly-unchanged sections (§1, §3.3) have small corrections. A per-item response to the review is
in this session's completion report, not duplicated here; this document states the corrected
design directly, as the design should read once corrected, not as a diff against v1.

**v3 — responding to a second design review (APPROVE-WITH-CHANGES, 9 mandatory items).** The
second review independently typechecked the `bv_decide` route on this toolchain and confirmed the
two biggest v1 risks (the impossible connection-theorem route, the `instructionAtRip` cost model)
are correctly retired in v2, and called §3.4's block-level factoring a real insight. It also found:
a provably false conjunct in v2's Theorem 2 (`.rsp` is not preserved — M1); that v2's invariant was
*referenced* in three places (§3.5, §4.3, and implicitly by §3.4) but **never actually written
down** anywhere (M2) — the same failure shape as v1's `updateCrc32Internal`, one level up, and the
single most load-bearing miss in v2; a false fuel-stability clause (M3, the popped return address
is unconstrained and could alias back into the program); wrong replacement statistics for the exact
tree-wide tactic count v2 was correcting (M4 — six of seven figures wrong, several by 3-4×, on the
very item the first review made mandatory); an unpriced, unnecessary DSL-instruction dependency in
the §8(b) fix (M5 — a two-instruction fix using already-registered instructions exists); an
entirely un-cited existing coupling invariant and pointwise refinement theorem for `smolFree`
(`Stdlib/SmolAlloc/Equivalence.lean` — M6, which changes what the second routine's contribution
*is*); an unnecessary ownership precondition in §9.1 where a pure disjointness fact suffices for
the frame condition specifically (M7); an under-specified and overclaiming §9.1 postcondition (M8);
and two corrections to §3.6-policy's own tactic script and gate-tool claims (M9). This revision
fixes all nine directly in place (not as a diff) and folds in three non-blocking recommendations.
A per-item response is in the completion report; this document states the corrected design.

Per Law 5, this remains a **design document**, not an implementation. Two genuine assembly
defects are identified below (§8) and their fixes are adopted as prerequisites this design
depends on — i.e., the design below describes the contract for `crc32SymbolicProgram` **after**
those one-instruction fixes land, with the pre-fix behavior documented as the reason the fixes are
needed. This is a design decision (stated and justified in §8), not scope creep: proving a false-
by-omission ABI contract or carrying a permanently-false-until-bounded precondition into the
template that ~50 future routines will copy is worse than fixing two single-token substitutions
first.

Source of truth re-read against the **post-rebase** tree (this branch, `claude/codebase-review-
sonnet-4fe3c4` plus this commit) — line numbers below are current against that tree, not v1's:

- `Stdlib/Zlib/CRC32.lean:7,11-18,22-27,31-41,45-46` (`crc32Polynomial`, `mkCrcTableEntry`,
  `crc32Table`, `updateCrc32`, `crc32`) — unchanged from v1.
- `Stdlib/Zlib/Windows.lean:36-122` (`crc32SymbolicProgram`, unchanged: still exactly 61
  instruction/jump occurrences), `:127-149` (`adler32SymbolicProgram`, cited in §8 as the sibling
  with the identical signed-compare defect), `:801-832` and `:2210-2219` (the two real `zlib_crc32`
  call sites, cited in §4/§7/§8 — replacing v1's hypothetical caller), `:2287-2290` and
  `:2359-2363` (the two embedding splices).
- `Gasm/Targets/X86_64/Instructions/Base.lean:33-41` (`AnyX86_64Instruction`, line numbers shifted
  from v1 by the decoder-registry work landing a `roundtripCases` field on the typeclass — the
  wrapper's existential shape is otherwise unchanged), `Instructions.lean:45` (`abbrev X86_64Instr
  := AnyX86_64Instruction`).
- `Gasm/Targets/X86_64/Semantics.lean:29-37` (`instructionAtRip`) — unchanged from v1, now load-
  bearing for §3/§5's cost-model finding rather than an incidental read.
- `Gasm/Targets/X86_64/Instructions/Jcc.lean:206-211` (`JgeRel32`, signed), `:271-286` (`JaeRel32`,
  unsigned — confirmed to exist, confirmed `estimatedSize` for both near forms is 6 bytes,
  confirmed as the drop-in fix in §8).
- `Gasm/Targets/X86_64/Instructions/Div.lean:29,37` — the only two `faulted := true` sites in the
  tree, confirmed unchanged.
- `Gasm/Core/Verification.lean` (`VerifiedRoutine`, `couplingInv : SpecState → MachineState →
  Bool`) — confirmed unchanged; the `Bool`-valued field is load-bearing for §4.5's finding.
- `docs/TARGETS/WINDOWS.md:11-17` (§1.1: return register is `RAX` not `EAX`; callee-saved list;
  caller-saved list) — read in full for §2.4/§6.
- `Stdlib/SmolAlloc/Program.lean:78-103` (`smolFreeSymbolicProgram`) and `Stdlib/SmolAlloc/
  Spec.lean:16-24,117-138` (`SmolBlockHeader`, `free`) — the second routine, §9.
- `Stdlib/SmolAlloc/Equivalence.lean:23-30` (`smolAllocInvariant`, a `Bool`-valued coupling
  invariant between `SmolAllocState`/`TracedPageState` and `X86_64MachineState`) and `:76-89`
  (`smol_free_refinement_soundness_inst`, a single-ground-vector `decide` instance) — missed
  entirely in v2, load-bearing for §9's revised framing.
- `Gasm/Targets/X86_64/Registers.lean:246-248` (`pop64`: `setGpr64 .rsp (rsp + 8)`) — confirms
  M1's finding that `RSP` is not preserved by `ret`.
- `Tools/CheckGatesAxioms.lean:68-76` (`hasNativeComponent`: matches any `Name` component literally
  equal to `"_native"`) — confirms M9(b)'s correction that the axiom-level gate tool, unlike the
  source-level pre-check, already catches `bv_decide`'s emitted axiom.
- `MODEL_DEBT.md` B3 (no-fault, no-permission memory model) and B6 (self-modifying-code /
  `instructionAtRip` O(n²) note — now also cited as a proof-cost finding, §3/§5).

## 1. Why `crc32SymbolicProgram` Specifically

No syscalls (a pure routine — §2.6), loop-heavy over a dynamically-bounded buffer (Law 7's anti-
jump-table discipline), and **dual-implemented**: `Stdlib/Zlib/CRC32.lean` computes CRC-32 via a
256-entry table (`crc32Table`, built by `mkCrcTableEntry`'s 8-iteration per-bit loop), while
`crc32SymbolicProgram` computes the same per-bit polynomial recurrence inline, with no table, 8x
unrolled per byte — a genuine Law 12 connection-theorem shape (§3.4), and a small-scale rehearsal
of the same proof shape a future table-driven-vs-`PCLMULQDQ` CRC connection would need.

### 1.1 Scope discipline (same-file churn only)

This pathfinder does not migrate onto `MemoryPermissions`/`BlockM`/capability obligations
(reserved for a later capability-adoption task). The memory theorems here (§2.5) are explicit
state predicates, not capability tokens.

## 2. Contract Shape for `crc32SymbolicProgram`

### 2.1 Register-level ABI (as-used)

| Register | Role |
|---|---|
| `rcx` (in) | buffer pointer `ptr` |
| `rdx` (in) | buffer length `len` (bytes) |
| `eax`/`rax` | CRC accumulator; init `0xFFFFFFFF`; final value is the return value |
| `r8`/`r8d` | byte index `i`, `0 ≤ i < len`, loop induction variable |
| `r9`/`r9d` | scratch: byte address (`rcx+r8`), then the loaded byte, zero-extended |
| `r10`/`r10d` | the constant `0xEDB88320`, reloaded every byte iteration |
| `r11` | scratch: single-bit test value (`rax & 1`) in the unrolled bit chain; post-§8(b)-fix, also holds the `0xFFFFFFFF` mask constant for the final RAX-narrowing fix |
| flags | clobbered throughout |

**The routine performs zero memory writes** — grep-confirmed: the only memory-touching
instruction in the entire 61-occurrence list is the single `movzx_r64_mem8 .r9 .r9 0` load.

### 2.2 Precondition

```
Pre(m₀, ptr, len, buf) :=
  m₀.gprs .rcx = ptr ∧
  m₀.gprs .rdx = len.toUInt64 ∧
  buf.size = len ∧                                                -- M4: NOT implied by the read
                                                                    -- conjunct below; crc32 folds
                                                                    -- over buf.size (CRC32.lean:35),
                                                                    -- the asm loops over rdx — for
                                                                    -- buf.size > len these diverge
  (∀ i, i < len → m₀.memory (ptr + i.toUInt64) = buf.get! i) ∧
  ptr.toNat + len < 2^64 ∧                                         -- M4: no pointer-arithmetic
                                                                    -- wraparound in the read set
  ValidFunctionEntryStack m₀.rsp ∧                                 -- §2.4, defined minimally
  (let progLen := (assembleProgram m₀.rip crc32SymbolicProgram)
                     |>.foldl (fun acc i => acc + (X86_64Instruction.encode i).size) 0
   (m₀.read64 m₀.rsp).toNat < m₀.rip.toNat ∨
   (m₀.read64 m₀.rsp).toNat ≥ m₀.rip.toNat + progLen)              -- M3: the popped return
                                                                    -- address must lie OUTSIDE the
                                                                    -- assembled program's own
                                                                    -- address range (see §2.3)
```

Note what is **not** here versus v1: no `len < 2^63` signed-compare bound. §8 adopts the fix
(`jge` → `jae`) rather than the bound, so the precondition needs no artificial restriction on
`len` at all — any `len : Nat` with `len.toUInt64` well-formed (i.e. `len < 2^64`, implied by
`buf.size = len` for any real `ByteArray`) is admitted. **This is a direct consequence of fixing
the assembly rather than working around it in the contract (Law 9: shrinking a contract to
accommodate a defect the code needn't have is the wrong direction).**

`buf : ByteArray` and `len : Nat` remain free-bound universal variables, never pinned (Law 9) —
the in-memory-routine analog of Law 9's `read`-binder mandate: this routine has no `read` effect,
but the same anti-pinning discipline applies to the memory image the contract quantifies over.

**The final conjunct is new in v3 (M3) and is not optional.** `runProgramWithLoops` halts only when
`instructionAtRip` returns `none` at the current `rip` — it cannot distinguish "execution reached
`ret` and returned to genuinely external code" from "execution reached `ret` and returned to some
address that happens to alias back into the assembled program." `Pre` leaves the popped return
address (`m₀.read64 m₀.rsp`) entirely unconstrained otherwise; if a caller (adversarially, or by
accident of memory layout) arranged for that address to land inside `[m₀.rip, m₀.rip + progLen)`,
the interpreter would keep executing past the `ret` instead of halting, and v2's fuel-stability
claim (§2.3) would be **false** for that `m₀`. This conjunct is what makes fuel-stability true in
general rather than true only for well-behaved callers — real callers trivially satisfy it (their
own code is never overlapping the callee's), but the contract must say so rather than assume it.

### 2.3 Postcondition (Theorem 1: Functional Equivalence & Memory Framing)

```
∀ m₀, Pre(m₀, ptr, len, buf) →
  ∃ m_final N,
    (∀ fuel ≥ N, runProgramWithLoops m₀.rip (assembleProgram m₀.rip crc32SymbolicProgram) fuel m₀
                   = m_final) ∧                                   -- M9: fuel-stability
    m_final.rip = m₀.read64 m₀.rsp ∧                               -- M9: exits THROUGH ret, at the
                                                                    -- return address popped from
                                                                    -- the entry stack — not merely
                                                                    -- "fuel ran out here"
    m_final.gprs .rax = (Stdlib.Zlib.crc32 buf).toUInt64 ∧          -- M7: full 64-bit RAX, not
                                                                    -- `.toUInt32` (see §2.4, §8(b))
    (∀ a, m_final.memory a = m₀.memory a)                          -- see §2.5, renamed there
```

Two points carried over from v1, still load-bearing:

1. **`crc32SymbolicProgram : List SymbolicInstr`, not `List X86_64Instr`.** The postcondition is
   stated over `assembleProgram m₀.rip crc32SymbolicProgram`; the two-pass assembly's soundness
   (label resolution matches `estimatedSize`'s bookkeeping) is a prerequisite this proof consumes.
   **Checked, and easier than v1 feared**: `estimatedSize (.concrete i) = (X86_64Instruction.encode
   i).size` holds *definitionally* (`Assembler.lean`'s `estimatedSize` for `.concrete` is literally
   `(X86_64Instruction.encode i).size`), and every symbolic jump's `estimatedSize` entry matches
   both `assembleProgram`'s own `nextRip` arithmetic at emission and the corresponding concrete
   `Jcc`/`Jmp` instruction's `rip`-advance in its `step` (e.g. `estimatedSize .jgeNear = 6` matches
   `assembleProgram`'s `nextRip := curRip + 6` for `.jgeNear` matches `JgeRel32.step`'s `nextRip :=
   s.rip + 6`). Pass-1/pass-2 agreement for this specific program is a structural fact, not an
   open proof risk.
2. **The embedding/splicing question (was §6/M8 in v1, generalized here)**: this contract is
   stated for `crc32SymbolicProgram` **standalone** (assembled at a symbolic `m₀.rip`, called via
   the entry-stack precondition rather than spliced inline). What ships is `crc32SymbolicProgram`
   embedded inside `gzipStreamSymbolicProgram` (`Windows.lean:2287-2290`) and separately inside
   `gunzipStreamSymbolicProgram` (`:2359-2363`), each via `[...] ++ crc32SymbolicProgram ++ [...]`
   with a local `label "zlib_crc32"` immediately before the splice. The connection between the
   standalone contract and the spliced instance is true — labels are routine-local and
   `toDisp32`'s displacement arithmetic is base-invariant, so relocating the whole block by a
   constant offset changes no computed displacement — but **is not proven by this design and
   should be stated as an explicit relocation/embedding lemma consumed by any caller-composition
   proof**, not assumed for free. `buildSymbolTable`'s `lookupSymbol` returns the **first** match
   in its accumulator (built by prepending, so textually-first-declared labels shadow later
   duplicates) and `.getD curRip` silently turns a lookup miss into a self-jump — the mechanism is
   unsound in general for a program with a repeated label, though **not currently triggered**:
   `gzipStreamSymbolicProgram` and `gunzipStreamSymbolicProgram` are two separate top-level lists,
   each independently assembled, so the two `label "zlib_crc32"` occurrences never appear inside
   the same `assembleProgram` call. Flagged for PA2/a future DSL-hygiene pass as a construction
   that is unsound-in-general and happens to be safe today by convention, not by proof.

### 2.4 Postcondition (Theorem 2: Callability & ABI Preservation)

```
∀ m₀, Pre(m₀, ...) →
  ∃ m_final N, ... (as §2.3) ∧
  (∀ reg ∈ [Reg64.rbx, .rbp, .rdi, .rsi, .r12, .r13, .r14, .r15],
     m_final.gprs reg = m₀.gprs reg) ∧        -- callee-saved preservation (M6[v2]) — the core
                                                -- clause of the §4.2-pattern template, trivially
                                                -- true here since none of these registers are ever
                                                -- touched, but omitted from v1 entirely. NOTE (M1,
                                                -- v3): `.rsp` is deliberately NOT in this list —
                                                -- see below, it is provably false as a preserved
                                                -- register
  m_final.gprs .rsp = m₀.gprs .rsp + 8         -- M1 (v3): RSP is NOT preserved. `RetOp.step` is
                                                -- `let (retAddr, s') := s.pop64`, and `pop64`
                                                -- (Registers.lean:246-248) does `setGpr64 .rsp
                                                -- (rsp + 8)`. v2 listed `.rsp` among "preserved"
                                                -- registers; that conjunct was false. RSP's exact
                                                -- post-state is known and stated precisely — it is
                                                -- not "clobbered" in the arbitrary sense either —
                                                -- just not equal to its entry value.
  -- clobbered, stated explicitly (NOT preserved, per docs/TARGETS/WINDOWS.md §1.1's caller-saved
  -- list — rcx and rdx are caller-saved and MUST NOT be pinned as preserved, unlike v1):
  -- rax, rcx, rdx, r8, r9, r10, r11, flags
```

**`ValidFunctionEntryStack`, defined minimally (M6[v2]):** this name is used aspirationally in
`docs/EQUIVALENCE_PROOFS.md` §4.2 but is not defined anywhere in the tree. Define it as exactly
what a leaf `ret` needs and nothing more: `ValidFunctionEntryStack (rsp : Address) : Prop := ∃ retAddr, <rsp is
readable as an 8-byte quantity holding retAddr>` — i.e. "RSP points at a readable return address."
**Do not** strengthen this to the full §1.2 discipline (`RSP ≡ 8 mod 16`, 32-byte shadow space)
for this contract: **neither real call site can discharge that** — `Windows.lean:801-804`'s `mov
rcx,r15; mov rdx,rbx; call zlib_crc32` and `:2212-2214`'s `mov rcx,r14; mov rdx,r13; call
zlib_crc32` both call with no preceding `sub rsp, 40`. This is not a bug to fix (a locally-emitted
`call_label` to a routine that itself pushes nothing and needs no argument shadow space has no
correctness reason to allocate shadow space it never uses) — it is a reason to keep the
precondition scoped to what this routine's `ret` actually requires, matching real call sites
rather than the full external-ABI discipline those call sites were never trying to satisfy.

**The RAX-upper-bits finding from v1 is resolved by the §8(b) fix, not carried as a caveat.**
v1's Theorem 2 would have needed to state that `RAX`'s upper 32 bits become `0xFFFFFFFF` after
`not_r64 .rax` — a genuine ABI violation against `docs/TARGETS/WINDOWS.md:13`'s "Return Value:
RAX" (not "the low 32 bits of RAX"). §8(b) adopts fixing the assembly (narrow the final `NOT` to
32 bits) over documenting the violation forever, so Theorem 1/2 above are already written against
the fixed behavior (`m_final.gprs .rax = (crc32 buf).toUInt64`, full-width, zero-extended).

### 2.5 Postcondition (Theorem 3, renamed: memory safety is not statable as such — M5)

v1 named this "Memory Safety" and stated an awkward prose conjunct ("no instruction dereferences
`a`") because the machine model (`MODEL_DEBT.md` B3: no faults, no permissions, no bounds-checking
at all — `memory : Address → Byte` is total, and the only two `faulted := true` sites in the whole
tree are `Div.lean:29,37`) gives no trace event to quantify over. There is no access log to state
a confinement claim against. **Two constructive, honestly-named substitutes, both actually
statable and both true:**

```
theorem crc32_no_writes :
  ∀ m₀, Pre(m₀, ...) → ∃ m_final N, ... ∧ (∀ a, m_final.memory a = m₀.memory a)
  -- strong, true, trivially statable: the frame condition a caller actually needs

theorem crc32_result_depends_only_on_buffer :
  ∀ m₁ m₂ ptr len buf,
    Pre(m₁, ptr, len, buf) → Pre(m₂, ptr, len, buf) →
    m₁.gprs .rcx = m₂.gprs .rcx → m₁.gprs .rdx = m₂.gprs .rdx →
    -- (m₁ and m₂ may differ arbitrarily OUTSIDE [ptr, ptr+len) — that's the whole point)
    ∃ m₁' m₂', <Theorem 1 conclusions for m₁,m₁' and m₂,m₂' resp.> ∧
      m₁'.gprs .rax = m₂'.gprs .rax
  -- falls out of Theorem 1 as a free corollary: both sides equal `(crc32 buf).toUInt64`.
  -- THIS is the actual confinement claim — the result is provably insensitive to memory outside
  -- the window — stated without a trace, a fault, or a capability token, and it is Law-9-∀-shaped.
```

Neither is named "memory safety" — that name implies a guarantee (bounds-checked access,
rejection of an out-of-range read) this model cannot provide and this routine does not need,
since it never writes and its one read's address is pinned by the precondition. Naming them
`crc32_no_writes` and `crc32_result_depends_only_on_buffer` says exactly what is proven and no
more. (This directly answers v1's own §7 Q1: yes, rename — the original name would read as
stronger than what is actually established.)

**This pairing is also why crc32 alone cannot test the frame-condition half of the modular-
contracts hypothesis** — see §7.

### 2.6 No `VerifiedProgram`/`EnvironmentLoader` needed

Unchanged from v1: no syscalls, no `Environment`, pure `∀ m₀` obligation. Stated explicitly rather
than silently omitted.

## 3. Step-Lemma Inventory

### 3.1 Fourteen distinct instruction types (revised again — M5)

v2 counted 15 types, adding a hypothetical `NotR32` to fix §8(b). **M5 (v3) adopts a different
fix for §8(b)** (two already-registered instructions instead of one new one — see §8(b)) that
needs no `Not`-family instruction at all, so the type count drops to **fourteen**, and two rows'
occurrence counts each go up by one instead:

| # | Type | Occurrences | Step shape |
|---|---|---|---|
| 1 | `MovR32Imm32` (`mov_r32`) | 3 (was 2 — §8(b) adds `mov_r32 .r11d 0xFFFFFFFF`) | `setGpr32 dst imm`, `rip += 5\|6` |
| 2 | `XorR32R32` (`xor_r32`) | 11 (was 10 — §8(b) adds `xor_r32 .eax .r11d`) | `setGpr32 dst (d^^^s)`, `setFlagsLogic64`, `rip += 2\|3` |
| 3 | `CmpR64R64` (`cmp_r64`) | 1 | `setFlagsCmp64`, `rip += 3` |
| 4 | `JaeRel32` (`jae_near_label`, §8(a) fix) | 1 | branch iff `!s.cf` — **unsigned**, replaces v1's `JgeRel32` |
| 5 | `MovR64R64` (`mov_r64`) | 9 | `setGpr64 dst (gprs src)`, `rip += 3` |
| 6 | `AddR64R64` (`add_r64`) | 1 | `setGpr64 dst (d+s)`, `setFlagsAdd64`, `rip += 3` |
| 7 | `MovzxR64Mem8` (`movzx_r64_mem8`) | 1 | `setGpr64 dst ((memory addr).toUInt64)`, `rip += 4` — the only memory-touching occurrence |
| 8 | `AndR64Imm8` (`and_r64_imm8`) | 8 | `setGpr64 dst (d &&& signExtend8 imm)`, `setFlagsLogic64`, `rip += 4` |
| 9 | `ShrR64Imm8` (`shr_r64_imm8`) | 8 | `setGpr64 dst (d >>> count)` + CF/OF, `rip += 4` |
| 10 | `CmpR64Imm8` (`cmp_r64_imm8`) | 8 | `setFlagsCmp64 d (signExtend8 imm)`, `rip += 4` |
| 11 | `JeRel32` (`je_near_label`) | 8 | branch iff `zf` |
| 12 | `AddR64Imm8` (`add_r64_imm8`) | 1 | `setGpr64 dst (d + signExtend8 imm)`, `setFlagsAdd64`, `rip += 4` |
| 13 | `JmpRel32` (`jmp_near_label`) | 1 | unconditional |
| 14 | `RetOp` (`ret_op`) | 1 | `pop64`, `rip := popped value` |

**62 total occurrences** post-§8(b)-fix (61 in the as-shipped assembly, minus the one `not_r64`
instruction it removes, plus the two instructions that replace it), across these 14 types. No
`Not`-family instruction is used anywhere in the fixed routine — see §8(b) for why this fix was
chosen over the `NotR32` alternative v2 proposed.

### 3.2 The wrapper problem: step lemmas at concrete types do not fire (M2a)

**v1's statement shape (`theorem step_xor_r32 : X86_64Instruction.step (XorR32R32.mk dst src) s =
...`) is unusable as written.** `X86_64Instr = AnyX86_64Instruction` (`Instructions.lean:45`) is a
dependent existential (`Base.lean:33-36`: `{α : Type} [inst : X86_64Instruction α] (instr : α)`),
and `crc32SymbolicProgram`'s elements, once assembled, are `X86_64Instr` values, i.e. packed
`AnyX86_64Instruction` terms (`⟨XorR32R32.mk dst src⟩` via the `xor_r32` smart constructor, whose
return type is already `AnyX86_64Instruction`). A goal after one `stepX86_64`/`X86_64Instruction.step`
unfolding is stated over the **wrapper's** `step` field (`Base.lean`'s `instance :
X86_64Instruction AnyX86_64Instruction where step pkg s := @X86_64Instruction.step pkg.α pkg.inst
pkg.instr s`), not directly over `XorR32R32`'s `step`. A `@[simp]` lemma stated at the concrete
type will not match that goal shape without an unfolding step through the wrapper first. **Fix**:
state each of the 14 lemmas at the point of construction — i.e. as a fact about
`X86_64Instruction.step (⟨XorR32R32.mk dst src⟩ : AnyX86_64Instruction) s = ...` (equivalently,
`@[simp]` on the *wrapper instance's* `step` field applied to a literal `⟨...⟩` packing, which
`simp`/`dsimp` should reduce projection-then-dispatch in one step since the existential is
resolved at the literal construction site, not behind an opaque `α`). This is a statement-shape
correction, not new proof content — the 14 semantic facts in §3.1 are unchanged; only the type
they must be proven at changes.

### 3.3 The dominant tractability risk: `instructionAtRip`'s linear re-walk (M2b — new, not in v1)

v1 worried about the specification side's `Id.run`/`for`-loop structure (§3.6 below) and never
looked at the machine side. **The machine side is worse, and is the actual bottleneck:**
`runProgramWithLoops` (`Semantics.lean`) advances by calling `instructionAtRip baseRip
instructions s.rip`, which **linearly walks the (62-element, post-§8(b)-fix) list from the top, re-encoding every
instruction it passes to compute the next candidate address**, comparing against the target `rip`
each time (`Semantics.lean:29-37`). One machine step through this proof's loop body therefore
forces `simp`/the elaborator to:

1. Decide `curRip == targetRip` against a *symbolic* `rip` value (`m₀.rip + n` for some computed
   `n`) at each of up to 62 list positions — up to 61 of which must be **disproven**, each
   requiring a `UInt64` injectivity/arithmetic fact, not a `rfl`.
2. Evaluate `X86_64Instruction.encode` **through the `AnyX86_64Instruction` wrapper** at each
   position passed, to get that position's size, before it can even attempt step 1 at the next
   position.

Across one full loop-iteration body (roughly 57 of the 62 instructions execute per byte processed
— everything except the two pre-loop init instructions and the two post-loop tail instructions),
the walk cost is the **sum of the executed instructions' own list positions**, not (executed
count) × (list length) — corrected in v3 per the second review's note: this is on the order of
**~1,800 `encode` reductions and ~1,800 disequality obligations per iteration** (not the v2 figure
of ~3,700, which overstated it by treating every step as if it always re-scanned the full list),
still per iteration, not per proof — i.e. this cost recurs at *every one of `len` induction steps*
if the proof re-runs the interpreter naively, and the order of magnitude and the conclusion (this
is the dominant risk, and a decode-lemma set is mandatory, not optional) are unchanged by the
correction.
`MODEL_DEBT.md` B6 already flags `instructionAtRip`'s re-encoding walk as an O(n²) *performance*
wall for the emitted binary; it is equally, independently, an O(n²) *proof-tactic* wall for this
exact proof, and nobody had previously connected the two. **This, not the specification side's
`Id.run` structure, is the primary tractability risk for PA1** — see §3.6/§5 for the fix.

### 3.4 The genuinely-unrolled inner chain, factored at block level, not step level (M7b)

The 8x bit-unrolled chain (`crc_sub_bit0`..`crc_sub_bit7`) is straight-line code with forward-only
conditional skips — no back-edge, no induction. v1 correctly identified this needs no loop
invariant, but its proposed discharge (`simp` unfolding plus `by_cases`/`split` on each of the 8
`je` conditions independently) is **2⁸ = 256 leaf goals per byte iteration** if the 8 bit-blocks
are case-split independently rather than composed. **The actual reuse unit (ADR-0011's "prove the
language once" move, applied at the right granularity) is the 6-instruction bit-block itself, not
the individual step lemma**: prove one composite lemma —

```
theorem step_crc_bit (c : UInt32) (poly : UInt32) (s : X86_64MachineState) :
  <6-instruction sequence starting from eax = c, r10d = poly, executes mov r11,rax; and r11,1;
   shr rax,1; cmp r11,0; je skip; xor eax,r10d; [skip:]> produces eax =
    if c &&& 1 != 0 then (c >>> 1) ^^^ poly else c >>> 1
```

by a single `by_cases hc : c &&& 1 != 0` (2 cases, not 8 independent ones), then **apply this one
lemma 8 times** — 16 leaf cases total across a full byte's bit-chain (2 cases × 8 applications),
not 256. This is the block-level analog of the per-instruction step-lemma reuse §3.1 already
gets right, and it is the single most under-exploited leverage point in v1's design — v1 treated
the 14 step lemmas as the only unit of reuse and missed that the *block* is the real one here.

**This lemma is stated over `UInt32` (`c : UInt32`), but the block's actual `shr rax,1` instruction
is a 64-bit shift over the full `rax` register (§3.1 row 9) — the lemma is only sound to apply when
`rax`'s upper 32 bits are already known to be zero at block entry.** That fact is not free; it is
exactly the invariant's ★2 conjunct in §4.0, which the loop-body proof must establish at every
iteration for this lemma to apply at all. Stated here, resolved there — this cross-reference is
itself a correction (M2): v2 left this dependency unstated and un-sourced.

### 3.5 The genuine loop: outer, over bytes — the induction target

Unchanged in shape from v1 (the one back-edge, gated by `cmp r8,rdx; jae crc32_calc_done` post-§8
fix, is the one induction Law 7 requires). **The invariant itself is written in §4.0** — v2 said
"restated in §4.2" here and again in old-§4.3, but §4.2 (titled "what a caller-composition proof
would need") never contained one. This was the single largest miss the second review found (M2):
two dangling forward-references to an artifact that was never actually written, one level up from
v1's identical `updateCrc32Internal` miss. §4.0 fixes this directly.

### 3.6 The connection theorem: `bv_decide` on a branch-free normal form, not linearity (M1)

**v1's recommended route — "unfold both sides to a shared normal form" — is impossible, and v1's
own text half-noticed this** ("this is not quite the standard Sarwate derivation... wait") before
recommending it anyway. The two sides apply the same 8-step map `G` to **different arguments**:
the asm side applies `G⁸` to the full 32-bit `c ^^^ b`; `mkCrcTableEntry`'s table-entry side
applies `G⁸` to an **8-bit seed** (`n.toUInt32`, `n < 256`) and then requires an *additional*
`(c >>> 8) ^^^` wrapped around the result. There is no shared normal form where these two
expressions coincide syntactically — the "unfold both sides" route cannot close, full stop.

**The working route, verified on this toolchain (2.3s, ∀ over all 2³² accumulators, no linearity
library, no induction):**

1. **Normalize `G` branch-free**: `Gbf c := (c >>> 1) ^^^ (poly &&& (0 - (c &&& 1)))`, using
   `0 - (c &&& 1)` as the standard bit-trick for "all-ones if bit 0 set, else all-zero" over
   `UInt32` (`c &&& 1` is `0` or `1`; `0 - 1 = 0xFFFFFFFF` under `UInt32` wraparound). Prove `G =
   Gbf` pointwise by `by_cases (c &&& 1 != 0)` (2 cases) + `bv_decide` per case — **with one
   correction, per M9(a) below: the naive script fails even here and needs a normalization step
   first.**
2. **Prove `G8bf_table : Gbf^8 x = (x >>> 8) ^^^ Gbf^8 (x &&& 0xFF)` by `bv_decide` directly** — a
   single proposition, ∀ over all `x : UInt32` (the complete finite domain, 2³² values), discharged
   by a SAT certificate.
3. Chain: the asm's per-byte update is `G^8 (c ^^^ b) = Gbf^8 (c ^^^ b) = (c >>> 8) ^^^ Gbf^8 ((c
   ^^^ b) &&& 0xFF) = (c >>> 8) ^^^ G^8 ((c ^^^ b) &&& 0xFF)`, and `(c^^^b) &&& 0xFF < 256`, so
   `G^8` applied to it is exactly what `mkCrcTableEntry`'s loop computes for that index — closing
   the connection theorem entirely by rewriting, no induction.

**The branch-free normalization in step 1 is load-bearing, not stylistic**: `bv_decide` on `G`
directly (with its native `if c &&& 1 != 0 then ... else ...` conditional) **fails** — it abstracts
the `!= 0` decidable condition as an opaque boolean and returns a spurious counterexample, because
it cannot see through `Decidable`-instance dispatch on a runtime-computed guard the way it can see
through pure bitvector arithmetic. Both the failure mode and the fix were confirmed on the actual
toolchain by the reviewer; §3.7 has the fallback if this needs revisiting, but this is the primary
route, not a fallback.

**M9(a), second review — the step-1 tactic script above (`by_cases` then `bv_decide` per case)
does NOT work as literally written, and the reason is the same failure recurring one level up.**
`by_cases h : c &&& 1 != 0` splits the *goal*, but the residual `c &&& 1 != 0`/`c &&& 1 = 0`
hypothesis in context is still `Bool`-decidability-flavored (a `Bool`-valued expression compared
via `!=`/`Decidable`), and `bv_decide` invoked on either branch **fails with the identical error
family**: "abstracted the following unsupported expressions as opaque variables: `[c &&& 1 != 0]`"
— it does not automatically discharge using the `by_cases` hypothesis just because the case split
happened. **The fix**: normalize the `Bool`-valued disequality to a propositional bitvector
equality *before* invoking `bv_decide` (e.g. rewrite `c &&& 1 != 0` to `c &&& 1 = 1` — or
`c &&& 1 = 0` in the other branch — via the standard `decide_eq_true_iff`/`Bool.decide_eq_true`-
shaped simp lemma bridging `Bool` and `Prop`, then substitute that equality into the goal before
calling `bv_decide`). This is a one-line addition once known, but costs real debugging time if
not — recorded here specifically so the implementer does not lose it.

**If the kernel-checked route is preferred over `bv_decide`** (see §3.7-policy below for why one
might be): the reviewer's cost estimate is that this is **cheaper than v1 feared** — G-linearity
is a 4-case split (bit-0-of-`c`, bit-0-of-`b`, combined) plus standard shift/XOR distributivity,
and "`G⁸` applied to an input `< 256` never sets bits above position 7 until poly-XORs accumulate"
is an 8-step unfold — roughly 4 small lemmas, not a linearity *library*. The one real gap: `decide
+kernel` cannot discharge the `UInt32` distributivity primitive this route needs — genuine
`BitVec`-bridging lemma-writing is required there, unlike the `bv_decide` route.

#### 3.6-policy: `bv_decide`'s axiom footprint under Law 10 (M1b)

`#print axioms` on a `bv_decide`-closed goal (Lean/toolchain version 4.33.1) shows dependence on a
`<decl>._native.bv_decide.ax_*`-shaped axiom — a native-evaluation axiom in the same family Law 10
already gates (`ofReduceBool`/`ofReduceNat`), and this toolchain version has no
`bv_decide (config := {checkProofs := true})` kernel-replay option to avoid it. **Correction (M9(b),
second review): only one of the two gate tools is actually blind to this.**
`scripts/check_gates.py`'s source-level pre-check matches known tactic *spellings* by regex and
does not currently recognize `bv_decide` as text, so it will not flag (or corroborate) the
occurrence at all. `lake exe check_gates_axioms`, however, **already catches it**:
`Tools/CheckGatesAxioms.lean`'s `hasNativeComponent` (`:68-76`) matches any component of an axiom's
`Name` that is literally `"_native"` — a structural check, not a check for the specific substring
`native_decide` or `decide` — and `<decl>._native.bv_decide.ax_*` has exactly such a component. So
this proof will already be flagged (correctly) by the load-bearing axiom-level gate; it is only the
faster source-level pre-check that needs teaching the spelling, and only for its own corroboration-
signal / stale-entry bookkeeping, not for the gate's actual soundness.

**Ruling, recorded here per Law 5 (design decisions are made in the design, not deferred to
implementation time): this is admissible under Law 10 as written.** Law 10's actual target is
"evaluation at sampled points" masquerading as a universal claim; a SAT solver's certificate for
`∀ x : UInt32, P x` is categorically not that — it is a machine-checked (if not kernel-checked)
proof that the proposition holds for the **complete** finite domain, exactly the "exhaustive
finite-∀" case Law 10 already admits `native_decide`/`decide` for. The novelty is only that the
*mechanism* generating the certificate is a SAT solver rather than a brute-force evaluator; that
distinction is not what Law 10 gates on. **Decision**: allowlist the `G8bf_table` (and `G =
Gbf`) occurrences under `finite-forall`, with justification text naming the SAT certificate and
the finite domain size (`2^32`, `UInt32`'s complete domain) explicitly, per
`scripts/gate_allowlist.txt`'s five-field format. **Follow-up (small, separate task, not PA1's own
scope, and corrected per M9(b) above)**: only `scripts/check_gates.py`'s source-level pre-check
needs to learn the `bv_decide` spelling for its own corroboration-signal regex — the axiom-level
`lake exe check_gates_axioms` gate already catches the occurrence structurally via
`hasNativeComponent` and needs no change. File the pre-check teaching as backlog alongside the
existing Law 10 gate-tooling backlog items rather than block PA1 on it; it is a nice-to-have for
faster local feedback, not a soundness gap.

### 3.7 What discharges by `simp` + step/block lemmas vs. `omega` vs. induction

Unchanged in spirit from v1: straight-line ALU/branch/load transitions and the 8-fold bit-chain
(now block-factored, §3.4) via `simp` + the 14 lemmas; `k ≤ len`/loop-exit arithmetic via `omega`;
the outer-byte induction (§3.5) as the one genuine induction. **Precedent check, corrected a
second time (M4, second review)**: v2's own "corrected" count (106 theorems: 72 `rfl`, 20
`native_decide`, 7 `decide`, 4 `omega`, 2 `simp`, 1 `induction`) was itself substantially wrong —
exactly the failure this review round exists to catch, on the very item the first review made
mandatory. Two independent recounts (the second review's, and this session's own re-verification
via direct grep against the tree) agree closely: **~92-98 theorem/lemma declarations, `rfl` 17,
`native_decide` 47, `decide` 35, `omega` 8, `simp` 3, `induction` 1**. Six of seven figures in v2's
table were wrong, several by 3-4×. The corrected numbers still support the same qualitative point
(structural proof is rare; `native_decide`/`decide` dominate), but **the sharper and more directly
load-bearing fact, which this design's argument actually needs and did not previously state, is
qualitative, not a count: `by_cases` occurs ZERO times anywhere in `Gasm`/`Stdlib`/`Spikes` today
(independently confirmed)**. Both §3.4's block-lemma case split and §3.6's connection-theorem case
split depend on `by_cases` — this proof would be introducing that tactic's first use in the tree,
not applying an established idiom, which is the real-strength version of the argument that follows.

### 3.8 The reformulation is THE design, on both sides, not a fallback (M3)

v1 filed this under "fallback if `Id.run` resists `simp`." It is not conditional, on either side:

**Machine side (new, per §3.3's finding)**: the fix for the `instructionAtRip` linear-rewalk cost
is a **decode-lemma set** — one lemma per instruction offset, `instructionAtRip m₀.rip
(assembleProgram m₀.rip crc32SymbolicProgram) (m₀.rip + nᵢ) = some instrᵢ`, proven once per
offset (62 small facts, each closing by the same `unfold`+arithmetic pattern, not 62 independent
proof efforts) — so that the loop-body proof advances by rewriting through this lemma set instead
of re-invoking `instructionAtRip`'s recursion and re-deriving up to 61 disequalities every step.
Equivalently, define a small-step relation over `(k : Nat) × <register/memory state>` that the
proof advances directly, with the decode-lemma set as the (proven-once) bridge back to
`runProgramWithLoops`. Either way, this must be built **before** the per-iteration proof is
attempted — it is not a contingency for if `simp` struggles, it is the difference between a
tractable proof and a proof whose per-step cost scales with program length squared.

**Recommended, not blocking (flagged, not resolved, by the second review): the base-`rip` is
symbolic, and neither obvious way to state the decode-lemma set closes it cleanly.** Each decode
lemma's target address is `m₀.rip + nᵢ` for a *symbolic* `m₀.rip` (the contract is universal over
the caller's entry state, §2.2 — there is no reason `m₀.rip` is any particular concrete value).
`toDisp32`'s displacement arithmetic (used by `assembleProgram` to resolve every symbolic jump,
§2.3 point 1) computes differences like `(m₀.rip + a) - (m₀.rip + b)`, and showing this equals the
constant `a - b` regardless of `m₀.rip`'s actual value needs a `UInt64` subtraction-cancellation
fact (`(x + a) - (x + b) = a - b`, valid for `UInt64`'s wraparound semantics but not `rfl`) that
this design does not currently name a source for. Two routes are open and neither is chosen here:
(a) prove the decode-lemma set generically over a symbolic base via this cancellation lemma
(pushes the gap into one small arithmetic fact, reusable by every future routine's decode-lemma
set); or (b) prove the whole contract at one fixed concrete base address first, then transport the
result to an arbitrary `m₀.rip` via the relocation/embedding lemma §2.3 point 2 already defers
(pushes the gap into that already-deferred lemma instead, rather than adding a new one). Recorded
here so the implementer chooses deliberately rather than discovering the hole mid-proof.

**Spec side**: `updateCrc32`'s `Id.run do ... for i in [start:stop] do ...` does not obviously
expose the loop-carried accumulator `c` as a term the invariant (§4.0) can even *name* —
`Std.Range.forIn'`/`ForIn` machinery is not a structural recursion a term-mode induction pattern-
matches on directly. **v1's own §7 Q3 asked exactly this and left it open; the answer is: the
reformulation must precede *stating* the invariant, not just proving it.** Concretely, this design
requires (as a prerequisite definition, to be authored alongside the proof, not assumed to already
exist — v1 incorrectly wrote as if `updateCrc32Internal` already existed in the tree; it does not):

```
def crc32InternalFold (buf : ByteArray) (n : Nat) : UInt32 :=  -- explicit fold, n ≤ buf.size
  (List.range n).foldl (fun c i => (c >>> 8) ^^^ crc32Table[(c ^^^ (buf.get! i).toUInt32) &&& 0xFF]!)
    0xFFFFFFFF
```

**M3b: the fact that this equals `updateCrc32`'s actual `for`-loop behavior is itself a second Law
12 connection theorem** — `crc32InternalFold buf buf.size = updateCrc32 0 buf 0 buf.size ^^^
0xFFFFFFFF`'s precursor, i.e. `updateCrc32`'s `Id.run`/`for` form must be shown equal to this
explicit `List.foldl` form before the invariant (§4.0) can be stated against it. **PA1 needs two
connection theorems, not one**: this fold-normalization one, and §3.6's table/closed-form one.
This has implications beyond `crc32`: the `Id.run do ... for i in [a:b] ...` pattern recurs across
`Stdlib/Zlib/*.lean` (it is exactly how `crc32Table` itself, `Adler32`, and — per recent commits —
the Huffman/LZ77 machinery are written), so a companion "foldl normal form" lemma is generically
needed before any of them are inductively tractable against assembly, not a `crc32`-specific
concern.

**Recommended, not blocking (the second review's addition): this connection theorem's own
obligation is slightly larger than the sketch above shows.** `updateCrc32` (`CRC32.lean:31-41`)
indexes `crc32Table` via a **dependent `if`** (`if h : idx < tbl.size then tbl[idx] else
mkCrcTableEntry idx`, guarding the safe-indexing proof obligation), where `crc32Table` is itself
built by a *second* `Id.run`/`for`-loop (`CRC32.lean:22-27`) — whereas `crc32InternalFold` above
uses the unchecked `crc32Table[...]!` panic-on-failure indexing for readability. Discharging the
fold-normalization connection theorem therefore also needs `crc32Table.size = 256` (to know the
dependent `if`'s `then` branch is always taken, and that `!`-indexing never panics) — itself a fact
about a *second* `Id.run`/`for`-loop, proven the same way as the first. Not a new kind of
obligation, but one more instance of it than the sketch above shows explicitly.

## 4. Composition Story

### 4.0 The Loop Invariant (M2 — the artifact that was missing from v2)

Stated concretely, at the point in execution immediately before the `k`-th iteration's loop-test
(`cmp r8,rdx`) executes, for `0 ≤ k ≤ len`:

```
Inv (k : Nat) (m₀ s : X86_64MachineState) (ptr len : UInt64) (buf : ByteArray) : Prop :=
  s.rip = <address of the "crc32_calc_loop" label>  ∧      -- ★1 (M2): without this, "the state at
                                                             -- the start of iteration k" is not a
                                                             -- well-defined thing to talk about —
                                                             -- the induction step has no fixed
                                                             -- point to begin from
  s.gprs .rcx = ptr  ∧
  s.gprs .rdx = len  ∧
  s.gprs .r8 = k.toUInt64  ∧
  k ≤ len  ∧
  s.gprs .rax = (crc32InternalFold buf k).toUInt64  ∧        -- ★2 (M2): full 64-bit equality, NOT
                                                             -- `.toUInt32`-truncated — see below,
                                                             -- this is the conjunct §3.4's block
                                                             -- lemma silently depends on
  s.rsp = m₀.rsp  ∧
  (∀ a, s.memory a = m₀.memory a)
```

**★2 is the conjunct v2 never wrote down, and its absence is not cosmetic.** §3.4's block lemma
(`step_crc_bit`) is stated as a fact about `UInt32` arithmetic (`c : UInt32`, `eax = c` at block
entry, produces `eax = (if ... then ... else ...) : UInt32` at block exit) — but the assembly's
`shr rax,1` inside that block (`ShrR64Imm8`, §3.1 row 9) is a genuine **64-bit** shift over the
full `rax` register, not a 32-bit shift over `eax` alone. If `rax`'s upper 32 bits were ever
nonzero at block entry, that 64-bit shift would leak bit 32 down into bit 31 of the result, and
the block lemma's `UInt32`-only characterization of the post-state would simply be **false** for
that state — the lemma would not apply, silently, wherever it was invoked. The invariant's ★2
conjunct is precisely what rules this out at every iteration: `crc32InternalFold buf k : UInt32`
is (by construction, §3.8) a genuinely 32-bit value, so stating `s.gprs .rax` (the full 64-bit
register) equal to its `.toUInt64` zero-extension is what carries "upper 32 bits are 0" forward
through the induction — without it, §3.4's block lemma would need to be independently re-proven
sound against a `rax` whose upper bits are unconstrained, which it is not stated to handle. This
is exactly the invariant conjunct the loop-body proof step must establish going *into* the block
lemma's application, not merely something true incidentally.

**★1 (the `rip` conjunct)** is what makes "prove `Inv k → Inv (k+1)`" a statement about a concrete
program transition at all: without pinning where control actually is, there is no fixed starting
point for "run the loop body once" to be a well-typed operation on.

**Base case** (`k = 0`): follows from `Pre` (§2.2) directly — `r8` is zeroed by the routine's own
init (`xor_r32 .r8d .r8d`), `rax` is `0xFFFFFFFF`, matching `crc32InternalFold buf 0 = 0xFFFFFFFF`
by the fold's own definition (empty range), and `rip` is at the loop label by construction of
"the two init instructions ran and control fell through to the label."

**Step case** (`Inv k → Inv (k+1)`, given `k < len`): the loop-test takes the "continue" branch
(`jae` does not fire, §8(a)); the byte-load-and-XOR prologue (§3.1 rows 5-8) establishes `eax = 
acc ^^^ buf.get! k` where `acc` is the pre-byte accumulator; the 8-block bit-chain (§3.4, applied
8 times) computes `G^8` of that value; the connection theorem (§3.6) identifies this with
`(acc >>> 8) ^^^ crc32Table[(acc ^^^ buf.get! k) &&& 0xFF]`, which is exactly `crc32InternalFold`'s
own one-step update (§3.8) — establishing `Inv (k+1)`'s `rax` conjunct; `r8` advances by the
routine's `add_r64_imm8 .r8 1`; `rip` returns to the loop label via the back-edge `jmp`; nothing
else in `Inv` changes (no writes, §2.1; `rcx`/`rdx`/`rsp` untouched by the loop body).

**Exit** (`Inv len s`, loop-test takes the "done" branch): `s.gprs .rax = (crc32InternalFold buf
len).toUInt64 = (Stdlib.Zlib.crc32 buf).toUInt64` by M3b's fold-normalization connection theorem
(§3.8) plus `crc32`'s own definition (the `^^^ 0xFFFFFFFF` in `updateCrc32`'s spec matching the
`xor eax,r11d` tail post-§8(b)-fix) — this is Theorem 1's conclusion (§2.3), and the remaining
`Inv` conjuncts (`rsp`, memory-unchanged) transfer directly into Theorems 2/3 (§2.4/§2.5).

### 4.1 Sequential composition (within this proof)

Unchanged from v1: the routine's own proof chains one "process one byte" step (§3.4's block
lemma, applied once per byte via §3.5's induction) through the decode-lemma-mediated advance
(§3.8); no general sequential/call/loop composition calculus needs building for this proof alone.

### 4.2 What a caller-composition proof would need — against the REAL call sites (M10)

v1 invented a hypothetical `gzip_header_and_crc` caller. Two real ones already exist and should
be the basis for this section instead — using them directly would have answered v1's own §7 Q5
immediately (see §8(b)):

**Call site 1 — `gzipCompressSymbolicProgram`, `Windows.lean:801-832`** (compress path, "5.
Calculate CRC-32 of inBuf"): `mov rcx,r15; mov rdx,rbx; call_label "zlib_crc32"`, then **four**
extractions — `mov r8,rax; shr r8,{0,8,16,24}; mov_mem8 r9,r8` — writing the CRC's four bytes
little-endian into the trailer. Each `mov_mem8` writes `.toUInt8` (low 8 bits only) of a value
shifted right by at most 24, so **even pre-§8(b)-fix, this call site's output is correct**: the
corrupted upper 32 bits of `RAX` (all-ones, pre-fix) never surface in any of the four bytes
actually written, since every extracted byte comes from bit positions ≤ 31. This is exactly why
the defect was latent rather than an observed test failure (§8(b)).

**Call site 2 — `gzipDecompressSymbolicProgram`, `Windows.lean:2210-2219`** (`decompress_finish`):
`mov rcx,r14; mov rdx,r13; call_label "zlib_crc32"`, followed **immediately** by `xor_r32 .eax
.eax`. This call site does not use the CRC result at all — see the note below and the out-of-scope
bug flagged in §10.

**What a real composition proof needs from this pathfinder, concretely, against call site 1**:

1. Theorem 1 (§2.3) instantiated at the caller's `r15`/`rbx` — works as stated provided the caller
   discharges `Pre` (its own memory readability over `[r15, r15+rbx)`) and `ValidFunctionEntryStack`
   at the call.
2. Theorem 2 (§2.4) — the caller must know `rax,rcx,rdx,r8-r11,flags` are clobbered and must NOT
   depend on `rcx`/`rdx` surviving the call (this caller doesn't — it reloads `r9`/`r8` from `r14`/
   `r13` afterward, never reusing `rcx`/`rdx`, consistent with treating them as clobbered).
3. `crc32_no_writes`/`crc32_result_depends_only_on_buffer` (§2.5) — the caller needs to know the
   CRC call didn't clobber the header bytes it already wrote to `outBuf` before the call. This is
   exactly the frame condition composition needs, and per §7 it is the dimension this pathfinder
   alone cannot fully validate (crc32 has no writes to frame *against*).
4. **The relocation/embedding lemma (§2.3 point 2)** — the contract above is proven for
   `crc32SymbolicProgram` assembled standalone; the caller's proof needs it proven for the same
   list assembled as a sub-range of `gzipStreamSymbolicProgram` at a different base address. Not
   proven by this design.
5. **A `call`/`ret` pairing lemma this pathfinder does not produce**: `crc32SymbolicProgram` is a
   leaf with no callees, so nothing here validates that a *sequence* of calls (e.g., this call
   followed by later calls in the same caller) composes correctly through the push/pop discipline.
   This is the concrete gap PA2 should generalize into a reusable `call`-composition rule taking
   two already-proven routine contracts and producing the composed contract without re-proving
   either body.

### 4.3 Slotting into `VerifiedRoutine`: do not attempt it in PA1 (M11)

v1 flagged a step-ratio mismatch (`VerifiedRoutine.traceEquivalence` is single-step; this routine's
loop body is ~9-15 machine steps per spec-step) and left it as an open question. **There is a
second, harder mismatch that makes the question moot regardless of the first fix**:
`couplingInv : SpecState → MachineState → Bool` is `Bool`-valued — decidable, finite-witness — and
this design's own invariant (§4.0) contains `∀ a, m.memory a = m₀.memory a`, a universal
quantification over `2^64` addresses on a function-typed field. This is not expressible as a
`Bool` under any step-ratio fix; it would need `couplingInv : SpecState → MachineState → Prop`
first, which is a different (larger) redesign of the structure, not a parameter addition. **This
claim needs one caveat, per the second review's M6: it is not true that no Bool-valued coupling
invariant of a similar shape works at all** — `Stdlib/SmolAlloc/Equivalence.lean`'s
`smolAllocInvariant` (§9) is exactly a `Bool`-valued coupling invariant between an abstract state
and `X86_64MachineState`, already in use. The distinction is that `smolAllocInvariant` only
quantifies over a *finite* list (`spec.blocks.all (...)`), which is genuinely `Bool`-representable;
`crc32`'s own invariant needs a universal quantifier over all `2^64` addresses (the no-writes
conjunct) specifically, which is not. The claim above is therefore about *this contract's*
invariant shape, not a blanket claim that `VerifiedRoutine`'s `couplingInv` field can never work —
see §9 for where the existing `Bool`-valued precedent is directly relevant instead.
**Decision: do not instantiate `VerifiedRoutine` in PA1.** Prove the three split theorems directly
against `X86_64MachineState`, unstructured (as §2 already does), and hand PA2 both mismatches
(step-ratio and `Bool`-vs-`Prop`) as findings against existing, currently-unused infrastructure —
this avoids entangling PA1 in a second untested hypothesis, mirroring the same reasoning already
applied to Law 11/capability adoption in §1.1.

### 4.4 Fuel-stability and exit-through-`ret` (M9, folded into §2.3 already; restated for emphasis)

`runProgramWithLoops` returns its input state unchanged both when fuel is exhausted **and** when
`instructionAtRip` finds nothing at the current `rip` — the two cases are indistinguishable from
the return value alone. §2.3's postcondition avoids this ambiguity by (a) stating fuel-stability
explicitly (`∃ N, ∀ fuel ≥ N, ... = m_final`, not just "for `fuel := <some number>`") and (b)
pinning `m_final.rip` to the return address popped off the entry stack, so the theorem witnesses
that execution actually reached and executed the trailing `ret`, not that fuel simply ran out
somewhere plausible-looking.

## 5. Proof-Tactic Strategy Summary

- **`simp` + the 14 step lemmas (correctly stated at the wrapper construction site, §3.2) + the
  block-level bit lemma (§3.4)**: discharges each byte's straight-line instruction sequence.
- **The decode-lemma set (§3.8)**: discharges "what instruction executes next" without
  `instructionAtRip`'s O(n) rewalk — this, not `simp` congestion, is what makes the per-iteration
  proof cost bounded rather than growing with program length (§3.3).
- **`bv_decide` on the branch-free-normalized connection theorem (§3.6)**: discharges the per-byte
  table/closed-form connection in one ∀-2³² SAT certificate, allowlisted per §3.6-policy.
- **A second connection theorem, `crc32InternalFold` vs. `updateCrc32`'s `Id.run`/`for` form
  (§3.8/M3b)**: needed before the invariant can be *stated*, not only before it can be proven.
- **`omega`**: the `k ≤ len`/loop-exit `Nat`/`UInt64` bridging arithmetic. Likely needs a small
  bridging-lemma layer (`UInt64`↔`Nat` round-trip facts) that does not yet exist generically in
  the tree — flagged as PA2/PA3 backlog, not hand-rolled per proof.
- **`induction`**: exactly once, on the outer byte count `k : 0..len` (§3.5) — the one Law-7-
  mandated induction; everything else above is unfolding/rewriting, not induction.

## 6. Composition-Sketch Summary for PA2 (what generalizes)

1. **The 14 step lemmas, stated at the correct wrapper-construction shape (§3.2)** — near-
   universal ISA coverage, genuinely validated by the 61-instruction census.
2. **The block-level lemma as the reuse unit** (§3.4) — the most under-exploited insight in v1;
   ADR-0011's "prove the language once" applies one level above individual instructions wherever a
   DSL program repeats a multi-instruction idiom (the 6-instruction bit-test-and-conditional-XOR
   block recurs 8× here; similar multi-instruction idioms likely recur across the Huffman/LZ77
   bit-packers).
3. **The decode-lemma set / step-relation reformulation (§3.8), promoted from fallback to
   mandatory** — needed on the machine side for *any* loop-bearing routine, not just this one,
   because `instructionAtRip`'s cost is a property of `runProgramWithLoops` itself.
4. **A bounded-counting-loop combinator** — `crc32_calc_loop`'s shape (index register vs. length
   register, unconditional increment, unconditional back-edge, exit test) is not `crc32`-specific:
   `adler32SymbolicProgram` (`Windows.lean:127-149`) has the **identical** shape, and per §8(a)
   both currently share the same signed-compare defect. A generic combinator — given an invariant,
   a measure, and a per-iteration step fact, produce the whole-loop theorem, **and emit the
   unsigned `jae`/`jnb` exit test by construction** rather than allowing `jge`/`jle` to be chosen
   for an unsigned index comparison — closes the defect class structurally (Law 13) rather than
   catching instances of it by lint.
5. **Branch-free normalization + `bv_decide` for bit-twiddling connection theorems (§3.6)** — the
   single most transferable technique found here; it will matter far more for the Huffman/LZ77
   bit-packers' connection theorems than for `crc32` itself, and the `bv_decide` axiom-gate policy
   (§3.6-policy) needs to be settled once, not re-litigated per future routine.
6. **`VerifiedRoutine`'s two mismatches (§4.3)**: single-step `traceEquivalence` vs. multi-step
   routines, and `Bool`-valued `couplingInv` vs. a memory-quantifying invariant. Both are findings
   against existing, currently-unused infrastructure — PA2 should address both before anything
   attempts to instantiate the structure for a real routine.
7. **The relocation/embedding lemma (§2.3 point 2, §4.2 point 4)** — every routine in this codebase
   that is more than a standalone spike ships spliced into a larger program at a non-zero base
   address; this lemma (or its absence) affects all of them, not just `crc32`.

## 7. Honest Accounting Against the Architecture Hypothesis

v1 correctly flagged composition as unexercised (§4) but framed three other properties of this
routine as simplifications rather than as the dimensions of the D2/D11 hypothesis most likely to
fail. Restated honestly: **PA1, scoped to `crc32SymbolicProgram` alone, cannot falsify the modular-
contracts hypothesis — it can only confirm the easiest quadrant.** Specifically:

- **Zero memory writes** (§2.1) means the **frame-condition half of the hypothesis is completely
  untested** by this routine. `docs/VISION.md` §4's central architectural claim is that capability
  tokens *are* the frame conditions that let proofs compose without global reasoning — but a
  routine that writes nothing needs no frame condition beyond "nothing changed," which is the
  degenerate case of that claim, not a test of it. The routine in this codebase that actually
  needs a real frame condition and does not have one — `gzipCompressSymbolicProgram`'s header-
  writing prologue, which writes to `outBuf` at hand-computed offsets from a caller-supplied
  pointer, and its Dynamic-Huffman decompression path's 4096-byte hand-offset scratch region
  (`sub rsp, 4096`, `Windows.lean` decompress path) — is exactly `MODEL_DEBT.md` B3's named hidden-
  bug class (no bounds checking means a hand-computed offset write that goes wrong is
  unrepresentable as a *caught* error, only as silently wrong output). Nothing about crc32
  exercises whether a frame condition for a routine like that is even statable cleanly, let alone
  provable.
- **A leaf routine** (no callees) means the call-composition rule (§4.2 point 5) is completely
  unexercised, as v1 already said well.
- **A bounded, straight-line inner body with 1:1 spec/asm loop correspondence** (one byte per
  iteration on both sides) is the easiest possible shape for the outer induction (§3.5) to line up
  with the spec's own recursion — a routine whose asm and spec loop structures diverge (different
  iteration counts, different natural induction measures) would test the composition/invariant
  machinery far harder than this one does.

**Decision, adopted per the design review's recommendation: add a second, deliberately-chosen
routine to PA1's scope, specifically to exercise the frame-condition dimension crc32 structurally
cannot.** See §9.

## 8. Two Assembly Defects, Adopted as PA1 Prerequisites

### 8(a). Signed loop-exit compare (`jge` should be `jae`) — real, and systemic

`cmp r8,rdx` followed by `jge_near_label` branches on `s.sf == s.of_` (`JgeRel32`,
`Jcc.lean:206-211`) — a **signed** ≥ comparison. `r8`/`rdx` are an unsigned byte index and an
unsigned length; the correct instruction is the unsigned form. **`JaeRel32` already exists**
(`Jcc.lean:271-286`, branches on `!s.cf`) and **`jae_near_label` already exists**
(`Assembler.lean`), with `estimatedSize` for both near forms equal to 6 bytes — a drop-in, same-
size, single-token substitution. v1's `len < 2^63` precondition was an honest, non-vacuous
workaround, but it was the wrong remedy under Law 9: shrinking the contract to accommodate a
defect the assembly needn't have is backwards, and doing so here would enshrine the workaround as
the template for every future routine with the same idiom. **This is systemic, not cosmetic**: 53
uses of `jge_near_label` exist in the tree (against 3 of `jae_near_label`), and
`adler32SymbolicProgram` (`Windows.lean:127-149`) has the *identical* loop shape with the same
defect. Shipping `len < 2^63` as PA1's template risks propagating a small permanent lie into
roughly 50 future contracts. **Decision: fix the assembly** (§2.2's precondition already reflects
this — no length bound is needed at all once the compare is unsigned). **Mechanization (Law 13)**:
file a lint (or, better, the bounded-counting-loop combinator from §6 item 4) that flags a signed
`Jcc` consuming a `cmp` between an index-like register incremented from zero and a length-like
register, and emits the unsigned form by construction going forward.

### 8(b). `RAX` upper-bits ABI violation — real, latent at both current call sites

`not_r64 .rax` flips all 64 bits; because `rax`'s upper 32 bits are `0` throughout the loop
(`setGpr32`'s zero-extension), the routine's declared return value (per `docs/TARGETS/WINDOWS.md
§1.1`: "Return Value: RAX", not "the low 32 bits of RAX") is `0xFFFFFFFF_<crc>` rather than the
zero-extended `crc` a `uint32_t`-returning routine should produce. **Both real call sites happen to
survive this today** (§4.2: call site 1 only ever extracts bytes ≤ bit 31 via `shr`+`mov_mem8`;
call site 2 discards the result entirely, see §10) — but "latent, not currently wrong" is not the
same as "not a defect," and every future composition proof would otherwise inherit a "RAX's upper
bits are actually all-ones, not zero" caveat forever, to save rewriting one instruction now.

**Decision (M5, revised in v3): fix using two already-registered instructions, adding no new DSL
instruction.** v2 proposed narrowing the tail `NOT` to `not_r32 .eax` and, correctly, flagged that
this instruction does not exist — but did not price what adding it costs, and there is a cheaper
fix available today. Replace the tail's `not_r64 .rax` with:

```
instr (mov_r32 .r11d 0xFFFFFFFF),
instr (xor_r32 .eax .r11d),
```

`x ^^^ 0xFFFFFFFF = ~x` at 32-bit width, and `XorR32R32.step` (§3.1 row 2) writes its result via
`setGpr32`, which zero-extends — giving exactly `RAX = zero_extend(~eax)`, the correct convention,
using only instruction types already in this design's inventory (`MovR32Imm32`, `XorR32R32` —
§3.1's counts already reflect this fix, at 3 and 11 occurrences respectively). `r11` is already
declared dead-scratch at loop exit (§2.1) and its flags are already declared clobbered (§2.4), so
this fix introduces no new register-preservation obligation either. **This is the fix this design
adopts.**

**The alternative (`NotR32`) remains the more ISA-idiomatic answer and is defensible under a
demand-driven-growth principle** (add a real instruction only when a real need surfaces, rather
than working around its absence indefinitely) — **but its real cost, which v2 never priced, is not
small**: per this tree's own registered-instruction discipline, a new instruction type needs (a)
an entry in the instruction registry's expected-types list (an audited build-time check fails the
build on an unregistered instance), (b) a non-empty case list under `RoundtripGate`'s coverage
floor for the new instruction, (c) `Decoder.lean` support for decoding the non-REX.W `F7 /2` byte
pattern (distinguishing it from `NotR64`'s REX.W-prefixed form), and (d) the full
`X86_64Instruction` typeclass surface (`toNASM`, `toLean`, `toUops`, `canFuzzHardware`,
`generateFuzzStates`), not merely `encode`/`step`. None of this is prohibitive, but all of it is
implementation work this design does not need to take on to fix a one-instruction ABI defect, when
the two-instruction fix above achieves the identical result with zero registry/decoder/gate
surface area touched. If a future task independently wants `NotR32` for its own reasons (a routine
that genuinely wants a 32-bit `NOT` mid-computation, not just at a tail), that is a separate,
independently-justified addition — not a PA1 prerequisite.

## 9. The Second Routine: `smolFreeSymbolicProgram` (§7's fix)

**Pick: `Stdlib/SmolAlloc/Program.lean:78-103`, `smolFreeSymbolicProgram`** (not
`smolMallocSymbolicProgram`, and not any of the zlib routines). Justification:

- **It is the smallest genuinely memory-*writing* leaf in the tree.** 11 concrete instructions,
  one conditional branch (`je "free_null"`), **no loop at all** — smaller than `crc32` by
  instruction count and orthogonal to it in proof shape: where `crc32` stresses the loop-invariant
  machinery with zero writes, `smolFree` stresses the frame-condition/write machinery with zero
  loop induction. Together they cover the two dimensions §7 identifies as untested without either
  routine needing to be complicated.
- **It writes to a hand-computed offset from a caller-supplied pointer** (`rax := rcx - 32`, then
  `mov_mem64_disp_imm rax 0x08 1` to mark the block free, and `mov_mem64_disp rax 0x18 r10` to link
  the freelist), which is exactly `MODEL_DEBT.md` B3's named hidden-bug class in miniature: there
  is no check in the model or the routine that `rcx - 32` is a validly-owned header address (a
  caller passing a bad/foreign `rcx` produces silently-wrong writes, not a caught fault) — the
  smallest possible instance of the risk §7 says `crc32` cannot exercise.
- **It already has both a coupling invariant and a pointwise refinement theorem in the tree — a
  fact v2 completely missed (M6, second review), and one that changes what this routine's
  contribution to PA1 actually is.** `Stdlib/SmolAlloc/Equivalence.lean:23-30` defines
  `smolAllocInvariant : SmolAllocState → TracedPageState → X86_64MachineState → Bool`, a `Bool`-
  valued representation relation stating exactly the header-layout correspondence this design would
  otherwise have had to invent (`[b.address+0x00]=blockSize`, `[+0x08]=isFree`, `[+0x10]=alignment`,
  `[+0x18]=nextFree`, plus `r10 = freeListHead`). `:76-89` defines
  `smol_free_refinement_soundness_inst`, proved by `decide` on a **single ground vector** (one
  `malloc` then one `free`, both at concrete arguments) — a Law-10-grandfathered pointwise instance,
  not a universal theorem. **PA1's smolFree contribution is therefore not "author the first frame
  condition from scratch" — it is "universalize an existing pointwise refinement instance against
  an existing coupling invariant," turning a standing Law 9 violation into a Law 9 win.** This is a
  materially better story than v2's framing and should be stated as the primary justification for
  picking this routine, not a secondary one.
- **It has two exit paths** (`free_null` early return vs. the normal path), which `crc32`'s single
  loop-exit does not exercise — a different, useful stress on whether the contract/proof shape
  handles multiple return points cleanly.
- **It is a leaf with no callees**, matching crc32's composition-scope discipline (§1.1) — adding
  it does not also entangle PA1 in the call-composition question §4.2 already defers to PA2.

### 9.1 Two separable deliverables, not one contract (M7)

The second review's ruling, confirmed and refined here: **the frame condition and the spec
refinement are different claims with different preconditions, and conflating them (as v2's single
★-flagged `Pre` did) overcharges the cheaper one.**

**(i) The frame condition — needs no ownership precondition at all, and is what PA1 adopts as its
primary smolFree deliverable.** Both write addresses (`ptr - 32 + 8`, `ptr - 32 + 24`) are derived
*purely syntactically* from `rcx` via `mov rax,rcx; sub rax,32` — nothing about which addresses get
written depends on whether the block is actually allocated, freed, or garbage. The frame condition
is provable by unfolding two `write64` calls and is a pure arithmetic/disjointness fact:

```
Pre_frame(m₀, ptr) :=
  m₀.gprs .rcx = ptr ∧
  ptr.toNat ≥ 32 ∧                                              -- M8: no-wrap hypothesis on
                                                                  -- `ptr - 32`, was missing in v2
  ValidFunctionEntryStack m₀.rsp

Post_frame (Theorem 3', the actual point of choosing this routine):
  ∃ m_final, ... ∧
  (ptr = 0 → ∀ a, m_final.memory a = m₀.memory a) ∧                    -- null path writes nothing
  (ptr ≠ 0 →
     m_final.read64 (ptr - 32 + 8)  = 1 ∧                              -- isFree flag, full 8-byte
                                                                        -- write (M8: `write64`
                                                                        -- writes 8 bytes, not 1 —
                                                                        -- v2 pinned a single byte
                                                                        -- address, which under-
                                                                        -- states what changed and
                                                                        -- over-states the frame
                                                                        -- clause's exclusion)
     m_final.read64 (ptr - 32 + 24) = m₀.gprs .r10 ∧                    -- nextFree, same correction
     (∀ a, (a < ptr - 32 + 8 ∨ (ptr - 32 + 16 ≤ a ∧ a < ptr - 32 + 24) ∨ ptr - 32 + 32 ≤ a)
        → m_final.memory a = m₀.memory a))                             -- EVERYTHING else preserved:
                                                        -- blockSize (+0x00), alignment (+0x10), AND
                                                        -- the entire payload [ptr, ptr+blockSize) —
                                                        -- the actual frame-condition test crc32
                                                        -- cannot pose at all
```

This needs **no** assumption that `ptr` is validly-owned, currently-allocated, or anything else
about allocator state — it is true for *any* nonzero `ptr` satisfying the trivial no-wrap bound,
including a garbage pointer, because "what gets written" and "whether the write was a good idea"
are independent questions, and the frame condition only answers the first.

**(ii) The spec-refinement universalization (M6's reframing) — genuinely needs an ownership-
adjacent precondition, and surfaces a real spec/asm divergence that must be recorded, not
silently assumed away.** Universalizing `smol_free_refinement_soundness_inst` means proving, for
**arbitrary** `spec : SmolAllocState`, `p : TracedPageState`, `mach : X86_64MachineState` with
`smolAllocInvariant spec p mach = true` and `mach.gprs .rcx = ptr` for some block-owning `ptr`, that
running `smolFreeSymbolicProgram` on `mach` produces a `mach'` with `smolAllocInvariant spec' p
mach' = true` where `spec' = (free (m := SmolTracedM) ptr) spec p`'s resulting state — i.e., a real
∀-quantified version of the existing instance. **This needs a "block is currently allocated" (not
already free) hypothesis, and here is why it cannot be dropped**: `Stdlib/SmolAlloc/Spec.lean`'s
`free` (`:119-138`) guards on `s.blocks.find? (fun b => b.address == headerAddr && !b.isFree)` —
double-freeing an already-free block returns `false` and mutates nothing. **The assembly has no
such guard**: `smolFreeSymbolicProgram` unconditionally writes `isFree := 1` and
`nextFree := <current r10>` for any nonzero `rcx`, returning `1` regardless of whether the block
was already free — including re-linking an already-freed block into the freelist a second time,
which can corrupt the freelist into a cycle. **The refinement theorem is therefore only true under
a "not already free" precondition** — without it, the asm and the spec provably diverge (asm
"succeeds," spec returns `false`), and no universal refinement theorem can paper over that; it can
only be scoped around it. Record this precondition explicitly rather than assume double-free cannot
happen; do not attempt to make the refinement theorem unconditionally true, since it is not.

**Decision**: PA1 adopts (i) unconditionally (cheap, needs nothing new, tests the frame-condition
dimension §7 identifies). PA1 **also** attempts (ii) — universalizing the existing instance — as
its composability-relevant contribution, explicitly scoped to non-double-free calls, with the
double-free divergence recorded as a known, real semantic gap in `smolFreeSymbolicProgram` (a
candidate finding for whoever eventually hardens the allocator, out of PA1's own fixing scope,
analogous to §10's gunzip finding).

**Recorded per the second review's ruling: capabilities/Law-11 adoption (PA4) is NOT a prerequisite
for the frame-condition dimension (i) — it is fully statable and provable against the existing
no-fault memory model, needing only ordinary arithmetic disjointness reasoning, no permission
tokens. PA1 does not block PA4, and PA4 is not a blocker for PA1's frame-condition half.** This
directly resolves v2's own §11 Q7, which had wrongly suggested the frame-condition dimension might
not be testable before capability tokens exist — it is testable, and (i) above is exactly that
test, cheaply.

**What smolFree does NOT test, stated plainly (M8) — §9's opening claim that it "covers the
dimension §7 identifies as untested" overclaimed; it covers *statability*, not *composability*:**

- Both write addresses are `rcx - 32 + <literal>` — nothing here forces the disjointness reasoning
  a *caller* would need (e.g., proving the write doesn't clobber a *different* region the caller
  cares about that happens to overlap `[ptr-32, ptr)`); the frame condition above is a fact about
  this routine's own writes in isolation, not a composed fact against an arbitrary caller's memory
  layout.
- No write address depends on loop-carried state — `MODEL_DEBT.md` B3's actual named bug class
  (a hand-computed offset that drifts across loop iterations, as in `gzipCompressSymbolicProgram`'s
  header-writing loop or its Dynamic-Huffman scratch region, §7) is still completely untested by
  either routine in PA1's scope now.
- Being a leaf, `smolFree` cannot test **composition** of frame conditions across a call boundary —
  exactly `docs/VISION.md` §4's actual central claim (capability tokens double as frame conditions
  *that compose*). PA1, even with both routines, tests that two different routines can each *state*
  a frame condition; it does not test that two routines' frame conditions *combine* correctly when
  one calls the other. That remains squarely PA2/PA4 territory.

## 10. Out-of-Scope Finding, Flagged for Filing (Not Fixed Here)

`Windows.lean:2210-2219` (`gunzipStreamSymbolicProgram`'s decompression path, `label
"decompress_finish"`, under the comment header "Finish & CRC Calculation"): sets up `rcx`/`rdx`,
calls `zlib_crc32`, and **immediately** executes `xor_r32 .eax .eax`, discarding the computed CRC
and returning hardcoded success (`RAX = 0`) unconditionally. **The gzip trailer CRC is computed
and then thrown away — it is never compared against the trailer's stored CRC, so decompression
never verifies stream integrity.** This is a Law 8 facade (a section captioned "CRC Calculation"
that computes a value used for nothing) and is structurally invisible to a Python-oracle
differential fuzzer (a corrupted-CRC input still decompresses to the correct plaintext, since the
plaintext decoding is independent of the trailer check that never happens). This is out of PA1's
scope (a decompression-correctness defect, not a `crc32SymbolicProgram` contract question) — noted
here per the review's instruction so the coordinator can file it, not fixed as part of this design.

## 11. Design-Review Questions (Revised again, v3)

Several questions from earlier revisions are now resolved; recorded here as resolved, alongside
genuinely open ones. Items 1-6 are v1's, carried forward; item 7 is corrected per M7; items 10-12
are new in v3.

1. ~~Is Theorem 3's memory-safety claim honest given MODEL_DEBT B3?~~ **Resolved (§2.5, M5[v2])**:
   renamed to two constructive theorems that do not claim more than is proven.
2. ~~Does the connection theorem close by unfolding both sides?~~ **Resolved (§3.6, M1[v2])**: no;
   the `bv_decide`-on-branch-free-normal-form route is adopted and verified working (and its own
   tactic script needed one further correction — M9(a) — recorded in §3.6).
3. ~~Does the invariant survive the table-free bitwise formulation / the `Id.run` structure?~~
   **Resolved as "no, not without the fold-reformulation first" (§3.8, M3[v2])**: the
   reformulation must precede stating the invariant, and is itself a second connection theorem —
   and per M2 (v3), the invariant itself is now actually written down, in §4.0.
4. ~~Is `len < 2^63` the right precondition, or does it mask an assembly bug?~~ **Resolved
   (§8(a))**: it masked a real, systemic defect; fixed by an unsigned-compare substitution, and
   the precondition is removed entirely.
5. ~~Does the RAX-upper-bits behavior constitute a genuine ABI defect?~~ **Resolved (§8(b))**: yes
   — and per M5 (v3, correcting v2), the fix needs **no** new DSL instruction; two already-
   registered instructions (`mov_r32`, `xor_r32`) suffice.
6. ~~Should `VerifiedRoutine` be instantiated or redesigned now?~~ **Resolved (§4.3, M11[v2])**:
   neither — prove the three theorems directly; both mismatches (step-ratio, `Bool`-vs-`Prop`) are
   findings for PA2, not blockers for PA1. **Corrected per M6 (v3)**: the `Bool`-valued mismatch is
   about *this contract's* invariant shape specifically (its `∀ a, memory a = ...` conjunct), not a
   blanket claim that `Bool`-valued coupling invariants never work — `smolAllocInvariant` (§9) is
   exactly one, already in use, for a finitely-quantified invariant shape.
7. ~~Is the ownership precondition an acceptable stand-in for a capability token, or does it defer
   the frame-condition dimension until PA4?~~ **Resolved and corrected (§9.1, M7)**: the question's
   premise was wrong — the frame condition needs no ownership precondition at all (both write
   addresses derive syntactically from `rcx`); ownership is needed only for the separate spec-
   refinement universalization (§9.1(ii)), which is scoped around the double-free divergence rather
   than blocked by it. **Capabilities/PA4 are not a prerequisite for the frame-condition dimension,
   and PA1 does not block PA4** — recorded per the review's explicit ruling.

**New, genuinely open (v3):**

8. **Does the decode-lemma set (§3.8) actually keep the per-iteration proof cost bounded in
   practice**, or does proving 62 individual `instructionAtRip` facts (even though each is
   individually cheap) introduce enough elaboration overhead of its own that the net win over the
   naive re-walk is smaller than §3.3's (twice-corrected) estimate suggests? This is an empirical
   question the implementer should measure, not assume.
9. **Is the `bv_decide` allowlist policy (§3.6-policy) actually going to be accepted at review
   time**, or does "a SAT certificate is not sampling" need a firmer citation/precedent than this
   design provides before a reviewer signs off on the first `bv_decide` occurrence in the tree's
   allowlist? Flagging this as a question rather than treating §3.6-policy's ruling as
   self-evidently final, since it is a policy call, not a mechanical check.
10. **Is the "not already free" precondition scoping §9.1(ii)'s refinement universalization to
    exclude double-free acceptable, or should PA1 instead treat the double-free divergence itself
    (asm silently "succeeds" and can corrupt the freelist into a cycle; spec correctly rejects it)
    as a defect to fix before proving anything** — analogous to §8's two assembly-defect fixes?
    This design chose "scope around it, record it, don't fix it" (closer to §10's gunzip-CRC
    treatment than §8's) on the grounds that a bump allocator silently tolerating double-free is a
    plausible intentional simplification rather than an obvious defect the way a wrong comparison
    instruction is — but that judgment call is exactly what a reviewer should re-examine, not
    accept on this design's say-so.
11. **Given how much of this round's findings were "an artifact was referenced but never written"
    (M2, and v1's `updateCrc32Internal` before it) or "a replacement count was itself wrong" (M4,
    on the exact item the previous review made mandatory) — is there a process gap here worth
    naming as its own finding**, independent of any individual mistake: revising a design document
    under review pressure seems to reliably introduce a *new* instance of the same failure class
    the review just caught (forward references to unwritten content; approximate counts presented
    as corrected-and-precise). Whether that pattern is specific to this document or general enough
    to warrant its own process gate (e.g., a mechanical check that every section reference resolves
    to actual content, or a policy of never stating a tree-wide count without pasting the exact
    command used to produce it) is worth surfacing to whoever reviews PA2's own design doc, since
    the same pressure will recur there.
