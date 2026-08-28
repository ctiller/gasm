---
id: MEM-COST
title: X86_64Memory closure-chain cost curve — independent measurement and carrier-change assessment
status: done
blocked_on: ""
after: []
related: [TRUST-FINDINGS, MH1]
bar: ""
track: proof-arch
priority: 7.0
priority_set: 2026-08-28T00:00:00Z
design: ""
design_review: ""
date: 2026-08-28
---

# X86_64Memory closure-chain cost curve — independent measurement record

Measured 2026-08-28 against local `main` @ `d313251` (allowlist baseline **73** entries:
44 `axiom-only` + 29 `grandfathered`; `origin/main` reads 79). Toolchain `leanprover/lean4:v4.33.1`,
no Mathlib. **No source file was modified to produce any of this data.**

## Method, and why wall-clock was discarded

First attempt used wall-clock. It produced an impossible curve (`d1_50` 12.9s > `d1_100` 11.7s >
`d1_200` 8.0s > `d1_400` 6.1s — monotonically *decreasing* in problem size). Cause: 6+ concurrent
`lean.exe` processes from other agents' worktrees (`integration-land`, plus another agent's
`s3win_canonical__kdecide.lean` probes). This is the same failure mode as the previously reported
"fuel 880 faster than fuel 440".

All numbers below are therefore **process CPU time** (`Start-Process -PassThru`,
`TotalProcessorTime`), not wall-clock. CPU time is largely but not wholly contention-independent:
re-running the same P2 files while three of my own jobs ran inflated them ~1.7x (`p2_400`
14.72s → 25.17s). Comparisons within a single sweep are sound; across sweeps, treat as ±2x.

Every probe was checked non-vacuous with a negative control (a false variant must be *rejected*):

- `(readByte (chain 1600) 3 == 7) = true` → "Tactic `decide` proved that the proposition … is false" ✓
- `(asmAt == []) = true` on the real Spike 2 trace → rejected ✓

Baselines to subtract: probe files importing only `MemoryCell` ≈ **1.7–2.7s**; files importing
`Spikes.Spike2Fibonacci.Windows.Equivalence` ≈ **7.27s**.

## 1. Where the cost sits: 100% kernel

`set_option profiler true` on the N=400 two-dimensional probe:

```
elaboration took                                   9.06ms
tactic execution of Lean.Parser.Tactic.decide took   11ms
type checking took                                  76.4s
```

The cost is **kernel type-checking of the proof term**. Not elaboration, not `simp`, not the
`decide` tactic. Corollary: no simp set, `@[simp]` normal form, or `writeBytes`-collapsing lemma
can touch it — those run in the elaborator, which is already spending 9ms. Candidate direction A
is dead **for `decide`-shaped proofs** by construction.

Related: plain `decide` costs 51.27s where `decide +kernel` costs 14.72s at N=400 — the
elaborator path does the reduction twice.

## 2. Chain *depth* alone is nearly free (P1)

N writes at distinct literal addresses, then **one** read at an unwritten address:

| N (chain depth) | cpu | net |
|---|---|---|
| 200 | 2.20s | ~0 |
| 800 | 2.36s | ~0.2s |
| 3200 | 2.89s | ~0.7s |

Linear, ≈0.2ms per layer traversed. **A single read down a 3200-layer closure chain is
essentially free.** The "every byte read walks the chain" mechanism is real but is not by itself
the cost.

## 3. Address-dependent writes are NOT a factor (D1 vs L1)

Hypothesis tested: in a real trace the write *address* is computed from registers that may
themselves come from memory reads, so each layer's `if addr == a` guard could force a nested
chain walk and re-reduce on every traversal (which would give the observed cubic).

`chainD` (write address = `(readByte m 0).toUInt64 + n*8 + 1`, forcing a walk to the bottom of the
chain to resolve each guard) vs `chainL` (literal address), one read:

| N | chainD | chainL |
|---|---|---|
| 50 | 1.66s | 1.73s |
| 100 | 1.77s | 1.75s |
| 200 | 1.92s | 1.67s |
| 400 | 1.97s | — |
| 800 | 2.39s | — |

Indistinguishable and flat. The kernel's whnf cache handles the shared subterms.
**Hypothesis refuted** — the cost is not address-dependence.

## 4. The cost is reads × depth, and it breaks upward (P2)

N writes at distinct addresses, then N reads (each read walking to its own layer):

| N | cpu | net | ratio |
|---|---|---|---|
| 100 | 2.34s | 0.6s | — |
| 200 | 4.69s | 3.0s | 5.0 |
| 400 | 14.72s | 13.0s | 4.3 |
| 800 | 129.11s | 127s | **9.8** |

Quadratic (ratio ~4.3, exponent ~2.1) through N=400, then **breaks upward to ratio 9.8
(exponent ~3.3) between 400 and 800.**

## 5. The break reproduces on the real trace

Spike 2 Windows, `decide +kernel` on `(asmAt == asmAt)` where
`asmAt = runAsmTrace spike2Instructions spike2Executable.load <fuel>`. Baseline 7.27s subtracted:

| fuel | cpu | net | ratio |
|---|---|---|---|
| 55 | 18.81s | 11.5s | — |
| 110 | 27.50s | 20.2s | 1.75 |
| 220 | 182.94s | 175.7s | **8.69** |

Same signature. The break lands one step earlier than the previously reported wall-clock table
(which put it at fuel 440, ratio 8.19), consistent with my run being more contended.

**The two break points coincide in chain depth.** At ~30 layers per loop iteration, fuel 220 is
roughly 700–800 accumulated layers — the same place the isolated memory probe (§4) breaks.
This is the evidence that the minimal probe reproduces the real system's pathology, i.e. that the
memory chain is the cause rather than something co-varying with it.

Mechanism of the break itself is **unconfirmed**. The leading hypothesis is kernel whnf-cache /
GC pressure from the O(N²) distinct retained subterms. `PeakWorkingSet64` read after process exit
returned 0, so peak-memory evidence was not obtained.

## 6. Prototype replacement carrier, measured

`initRegion : (Address → Byte) → X86_64Memory` accepts an arbitrary total function (loaders
install a computed image), so a finite map **cannot** replace the carrier — it can only be put in
front of a retained base function. Prototype: `{ base : Address → Byte, ov : Ovl }` where `Ovl` is
a 64-deep bitwise trie on the address; reads are O(64) independent of write count.

| N | trie | closure (§4) |
|---|---|---|
| 100 | 10.98s | 2.34s |
| 200 | 9.44s | 4.69s |
| 400 | 15.08s | 14.72s |
| 800 | 32.25s | 129.11s |

Trie is **linear, with no break**, but carries a much larger per-operation constant: it is ~13x
slower at N=100. **Crossover ≈ N 300–400**; 4x faster at N=800, and the gap widens past the break.
Same-contention-window comparison: `tr_400` 15.08s vs `p2_400` 25.17s.

Read this as an argument in both directions: it would speed up the handful of long traces and slow
down the many short proofs (RoundtripGate, MemoryFrame, LoopInvariant step lemmas), which all sit
far below the crossover.

## 7. Representation surface (what a carrier change would touch)

- `X86_64Memory` is named in only **5 files** outside `MemoryCell.lean`: `MemoryFrameAudit.lean`
  (7), `Memory.lean` (4), `Registers.lean` (2), `Stdlib/SmolAlloc/Equivalence.lean` (1),
  `Spike3SortLines/Windows/InstructionStepLemmas.lean` (1).
- **14 sites unfold the representation** (`X86_64Mem.write`/`writeByte` inside `simp`/`simp only`
  lists, then discharge the exposed `if`-chain with `simp [Ne.symm h…]`): `MemoryFrame/Mov.lean`
  (8), `Call.lean` (2), `Memory.lean` (2), `Push.lean` (1), `NegativeControl.lean` (1).
  These are the proofs that would need re-proving against trie lemmas.
- `Tools/` has **zero** references to `X86_64Memory`/`X86_64Mem.` — MH1/MH2/MH3, `memAccesses`,
  `MemRef` and `CheckX86Obligations.lean` depend on the *descriptor vocabulary and API*, not the
  carrier. (`CheckedAsm.lean` does not exist in this worktree.)
- **No `funext` on memory anywhere in the tree.** The premise that the closure buys free
  extensionality is not currently exercised: every frame obligation is stated pointwise through
  the API (`X86_64Mem.read .w8 a m1 = X86_64Mem.read .w8 a m2`), and there is no `DecidableEq`/
  `BEq` instance on `X86_64Memory` — memories are only ever *evaluated*, never compared.
- The seal survives either way: a two-field structure still takes `private mk ::`, and the
  `MemoryFrameAudit.lean` eliminator lint is unaffected. It remains **tier 3** (`casesOn`
  representable and audited, not unrepresentable).

What the closure genuinely buys, and a trie would lose: read-over-write and disjointness at a
*symbolic* address are one-line `simp` steps on an `if` (`readByte_writeByte_same/_diff`,
`readByte_write_disjoint`). Against a trie each becomes an induction over the 64 trie levels plus
a "distinct addresses ⇒ distinct bit-paths" injectivity lemma. Bounded and provable once, but it
is real work, and `docs/MEMORY_HOOK.md` §7 makes `rfl`-preservation an explicit design commitment
(§7 line 614 warns that an incomplete lemma set makes `rfl`/`simp` proofs "stall against the extra
layer").

## 8. Probe sources

Standalone files, run via `lean` with `LEAN_PATH` from `lake env`; deliberately **not** committed
as `.lean` files in-tree so they cannot enter anyone's build.

```lean
-- §2/§4 closure probe (P1 reads once; P2 reads N times)
def chain : Nat -> X86_64Memory
  | 0 => zero
  | n+1 => writeByte (chain n) (n.toUInt64 * 8) (n.toUInt8)

def allOk : Nat -> X86_64Memory -> Bool
  | 0, _ => true
  | k+1, m => (readByte m (k.toUInt64 * 8) == k.toUInt8) && allOk k m

theorem p1 : (readByte (chain N) 3 == 0) = true := by decide +kernel   -- one read
theorem p2 : allOk N (chain N) = true := by decide +kernel             -- N reads
```

```lean
-- §3 address-dependence probe: chainD's guard needs a walk to the chain bottom to resolve.
-- readByte m 0 is always 0 (address 0 is never written), so chainD n and chainL n hold the
-- same bytes at the same addresses.
def chainD : Nat -> X86_64Memory
  | 0 => zero
  | n+1 => let m := chainD n
           writeByte m ((readByte m 0).toUInt64 + n.toUInt64 * 8 + 1) (n.toUInt8)
```

```lean
-- §6 prototype carrier
inductive Ovl | empty | val (v : UInt8) | node (l r : Ovl)

def Ovl.ins : Nat -> UInt64 -> UInt8 -> Ovl -> Ovl
  | 0, _, v, _ => .val v
  | d+1, a, v, t =>
      let (l, r) := match t with | .node l r => (l, r) | _ => (Ovl.empty, Ovl.empty)
      if (a >>> d.toUInt64) &&& 1 == 1 then .node l (Ovl.ins d a v r)
      else .node (Ovl.ins d a v l) r

structure HMem where
  base : Address -> Byte
  ov   : Ovl
```

```lean
-- §5 real-trace probe
def asmAt : List AnyEvent :=
  runAsmTrace (Event := AnyEvent) spike2Instructions spike2Executable.load <FUEL>
theorem probe : (asmAt == asmAt) = true := by decide +kernel
```

## 9. Measured vs inferred

**Measured**: everything in §1–§6, and the file/site counts in §7.

**Inferred, not measured**: the mechanism of the upward break (whnf-cache/GC pressure);
the extrapolation of the trie's linear fit past N=800; the claim that a trie's frame-lemma
re-proofs are "bounded" (the lemmas were not attempted); and the extrapolated full-trace cost for
Spike 2 (~15,500 fuel) under either carrier.
