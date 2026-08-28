# TRUST_PLAN F1 — obstruction census for the 18 never-measured `grandfathered` entries

**Status**: measurement complete, 2026-08-28. **This is measurement, not proof work.** No proof
was attempted, no oracle substituted, and `scripts/gate_allowlist.txt` was not edited: **no entry
added, removed, or re-categorised by this task.**

## Baseline — state it, because three coexist

| baseline | `grandfathered` | `axiom-only` | total | all 18 targets still listed? |
|---|---|---|---|---|
| `origin/main` (`38eff9b`) | 34 | 45 | **79** | **yes — all 18** |
| local `main` (`d313251`, unpushed) | 29 | 44 | 73 | 13 of 18 |
| `964c1b5` (this task's dispatch) | 34 | 44 | 78 | yes |

**Measured against `origin/main`.** Runs executed in a worktree at local `main` (`d313251`);
`git diff --stat origin/main d313251` over `Stdlib/Zlib/Deflate.lean`, `Huffman.lean`, `Gzip.lean`,
`Stdlib/Png/`, `Spikes/Spike2Fibonacci/`, `Spikes/Spike3SortLines/`, `Gasm/Effects/`,
`Gasm/Targets/X86_64/Semantics.lean`, `Gasm/Targets/WASI/`, `Gasm/Targets/Wasm/` is **empty** —
every function the 18 statements reduce over is byte-identical, so the measurements apply to
`origin/main`. The local tree differs only in which theorems and allowlist lines exist.

## Method, and why `decide +kernel` is the load-bearing number

Each entry's exact proposition was restated in a scratch module outside the repo tree and
discharged with `decide` and with `decide +kernel` under `maxRecDepth 10000000`,
`maxHeartbeats 0`. Sub-terms were bisected to find the first irreducible head, and each theorem
statement's constant closure was walked transitively (`Expr.getUsedConstants`) to name blockers by
fully-qualified constant rather than infer them from source text.

**Plain `decide` is unreliable here and its "stuck" verdicts must not be trusted.** It reduces
through the *elaborator's* `whnf`, which reports "stuck" on `Nat.brecOn`-compiled matcher
applications the kernel handles — the incompleteness `Spikes/Spike1Hello/Wasm/Equivalence.lean`
already documents. Measured counterexample: `flushBitWriter (writeBits {} 3 3)` is *stuck* for
`decide` and *succeeds* for `decide +kernel`. Every verdict below is the `+kernel` verdict.

**Discarded data.** A concurrent agent ran `taskkill //F //IM lean.exe` machine-wide, and this
machine's Cygwin `fork` failed repeatedly under load, killing three background runners mid-pass.
Any run that exited non-zero with **zero diagnostic bytes** was discarded and re-run, not
recorded. One earlier reading (Spike 3 Windows canonical, "461 s, exit 1, empty output") was
discarded on exactly this test. Every "stuck" below is backed by a real Lean diagnostic; every
"timeout" is backed by a full time-box elapsing.

## Results — all 18

No entry closed. **0 of 18 succeeded**, so nothing was retirable and nothing was retired.

| # | entry | `decide` | `decide +kernel` | class | blocking construct | domain |
|---|---|---|---|---|---|---|
| 1 | Zlib `deflate_roundtrip_empty_inst` | stuck 22.1 s | **stuck 24.1 s** | stuck | W3 + W2 | sampled pointwise |
| 2 | Zlib `deflate_roundtrip_soundness_inst` | stuck 3.0 s | **stuck 23.4 s** | stuck | W3 + W2 | sampled pointwise |
| 3 | Zlib `deflate_roundtrip_repetitive_inst` | stuck 2.7 s | **stuck 17.8 s** | stuck | W3 + W2 | sampled pointwise |
| 4 | Zlib `zlib_roundtrip_soundness_inst` | stuck 9.5 s | **stuck 21.7 s** | stuck | W3 + W2 | sampled pointwise |
| 5 | Zlib `gzip_roundtrip_soundness_inst` | stuck 2.4 s | **stuck 6.5 s** | stuck | **W2 only** | sampled pointwise |
| 6 | Zlib `deflate_idempotent_canonical_roundtrip_inst` | stuck 2.3 s | **stuck 41.8 s** | stuck | W3 + W2 | sampled pointwise |
| 7 | Zlib `zlib_idempotent_canonical_roundtrip_inst` | stuck 4.0 s | **stuck 16.5 s** | stuck | W3 + W2 | sampled pointwise |
| 8 | Zlib `gzip_idempotent_canonical_roundtrip_inst` | stuck 2.4 s | **stuck 3.0 s** | stuck | **W2 only** | sampled pointwise |
| 9 | PNG `png_roundtrip_soundness_inst` | stuck 2.4 s | **stuck 14.8 s** | stuck | W3 + W2 | sampled pointwise |
| 10 | PNG `png_idempotent_canonical_roundtrip_inst` | stuck 2.4 s | **stuck 26.1 s** | stuck | W3 + W2 | sampled pointwise |
| 11 | Spike 3 Win `spike3_canonical_effect_trace_equivalence_inst` | t/o 99 s | **stuck** (3.6 s isolated) | stuck | W4 | sampled pointwise |
| 12 | Spike 3 Win `spike3_empty_effect_trace_equivalence_inst` | t/o 61 s | **stuck** (isolated) | stuck | W4 | sampled pointwise |
| 13 | Spike 3 Lin `spike3_canonical_effect_trace_equivalence_inst` | t/o 60 s | **stuck** (4.4 s isolated) | stuck | W4 | sampled pointwise |
| 14 | Spike 3 Lin `spike3_empty_effect_trace_equivalence_inst` | t/o 67 s | **stuck 122.8 s** (whole) | stuck | W4 | sampled pointwise |
| 15 | Spike 3 Wasm `spike3_wasm_canonical_effect_trace_equivalence` | stuck 4.4 s (elab) | **timeout 570 s** | timeout | none found | sampled pointwise |
| 16 | Spike 2 Win `spike2_canonical_effect_trace_equivalence` | stuck 31 s (elab) | **timeout 560 s** | timeout | none found | complete-domain pointwise |
| 17 | Spike 2 Lin `spike2_canonical_effect_trace_equivalence` | stuck 34 s (elab) | **timeout 60 s** | timeout | none found | complete-domain pointwise |
| 18 | Spike 2 Wasm `spike2_wasm_canonical_effect_trace_equivalence` | t/o 62 s | **timeout 915 s** | timeout | none found | complete-domain pointwise |

Entries 11–14: the whole-theorem run exhausts its budget on the enormous *assembly* side before
reaching the model side, so the whole-theorem number is a timeout. The **verdict is stuck**, from
isolated model-side probes on the current build (below), which fail in seconds. Entry 14 reached
the categorical verdict on the whole theorem in 122.8 s.

### Isolation probes that produced the verdicts (current main, `decide +kernel`)

| probe | result |
|---|---|
| `compressFixed "abcabcabc".toUTF8` | **reduces**, 2.9 s |
| `gzipCompress <literal>` | **reduces**, 11.1 s |
| `zlibCompress <literal>` | **stuck**, 34.2 s (W3) |
| `encodeImageRGBA8 sample2x2Image` | **stuck**, 17.4 s (W3) |
| `decompress (ByteArray.mk #[3,0])` (shortest valid stream) | **stuck** (W2) |
| `[3,1,2].mergeSort (· ≤ ·) == [1,2,3]` | **stuck**, 2.9 s (`decide` 6.0 s) — Lean *core* |
| Spike 3 Win `modelTraceCanonical.length == 7` | **stuck**, 3.6 s (W4) |
| Spike 3 Lin `modelTraceCanonical.length == 7` | **stuck**, 4.4 s (W4) |
| `#print Spikes.Spike3SortLines.readAllLines` | `opaque …` (W4) |
| `tokenize ByteArray.empty`; `emitFixedBlock #[]`; `buildHuffmanTable` (288 syms); `writeBits` | all **reduce** (11.1 / 20.3 / 18.1 / 7.9 s) |
| `spike3Instructions.length == 350` | **reduces**, 11.0 s — the assembler/linker is not a blocker |

## The walls, as they stand on `origin/main`

### W1 — `Lean.Loop.forIn` → `repeatM` → opaque `_private.Init.While.0.repeatM.impl`

**Gone from Zlib.** The `findLongestMatch` and `compressFixed` fuel conversions
(`matchScan`/`matchExtend`, `compressFixedLoop`) removed it; measured above — both now reduce.
This was the wall TRUST_PLAN recorded for Spike 5, and its irreducible core has a name: an
`opaque` constant in Lean's `Init.While`, reached via `Lean.Loop.forIn → repeatM`.

### W2 — `Stdlib.Zlib.decodeHuffmanSymbol.step` (well-founded → `Acc.rec`)

```
decompress -> decompress.go -> decompress.go._unary -> decodeHuffmanStream
  -> decodeHuffmanStream.go -> decodeHuffmanStream.go._unary
  -> decodeHuffmanSymbol -> decodeHuffmanSymbol.step -> decodeHuffmanSymbol.step._unary
  -> WellFounded.fix -> WellFounded.fixF -> Acc.rec
```

**Refines the plan's Wall 2.** `decompress.go._unary` and `decodeHuffmanStream.go._unary` do *not*
use `WellFounded.fix` — they are structural. The single well-founded node is
**`decodeHuffmanSymbol.step`**. Converting `decompress`/`decodeHuffmanStream` without it would not
move the wall. A2 should name it.

### W3 — `List.mergeSort` inside `packageMergeLengths` — **not in TRUST_PLAN**

```
compress -> compressPlan -> buildDynPlan -> packageMergeLengths
  -> List.mergeSort -> List.mergeSort._unary -> List.merge -> List.merge._unary
  -> WellFounded.fix -> WellFounded.fixF -> Acc.rec
```

`Stdlib/Zlib/Deflate.lean:1108` sorts Huffman leaves with `List.mergeSort`; Lean core's
`List.merge` is well-founded, so a 3-element `mergeSort` is itself stuck under both tactics. No
project code is involved in the irreducible step. `compressPlan` forces `buildDynPlan`
unconditionally (the fixed/dynamic bit-cost comparison needs it), so **every `compress` /
`zlibCompress` call is blocked regardless of input**. `gzipCompress` escapes only because it
routes through `compressFixed`, which never builds a dynamic plan — the same `compressFixed` /
`compress` split the plan flags as a Law 12 unlinked twin, reappearing as a difference in *which
wall* each side hits.

### W4 — `partial def Spikes.Spike3SortLines.readAllLines` — **not in TRUST_PLAN**

`Spikes/Spike3SortLines/Spec.lean:75` is still `partial def` on `origin/main`, and `#print`
confirms `opaque Spikes.Spike3SortLines.readAllLines : …`. `sortLinesSpec` binds it as its first
action, so the model side of all four Spike 3 x86 entries is irreducible in ~4 s, before the
assembly side is consulted.

**W4 blocks rung 1 as well as rung 2.** A `partial def` has no defining equations of any kind, so
there is no lemma to state about `readAllLines`' unfolding and nothing for `simp`/`rw`/`unfold` to
use. Unlike W1–W3, no proof of any kind can relate `runModelTrace sortLinesSpec` to a concrete
trace while it stays `partial`. That makes it a hard prerequisite for Track C1/C2, not an
optimisation. (An unpushed working copy in the main checkout is converting it to
`readAllLinesFueled`; that had not reached `origin/main` when this was measured.)

**Track C as written attacks the wrong half.** C1/C2 propose hand-tracing ~96 instructions of
register/stack state — the *assembly* side, which measurably is not the obstruction
(`spike3Instructions.length` reduces in 11 s). Spike 1's spec contains no `partial def`, which is
exactly why `Spikes/Spike1Hello/Windows/Equivalence.lean` closes with plain `decide` and no
allowlist entry.

## Pointwise vs universal — the distinction the score cannot see

**All 18 statements are pointwise.** None quantifies over its real input domain. But "pointwise"
is only a defect when the real domain is larger, and that splits the 18 three ways:

- **Sampled pointwise — 15 entries** (Zlib 8, PNG 2, Spike 3 5). The real domain is
  `∀ data : ByteArray` / `∀ stdin : ByteArray`; the statement covers one literal. A `decide` that
  closed one of these would delete its ledger entry while leaving the Law 9 gap exactly where it
  was. PA17 already documents the `∀ b : Bool` wrapper over Spike 3 as a two-element proxy, not
  the stdin domain.
- **Complete-domain pointwise — 3 entries** (Spike 2 ×3). These programs take no input, so the
  single ground instance *is* the whole domain. A `decide` here would be a legitimate Law 10 rung-2
  discharge, not scoring — the same standing Spike 1 has. Spike 2's residual problem is Law 8/12,
  not Law 9.

**Both patterns are live in the tree right now, and they look identical in the count.** The
unpushed local `main` retires five entries; measured, they are opposite in kind:

- The **four `deflate_*_inst` retirements** deleted the pointwise theorems outright and rest on
  `deflate_roundtrip_soundness (data : ByteArray) : decompress (compress data) = .ok data`
  (`Stdlib/Zlib/DynamicRoundtrip.lean:1457`) — genuinely universal and unconditional. The
  obligation was **fixed**; the count moving is a true signal.
- The **`spike3_empty_effect_trace_equivalence_inst` retirement** changes `native_decide` to
  `decide +kernel` on a single-vector statement that is otherwise unchanged. Domain, statement and
  Law 9 violation are identical before and after. The count moved; **nothing was fixed.**

The ledger records both as "−1". Only the domain column distinguishes them, which is why it
belongs in the ledger rather than in a report. *(Note in passing: in local `main` `d313251` the
allowlist deletion for `spike3_empty_effect_trace_equivalence_inst` is committed while the source
still reads `native_decide` — a `native_decide` with no authorising entry. Presumably transient
mid-task state, flagged so it is not lost.)*

## The propagation claim — tested in both directions, and it is half true

Measured with `Lean.collectAxioms` (the `#print axioms` machinery `Tools/CheckGatesAxioms.lean`
uses) over **all 78** entries of the `964c1b5` allowlist via 31 per-module probes, matching each
`axiom-only` entry's non-standard axioms against the `<root>._native.native_decide.ax_*` axioms
owned by the 34 `grandfathered` roots. `origin/main` adds one entry
(`spike4_linux_trace_equivalence_for_request`), a PA17-shaped wrapper identical in form to its
already-measured Windows and Wasm siblings.

**Direction 1 — "every `axiom-only` entry is propagation from a `grandfathered` root": TRUE.**
Zero orphans across all 44. No `axiom-only` entry needs a step of its own; none is missing from the
plan.

**Direction 2 — "retiring a `grandfathered` root cascades": FALSE for 12 of 34 roots**, which have
no dependents at all and retire only themselves:

- all 8 `Stdlib/Zlib/Equivalence.lean` roots
- both `Stdlib/Png/Equivalence.lean` roots
- Spike 5's `gzip_roundtrip_soundness_inst` and `gzip_idempotent_canonical_roundtrip_inst`

Spike 5's 11 `axiom-only` entries all cite its five *trace equivalences*; none cites either `_inst`
roundtrip. That is the counterexample flagged to this task, confirmed by measurement.

A second qualification: **an `axiom-only` entry retires only when *every* root it cites retires.**
Ten entries cite more than one. `Spikes/Spike4HttpServer/Test.lean::main` cites all nine Spike 4
roots; `Spikes/Spike5Gzip/Test.lean::main` cites four of Spike 5's; each Spike 3 `Emit.lean::main`,
`Test.lean::main`, `runTests` and `spike3VerifiedProgram` cites both of its target's roots.

**Empirical confirmation, from the tree itself**: the five retirements in local `main` cascaded to
**zero** `axiom-only` retirements — that count is unchanged at 44. Four of the five roots had no
dependents; the fifth (Spike 3 Windows empty) has five, but each of them also cites the *canonical*
root, which is still open.

### Corrected cascade totals (78 baseline; all 78 accounted for)

| track | roots | distinct `axiom-only` dependents | total gated | TRUST_PLAN estimate |
|---|---|---|---|---|
| Spike 4 | 9 | 12 | **21** | ~21 ✓ |
| Spike 5 | 7 | 11 | **18** | ~18 ✓ |
| Spike 3 | 5 | 13 | **18** | ~16 (undercount) |
| Spike 2 | 3 | 8 | **11** | ~6 (undercount) |
| Zlib | 8 | 0 | **8** | 8 ✓ |
| PNG | 2 | 0 | **2** | 2 ✓ |
| **total** | **34** | **44** | **78** | 78 ✓ |

The Spike 3 and Spike 2 undercounts come from the plan's per-file table counting only
`Equivalence.lean`; the `Emit.lean` / `Test.lean` `main` and `runTests` entries (TC15's findings)
belong to the same roots. **The 18 entries measured here gate 39 of the 78** (18 roots + 21
propagated).

## What this decides

- **Nothing in the 18 is research.** Every wall has a named, precedented fix: fuel conversion for
  W2/W4 (precedented three times — `tokenizeAux`'s own comment, `ccba443` for the Wasm interpreter,
  and now `findLongestMatch`/`compressFixed` themselves), and for W3 either a kernel-reducible sort
  or hoisting `buildDynPlan` behind the fixed/dynamic decision. What the measurement changes is the
  *dependency graph*, not the difficulty class.
- **The two cheapest entries in the whole ledger are `gzip_roundtrip_soundness_inst` and
  `gzip_idempotent_canonical_roundtrip_inst`.** Their sole remaining blocker is W2: measured,
  `gzipCompress` now reduces in 11.1 s and only the decompress side is stuck. **A2 alone puts both
  within reach of `decide +kernel`** — no other work needed. This corrects the standing guidance
  that PNG is the best harvest candidate: PNG needs **both** W2 and W3, because
  `encodeImageRGBA8 → zlibCompress → compress → buildDynPlan` is stuck (17.4 s, measured), so
  `filter_unfilter_soundness` cannot reach it while W3 stands.
- **Track E's dependency list is incomplete.** E4/E5 need A2 (W2) *and a new step for W3*. E5's
  "status unestablished" is now established: PNG is blocked identically to Zlib, through
  `zlibCompress`/`zlibDecompress`. `Stdlib/Png/`'s own filter algebra is not the obstruction, and
  `parsePngChunks` is structural, not well-founded — verified, not assumed.
- **Track C needs a W4 prerequisite before C1/C2 mean anything.** C3 (Wasm) is the only Spike 3
  entry with no categorical blocker; it is a 570 s timeout.
- **Track D is a design question and larger than stated.** No Spike 2 entry is categorically
  blocked — all three are timeouts. The Law 8 facade is **Wasm-only** (`_start` calls `fd_write`
  and `proc_exit` over a compile-time `spike2DataSegments`, never the exported `fibIter`); the x86
  programs compute the recurrence at runtime in `r14`/`r15`
  (`Spikes/Spike2Fibonacci/Windows/Program.lean:176-180`) but re-implement it inline rather than
  calling the verified `fibIterInstructions`, which `linkWindowsProgram spike2SymbolicProgram []`
  does not even link in — a Law 12 unlinked twin, so `fib_iter_asm_soundness` verifies a routine
  that ships in no executable. D2's figure should read **3 + 8 propagated = 11**, not 3 + 3.

## Suggested plan amendments

1. **New step (Track E)**: remove W3 — replace `List.mergeSort` in
   `Stdlib.Zlib.packageMergeLengths` (`Stdlib/Zlib/Deflate.lean:1108`) with a kernel-reducible
   sort, or hoist `buildDynPlan` behind the fixed/dynamic decision. Gates 8 of the 10 codec
   entries. The plan has no step for this.
2. **New step (Track C prerequisite)**: convert `partial def readAllLines`
   (`Spikes/Spike3SortLines/Spec.lean:75`) to structural recursion. Gates the model side of all
   four Spike 3 x86 entries, for rung 1 as much as rung 2. In flight, unpushed.
3. **Rename A2's target** to `Stdlib.Zlib.decodeHuffmanSymbol.step`; `decodeHuffmanStream` and
   `decompress` are already structural. Sequence A2 first — it is the only blocker on two entries.
4. **Correct the cascade arithmetic**: Spike 3 gates 18 (not ~16), Spike 2 gates 11 (not ~6); and
   12 of 34 roots gate nothing but themselves.
5. **Add a domain column to `scripts/gate_allowlist.txt`** (`sampled-pointwise` /
   `complete-domain` / `universal`). Without it the ledger cannot distinguish a retirement that
   fixed the obligation from one that only changed the tactic, and both shapes are in the tree
   today.
