---
id: TRUST-FINDINGS
title: Trust session findings index — measured obstructions, propagation limits, and the proxy-metric finding
status: done
blocked_on: ""
after: []
related: [TRUST-F1, MEM-COST]
bar: ""
track: trust-core
priority: 8.0
priority_set: 2026-08-28T00:00:00Z
design: ""
design_review: ""
date: 2026-08-28
---

# Trust session findings — index, 2026-08-28

**Status**: index only. Every finding below is recorded in full elsewhere; this file exists so
the next person does not reconstruct it from a dozen documents. Where a finding contradicts
`docs/TRUST_PLAN.md`, the contradiction is noted — **the plan has been wrong four times and
its obstruction claims should not be trusted without re-measurement.**

## Score

`origin/main` at `ce1452d`: **70 entries** — 25 `grandfathered`, 45 `axiom-only`. Started the
session at 81. The nine retirements came from real theorems (`zlib_roundtrip_soundness`, L9
GZIP, and the four DEFLATE roundtrips as corollaries of `deflate_roundtrip_soundness`), not
from tactic substitution. `bv_decide` is at zero tree-wide; `finite-forall` is empty.

## The finding that reframes the rest

**The allowlist count is a proxy that can be driven to zero without fixing anything.** Law 10
rung 2 needs no allowlist entry, so converting a pointwise `native_decide` to a pointwise
`decide` deletes the entry while the statement, its domain, and the Law 9 violation are
unchanged. Spike 1 is the existence proof: four contracts, all at `Unit`, zero entries, nothing
fixed.

Full argument: `docs/TRUST_DIRECTION_REVIEW.md`.

**Four agents independently declined that move when told not to take it.** One had already made
the edit — `native_decide` → `rfl` across all nine Spike 4 trace equivalences — and reverted it.

**The distinction that makes the rule usable** (from `docs/tasks/TRUST-F1-obstruction-census.md`):
a pointwise statement is either **sampled** (real domain is larger — a `decide` retirement is
score-without-fix) or **complete-domain** (the program genuinely takes no input, so `decide` is a
legitimate rung-3-to-rung-2 improvement). 15 of the 18 measured are sampled; Spike 2's 3 are
complete-domain. **The count cannot distinguish them; a domain column in the allowlist could.**

## Where the honest theorem lives for input-free programs

`VerifiedProgram` (`Gasm/Core/Verification.lean:82`) is correctly shaped — it bundles spec, asm,
and a ∀-quantified `traceEquivalence`, and cannot be constructed without the theorem. Output is
fully captured: `ConsoleEvent.out (text : String)` carries payloads, not occurrence markers.

The gap is that `traceEquivalence` **fixes** `s0 := loadEnvironment executable env`. For
`Env := Unit` that is the single state `exe.load` happens to build.

**`isValidEntryState` (`Gasm/Targets/Windows/Win32API.lean:391`) has exactly one occurrence in
the tree — its own definition.** It is the formal MS x64 entry precondition (`rip` at entry,
`rsp % 16 == 8`, `.rdata` loaded, IAT non-null) and no theorem references it. The honest
statement for a program taking no input quantifies over *valid entry states*, not over `Env`:

```lean
∀ (s : X86_64MachineState), isValidEntryState exe s → (runAsmTrace instructions s == spec) = true
```

**Owner direction**: make an invalid entry state fail to type-check rather than carry it as a
forgettable hypothesis — the `memAccesses` defaultless-field precedent (ADR-0040). **Status**:
under investigation at session end; the load-bearing open question is whether `exe.load`
provably satisfies its own precondition. **Nobody has ever checked.**

## Obstructions — measured, superseding the plan's claims

`docs/tasks/TRUST-F1-obstruction-census.md` has the full table for all 18 never-measured
entries. **0 of 18 closed.** Four walls:

- **W1** (`Lean.Loop.forIn → repeatM`) — **gone from Zlib.** `gzipCompress` and `compressFixed`
  now reduce (11.1s / 2.9s) after the `cdc98bf`/`f80e2c8` fuel conversions.
- **W2** — `Stdlib.Zlib.decodeHuffmanSymbol.step` → `Acc.rec`. **Not** `decompress` or
  `decodeHuffmanStream`, which are structural. **TRUST_PLAN's A2 is aimed one level too shallow
  and should be renamed.**
- **W3** (new, no step covers it) — `List.mergeSort` in `packageMergeLengths`
  (`Deflate.lean:1108`), Lean core. `compressPlan` forces `buildDynPlan` unconditionally, so
  **every `compress`/`zlibCompress` is blocked on any input.** This is why PNG is not a cheap
  harvest: `encodeImageRGBA8 → zlibCompress → compress → buildDynPlan` is stuck, and
  `filter_unfilter_soundness` cannot bypass it.
- **W4** (new) — `partial def readAllLines` (`Spikes/Spike3SortLines/Spec.lean:75`). A `partial
  def` compiles to an opaque constant with **no equations**, blocking rung 1 as well as rung 2.
  Converted in `52ae8a5`.

**Cheapest entries in the ledger**: `gzip_roundtrip_soundness_inst` and
`gzip_idempotent_canonical_roundtrip_inst` — sole blocker W2, so one fix reaches both.

**Spike 4 is not categorically blocked** and the plan's stated reason is false. `@[extern]` governs
compilation, not kernel reduction; `String.toUTF8` and `String.fromUTF8?` both reduce, confirmed
independently by two agents. The real blockers were `ByteArray.toList`, `String.splitOn`, and
`Std.Range.forIn` — all `@[irreducible]` well-founded recursions in Lean core, and all removable.
**TRUST_PLAN:43-47 still states the false rationale.**

## Propagation — half true, and the half that fails carries the plan's arithmetic

Every `axiom-only` entry is downstream of a `grandfathered` root — **0 orphans**. But **12 of 34
roots gate nothing but themselves**, and an `axiom-only` entry retires only when *every* root it
cites retires. **Measured: the recent retirements cascaded to zero.**

Cascade is real for Spike 4 (all 12 `axiom-only` cite the nine roots) and Spike 2 (7 = 2 roots +
5 dependents, verified by `#print axioms`). It is **absent** for Spike 5, whose 11 `axiom-only`
entries cite trace equivalences and never the `_inst` roundtrips.

The plan's leverage figures are therefore not reliable per-cluster and must be measured.

## The structural conclusion, reached independently three times

**Composition lemmas are mandatory, not optional.** `decide` is the wrong proof method, and no
amount of making it faster changes that — brute reduction cannot quantify over an infinite domain.

`docs/tasks/MEM-closure-cost-curve-measurements.md` establishes this by measurement rather than
argument: the `X86_64Memory` closure-chain cost is **100% kernel** (type-checking 76.4s against
`decide` 11ms and elaboration 9ms), which rules out any simp-level fix; a trie carrier is **13×
slower at N=100** with crossover near N≈400, above where most of the tree lives; and `initRegion`
takes an arbitrary `Address → Byte`, so a finite map cannot replace the carrier at all. **The
recommendation is to change nothing** — a symbolic step-lemma proof never builds a deep chain in
the first place.

**The gap that blocks it**: there are **no peeling lemmas anywhere for
`runProgramTraceWithLoops`** — verified tree-wide. `LoopInvariant.lean`'s
`runProgramWithLoops_step`/`_stuck` are for the *state* evaluator, with no events and no
interception. TRUST_PLAN's G1 scopes this for WASI only; **x86 needs the same family and has no
step covering it.**

Corrections to what was believed earlier: `fib_iter_asm_soundness` proves a *state* theorem, not
a trace one, so it does **not** establish trace-level fitness. And it is a **Law 12 unlinked
twin** — `spike2SymbolicProgram` never calls `fibIterSymbolicProgram`, so 701 lines verify a
routine that ships in no executable. On Linux `fibIterInstructions` is referenced by nothing at
all.

## The pattern under several of these

Mechanisms built correctly and never wired to anything: `isValidEntryState` (0 consumers),
`fibIterInstructions` (proven, not linked), `TraceStepLemmas`/`InstructionStepLemmas`/
`InterceptLemmas` (0 consumers), `BlockM` (D3's authoring surface, only an unused import),
`MemoryPermissions Arch` (phantom parameter). **Status**: a full audit of this pattern was still
running at session end; its result is not yet on disk.

This is a different defect from the one TRUST_PLAN attacks. The plan assumes the debt is missing
proofs; a substantial part of it is proofs and mechanisms that exist and are not connected.

## Law 1 citations

`docs/CITATION_REVIEW.md`: of 289 citations read across the six largest clusters, **13 are
justified**. 116 are **false** — the cited section describes something else. Three clusters are
*missing documents* rather than bad citations: Spike 2 has no design document at all, Spike 3's
covers only Windows, and Spike 5's §4 has no Linux subsection.

The proposed prose-floor gate was **measured and rejected** — at a four-line floor it flags 59
anchors and 662 citations to catch five, and false-positives the best anchors in the repo. This
cannot be gated into correctness; `docs/REVIEW.md` §4.2 subsection **C — Citation Adequacy Audit**
was ratified and landed (`2c41dad`) to make it a standing review obligation instead.
