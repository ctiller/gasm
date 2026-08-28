# ORACLE DEBT — audit of scripts/gate_allowlist.txt and the path to zero

> Audit of all 80 `scripts/gate_allowlist.txt` entries (37 `grandfathered`, 10 `finite-forall`,
> 33 `axiom-only`) against the owner's ratified target: **no axioms, strong verification, checked
> models** — not merely "37 pointwise proofs migrated to universal form," the original framing of
> this audit's brief, but every one of the 80 entries reaching zero non-standard-axiom dependence,
> with the sole permitted residue being Lean's own foundational axioms (`propext`, `Classical.choice`,
> `Quot.sound`). Produced 2026-08-27, tree at `46d56ce`+. Feeds `docs/tasks/` (PA10–PA18, plus
> frontmatter edits to PA1/PA5–PA9/N2/TC5/TC9/TC12/TC16/TC17/TC21/B7).

**Status**: this document is an audit and a plan, not a completed migration. Every task it names as
"closing" an allowlist entry is planned work tracked under the cited `PA#`/`TC#` id; none of PA10–PA18
has landed as of this writing. `scripts/gate_allowlist.txt` itself has not been edited by this audit —
no `.lean` file was touched, per this task's own scope (audit and re-plan, not implementation).

---

## The headline answer

**No.** Before this audit's new tasks, the existing `docs/tasks/` plan reaches roughly **8 of the 37**
grandfathered entries (22%) and **0 of the 10** finite-forall entries — the rest of the 37, all 10
finite-forall entries, and (as a consequence) most of the 33 axiom-only entries have **no task that,
completed as written, removes them**. Two of the 33 axiom-only entries also have an independent
dependency on one specific finite-forall entry that is itself the hardest item in the whole ledger —
see Part 5.

After this audit's nine new task files (PA10–PA18) and the frontmatter corrections in Part 6, every
one of the 80 entries now has a named covering task. But two of those tasks — PA14 (`G8bf_table`,
a CRC bit/table identity currently closed by a SAT certificate) and PA16 (full DEFLATE/zlib/gzip/PNG
codec roundtrip soundness) — are honestly classified in Part 4 as **not confidently reaching zero on
any bounded timeline**: PA14 may need either new Lean tooling or a from-scratch bitvector-algebra
proof; PA16 is a large, genuine formal-methods project (comparable in scope to a from-scratch DEFLATE
correctness formalization), not a single theorem. Naming a task for these is right — leaving them
untracked would be worse — but completing "every mapped task, as specified" still does not guarantee
zero for these two specifically. Everything else in the plan (35 of 37 grandfathered via existing +
new tasks minus the roundtrip dozen, 9 of 10 finite-forall) is concretely tractable engineering with
no research risk identified.

---

## Part 1 — the 37 `grandfathered` entries: shapes, not a flat list

Read in full: `Stdlib/Zlib/Equivalence.lean`, `Stdlib/Zlib/CRC32.lean`, `Stdlib/Zlib/Adler32.lean`,
`Stdlib/Png/Equivalence.lean`, all ten `Spikes/*/Equivalence.lean` files,
`Gasm/Targets/Wasm/SemanticsFuzzer.lean`, `Gasm/Targets/Wasm/LEB128.lean`. They fall into four shapes,
not two — the brief's hypothesis (spikes = trace equivalence, Zlib/Png = roundtrip) was half right;
there are two further shapes that don't fit either bucket.

### Shape A — spike trace equivalence at one concrete environment (18 entries)

`theorem spikeN_..._trace_equivalence : (runAsmTrace/runWasiTrace instructions (executable.load
<one fixed input>) == runModelTrace spec <same fixed input>) = true := by native_decide`. The
*claim* (`∀ env, ...`) is the right shape (`docs/EQUIVALENCE_PROOFS.md` §5); the *proof* evaluates it
at one hand-picked `env` (empty stdin, one canonical 3-line input, one literal HTTP request string,
one sample payload) via the in-Lean simulator, and calls that universal. This is the shared root
cause across every spike: Spike1 Windows + Wasm (2), Spike2 Windows + Wasm (2 — plus the separate
`fib_iter_*_soundness` finite-forall pair, Shape D below), Spike3 Wasm (1) + Spike3 Windows'
`Bool`-cased pair (2), Spike4's six `{windows,wasm}×{root,status,404}` theorems (6), Spike5's three
`*_trace_equivalence` theorems (windows_gzip, wasm_gzip, windows_gunzip — 3, distinct from its two
roundtrip entries below). Total: 2+2+1+2+6+3 = 16, plus Spike1/2's four already counted = confirm by
recount below in the matrix; the exact per-file tally is in Part 2's table.

What the universal version needs: `∀ (env : Environment)` (or the real per-route byte-string domain
for Spike4/Spike3), not a spike-defined enum standing in for it — exactly Law 9's read-binder clause.
PLAN.md's own Law 9 census already flagged most of these (Tier 1: constant-function specs; Tier 2:
Spike5's single-constructor `GzipOp`/`GunzipOp`) but classified Spike3-Windows' `Bool` and Spike4's
`HttpRoute` as **Tier 3, "legit pattern"** — Part 2 disputes that classification is complete: the
*outer* composition over 2 or 3 cases is legitimate, but each *inner* case is still checked at exactly
one literal byte string, not the real input domain each case is supposed to represent.

### Shape B — codec roundtrip soundness at one or two concrete vectors (19 entries)

`theorem X_roundtrip_..._inst : (match decompress (compress data) with | .ok r => r == data | .error
_ => false) = true := by native_decide`, for one fixed `data` literal (`ByteArray.empty`, a short ASCII
string, a repetitive byte pattern, a 2×2 RGBA image) — and its "1.5-roundtrip" idempotency variant
(compress the decompressed output of a fixed compressed stream, check it decompresses back to the
same thing). This is `Stdlib/Zlib/Equivalence.lean` (8: 3 plain-DEFLATE roundtrips + zlib + gzip +
3 idempotent variants), `Stdlib/Png/Equivalence.lean`'s whole-image pair (2, *distinct* from its
five per-filter-step entries below), and `Spikes/Spike5Gzip/Equivalence.lean`'s near-duplicate pair
(2) — 12 total in this exact "whole codec" sub-shape. A **related but structurally different**
5-entry sub-shape lives in the same PNG file: `filter_{none,sub,up,average,paeth}_invertible_inst`
each check one fixed 8-byte scanline against one filter type — these are *not* whole-codec claims,
they are per-byte-step claims that (unusually) already have their fully general form proven four
lines above them in the same file (`sub_filter_step_invertible` etc., by `omega`) and simply never
connected to the scanline-level function. 12 + 5 = 17 in Shape B overall (2 sub-shapes); plus
`crc32_empty`/`adler32_empty` (2 more, but these are trivial closed facts with no loop iterations at
all for an empty buffer — a third, degenerate sub-shape) = 19.

### Shape C — Wasm-interpreter ground-instance witnesses (2 entries)

`trapShortCircuitGuard_inst` (a 5-instruction mutation-tested regression pin that `evalInstr`'s
trap guard stops subsequent instructions from running) and `encodeI32SLEB128_exceeds_i32_budget_inst`
(a single witness that `encodeI32SLEB128 (2^40)` needs ≥6 bytes, `native_decide`d only because
`encodeSLEB128List`'s well-founded recursion gets stuck under kernel `decide`). Neither is a
codec-roundtrip or trace-equivalence claim; both are provable structurally (induction over the
instruction list; an equation lemma or structural-recursion rewrite, respectively) with no oracle.

### What the universal version needs, by shape

- Shape A: real `∀`-quantification over `Environment`/the request-byte domain (PA6/PA7/PA8/PA9's
  architecture), discharged by structural induction over the assembly/Wasm step semantics — PA1
  already demonstrated this technique is tractable for a buffer-indexed loop.
- Shape B (whole-codec): a genuine formal DEFLATE/zlib/gzip/PNG correctness proof — large, no
  shortcuts, the least tractable single item after PA14 (see Part 4).
- Shape B (PNG per-filter-step): trivial — lift the already-proven general lemma across a scanline
  by induction. The cheapest closure in the entire ledger.
- Shape B (empty-buffer checksums): trivial — the loop bound is 0, `decide`/`rfl` should close it
  directly, no `native_decide` needed at all.
- Shape C: structural, bounded engineering; no research risk.

---

## Part 2 — coverage matrix (all 80 entries)

Legend: **G** = grandfathered, **F** = finite-forall, **A** = axiom-only. "Covers?" states whether an
*existing* task (before this audit) removes the entry, per the brief's strict rule (touching the file
is not enough; the task's acceptance criteria must actually eliminate the oracle dependency). "New
task" is this audit's addition where no existing task covered the entry.

### Grandfathered (37)

| # | Entry (file :: decl) | Existing coverage? | New task |
|---|---|---|---|
| 1–8 | `Stdlib/Zlib/Equivalence.lean` :: `deflate_roundtrip_{empty,soundness,repetitive}_inst`, `zlib_roundtrip_soundness_inst`, `gzip_roundtrip_soundness_inst`, `{deflate,zlib,gzip}_idempotent_canonical_roundtrip_inst` | **None.** F6 assumes this baseline, does not prove it; PA8 does not touch pure-functional roundtrip claims. | **PA16** |
| 9 | `Stdlib/Zlib/CRC32.lean` :: `crc32_empty` | None | **PA11** |
| 10 | `Stdlib/Zlib/Adler32.lean` :: `adler32_empty` | None | **PA11** |
| 11–15 | `Stdlib/Png/Equivalence.lean` :: `filter_{none,sub,up,average,paeth}_invertible_inst` | None | **PA10** |
| 16–17 | `Stdlib/Png/Equivalence.lean` :: `png_{roundtrip_soundness,idempotent_canonical_roundtrip}_inst` | None (depends on Zlib's codec, sequenced after it) | **PA16** |
| 18–19 | `Spikes/Spike5Gzip/Equivalence.lean` :: `gzip_{roundtrip_soundness,idempotent_canonical_roundtrip}_inst` | None — PA8's Spike5 fix targets `GzipOp`/`GunzipOp` env-quantification, not these direct functional checks | **PA16** |
| 20 | `Spikes/Spike5Gzip/Equivalence.lean` :: `spike5_windows_gzip_trace_equivalence` | **PA8** (Tier 2) | — |
| 21 | `Spikes/Spike5Gzip/Equivalence.lean` :: `spike5_wasm_gzip_trace_equivalence` | **PA8** (Tier 2) | — |
| 22 | `Spikes/Spike5Gzip/Equivalence.lean` :: `spike5_windows_gunzip_trace_equivalence` | **PA8** (Tier 2) | — |
| 23–28 | `Spikes/Spike4HttpServer/Equivalence.lean` :: `spike4_{windows,wasm}_{root,status,404}_trace_equivalence` (6) | None — Tier 3 "legit" per census, but only the outer `HttpRoute` composition is legit; each inner case is still pointwise. `N8` fixes bugs found here with regression tests, not a universal proof. | **PA17** |
| 29 | `Spikes/Spike3SortLines/Wasm/Equivalence.lean` :: `spike3_wasm_canonical_effect_trace_equivalence` | **PA8** (Tier 1) | — |
| 30–31 | `Spikes/Spike3SortLines/Windows/Equivalence.lean` :: `spike3_{canonical,empty}_effect_trace_equivalence_inst` | None — Tier 3 "legit" per census; same critique as Spike4 above | **PA17** |
| 32 | `Spikes/Spike2Fibonacci/Windows/Equivalence.lean` :: `spike2_canonical_effect_trace_equivalence` | **PA8** (Tier 1) | — |
| 33 | `Spikes/Spike2Fibonacci/Wasm/Equivalence.lean` :: `spike2_wasm_canonical_effect_trace_equivalence` | **PA8** (Tier 1) | — |
| 34 | `Spikes/Spike1Hello/Wasm/Equivalence.lean` :: `spike1_wasm_canonical_effect_trace_equivalence` | **PA8** (Tier 1) | — |
| 35 | `Spikes/Spike1Hello/Windows/Equivalence.lean` :: `spike1_canonical_effect_trace_equivalence` | **PA8** (Tier 1) | — |
| 36 | `Gasm/Targets/Wasm/SemanticsFuzzer.lean` :: `trapShortCircuitGuard_inst` | None | **PA12** |
| 37 | `Gasm/Targets/Wasm/LEB128.lean` :: `encodeI32SLEB128_exceeds_i32_budget_inst` | None | **PA12** |

**Pre-audit existing-task coverage: 8/37 (21.6%).** Post-audit (with PA10–PA18): 37/37 named, of
which 25 (PA8's 8 + PA10's 5 + PA11's 2 + PA12's 2 + PA17's 8, i.e. everything but PA16's 12) are
concretely tractable with no identified research risk; PA16's 12 are honestly flagged long-horizon
(Part 4).

### Finite-forall (10)

| # | Entry | Oracle today | Structural closure assessed | New task |
|---|---|---|---|---|
| 1 | `Stdlib/Zlib/Equivalence.lean::reverse_bits_8_involutive_inst` | `native_decide`, 256-elt domain | Likely: plain `decide` may just work | **PA18** |
| 2 | `Spikes/Spike5Gzip/Equivalence.lean::bit_reversal_8_involution_inst` (exact duplicate of #1) | `native_decide` | Same | **PA18** |
| 3 | `Stdlib/Zlib/Equivalence.lean::encode_length_bounds_inst` | `native_decide`, 256-elt domain | Likely: plain `decide` | **PA18** |
| 4 | `Stdlib/Zlib/Equivalence.lean::encode_distance_bounds_inst` | `native_decide`, 32768-elt domain | Plausible via `decide` or a ~30-band structural case-split if `decide` is too slow | **PA18** |
| 5 | `Stdlib/Zlib/CRC32Equivalence.lean::and_one_cases` | `bv_decide` | Likely: small `BitVec`/`omega` proof | **PA13** |
| 6 | `Stdlib/Zlib/CRC32Equivalence.lean::G_eq_Gbf` | `bv_decide` | Plausible: reduces to `and_zero`/`and_allOnes`-class lemmas after case split | **PA13** |
| 7 | `Stdlib/Zlib/CRC32Equivalence.lean::xor_byte_shr8` | `bv_decide` | Plausible: bit-extensionality argument | **PA13** |
| 8 | `Stdlib/Zlib/CRC32Equivalence.lean::G8bf_table` | `bv_decide` | **Hard** — see Part 4 | **PA14** |
| 9 | `Spikes/Spike2Fibonacci/Windows/Equivalence.lean::fib_iter_asm_soundness` | `native_decide`, 91-case enumeration of a real loop | Tractable via loop-invariant induction (PA1's technique) | **PA15** |
| 10 | `Spikes/Spike2Fibonacci/Wasm/Equivalence.lean::fib_iter_wasm_soundness` | `native_decide`, same shape | Same | **PA15** |

**Pre-audit existing-task coverage: 0/10.** No task in `docs/tasks/` touched the question of whether
these ten need an oracle at all — they were treated as permanently settled once allowlisted. Post-audit:
9/10 assessed as plausibly closable without any oracle; #8 (`G8bf_table`) is the one genuinely hard
case (Part 4).

### Axiom-only (33) — see Part 5 for the propagation-claim verification in full; summary here

31 of the 33 cite only Shape-A `*_trace_equivalence`/`*VerifiedProgram` theorems (directly or via a
`main`/`runTests` → `emitVerifiedExecutable` chain) and clear automatically once their respective
Shape-A root (PA8 or PA17) lands. **2 of the 33 — `G8_eq_Gbf8` and `crc32ByteStep_eq_G8`
(`Stdlib/Zlib/CRC32Equivalence.lean`) — transitively depend on `G8bf_table` (PA14's hard case)**, per
the allowlist's own comment ("`crc32ByteStep_eq_G8` transitively depends on FIVE such axioms... one
each from `G8bf_table`, `xor_byte_shr8`, `and_one_cases`, and two from `G_eq_Gbf`'s two case-split
calls"). These two do **not** automatically clear from the grandfathered-37 work alone; they need
PA13 (3 of the 5) and PA14 (the fourth, hardest one) both to land.

---

## Part 3 — new tasks written (this audit)

Nine new task files, `docs/tasks/PA10-PA18` (skipping nothing; the numbers are simply the next free
`PA` ids). Each validated against `scripts/task_frontier.py --validate` (see Verification below).

| id | Title | Entries closed | Prerequisite | Difficulty |
|---|---|---|---|---|
| PA10 | PNG filter scanline invertibility | 5 grandfathered | none | trivial |
| PA11 | crc32_empty / adler32_empty via decide | 2 grandfathered | none | trivial |
| PA12 | Wasm trap guard + LEB128 witness, structural | 2 grandfathered | none (related: B7) | low |
| PA13 | CRC32 bit-trick lemmas without SAT | 3 finite-forall | none | low-medium |
| PA14 | G8bf_table structural closure | 1 finite-forall | none | **high / uncertain** |
| PA15 | Fibonacci loop-invariant induction | 2 finite-forall | none (related: B7) | medium |
| PA16 | Codec roundtrip universal soundness | 12 grandfathered | none | **very high / long-horizon** |
| PA17 | Spike3-Windows/Spike4 domain honesty | 8 grandfathered | PA7, PA8 | medium-high |
| PA18 | Small-domain decide migration | 4 finite-forall | none | trivial-low |

`after`/`related` edges were set to reflect genuine dependency, not sequencing convenience: PA17 is
the only new task with a hard `after` (it needs PA7's reactive-contract type and PA8's
Environment-quantification precedent); everything else is unblocked today. PA12/PA15 carry
`related: [B7]` (not `after`) because B7 changes the same Wasm trap-semantics code these two touch,
but neither routine performs an out-of-bounds access, so B7 is not a hard blocker — only a
"re-verify against the corrected model if B7 lands first" note.

---

## Part 4 — what does not confidently reach zero, and why

Per the brief: an honest "these cannot reach zero, here is why" beats a plan that quietly assumes
everything is tractable. Two items:

**PA14 — `G8bf_table` (`Gbf8 poly x = (x >>> 8) ^^^ Gbf8 poly (x &&& 0xFF)`, over the complete
`UInt32 × UInt32` domain).** This is a genuinely finite, decidable claim (which is exactly why
`bv_decide` can certify it in ~1.8s) — it is not an infinite-domain problem the way F6's optimization
claims would be. But "finite and decidable" does not mean "cheap to hand-prove": the natural
structural argument requires either (a) unfolding `Gbf`'s bit-level update eight times and showing
bit-extensional equality at every position — mechanically possible but likely a very long, fragile
proof — or (b) building enough GF(2)-polynomial-ring algebra from scratch to state the standard
"CRC table precomputes repeated polynomial division" argument, which is a small mathematical library,
not a lemma. The upstream escape hatch — Lean core adding a kernel-replay path for `bv_decide`'s LRAT
certificates, making the SAT step itself kernel-checked — is outside this project's control and has
no announced timeline (`TCB.md` T14 confirms no `checkProofs`-style option exists in the pinned
v4.33.1 toolchain). PA14 is written to attempt a structural proof with a stated abandonment criterion,
and an honest "did not close, here is what a future attempt needs" is an explicitly acceptable
outcome for that task. The owner's prior approval of `bv_decide` as an interim posture ("ok, bv_decide
seems fine then," in the context of it being the only mechanism reaching a 10¹² domain at all) stands
for this one entry until either avenue above bears fruit.

**PA16 — full DEFLATE/zlib/gzip/PNG codec roundtrip soundness (12 entries).** Not a new-mathematics
risk the way PA14 is — every sub-piece (Huffman prefix-code correctness, LZ77 match/copy inversion,
block framing, container checksums) is well-understood, previously-formalized-elsewhere territory.
The risk here is pure scale: this is realistically a multi-week, multi-lemma formalization project,
not a task with a single clean proof strategy. PA16 is written as a Law-5 design-first task explicitly
because a monolithic attempt is the wrong shape; its first deliverable is a decomposition, and its
acceptance criteria accept partial closure (some sub-lemmas landed generally, others still gated)
as an honest intermediate state rather than demanding all-or-nothing.

**Everything else in the 80-entry ledger** — the 25 grandfathered entries covered by PA8/PA10/PA11/
PA12/PA17, and 9 of the 10 finite-forall entries (PA13/PA15/PA18) — is assessed as concretely
tractable engineering: known techniques (induction over a loop/instruction list, an already-proven
general lemma sitting unused nearby, a bit-extensionality argument, a well-founded-recursion
workaround), no open mathematical or tooling question. The honest split is 2 hard items out of 80,
not a uniformly hard ledger — but those 2 are also, not coincidentally, the two that most directly
motivated the owner's zero-axiom mandate (PA14 is PA1's own `bv_decide` work; PA16 is the "is zlib
actually correct" question F6 has been quietly assuming an answer to).

**A third, distinct concern: checked models.** Every Wasm-target proof this plan produces or leaves
standing (Shape A's 7 Wasm-target entries, PA12's trap-guard theorem, PA15's Wasm Fibonacci proof) is
stated against `Gasm/Targets/Wasm/Semantics.lean` as it exists today — a model `docs/tasks/
B7-wasm-oob-trap-and-limits.md` documents as **not** trapping on out-of-bounds memory access (it
silently zero-pads and grows the backing array instead), contrary to the real WebAssembly spec. An
axiom-free, fully universal proof about this model would still be a proof about a machine no real
engine implements for that behavior. None of the routines this plan's new tasks touch (Fibonacci, the
trap short-circuit fact itself, Spike1/2/3/5's happy-path bodies) perform an out-of-bounds access
today, so this is not a blocking dependency — but it is a live instance of exactly the gap the owner
named, and `docs/ORACLE_DEBT.md`'s Part 6 raises B7's priority accordingly rather than treating it as
someone else's problem.

---

## Part 5 — the propagation claim, verified rather than trusted

Traced a representative sample spanning every distinct citation shape in the 33 `axiom-only` entries,
reading the actual source (not just the allowlist's justification text) for each:

- **`VerifiedProgram` struct field, direct citation**: `Spikes/Spike1Hello/Windows/Equivalence.lean`'s
  `spike1VerifiedProgram.traceEquivalence := fun _ => spike1_canonical_effect_trace_equivalence` —
  a bare reference, no tactic, no computation. Clean.
- **`cases`-composition over a finite route/session enum**: `Spikes/Spike4HttpServer/Equivalence.lean`'s
  `spike4_windows_route_equivalence (r : HttpRoute) := by cases r · exact spike4_windows_root_..
  · exact spike4_windows_status_.. · exact spike4_windows_404_..` — three `exact`s citing the three
  already-grandfathered per-route theorems, nothing else. Clean.
- **Emit.lean `main`**: `Spikes/Spike1Hello/Windows/Emit.lean`'s `main` calls
  `emitVerifiedExecutable spike1VerifiedProgram` and writes bytes to disk — no proof term, no
  `native_decide`/`bv_decide` anywhere in the file. Clean.
- **Test.lean `runTests`/`main` delegation**: `Spikes/Spike3SortLines/Windows/Test.lean`'s `runTests`
  calls `emitVerifiedExecutable spike3VerifiedProgram` and drives the emitted binary via
  `IO.Process.output` for black-box regression checks — real subprocess I/O, but no independent
  oracle-backed *proof* tactic anywhere in the file; `main` is a one-line delegation to `runTests`.
  Clean.
- **`rw`-chain connection theorems**: `Stdlib/Zlib/CRC32Equivalence.lean`'s `G8_eq_Gbf8` and
  `crc32ByteStep_eq_G8` — both close by `rw [...]` chains citing `G_eq_Gbf`/`G8bf_table`/
  `and_one_cases`/`xor_byte_shr8`, no tactic of their own that could introduce a fresh axiom.
  **Not clean in the "clears once the 37 land" sense** — see below.

**Verdict**: the propagation claim holds for every sampled instance — no axiom-only entry hides an
independent oracle dependency of its own; each is exactly what its allowlist justification says, a
downstream citation with no native/SAT tactic invocation in its own proof term. **With one caveat that
matters**: `G8_eq_Gbf8` and `crc32ByteStep_eq_G8` cite `G8bf_table` (PA14's hard case) among their
five constituent axioms, so these two specifically do not automatically clear once the grandfathered-
37 work (PA8/PA10-PA12/PA16/PA17) lands — they also need PA13 (3 of their 5 constituent axioms) and
PA14 (the fourth, hardest one). **A structural gap in the enforcement mechanism itself, found while
checking this**: `Tools/CheckGatesAxioms.lean` matches an `axiom-only` allowlist entry by
`(moduleName, fqn)` only (`matchKey`, line 269) — it authorizes *any* non-standard axiom set the
named declaration carries, not a specific expected axiom name. A hidden, independent `native_decide`
accidentally introduced inside an already-`axiom-only`-allowlisted declaration would not be caught by
this tool; only the kind of manual reading this Part 5 did would catch it. This is a real, if narrow,
gap in the load-bearing gate's precision — flagged here rather than silently worked around; it did
not change this audit's verdict (the sampled entries are genuinely clean) but is worth a future
mechanical fix (tightening `matchKey` to also record and check the *specific* axiom set an
`axiom-only` entry was authorized for, so drift is caught structurally rather than by inspection).

---

## Part 6 — re-prioritization and stale-status corrections

### Stale statuses corrected (verified against the tree, not assumed)

| id | Old status | New status | Evidence |
|---|---|---|---|
| PA1 | `designing` | `implementing` | `Stdlib/Zlib/CRC32Equivalence.lean` (423 lines, 0 `sorry`) has landed substantial contract groundwork, but its own header comment states it is "not a completed end-to-end contract" and no completion report is appended — `done` would overstate, `designing` understated. |
| TC5 | `implementing` | `done` | `scripts/run_gates.py` (1027 lines) exists, self-describes as this task's implementation, matches every acceptance criterion in its own docstring. |
| TC9 | `implementing` | `done` | `GzipFuzzer.lean` has an oracle-presence check + `--count` floor; both Spike1/Spike2 Wasm `Test.lean` now report honest "did not run" instead of synthesized "100% sound." |
| TC16 | `implementing` | `done` | `scripts/check_references.py` has SHA-256 manifest support (21 occurrences) and an explicit `intel_sdm` disposition. |
| TC17 | `implementing` | `done` | `[VACUITY FLOOR TRIPPED]` diagnostics present in the x86 hardware, Wasm, perf, and encoding fuzzers. |
| TC21 | `ready` | `done` | `scripts/check_doc_facade.py` exists; git history shows it wired into `run_gates.py`/`REVIEW.md`/CI. |

All six had, in fact, landed — the coordinator's "believed to have landed" was correct for five of
six; PA1 is the exception, landed-but-incomplete rather than either fully done or undesigned.

### Priority changes

`AGING_RATE` is 1.0 effective-priority point per hour since `priority_set` — every priority below was
chosen, and its `priority_set` refreshed to the same audit timestamp, so the *relative* ordering the
raw `priority` field encodes is what matters; two tasks set at the same instant age identically.
Values:

- **9.7–9.8** (PA18, PA10, PA11): the three cheapest, zero-prerequisite closures in the whole ledger —
  ranked above PA1's existing 9.6 ceiling since they are strictly faster to land and directly serve
  the now-top-priority epic.
- **9.2–9.5** (PA12, PA13, PA15): ready-now, no architectural prerequisite, moderate engineering
  effort, no research risk.
- **9.4** (PA8, existing, raised from 6.5): the single highest-yield *existing* task — 8 of the 37
  grandfathered entries, more than any other one task, new or old.
- **8.3–8.8** (PA5/PA6/PA7, raised from 7.0/6.8/6.5; PA17, new): the architecture chain PA8's Spike4
  slice and the Spike3/Spike4 domain-honesty closure depend on — high because they gate top-priority
  closures, not raised to PA8's level because they are prerequisites, not the closures themselves.
- **8.5** (PA16, new) / **7.5** (PA14, new): still clearly above the pre-audit median, reflecting that
  they are part of the top-priority epic, but deliberately below the ready-now items so the cheap wins
  aren't starved of attention chasing the two hardest items first.
- **7.8** (PA9, raised from 6.7) / **7.2** (TC12, raised from 6.5): capstone/adjacent architecture,
  raised in proportion without claiming a blocking relationship that doesn't exist.
- **8.6** (B7, raised from 8.0) / **9.3** (N2, raised from 9.0): both already high; nudged further —
  B7 because the owner's "checked models" clause names exactly its defect class, N2 because it now
  doubly gates the oracle-debt chain on top of its original networking rationale.

### Resulting frontier (post-edit, `scripts/task_frontier.py --all`, top 20 of 68)

```
 1  TC4   done           trust-core      8.5     15.83    4.0540
 2  PA1   implementing   proof-arch      9.6     16.93    3.1949
 3  PA2   ready          proof-arch      8.0     15.33    1.7650
 4  G1    done           graphics        8.3     15.63    1.5587
 5  N2    ready          networking      9.3      9.30    1.5308
 6  TC5   done           trust-core      9.5     16.83    1.5108
 7  N1    designing      networking      9.0     16.33    1.2792
 8  B7    ready          wasm            8.6      8.60    1.2434
 9  PA5   ready          proof-arch      8.8      8.80    1.1458
10  PA13  ready          proof-arch      9.3      9.30    1.0116
11  PA14  ready          proof-arch      7.5      7.50    0.9920
12  TC16  done           trust-core      8.3     15.63    0.8662
13  F1    ready          perf            8.3     15.63    0.8127
14  N3    ready          networking      7.5     14.83    0.7649
15  PA16  ready          proof-arch      8.5      8.50    0.7467
16  G5    ready          graphics        7.3     14.63    0.7146
17  TC17  done           trust-core      7.8     15.13    0.7062
18  TC9   done           trust-core      7.5     14.83    0.6798
19  TC2   done           trust-core      7.5     14.83    0.6756
20  PA10  ready          proof-arch      9.7      9.70    0.6678
```

**Important caveat on this ranking, stated plainly**: `task_frontier.py`'s `leverage` column is a
PageRank score over the task DAG personalized by priority, not priority alone — it rewards being a
*prerequisite for many other tasks*, not urgency in isolation. PA10/PA11/PA18 (the cheapest,
highest-priority new closures) rank comparatively low on `leverage` specifically *because* nothing in
the DAG currently depends on them — they are leaves, not chokepoints, so their PageRank contribution
is small even at priority 9.7–9.8. This is the algorithm working as designed, not a mis-set priority:
the `--all` table's `prio`/`eff.prio` columns show these three correctly ranked near the very top on
raw urgency; the ready-now frontier view (`python scripts/task_frontier.py`, no `--all`) does surface
B7, PA13, PA14, PA16, PA10, PA15, PA12 in its top 15 actionable items, a marked shift from the
pre-audit frontier where no oracle-debt-specific task appeared in the top 15 at all.

---

## Verification performed

All run in the foreground from the repo root, exit codes captured directly (no pipe):

- `python scripts/task_frontier.py --validate` — **68 task files parsed and validated OK** (59
  pre-existing + 9 new), exit 0.
- `python scripts/task_frontier.py --all` / (no flag) — ranking shown above, exit 0.
- `python scripts/check_record.py` — see completion-report discussion; failures were exclusively
  this document's own not-yet-existing self-reference plus two literal-`...` placeholder citations in
  early drafts of the new task files, both fixed (full filenames substituted; this document created).
- `python scripts/check_refs.py`, `python scripts/check_licenses.py`, `python scripts/check_publishable.py`,
  `python scripts/check_doc_facade.py` — run after the fixes above; see the commit history for this
  change for final exit codes.

## Pointers

- `scripts/gate_allowlist.txt` — the audited artifact; not edited by this pass.
- `TCB.md` §T14 — the `bv_decide`-is-not-kernel-checked finding that reframed this audit's scope from
  37 to 80 entries mid-task.
- `MODEL_DEBT.md` §B7 — the Wasm trap-semantics gap Part 4's "checked models" discussion is about.
- `docs/tasks/PA1-crc32-pathfinder.md` — the induction-over-a-loop technique this plan's PA15/PA17
  reuse; also the origin of the `bv_decide` lemmas PA13/PA14 target.
- `docs/tasks/PA8-law9-migration.md`, `PA5-canonicalize-trace.md`, `PA6-read-binder-contract.md`,
  `PA7-verified-reactive-program.md`, `PA9-verified-program-derived.md` — the existing proof-
  architecture chain this audit's priority changes elevate.
- `docs/tasks/PA10-png-filter-scanline-invertibility.md`, `PA11-trivial-checksum-empty-facts.md`,
  `PA12-wasm-trap-guard-and-leb128-witness.md`, `PA13-crc32-bittrick-lemmas-without-sat.md`,
  `PA14-crc32-table-identity-structural-closure.md`, `PA15-fibonacci-loop-invariant-induction.md`,
  `PA16-codec-roundtrip-universal-soundness.md`, `PA17-spike3-spike4-domain-honesty.md`,
  `PA18-small-domain-decide-migration.md` — this audit's nine new task files.
