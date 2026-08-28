---
id: TC22
title: Doc-facade gate gap — fenced lean theorem blocks over nonexistent symbols are invisible to check_doc_facade.py
status: done
blocked_on: ""
after: []
related: [TC21]
bar: ""
track: trust-core
priority: 6.0
priority_set: 2026-08-28T00:00:00Z
design: ""
design_review: ""
date: 2026-08-28
---

# TC22: Doc-facade gate gap — fenced lean theorem blocks over nonexistent symbols are invisible to check_doc_facade.py

## Context — the finding (Law 13: a defect found by hand is a missing-gate report)

`docs/TARGETS/X86_64.md` §3 displayed, for an extended period, a fenced ` ```lean ` block
stating `theorem x86_mov_store_is_release` over `getMemoryType` / `isNonTemporalInstr` /
`PreservesStoreStoreOrder` / `PreservesLoadStoreOrder` — **none of which ever existed
anywhere in the `.lean` tree**. It read as an established memory-ordering proof in the one
document an ISA-expansion team would treat as ground truth. It was flagged in prose twice
(`MODEL_DEBT.md` §B1, `docs/X86_ISA_EXPANSION_PREREQUISITES.md` §7.5) and fixed by hand on
2026-08-28 — but `scripts/check_doc_facade.py` (TC21) never fired on it, and could not have:

- `MECHANISM_ABSENT` matches a backtick-quoted identifier on the **same physical line** as
  (and after) an enforcement-phrase trigger in *prose*. A fenced code block displaying a
  theorem is a different shape entirely: no backticks, no MUST-phrase, multi-line.
- This is a blind spot on the **highest-value case**: a fabricated theorem manufactures
  more confidence than any fabricated sentence — it carries the visual authority of checked
  code, in a repository whose whole premise is that displayed theorems are real.

## Measured precision analysis (done during this filing — do not skip re-measuring)

A prototype scan (fenced ` ```lean ` blocks in `docs/**/*.md` excluding `adr/`+`tasks/`;
declaration-header regex for `theorem|def|structure|class|inductive|abbrev`; name-token
presence anywhere in the `Gasm|Stdlib|Spikes|Tools` `.lean` text) measured at `27ab4ed`:

- 74 lean fences, 129 declaration headers in scope.
- **Naive check (any declaration kind): 61 hits — far too noisy to ship.** Nearly all are
  legitimate design sketches (`docs/MEMORY_HOOK.md`'s `RegionSpec`/`MemCostModel`,
  `docs/TARGETS/ARM.md`, `docs/SOFTWARE_MODELING_SDLC.md`'s worked examples, ...).
- **`theorem`-only: 19 hits** (incl. the now-fixed `x86_mov_store_is_release`). Still not
  shippable bare: e.g. `docs/STDLIB_ZLIB.md`'s roundtrip-soundness theorems and
  `docs/MEMORY_HOOK.md`'s `MemSafe` are declared design targets.
- **Section-scoped `**Status**:` markers rescue ~none of the legitimate cases** (0 of 61
  had one in the enclosing section): legitimate design docs disclose at *file* level
  ("this is a design document", `docs/MEMORY_HOOK.md` §1) or are wholly visionary, so the
  existing paragraph-scope escape hatch does not transfer to this check.

## Proposed gate (precise, ratcheted — reject anything noisier)

New check in `scripts/check_doc_facade.py`, `THEOREM_FENCE_ABSENT`:

1. Scope: fenced ` ```lean ` blocks in the linter's existing normative-doc set; **`theorem`
   (and `lemma`) declaration headers only** — the fabricated-proof shape; sketch `def`s and
   `structure`s stay the linter's explicitly rejected territory.
2. Absence test: the declared name (final dot-component) appears nowhere as a token in the
   `.lean` tree — the same deliberately-lenient presence test `MECHANISM_ABSENT` uses.
3. Escapes, in order: (a) the existing paragraph/section `**Status**:`-family marker,
   extended to "anywhere between the enclosing section heading and the block"; (b) a
   **file-level design declaration** — a `**Status**:`-family marker in the file's first
   section — which is how every legitimate design doc here actually discloses; (c) a
   justified entry in `scripts/doc_facade_allowlist.txt` (existing 5-field format).
4. **Ratchet**: seed with today's measured instances (~18 after the §3 fix) either by
   adding the missing file-level markers where true (preferred — most of these files ARE
   design docs and one sentence fixes them honestly) or by allowlist entry; count printed
   every run; new instances fail CI.
5. **Negative control before delivery** (Law 13): re-introducing the exact
   `x86_mov_store_is_release` block into `docs/TARGETS/X86_64.md` must fail the gate; and
   the current tree (post-seeding) must pass. Both demonstrated in the task's evidence
   record, RED/GREEN.

## Acceptance criteria

- `THEOREM_FENCE_ABSENT` implemented per above; `python scripts/check_doc_facade.py` exit 0
  on the seeded tree; RED/GREEN control recorded in Notes.
- Zero new required gate scripts (extends the existing wired gate — no
  `GATE_NOT_WIRED` irony).
- The linter's module docstring updated: this check's shape, the measured noise numbers
  that shaped it, and the rejected naive variant recorded alongside the existing
  "REJECTED SHAPES" notes.

## Notes

- 2026-08-28: task filed with the measured precision analysis above (measured at `27ab4ed`).
- 2026-08-28: **done.** `THEOREM_FENCE_ABSENT` implemented in `scripts/check_doc_facade.py`
  as check 3, wired into the same already-registered gate (no new gate script, no
  `GATE_NOT_WIRED` irony). Re-measured against the corpus at `f597a53` (180 tracked `.md`
  files, 80 ```lean fences, 135 declaration headers) — the numbers moved slightly from the
  filing but the shape of the analysis held:

  | variant | filed (`27ab4ed`) | re-measured (`f597a53`) |
  |---|---|---|
  | any declaration kind | 61 | 66 |
  | `theorem`/`lemma` only, token-presence resolution | (not separately measured) | 18 |
  | `theorem`/`lemma` only, declaration-site resolution | 19 | **19** |

  **One deliberate divergence from the filed design, on measurement.** §3 item 2 proposed
  reusing `MECHANISM_ABSENT`'s lenient "name appears as a token anywhere in the `.lean`
  text" presence test. That variant finds 18 and **misses `docs/STDLIB_ZLIB.md` §6.2's
  `deflate_roundtrip_soundness`** — because that name occurs in four doc comments in
  `Stdlib/Zlib/Equivalence.lean` (`:220`, `:361`, `:1523`, `:1883`) that name it as the
  *open* universal obligation, and in no declaration. A name the source tree itself
  describes as unproven is the worst possible false negative for this check, so resolution
  is by **declaration site** (`theorem|lemma|def|structure|inductive|abbrev|instance|class|
  axiom|opaque <name>`, matched fully-qualified or on the final dot-component). Cost: one
  extra false-positive class (a doc displaying a Mathlib/core theorem this repo does not
  declare), measured at zero instances today. Checks 1 and 2 keep token presence — they scan
  prose, where a comment mention really does mean the identifier is not fabricated.
- 2026-08-28: **RED/GREEN control** (`python scripts/check_doc_facade.py --self-test`, exit
  code **0**, all four checks PASS). The filed control — replanting the
  `x86_mov_store_is_release` block into `docs/TARGETS/X86_64.md` §3 — is no longer usable:
  commit `f597a53` deleted the block *and* added `**Status**:` disclosures to that section,
  so escape (a) would now correctly swallow it and the control would prove nothing. Replaced
  with a stronger one. The exact historical block is planted into two scratch documents in
  three configurations — unmarked, section-`**Status**:`-marked, and
  file-preamble-marked — and the assertion is that the finding count moves by **exactly +1**:
  `{"baseline": 0, "with_three_planted_blocks": 1, "after_revert": 0}`. That single run
  proves the check fires on the fabricated block AND that both escapes suppress the very same
  block. Scratch files are removed in a `finally`; the tree is verified green again after.
- 2026-08-28: **seeding, done honestly rather than by blanket allowlist.** 19 raw instances;
  1 already covered by a genuine file-level marker (`docs/MEMORY_HOOK.md` §1's `MemSafe`);
  18 blocking on first run. Of those: **6** were the real defect and were fixed at the source
  (`docs/STDLIB_ZLIB.md` §6.2/§6.3 — see that document); **1** was a second real instance
  found by the gate and not previously known (`docs/SPIKES/SPIKE5_GZIP.md` §5 displayed
  `gzip_roundtrip_soundness` and called it "discharged constructively with zero `sorry`");
  **9** were legitimate design targets or worked illustrations and got honest disclosures
  (`docs/EQUIVALENCE_PROOFS.md` §4, `docs/SOFTWARE_MODELING_SDLC.md` file-level,
  `docs/STDLIB_PNG.md` §6.2); **2** are allowlisted with justifications, both placeholder
  names in shape/format illustrations (`foo_correct` in a block captioned "PROHIBITED
  shape"; `memcpy_callability` as scaffolding under `docs/REVIEW.md` §1.1's citation-format
  example) where a design `**Status**:` marker would itself be a false claim.
- 2026-08-28: two design refinements the seeding pass forced, both recorded in the linter's
  module docstring. (i) The file-level escape (b) uses a **stricter** marker than the
  section escape (a): an explicit `**Status**:`-led *line*, not `STATUS_MARKER_RE`'s loose
  phrase family — applying the loose family to a whole preamble mis-rescued
  `docs/EQUIVALENCE_PROOFS.md`'s three `memcpy_*` blocks off the phrase "ratified design,
  implementation tracked as PA7" in a §1 bullet about an unrelated mechanism. (ii) The
  section escape searches ancestor sections' intro prose as well as the enclosing section,
  so a marker on `## 4` covers `### 4.1`–`### 4.3` (only the ancestor's own intro, never a
  sibling subsection's body). Scope extended beyond the filing to include root-level `*.md`
  as well as `docs/**` — measured as zero additional findings today, so it is free coverage.
