---
id: TC22
title: Doc-facade gate gap — fenced lean theorem blocks over nonexistent symbols are invisible to check_doc_facade.py
status: ready
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
