---
id: TC14
title: Emitter last-mile connection theorem (PE parser + codeMatches)
status: ready
blocked_on: ""
after: [TC4]
related: [TC19]
bar: bar-1-adjacent
track: trust-core
priority: 9.0
priority_set: 2026-08-27T18:25:47Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC14: Emitter last-mile connection theorem (PE parser + codeMatches)

## Context

Sourced from `TCB.md` **T5 — THE EMITTER LAST MILE — LARGEST ITEM** (TCB's ranked #1, tied):
everything past `serializeInstructions` (`Assembler.lean:349-350`) is **1,255 lines with zero
theorems**. The structural hole TCB names as the largest in the whole trusted-computing-base
ledger: `VerifiedProgram` (`Core/Verification.lean:64-72`) carries `executable` and
`instructions` as **independent fields — no proposition links `executable.textBytes` to
`serializeInstructions instructions`**. `traceEquivalence` walks the instruction list;
`emit` writes bytes to disk; nothing the proof observes ever reads the emitted bytes back. TCB's
exact words: "A `VerifiedProgram` with proven instructions and arbitrary bytes typechecks." Every
correctness proof in this repository currently proves something about a list of instructions that
is never mechanically shown to be what actually ended up in the executable file.

TCB also catalogs latent hazards discovered alongside this structural gap, all in the same
last-mile territory and worth fixing in the same pass since they'll surface the moment the
parser/theorem exists to catch them: `entryRva`/`imageBase` are honored by `load` but **ignored
by `emit`** (`Emitter.lean:196`); `computeSectionLayout` is called with three different
`idataSize` values that happen to coincide today; the linker lays out sections from
`estimatedSize` while emit/load use the actually-encoded size, with **no mechanical link between
the two** (a second instance of the same "estimate vs. reality" gap PLAN.md's findings ledger
separately flags — "Assembler: pass-1 `estimatedSize` must equal pass-2 encoded size; no
mechanical link"); symbol resolution's `.getD curRip` at 21 call sites means a mistyped import
name silently assembles a jump-to-self instead of failing; `dllCharacteristics` disagree between
spec and emit (`0x8160` vs `0x8120`); `imageBase` exists in three unlinked copies; and
`isValidEntryState` has zero call sites (an inert abstraction — Law 8 exposure). Validation today
is exactly three spike executables actually running; **TCB states plainly that Spike 4's and
Spike 5's Windows PEs are written and never executed at all.**

### Why this is Law-5-class

A byte-level PE parser plus a `parse ∘ emit = id`-shaped connection theorem is new model surface —
it is a specification of what "the emitted file correctly encodes these instructions" means,
which is exactly the kind of concept Law 5 requires be designed and reviewed before code, not
improvised inside a proof file. This task's `design_review` must be a real fresh-agent review
(not `waived-mechanical`) before implementation starts, precisely because a subtly wrong PE-format
model would let this task's own theorem lie about closing the gap it exists to close — the same
failure mode TCB is warning about in the first place.

### The three-part fix TCB proposes

1. **A byte-level PE parser written in Lean**, plus a connection theorem `parse (emit exe) = exe`
   (or the appropriate direction for this codebase's actual `emit`/`load` shapes), and a new
   `VerifiedProgram.codeMatches` field carrying the link `executable.textBytes =
   serializeInstructions instructions` as a proof obligation rather than an assumption. TCB is
   explicit about the preference here: "class unrepresentable — Law 13 pref 1" — the goal is that
   a `VerifiedProgram` with mismatched bytes and instructions **cannot be constructed**, not merely
   that a checker would catch it if run.
2. **A structural differential** against `dumpbin`/`pefile` (or equivalent) on every emitted
   binary, with corrupted-header control vectors (Law 13(4) — a known-bad PE must be demonstrably
   rejected before a known-good one's acceptance counts for anything).
3. **A loader-behavior harness that runs every spike PE** — closing the "2 of 5 PEs never
   executed" gap TCB flags (Spike 4 and Spike 5's Windows binaries).

TCB calls this "the highest-yield shrink in the repo" — of everything in the TCB ledger, this is
the item where the gap between "trusted but unproven" and "proven" is both largest and most
tractably closable by a single well-scoped proof, rather than by an unbounded fuzzing commitment.

## Deliverables & acceptance criteria

- A Lean PE parser sufficient to read back the structural fields this task's connection theorem
  needs (section table, entry point, IAT, text bytes at minimum).
- A kernel-checked connection theorem linking `executable.textBytes` to
  `serializeInstructions instructions`, exposed as (or feeding) a new `VerifiedProgram.codeMatches`
  field, such that a mismatched pair is unrepresentable — not merely checked at build time by a
  side script.
- The `entryRva`/`imageBase`/`idataSize`/`dllCharacteristics` inconsistencies enumerated above
  either fixed or, where fixing is out of scope for this task, filed as their own follow-up with
  the specific line references preserved (do not let them get lost inside a larger diff).
- A structural differential harness against an external PE reader (dumpbin/pefile), with at least
  one corrupted-header negative control demonstrated to be rejected (Law 13(4)).
- Every currently-unexecuted spike PE (Spike 4, Spike 5 Windows) actually run by a loader-behavior
  harness, with results in the completion report — this closes a concrete, named gap ("2 of 5 PEs
  never executed"), not a hypothetical one.
- `isValidEntryState`'s zero-call-site status resolved (wired into the real path, or removed per
  Law 8's dead-abstraction rule).
- Completion report must show: the connection theorem compiling with zero `sorry`/unauthorized
  axioms (`lake exe check_gates_axioms` clean), the differential harness's positive+negative
  control results, and confirmation all five spike PEs (not three) now execute under the harness.

## Pointers

- `Gasm/Core/Verification.lean:64-72` — `VerifiedProgram`, the structure this task adds
  `codeMatches` to (verify current line numbers by grep; TCB's line references are from
  2026-08-27 @ 1cf58d5, and same-day commits have already landed since).
- `Assembler.lean:349-350` (or current location — grep for `serializeInstructions`) — the boundary
  TCB names as "everything past this has zero theorems."
- `Emitter.lean:196` — `entryRva`/`imageBase` honored by `load`, ignored by `emit`.
- Grep for `computeSectionLayout`, `.getD curRip`, `dllCharacteristics`, `isValidEntryState` to
  locate the other hazards TCB catalogs before starting.
- `TCB.md` §T5 in full — written to be self-contained; read it directly rather than relying solely
  on this file's summary.
- `docs/REVIEW.md` Law 5 (stop-and-design — governs this task's design-review requirement), Law 13
  preference order (unrepresentable-by-construction over kernel theorem over linter over control
  vector — `codeMatches` should aim for the first tier).

## Notes

- 2026-08-27: priority 9.0 — TCB ranked-top-8 #1 (T5, 'the emitter last mile' — 1,255 lines / 0 theorems, 2 of 5 emitted PEs never executed) — the single largest correctness gap in the ledger.
- 2026-08-27: related: [TC19] — TC14 (emitter connection theorem) and TC19 (HardwareHarness self-hosting) are sibling self-hosting plays: both replace a hand-written/unlinked artifact with one derived mechanically from the same machinery it's meant to validate (PE bytes from `emit`/`serializeInstructions`; oracle machine code from the registry's `.encode`).

_(none yet — first entries append here as work begins; this is Law-5-class work, so consolidate
Notes into a real `docs/` design doc before implementation, and route that doc through a fresh-agent
design review before dispatching implementation.)_
