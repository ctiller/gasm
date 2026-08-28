---
id: TC12
title: Connection-theorem linter + known twins
status: ready
blocked_on: ""
after: [TC5]
related: [PA1]
bar: ""
track: trust-core
priority: 7.2
priority_set: 2026-08-28T02:00:00Z
design: ""
design_review: ""
date: 2026-08-27
---

# TC12: Connection-theorem linter + known twins

## Context

This task executes Law 12 (`docs/REVIEW.md`, "Connection Theorem Mandate — No Unlinked
Twins"): **"Two encodings of the same model-level fact... may coexist ONLY when linked by a
kernel-checked connection theorem proving their equivalence. Unlinked duplication of model-level
fact is a critical defect."** Law 12's stated preference order is (1) a single source of truth
from which other forms are derived; (2) where genuine re-encoding is necessary, a connection
theorem proving equality over the entire shared finite domain; (3) anything else fails review.
D4 (PLAN.md Decisions) names the two-part strategy this task implements: **"Duplication:
connection theorems + linter, PLUS review-protocol audit on top (embedding-similarity triage as
tooling extension)."** TASKS.md's one-liner names the concrete, already-cataloged twins this
task must close: **"connection theorem linter + known twins (RFC1951 ×3, compress/
compressFixed, CRC asm dup, clenOrder chain) — after: TC5."**

### Why TC5 gates this

The `after: [TC5]` edge matters here for the same reason it matters for TC10/TC11: a linter that
detects duplication is only a *gate* (per Law 13's own framing — "a gate nothing invokes binds
nothing") once something invokes it on every relevant change, which is what TC5's single entry
point provides.

### The known twins, named precisely (PLAN.md Phase 5 + findings ledger)

PLAN.md's Phase 5 ("Duplication — Law 12 execution") and its findings ledger together give the
specific, already-identified instances this task's linter must catch and whose connection
theorems it must verify exist (or author):

1. **RFC 1951 length/distance logic, duplicated three ways**: the lookup tables in
   `Deflate.lean` (grep-confirmed present: `Stdlib/Zlib/Deflate.lean`), the closed-form
   `encodeLength`/`encodeDistance` functions (grep-confirmed present in
   `Stdlib/Zlib/Equivalence.lean` and `Stdlib/Zlib/Gzip.lean` — confirm exact locations by grep
   at implementation time, since these are the "closed-form" half PLAN.md contrasts against the
   table), and the assembly branch trees realizing the same length/distance encoding in
   `Zlib/Windows.lean`. Three independent encodings of the same RFC-1951-mandated fact, with no
   stated connection theorem linking them as of this writing.
2. **`compress` vs. `compressFixed`** (`Deflate.lean`) — two DEFLATE compression routines whose
   relationship (is `compressFixed` a specialization of `compress` under a fixed-Huffman
   assumption? a genuinely parallel implementation?) is not currently stated as a proven
   equivalence.
3. **The CRC32 assembly duplication**: `crc32SymbolicProgram` (grep-confirmed present at
   `Stdlib/Zlib/Windows.lean:36`, used at two call sites — `Stdlib/Zlib/Windows.lean:804,2214`
   via `call_label "zlib_crc32"`, with the label itself defined at `:2287-2288`) versus whatever
   pure-Lean CRC32 spec/table it is meant to realize (grep for `crc32` outside `Windows.lean` —
   note MODEL_DEBT's auditor's-uncertainty section separately flags `adler32SymbolicProgram` as
   dead code with no asm ZLIB container, a related but distinct finding not to conflate with
   this one). This pairing is also directly relevant to PA1 (the crc32 pathfinder task, pulled
   forward specifically because it is "small, loop-heavy, dual-implemented → connection theorem
   for free, no syscalls" per PLAN.md's gaps register) — coordinate with whoever picks up PA1,
   since that task may produce (or need) exactly this connection theorem as a side effect of its
   own contract→asm→proof pathfinding work.
4. **The `clenOrder` 19-way branch chain vs. table**: `Deflate.lean:132` defines `clenOrder :
   Array Nat` (grep-confirmed present, a 19-entry permutation table used for the DEFLATE
   dynamic-Huffman code-length-alphabet ordering — consumed at `Deflate.lean:208`). The assembly
   realization of the *same* 19-value permutation exists in `Stdlib/Zlib/Windows.lean` as a
   flat sequence of `cmp`/`je` comparisons mapping a step index (`RCX`, 0..18) to a permutation
   index (`RDX`) — grep-confirmed present at `Windows.lean:1667` onward (comment: "Map step RCX
   to permutation index RDX"; note the branch chain does **not** reuse the identifier
   `clenOrder`, so a name-based grep for that literal string will not find the assembly side —
   search for the comment text or the permutation-index pattern instead). This is the exact
   pairing named in PLAN.md's findings ledger ("clenOrder 19-way branch chain (Windows.lean
   ~1667) vs table (Deflate.lean)") and confirmed still at the same location at time of writing.
5. **Duplicated xorshift RNGs**: `Gasm/Core/Rng.lean` versus a second xorshift implementation
   inside `Gasm/Targets/X86_64/Fuzzer.lean` (both grep-confirmed present) — PLAN.md's Phase-5
   list names this explicitly. Note also that `Stdlib/Zlib/GzipFuzzer.lean` defines its *own*
   third `FuzzRng`/xorshift64 struct (grep-confirmed present at `GzipFuzzer.lean:9-21`) — this
   task's scope should confirm whether this is a third unlinked twin PLAN.md's list didn't
   originally name, or whether it is intentionally independent (e.g. deliberately kept separate
   because it seeds a different oracle-facing fuzzer with different domain requirements) and
   should be documented as such rather than silently left out of the linter's known-twins list.
6. **gzip magic bytes, duplicated three ways** (PLAN.md Phase 5): `Gzip.lean` /
   `Zlib/Windows.lean` / `Zlib/Wasm.lean` — confirm current locations by grep; a constant this
   small (2 bytes, RFC-1952-mandated) is a good test case for whether the linter's detection
   threshold (see below) is tuned sensibly, since a 2-byte magic-number match risks being either
   trivially true everywhere or requiring the linter to reason about semantic role, not just
   byte-string length.

### The linter itself (D4, D12's tooling extension)

Per Law 12's own "Tooling obligation (backlog)" text: **"a linter (sibling of `check_refs.py`)
detects likely unlinked twins — repeated literal tables, repeated byte-string constants,
parallel same-shape definitions — and fails CI unless each detected pair is covered by a
registered connection theorem."** This is the mechanical half of this task; the six items above
are the concrete instances the linter must be validated against (a linter that doesn't flag any
of these six known-real twins on a clean checkout would itself be a failed control vector, per
Law 13(4)'s logic applied to linter-shaped gates rather than world-facing oracles). D4 also names
"review-protocol audit on top (embedding-similarity triage as tooling extension)" as a second,
softer layer — Law 12's own text calls this "belt and braces": Pillar 3's Factoring & DRY axis
catching semantic duplication the literal-matching linter structurally cannot see. This softer
layer is explicitly a triage aid for human/agent review, not itself a build-failing gate — do
not conflate the two tiers in this task's acceptance criteria.

## Deliverables & acceptance criteria

- A "connection theorem registry" concept (referenced in PLAN.md's Phase 2 stop-and-design list
  as "**Connection-theorem registry format** (Law 12) + twin-detection linter design" — check
  whether a design doc already exists for this registry format before inventing one; if not,
  this task's own design phase should produce it, since a registry format is exactly the kind of
  concept Law 5 requires be designed before the linter that consumes it is built).
- A linter (`scripts/`-sibling of `check_refs.py`, per Law 12's own text) that detects candidate
  unlinked twins by structural signal (repeated literal tables, repeated byte-string constants,
  parallel same-shape definitions) and fails when a detected pair has no corresponding entry in
  the connection-theorem registry.
- Validated against the six known instances named above as a mandatory control-vector set: the
  linter must actually flag each of RFC1951's triple duplication, `compress`/`compressFixed`,
  the CRC32 asm/spec pairing, the `clenOrder` table/branch-chain pairing, the RNG duplication
  (with the GzipFuzzer instance explicitly triaged as included or documented-exception), and the
  gzip magic-bytes triple, on a clean checkout before any connection theorems are authored — this
  is the linter's own positive-control demonstration (Law 13(4), applied to a linter rather than
  a world-facing oracle: a linter that has never been shown to actually catch a known-real
  instance of what it claims to detect is unverified in the same sense).
- Connection theorems authored for each of the six instances (or, where Law 12's preference-order
  item 1 applies — i.e. one form should simply be *derived* from the other rather than proven
  equivalent to it — a refactor collapsing the duplication instead of a theorem bridging it;
  state explicitly, per instance, which of Law 12's three preference-order tiers was applied and
  why).
- Wired into TC5's gate runner so the linter runs on every gate invocation, per the `after:
  [TC5]` edge.
- Completion report: for each of the six named instances, the connection theorem or refactor
  that closed it, plus confirmation the linter's positive-control demonstration (flagging all six
  on a clean pre-fix checkout) was actually performed and not merely asserted.

## Pointers

- `Stdlib/Zlib/Deflate.lean:132,208` (`clenOrder` table and its use site) and
  `Stdlib/Zlib/Windows.lean:1667` onward (the assembly branch-chain realization, identified by
  its "Map step RCX to permutation index RDX" comment, not by the `clenOrder` name — grep-
  confirmed both locations present and line-accurate at time of writing).
- `Stdlib/Zlib/Windows.lean:36` (`crc32SymbolicProgram`), `:804`, `:2214` (call sites via
  `call_label "zlib_crc32"`), `:2287-2288` (label definition) — grep-confirmed present; the
  asm-side CRC32 half of instance 3 above.
- `Gasm/Core/Rng.lean`, `Gasm/Targets/X86_64/Fuzzer.lean`, `Stdlib/Zlib/GzipFuzzer.lean:9-21` —
  grep-confirmed present; the three (not two — confirm PLAN.md's original "duplicated xorshift
  RNGs" note only meant the first two) xorshift implementations.
- `Stdlib/Zlib/Deflate.lean` — location of `compress`/`compressFixed` (grep to confirm current
  line numbers).
- PLAN.md, "Phase 5 — Duplication (Law 12 execution)" and the findings ledger's twin-list
  entries — the source of every named instance above.
- PLAN.md, "Phase 2 — Stop-and-design docs", the "**Connection-theorem registry format**" bullet
  — the design prerequisite this task may need to produce first.
- `docs/tasks/PA1-crc32-pathfinder.md` — the crc32 ∀-proof pathfinder task; likely produces or
  needs the same CRC32 connection theorem this task's instance 3 requires — coordinate rather
  than duplicate.
- `docs/REVIEW.md` Law 12 (full text, including its own tooling-obligation and review-protocol-
  audit subsections) and D4 in PLAN.md's Decisions section.
- `docs/adr/0005-connection-theorems-for-duplication.md` — confirmed present; the ratified ADR
  for this task's governing decision (D4). Read it directly for the ratified wording.

## Notes

- 2026-08-27: priority 6.5 — connection-theorem linter operationalizes Law 12 tree-wide and gates F6 (zlib-to-infinity); PA1 is its first real test case.
- 2026-08-27: related: [PA1] — PA1's crc32 pathfinder is explicitly a Law-12 connection-theorem shape (table-driven spec vs. inline per-bit assembly); it is the first real test case TC12's linter should be checked against once both exist.
- 2026-08-27 (oracle-debt audit, `docs/ORACLE_DEBT.md` Part 6): priority raised 6.5 → 7.2. Its
  known-twins list should also register the gzip-roundtrip duplication between
  `Stdlib/Zlib/Equivalence.lean` and `Spikes/Spike5Gzip/Equivalence.lean`, and the
  `bit_reversal_8_involution_inst`/`reverse_bits_8_involutive_inst` duplication, both surfaced by
  `docs/ORACLE_DEBT.md`'s audit (see `docs/tasks/PA16-codec-roundtrip-universal-soundness.md` and
  `docs/tasks/PA18-small-domain-decide-migration.md`).

_(none yet — first entries append here as work begins; the connection-theorem registry format
is new model surface (nothing like it exists yet) and is explicitly named in PLAN.md's Phase-2
stop-and-design backlog, so treat that piece as Law-5-class (real `docs/` design doc + fresh-
agent review before implementation); the linter implementation itself, once the registry format
is settled, is more mechanical and may be fine with an inline `## Design` section.)_
