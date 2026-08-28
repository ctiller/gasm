# Documentation cleanup — proposal

**Status**: this is a proposal, not a change. Nothing described here has been executed;
no file was added, edited, or deleted by the pass that produced it, other than this
document. Every disposition below is a recommendation awaiting the owner's ruling.

**Measurement pin**: every count, line number, and absence claim was measured against
commit `4ab1576` (this branch's merge of `main` at `f597a53`). `main` moved during the
audit — it is at `ef5407e` at the time of writing — so re-verify before acting on any
individual number. The findings are about document content and do not depend on the
exact tip.

---

## 1. Headline

The corpus is **182 tracked markdown files, 32,072 lines**. Every one of them was
written within the last 48 hours: `git log` puts the last touch on 149 files at
2026-08-27 and on 33 files at 2026-08-28, and **no file in the corpus is older than
that**. There is no archaeological layer here.

That single fact reframes the request. "Cruft" in a two-day-old corpus written by many
agents in parallel is not accumulated sediment — it is **concurrency residue**: documents
that were true when written and were falsified hours later by work landing on another
branch. The measurements bear this out:

- **Deletable volume is small.** After a file-by-file pass, the proposal deletes
  **zero whole files** and **96 lines** of genuinely duplicated, uncited prose. Even
  counting relocations and de-duplication, the corpus shrinks by roughly **530 lines,
  1.7%**.
- **Wrong volume is large.** 18 fenced Lean theorem statements name theorems that do not
  exist under those names; six normative documents describe mechanisms absent from the
  tree; one document denies machinery that exists and is cited as its specification;
  three documents state three different, all-wrong, sizes of the same allowlist; the
  hand-maintained status board in `TASKS.md` is wrong about **35 of 79** tasks.

**The corpus does not have a volume problem. It has a truth-maintenance problem.** The
recommendation is therefore weighted toward correction, status markers, and new
mechanical gates, not deletion. Section 8 states plainly what the deletion budget
actually is, so the owner can judge whether that answer is acceptable.

### Why deletion is so constrained here

Three mechanisms make most of this corpus load-bearing, and each was verified:

1. **`scripts/check_refs.py` is a required CI gate that resolves `/- REF: -/` citations
   to a file *and an anchor*.** It reports `Target file '<path>' not found` and
   `Anchor '#<slug>' not found` as errors and exits 1. There are **159 distinct cited
   anchors** across the corpus. Deleting a cited document, renaming it, or editing a
   cited *heading* fails the build.
2. **`scripts/check_record.py` is a required CI gate** whose `DANGLING_CROSS_REFERENCE`
   check requires every path cited from `PLAN.md`, `docs/adr/*.md`, `docs/tasks/*.md`,
   `TCB.md`, `MODEL_DEBT.md`, and `docs/REVIEW.md` to resolve to a tracked file. It also
   hard-fails on a *stale allowlist entry* — so deleting a file that an allowlist entry
   names breaks CI even when nothing links to it.
3. **ADR-0031 / PLAN.md D23 (`docs/adr/0031-flatten-not-history-scrub.md`)** rules that
   history will be dropped, and that "`PLAN.md`, `docs/adr/`, and `docs/tasks/` become
   the sole surviving decision history of the project". Under that ruling a completed
   task file is not a stale artifact — it is the only surviving record of why the work
   was done. That is why 79 of 79 task files come back `keep`.

Only **14 files in the whole corpus have zero inbound references of any kind**, and
three of those are standard GitHub community-health files. The corpus is densely
interlinked; it is not a pile of orphans.

---

## 2. Findings, most serious first

### S1 — Documents stating theorems that do not exist

`scripts/check_doc_facade.py` exists to catch documents claiming mechanisms nothing
provides. It has a known blind spot: `_strip_fenced_code_blocks` blanks every fenced
block before either pattern runs, so **a fabricated theorem displayed as Lean code is
invisible to it**. I swept all 182 files: **80 fenced Lean blocks, 135 declaration
headers, 62 whose declared name appears nowhere as a token in the 251-file `.lean`
tree.**

Restricting to the fabricated-proof shape — `theorem`/`lemma` only, which is what
carries the visual authority of checked code — gives **18 instances in 8 files**. Of
those, **13 have no disclosure of any kind**, neither a section-scoped nor a file-level
`**Status**:` marker.

The confirmed instance named in the brief, the x86-TSO ordering theorem in
`docs/TARGETS/X86_64.md` §3, is **already fixed** — commit `f597a53` retired it on
2026-08-28 and filed the gate gap as `docs/tasks/TC22-doc-lean-fence-facade.md`. §3 is
now the best example of the honest-disclosure pattern in the repository. What follows is
what remains after that fix.

**Two distinct shapes, and the difference matters for the fix:**

**(a) Fabricated — the name appears nowhere in the tree, even as a substring (5 of 18).**

| Location | Displayed theorem | Note |
|---|---|---|
| `docs/EQUIVALENCE_PROOFS.md` §4.1, §4.2, §4.3 | three fully-stated theorems over a `memcpy_program` | the string `memcpy` occurs in **zero** `.lean` files |
| `docs/REVIEW.md` §1.1 | the same `memcpy_callability`, as the worked example of `REF:` syntax | illustrative, but indistinguishable from a real citation |
| `docs/SOFTWARE_MODELING_SDLC.md` §1–§4 | 5 theorems + 7 defs/classes of a worked key-value/transaction example | pedagogical; no disclosure anywhere in the file |

`docs/EQUIVALENCE_PROOFS.md` is the most serious of these: it carries **107 `REF:`
citations**, making it the sixth-most-cited document in the tree, and its §4 displays
three complete theorem statements — functional equivalence with a separation-logic frame
condition, ABI callability, and memory safety — for a routine that does not exist. This
is a larger instance of exactly the shape that motivated TC22, in a more load-bearing
document.

**(b) Name drift — the doc drops a suffix the real theorem carries (7 of 18), and the
suffix is the part that matters.**

| Location | Doc displays | Tree actually has |
|---|---|---|
| `docs/STDLIB_ZLIB.md` §6.2 | `zlib_roundtrip_soundness`, `gzip_roundtrip_soundness` over `(data : ByteArray)` | `zlib_roundtrip_soundness_inst`, `gzip_roundtrip_soundness_inst` |
| `docs/STDLIB_ZLIB.md` §6.3 | `deflate_/zlib_/gzip_idempotent_canonical_roundtrip` | the same three with `_inst` |
| `docs/STDLIB_PNG.md` §6.2 | `png_idempotent_canonical_roundtrip` | `png_idempotent_canonical_roundtrip_inst` |
| `docs/SPIKES/SPIKE5_GZIP.md` §5 | `gzip_roundtrip_soundness` over `(data : ByteArray)` | `gzip_roundtrip_soundness_inst` |

The `_inst` declarations are **single-vector `native_decide` checks on one hardcoded
string**. `docs/STDLIB_ZLIB.md` §6.2's prose introduces them with "Every valid byte array
roundtrips losslessly through compression and decompression" and displays a universally
quantified binder the code has never had. `docs/SPIKES/SPIKE5_GZIP.md` §5 goes further
and adds "Discharged constructively with zero `sorry` and validated in automated test
suites."

The repository's own summary of Law 8, in `docs/README.md`, names this defect exactly:
*ground-instance checks are labeled `*_inst`, never presented as soundness theorems.*
Law 10 adds that they "MUST NOT be cited — in names, **docs**, or review artifacts — as
evidence that anything is verified."

**This is not undiscovered debt on the code side.** `docs/ORACLE_DEBT.md` rows 1–8 and
16–19 and `docs/PA16_CODEC_SOUNDNESS.md` catalogue all ten pointwise entries precisely
and honestly, and PA16 is the open task to close them. The defect is that the *normative
specification a newcomer reads* asserts what the *debt ledger* denies, and the spec
sections carry no marker pointing at PA16. One sentence per section fixes it.

**The sharpest single instance is not in either list above.**
`docs/SPIKES/SPIKE4_HTTP_SERVER.md` §5 names `spike4_windows_canonical_trace_equivalence`
and `spike4_wasm_canonical_trace_equivalence` — **neither exists**; the real theorems are
`spike4_{windows,wasm,linux}_{root,status,404}_trace_equivalence` — and asserts they
establish "that both distinct physical binaries execute identical verified protocol
semantics." `scripts/gate_allowlist.txt` lines 59–63 record that PA17 examined this and
found that widening to the real per-request domain **"would be FALSE"**, citing a
confirmed route-prefix-confusion counterexample. A document asserts a property that the
repository's own gate allowlist records as falsified. That file carries 55 `REF:`
citations and has no `**Status**:` marker.

### S2 — Prose describing mechanisms absent from the tree

Distinct from the fenced-block shape, and invisible to the linter for a different
reason. `MECHANISM_ABSENT` matches two syntactic shapes only: a trigger word followed
within 80 characters by an open parenthesis and then a backticked identifier, or one of
eight fixed "is implemented as/in/by"-family phrases. The prevalent shape in these
documents is **subject-first** — an identifier, then a verb — which neither pattern
matches. I confirmed this by running both regexes against the actual sentences.

Each of the following was verified by grepping the whole `.lean` tree:

| Document | Claim | Tree |
|---|---|---|
| `docs/TARGETS/TARGET_MODEL.md` §2, §3 | a `Gasm.Common.*` helper family and four capability predicates | `Gasm/` holds only `Core/`, `Effects/`, `Targets/`; **`Gasm/Common/` does not exist**; `UnlockedReadable`, `LockedExclusive` and siblings: zero hits |
| `docs/TARGETS/TARGET_MODEL.md` §1 | per-target slices with `Machine.lean`/`DSL.lean`/`Emit.lean` | none of those filenames exists anywhere; §1 is **`REF:`-cited 5×** |
| `docs/TARGETS/WINDOWS.md` §1.2 | a `WindowsCallerDiscipline` enforcing shadow-space and alignment before a call | zero hits; what exists is `WindowsFastcall` with a `shadowSpaceRequired := 32` **data field** — a recorded number, not an enforcement |
| `docs/TARGETS/WINDOWS.md` §2 | mechanically derived `.pdata`/`.xdata` unwind opcodes during PE serialization | zero hits for `pdata`, `xdata`, `UWOP_`, `RUNTIME_FUNCTION`, `unwind` |
| `docs/TARGETS/BARE_METAL.md` §5, §6 | TLB-invalidation proofs, a verified x86 IDT, ARM vector-table bindings | zero hits for `invlpg`, `lidt`, `VBAR_EL1`, `CR3`, `PageTable` — corroborated independently by `MODEL_DEBT.md` §F3 |
| `docs/TARGETS/LINUX.md` §2.3 | a `SyscallInterceptor` typeclass | zero hits; the real one is `ExternalCallInterceptor` |
| `docs/AUTHORING_ASM.md` §2.2 | an implementation-variant menu of `impl_compact`/`impl_fast`/etc. | all four: zero hits. Everything else the file names does exist |
| `docs/TARGETS/ARM.md` §4 | `gasm` restricting exclusive-monitor sequences to atomic-only blocks | there is no ARM backend at all |

`docs/TARGETS/WINDOWS.md` carries 43 `REF:` citations and `docs/TARGETS/BARE_METAL.md`
29, plus three `ci.yml` references. None of these files carries a `**Status**:` marker
for the affected sections.

### S3 — The inverted facade: a document denying machinery that exists

This is the finding I would put in front of the owner first, because the existing linter
is **structurally incapable** of catching it: `check_doc_facade.py` looks for claims that
overstate the tree. Nothing looks for claims that understate it.

`docs/MEMORY_HOOK.md` is the specification for the memory hook and carries **86 `REF:`
citations**, §3.3 alone accounting for 37. It states:

- §1: "this is a design document, not a report of built machinery. Nothing specified here
  exists in the tree unless a sentence explicitly says it was verified there"
- §2: "**Status**: none of the three exists; MH1/MH2/MH3 respectively."
- §3: "**Status**: unbuilt; MH1. Sketches below are design, not existing code."

MH1 landed. Verified: `Gasm/Targets/X86_64/Memory.lean` and `MemoryCell.lean` exist,
`Gasm/Targets/X86_64/MemoryFrame/` holds the frame-lemma set, `memAccesses` is a
defaultless field at `Instructions/Base.lean:66` and appears across 33 modules, and
`Instructions/Base.lean:40` cites `docs/MEMORY_HOOK.md` §3.3 *as the reason it has no
default*. `docs/X86_MEMORY_MODEL.md` §1.1 independently records that the access
descriptor landed. ADR-0040 approved the design in full.

`CONTRIBUTING.md` instructs contributors — explicitly including the external Linux
team — to trust `**Status**:` markers. Here they are systematically wrong in the
direction that causes duplicated work.

The same shape, less severe, appears in `docs/X86_ISA_EXPANSION_PREREQUISITES.md` §3 P4
— the anchor **cited 25×** — which states "**Status**: none of (a)–(c) exists today"
while all three landed: the fuzzer now derives its cases from
`Registry.allEncodableInstructions`, and `validationOracle` and `costProvenance` are
mandatory no-default fields with `lake exe check_x86_obligations` wired into `ci.yml`,
`run_gates.py`, and `REVIEW.md` §4.1 item 10.

Under Law 2 — once referenced, a section must be 100% realized — a section cited 25×
whose own text says it is unrealized is a contradiction that should not survive review.

### S4 — Staleness: documents contradicted by the current tree

Ranked by how likely the reader is to act wrongly on them.

1. **`docs/X86_ISA_EXPANSION_PREREQUISITES.md` §3 P3 marks B3 as `BLOCKING` and
   "unimplemented".** B3's frontmatter says `status: done`, `allTryDecoders` exists at
   `Decoder.lean:64`, and `docs/TARGETS/X86_64.md` §5 says "**Implemented**". This
   document has 128 `REF:` citations and is what an ISA-expansion team reads as the gate
   on their work; it currently tells them they are blocked when they are not.
2. **`canonicalizeTrace` exists; three documents say it does not.**
   `Gasm/Effects/CanonicalizeTrace.lean:149` defines it (commit `52facb1`), yet
   `docs/SYSTEM_EFFECTS.md` §6.3 says it "does not yet exist in the tree" and
   `docs/READ_BINDER_CONTRACT.md` §1 and §9 say the same, one of them quoting a grep that
   no longer returns what it claims.
3. **Three documents report three different, all-wrong sizes of the same allowlist.**
   `scripts/gate_allowlist.txt` today: **81 entries — 34 grandfathered, 2 finite-forall,
   45 axiom-only.** `docs/ORACLE_DEBT.md` says 80 (37/10/33);
   `docs/X86_ISA_EXPANSION_PREREQUISITES.md` §2 says 85 (36/1/48); `docs/CI.md` §8 says
   56 and §8a says 84. This is Law 12's unlinked-twin defect in prose: one fact,
   re-encoded four times, drifted four ways. ORACLE_DEBT's whole Part 2 matrix and Part 6
   ranking are stale as a consequence — eight of its ten finite-forall rows closed when
   PA13/PA18 landed.
4. **`docs/PRE_FLATTEN_CHECKLIST.md`'s front-page verdict is wrong.** It reads "NOT SAFE
   TO PUBLISH TODAY … 1,108 blocking findings … `references/` still contains all 1,049
   files". `references/` is deleted, `references.json` and `check_references.py` exist,
   `check_publishable.py` is wired into CI, `NOTICE` has been revised, and
   `.github/workflows/` exists — contradicting its §1.7 as well. The verdict is the part
   a reader acts on.
5. **`docs/CI.md` §7 and §11 say TC5's consolidated runner "has not landed".**
   `scripts/run_gates.py` is 1027 lines and is `REVIEW.md` §4.4 Gate 1's named standard
   invocation. §2's gate table also omits `check_x86_obligations`, `png_stability_fuzzer`
   and `x86_stability_fuzzer`, all of which `ci.yml` runs.
6. **A real gate hole found while checking that table**: `lake exe check_refs_coverage` is
   registered in `run_gates.py:402` and listed as required by `REVIEW.md` §4.1 item 2,
   but appears **zero times in `.github/workflows/ci.yml`**. This is not a documentation
   defect — CI is not running a gate the Laws mark required.
7. **`docs/PATHFINDER_CRC32.md`'s preamble asserts a repository state that does not
   exist**: that no commit on any branch touches `docs/adr/` or `docs/tasks/`. There are
   41 ADRs and 79 task files. It also names this review branch as "this branch" and pins
   line numbers to it. 34 `REF:` citations depend on the file.
8. **`docs/GRAPHICS_ARCHITECTURE.md` cites a vendored corpus that was deleted** —
   seven references to `references/vulkan/` and `references/spirv/` paths, including two
   cited as readable files. `references/` does not exist; ADR-0032 removed it.
9. **`docs/CALIBRATION_GOVERNANCE.md` §0 describes `scripts/regenerate_references.py` as
   the current Law 6 mechanism.** That script is deleted; `docs/CI.md` §7 records the
   deletion. `docs/tasks/TC5-gate-runner.md` names it as "verified present" in three
   places — that one is at least allowlisted, so it is documented rot rather than
   undetected rot.
10. **`docs/REFERENCE_INDEX.md`'s banner says its Law 4/6 amendments are "PROPOSED,
    pending the owner's ratification".** The migration landed and Law 6 was rewritten
    around it. 1,133 lines presented as a proposal are the as-built specification for
    `scripts/check_references.py`.
11. **`MODEL_DEBT.md` §B1 asks for a fix that landed** — the `X86_64.md` §3
    reconciliation, done in `f597a53`.
12. **`GRAPHICS_PREBUILD_AUDIT.md` §8** lists four housekeeping items that are all fixed
    in the tree. It is a dated audit, so this is defensible; a closure column would stop
    re-litigation.
13. **`docs/TARGETS/LINUX.md` §4 and `docs/SPIKES/SPIKE4_HTTP_SERVER.md`** describe spikes
    as "verified via constructive `native_decide` proofs" after commits `7a1a3e2` and
    `6024d95` retired `native_decide` from 23 spike trace-equivalence sites.

### S5 — Decision-record integrity

The ADR corpus is in better shape than the rest: all 40 ADRs carry a `## Provenance`
section, all `Status:` lines are well-formed, numbering 0001–0040 is contiguous with no
duplicates, and **no ADR's ruling is reversed by a later one**. No supersession marking
is needed anywhere. Four items are nonetheless worth the owner's attention:

1. **ADR-0002 reserved a question for the owner that has since been answered by a
   coordinator.** ADR-0002 says the stronger option — eliminating `native_decide`
   entirely — "has **not been decided** either way", and closes: "This question should be
   put back to the owner before any migration work assumes an answer either way."
   ADR-0037 then states "**The end state is zero allowlist entries.**" — and ADR-0037's
   own Provenance flags that framing as "the coordinator's synthesis", not owner words.
   Meanwhile the migration proceeded: `finite-forall` entries are down from 6 to 2 and a
   recent commit retired `native_decide` from 23 sites. The reserved question appears
   nowhere outside ADR-0002 itself. **This is the item to rule on first.**
2. **ADR-0008 forbids what ADR-0039 authorises, and ADR-0008 does not say so.**
   ADR-0008: models "grow only on spike demand, never speculatively or in bulk", and
   "'Complete the ISA' is explicitly ruled out as a goal at any point in the roadmap."
   ADR-0039 opens by naming a large x86 ISA expansion as "an eyes-open departure from that
   discipline". ADR-0039 cites ADR-0008 and bounds the exception; ADR-0008 carries no
   marker that an exception was granted, and it is the more widely cited of the two.
3. **ADR-0038 defers Law 13 without citing Law 13.** It rules "The ratchet gate is not
   built now" and reconciles this in substance ("reduce, demonstrate, then ratchet"), but
   never mentions ADR-0009 or Law 13, and silently resolves an explicit open item in
   ADR-0037 without citing that either. Two cross-links close this.
4. **ADR-0024 was amended after acceptance**, outside the window the directory README's
   remediation note covers (it names 0001–0020). ADR-0035's Context confirms the edit in
   writing. Either the note's scope needs extending or the owner should rule.

Separately, three mechanical defects in the record apparatus:

- **`PLAN.md`'s six ADR links are all broken.** Every one uses `adr/NNNN-…` relative to
  `docs/`, but `PLAN.md` sits at the repository root. There are zero correct-form ADR
  links in the file, and no gate checks relative markdown links.
- **`D8` is unassigned.** PLAN.md defines D1–D7 and D9–D31. `check_record.py` check 1
  tests uniqueness, not contiguity. Worse, `docs/tasks/B1-build-perf-iteration2.md` cites
  a PLAN.md section "Ongoing workstream — build performance (D8)" twice; the real heading
  is "Ongoing workstream — build performance (Craig: critical to workflow)", and
  ADR-0029 correctly cites it with no D-number. B1 invented the reference.
- **`scripts/decision_record_allowlist.txt`'s header contradicts its own contents.** It
  states the valid checks are "no-adr, no-provenance, completeness-claim" and that
  dangling references "are never allowlistable". The file contains **17 `dangling-ref::`
  entries**, and `check_record.py` accepts that check name. In a file whose purpose is
  record integrity, this is worth one line to fix.

### S6 — Redundancy

The brief anticipated a Law 12 twin population across the 14 target documents. **That
hypothesis does not survive measurement, and the negative result is itself the finding.**
A heading-overlap matrix across `docs/TARGETS/` returns **zero headings shared by three
or more files**. The files share a template *shape* — machine state, then encoding, then
calling convention — but the content under those headings is disjoint per-target fact.
Law 12 governs two encodings of the same fact; a template is not a twin.

Quantified: of the 2,810 lines in `docs/TARGETS/`, 1,599 (57%) are not target
specifications at all but three standalone documents — a harness design, an empirical
reconnaissance report, and an oracle design. Of the remaining 1,211 lines across 11 spec
files, roughly **38 lines are genuinely duplicated cross-file fact** and ~1,107 are
unique. Consolidating to a shared document plus deltas would move ~66 lines of title
boilerplate while breaking anchors carrying 648 `REF:` citations. **Do not do it.**

The real duplications found across the whole corpus, all verified by reading both sides:

| Twin | Size | Recommendation |
|---|---|---|
| `docs/STDLIB_PNG.md` §5 restates `docs/STDLIB_ZLIB.md` §2/§3.1/§4.2 | 24 lines | **delete §5.** Zero `REF:` citations on any `#5*` anchor; the ZLIB anchors carry 61/55/13/4. Already drifted: ZLIB documents the package-merge encoder, PNG §5.3 still calls dynamic Huffman decode-only |
| `docs/STACK_DISCIPLINE.md` §1 and §3 restate `docs/API_STATE_MODELS.md` §1 and §4 | 32 + 40 lines | **delete both.** Zero `REF:` citations; only STACK_DISCIPLINE §2 is cited. Already drifted: §3 has five terminator constructors to §4's six |
| `CpuTerminator` transcribed a third time in `docs/OBLIGATIONS_AND_CAUSALITY.md` §2 | ~10 of 25 lines | trim to the two constructors its anchors are cited for |
| ELF64 header fields in `docs/TARGETS/LINUX.md` §3.1 and `docs/TARGETS/BARE_METAL.md` §3.1 | ~15 lines | the only genuine Law 12 twin in `docs/TARGETS/`, and the **code already unified it** — `Gasm/Targets/ELF/` exists and LINUX §4 says so. Doc-level drift behind a unified implementation |
| Two tracked, divergent copies of `intel_sdm_frontmatter.json` | 461,784 vs 464,430 bytes, different hashes | **out of scope but the most alarming thing found.** `docs/PRE_FLATTEN_CHECKLIST.md` §1.6 says this data "exists nowhere else on earth" once `references/intel_sdm/` is deleted — and it has already forked. Resolve before the flatten |

All three transcriptions of `CpuTerminator` are **already false**: they name a
`jmpIndirect` constructor that exists in no `.lean` file, and all three write
`obligations : List Obligation` where `Gasm/Core/State.lean:32` says
`List ObligationToken`. This is precisely Law 12's predicted failure mode, observed.

**Pairs the brief flagged that are not duplicates**, each checked by reading both:
`X86_MEMORY_MODEL.md` vs `X86_ISA_EXPANSION_PREREQUISITES.md` (model vs readiness
assessment, cleanly cross-referenced); `CI.md` vs `CONTRIBUTING.md` (no gate enumeration
in the latter); `ORACLE_DEBT.md` vs `MODEL_DEBT.md` (allowlist entries vs model-fidelity
gaps); `WORK_TRACKING.md` vs `TASKS.md`/`PLAN.md` (a proposal *about* them);
`SOFTWARE_MODELING_SDLC.md` vs `REVIEW.md` (methodology vs law); root `README.md` vs
`docs/README.md` vs `VISION.md` — 7% literal line overlap, and the three serve different
audiences.

One near-twin that is **correctly handled** and should not be "fixed": the 14 Laws are
summarised in `docs/README.md` and `CONTRIBUTING.md` as well as stated canonically in
`docs/REVIEW.md`. Both restatements carry an explicit precedence link — CONTRIBUTING
says "If a Law and any other document (including this one) ever disagree,
`docs/REVIEW.md` wins." That is Law 12's preference-order tier 2 done properly.

### S7 — Navigation and verbosity

- **`docs/README.md`'s index reaches 11 of the 33 loose documents.** Missing: every
  `STDLIB_*.md` (including the two highest-`REF:` specs after REVIEW — `STDLIB_ZLIB.md`
  at 269 and `STDLIB_HTTP11.md` at 146), `SYSTEM_EFFECTS.md`, `MEMORY_HOOK.md`,
  `X86_MEMORY_MODEL.md`, `GRAPHICS_ARCHITECTURE.md`, `CALIBRATION_GOVERNANCE.md`,
  `ORACLE_DEBT.md`. For a team whose only channel is the repository, the index is the
  map, and it omits two thirds of the territory. **This is the single cheapest
  high-value fix in the proposal.**
- **Review-process meta-content embedded in specifications** — real Law 13 evidence, but
  it belongs in the task file or ADR that owns it, not in the spec a newcomer reads:
  `docs/CI.md` §8 + §8a (81 lines of past-incident verification tables),
  `docs/TARGETS/WIN32_DIFFERENTIAL_HARNESS.md` revision notes + §12 (109 lines),
  `docs/PATHFINDER_CRC32.md` §0 revision log (82 lines, ~40 removable),
  `docs/ORACLE_DEBT.md`'s dated `task_frontier.py` output dump (38 lines, already
  contradicted by the tool).
- **Task-file boilerplate**: `G2`–`G9` share a byte-identical 5-line closing disclaimer,
  `N2`–`N7` a 3-line one, and `PA1`–`PA9` repeat a ~10-line Law 9/10 block plus an
  identical closing paragraph. ~140 lines. Harmless; listed for completeness of the
  arithmetic, not recommended as urgent.
- **The `PA10`–`PA18` cohort is consistently tight and evidence-dense**, in sharp
  contrast to `PA1`–`PA9`. Worth noting as the pattern to copy.

---

## 3. Recommended gates (Law 13: findings become gates)

Each finding class above should terminate in a mechanical prevention rather than a
one-time correction. Four are proposed; the first already exists as a filed task.

1. **`THEOREM_FENCE_ABSENT` — extend `scripts/check_doc_facade.py` to fenced blocks.**
   Already filed as `docs/tasks/TC22-doc-lean-fence-facade.md`, `status: ready`, with a
   measured precision analysis. My sweep confirms its scoping decisions and adds two
   facts it can use: (a) restricting to `theorem`/`lemma` yields 18 live instances, of
   which 13 have no disclosure at all — a tractable seeding set; (b) widening scope to
   `docs/adr/` and `docs/tasks/` would add **zero** new findings (those directories
   contain 3 Lean fence declarations between them, all present in the tree), so the
   linter's existing exclusion is correct and needs no change. **Recommend: raise TC22's
   priority.** It is the gate for the highest-severity finding class in this report.
2. **A `MECHANISM_ABSENT` shape for subject-first claims.** The existing patterns require
   a trigger word *before* a parenthesised backticked identifier. Every S2 finding is
   subject-first. A third pattern — a backticked identifier absent from the tree,
   followed within ~80 characters by an enforcement verb, with the same `**Status**:`
   escape — would have caught all eight. Precision must be measured before shipping, as
   TC22 did.
3. **An inverted-facade check.** Nothing detects a `**Status**: … does not exist` marker
   whose named identifier *is* present in the tree. This is mechanically the easiest
   check in the set — invert the existing presence test inside a Status-marked
   paragraph — and it catches the S3 class, where the failure mode is duplicated work by
   a team that cannot ask.
4. **A relative-link checker.** `PLAN.md`'s six broken ADR links and one broken link
   elsewhere are invisible today: `check_record.py` validates cited *paths* in its six
   scoped files but not markdown link targets generally, and no other gate looks at
   links. A ~30-line check over all tracked markdown would close it.

**Status**: none of the four checks exists in `scripts/` today; item 1 is designed and
filed as TC22, items 2–4 are proposed here and have no task file yet.

---

## 4. Do not delete

This section is the counterweight to the inventory. Each of the following looks
prunable by at least one mechanical metric and is load-bearing.

**Looks orphaned, carries heavy `REF:` citation.** These appear in no index and in no
ADR, task, or plan, so a link-based sweep would flag them — but renaming or deleting any
of them fails `check_refs.py`:
`docs/STDLIB_HTTP11.md` (146 citations, zero inbound links),
`docs/STDLIB_SMOLALLOC.md` (44), `docs/ARCHITECTURE.md` (61 lines, 1 citation, plus
named from `check_doc_facade.py` and an allowlist).

**Zero `REF:` citations, still load-bearing.**

- `docs/TARGETS/ARM64.md` (371 lines) — **the most dangerous file in this audit.** Zero
  `REF:` citations, zero inbound markdown links; by every mechanical metric a prime
  deletion candidate. Its own header states it exists "so a second team can pick up the
  actual target implementation without re-deriving any of this from scratch." It holds
  hand-assembled AArch64 bytes, exact QEMU invocations, observed serial output, and
  exit-code conventions that exist nowhere else and were produced by physical
  experiment. Deleting it destroys unreproducible work and severs a channel to a team
  that cannot be contacted.
- `docs/TARGETS/LINUX.md` — the Linux target's sole consolidated specification and the
  `design:` target of `docs/tasks/B2-linux-strategy.md`. Its §2.3 and §4 defects must be
  corrected **in place**, never by removing the section.
- `docs/ORACLE_DEBT.md` — cited by 23 task files; the sole recorded rationale for the
  existence and scoping of PA10–PA18, plus the finding that the axiom gate's `matchKey`
  authorises any axiom set for an `axiom-only` entry.
- `docs/REFERENCE_INDEX.md` — the specification that `check_references.py`,
  `check_refs.py`, `check_publishable.py`, `migrate_intel_sdm_refs.py` and
  `publish_allowlist.txt` all cite by name for anchor grammars and exit-code semantics.
- `docs/CALIBRATION_GOVERNANCE.md` — F2's `design:` target; its §9 licensing
  determination is cited *from Lean source* as the reason no coefficient may cite
  external timing tables.
- `docs/THIRD_PARTY_LICENSES.md` — describes a deleted tree, and is retained
  deliberately as the durable answer to "was anything non-redistributable ever in this
  repository", because the flatten will erase the history that would otherwise show it.
- `docs/BARE_METAL_VALIDATION.md` — the sole record of a deliberate "not yet" plus the
  five named triggers that would convert it into a task. A recorded "we decided not to
  build this" is exactly what an uncontactable team needs so they do not build it.
- `docs/GRAPHICS_ARCHITECTURE.md` — the only briefing on graphics scope; its §2.2 exists
  specifically so ruled-out targets "are not silently reintroduced".
- `docs/X86_MEMORY_MODEL.md` — MT1 and MT2 are formally blocked on it,
  `Instructions/Xchg.lean` points at it as a tripwire, and it is the honest replacement
  for the retired §3 fiction.
- `docs/PA16_CODEC_SOUNDNESS.md` — `gate_allowlist.txt` and two `Equivalence.lean` files
  cite its §4 L-numbers as the map of what remains.
- `docs/PRE_FLATTEN_CHECKLIST.md` — the procedure for an irreversible one-way operation.
  Mark its findings superseded; keep the Part 2 procedure.
- `docs/CI.md` — cited from `ci.yml`, `scheduled.yml`, the PR template, and by name from
  two `.lean` files; §5 is the sole written justification for a gate CI does not run.
- `CODE_OF_CONDUCT.md`, `SECURITY.md`, `.github/PULL_REQUEST_TEMPLATE.md` — zero inbound
  references by design; GitHub surfaces them by convention.

**Completed task files that are the sole surviving record.** Under ADR-0031 there is no
commit message to fall back on. The strongest cases, each holding measurements or
refutations found nowhere else in the tree: `B3` (measured build cascade 39→14 modules,
the +146s finding that kept the exhaustive dispatch check out of the hot path, and a
planted-mutation control); `B7` (full RED/GREEN control with the literal oracle
divergence, plus a still-open `wasiHostCall` bypass recorded only there); `TC22` (the
fence-precision measurement); `PA12` (the empirical refutation of its own premise, with
a minimal repro); `PA14` (measured SAT wall-time and a genuine rejected-alternative
analysis); `PA10` (the `bpp >= 1` precondition discovery); `TC9` (the mechanism behind
the fuzzer's stderr defect, where TCB has only the one-liner); `TC21` (the four seed
drift instances); `MD1` (the only record of a *rejected* DAG edge and the PageRank reason
for rejecting it — tuning knowledge for a tool in `scripts/`); `MH4` (the
`EXCEPTION_RECORD` offset map and a reasoned exclusion).

**The most tempting deletions break hardest.** `TC1`–`TC4` are the four task files that
most plainly restate PLAN.md and add least. But `TC4` is named in nine other tasks'
`after` lists and `TC2` in one. Deleting both produces 11 validation errors and exit 1
from `task_frontier.py`, plus `check_record.py` failures on two files' path citations.
Making that work would mean rewriting ten `after:` lists — falsifying the DAG in order
to delete a record.

---

## 5. Needs an owner ruling

Ordered by consequence. These are genuinely close calls or questions only the owner can
answer; I have not resolved them by guessing.

1. **ADR-0002's reserved question**: is eliminating `native_decide` entirely still open,
   or has it been decided? Migration is proceeding on a coordinator's synthesis that
   ADR-0037 itself flags as not owner words. (S5.1)
2. **ADR-0008 vs ADR-0039**: is the x86 ISA expansion a sanctioned exception to
   demand-driven growth? If so, ADR-0008 should carry a pointer, which under the
   directory's immutability rule means a new ADR, not an edit. (S5.2)
3. **`docs/TARGETS/TARGET_MODEL.md`** — is `Gasm.Common.*` abandoned design or unbuilt
   intent? This decides whether the fix is "correct the document to match the tree" or
   "add a `**Status**:` marker and keep it as Law 3 backlog". §1 is cited 5× and its
   directory scheme is wrong either way.
4. **`docs/tasks/TC7-tcb-ledger.md`** — frontmatter says `done`; the body states twice
   that its status is `designing` and explains why it is not done. One of the two is
   wrong.
5. **`docs/tasks/B2-linux-strategy.md`** — the Linux modules all exist (commit `d3c2fc2`)
   but the task sits at `design-review`. Was that landing B2's deliverable, or the second
   team's work that B2's acceptance bar has not ratified?
6. **`docs/AUTHORING_ASM.md`** — the only document with zero inbound references *and* no
   `**Status**:` marker *and* content contradicted by the tree. It is onboarding-shaped,
   which is exactly the category the brief says to flag rather than delete. Abandoned, or
   an intended on-ramp that never got linked?
7. **`docs/WORK_TRACKING.md`** (484 lines) — an honest, wholly un-enacted proposal for
   multi-team claiming and handoffs. Nothing references it; `docs/handoffs/` does not
   exist; `found_by` appears zero times in `task_frontier.py`. Ratify it, fold it into
   TC13, or retire it — but it is a considered proposal, not cruft, and it correctly
   predicted the `TASKS.md` drift measured in S4.
8. **`lake exe check_refs_coverage` missing from CI** — deliberate carve-out (it needs a
   full build, like the axiom gate, which *is* wired) or an oversight? This is a gate
   question, not a documentation one, but it surfaced here.
9. **ADR-0024's amendment** — extend the README's remediation note to cover it, or treat
   it as a violation to be recorded?
10. **The two `intel_sdm_frontmatter.json` copies** — which is authoritative? They differ
    by 2,646 bytes and by hash, and the checklist calls the data unrecoverable after the
    flatten.

---

## 6. Inventory

Every tracked markdown file in the corpus appears below with a disposition and a reason.
Dispositions are `keep`, `keep (correct …)`, `delete`, `merge into X`, `mark superseded`,
or `needs owner ruling`.

Two conventions: **section-level dispositions** are written as `keep (delete §N)` where
the file stays and a section goes; and where a reason names a defect, that defect is
detailed in section 2 above.

### 6.1 `docs/tasks/` — 79 files, 11,149 lines

Frontier-tool answer, stated up front: **the proposed deletion set is empty, so
`python scripts/task_frontier.py --validate` continues to report `[+] 79 task files
parsed and validated OK`, exit 0, and `check_record.py` stays green.** Fourteen files
need their `status` field corrected; that changes no edge and no count.

For completeness, the mechanics if the owner wants pruning anyway: only 15 files have
neither an inbound `after`/`related` edge nor a scoped cross-reference. Two of those
(`G9`, `MH3`) are named by `decision_record_allowlist.txt` entries, and deleting them
makes those entries stale — a hard failure in `check_record.py` even though
`task_frontier.py` would stay green. That leaves 13 mechanically-safe deletions, which
would report `[+] 66 task files parsed and validated OK`, exit 0, with no dangling edge —
at the cost of silently rotting eight `TASKS.md` rows and four `docs/` citations, since
`TASKS.md` is outside `check_record.py`'s scope. On content I recommend none of the 13.

| Task file | `status` | Disposition | Reason |
|---|---|---|---|
| `B1-build-perf-iteration2.md` | implementing | keep (correct `status`) | Status `implementing`; Notes say iteration 2 complete and TASKS.md marks it done. |
| `B2-linux-strategy.md` | design-review | needs owner ruling | Linux modules all exist (d3c2fc2) but status is `design-review`. |
| `B3-stage-b-decoder-modularization.md` | done | keep | Gold-standard evidence record: measured cascade, mutation control, gate numbers. |
| `B4-instruction-index-lookup.md` | ready | keep | Open; quadratic re-encode finding. |
| `B7-wasm-oob-trap-and-limits.md` | done | keep | Gold-standard RED/GREEN record plus a still-open `wasiHostCall` bypass gap. |
| `F1-rdtsc-harness.md` | ready | keep | Most path-cited file in the repo: 26 `costProvenance` strings name it. |
| `F2-calibration-data-governance.md` | designing | keep | Active design with a real design doc (CALIBRATION_GOVERNANCE.md). |
| `F3-staged-model-calibration.md` | ready | keep | Open. |
| `F4-parametric-cost-functions.md` | ready | keep | Open; F6 names it in `after`. |
| `F5-composable-cost-views.md` | ready | keep | Open (MODEL_DEBT E2). |
| `F6-zlib-to-infinity.md` | ready | keep | Owner-named forcing function. |
| `G1-graphics-doc-rework.md` | done | keep (correct `status`) | Verified landed; Notes still carry the pre-completion placeholder. |
| `G2-synchronization-dsl.md` | ready | keep | Allowlisted; two tasks name it in `after`. |
| `G3-fp-kernel-dsl.md` | ready | keep | Open design. |
| `G4-gpu-differential-harness.md` | ready | keep | Open design. |
| `G5-spirv-emitter-validator.md` | ready | keep | Allowlisted; the licensing surface depends on it. |
| `G6-vulkan-host-model.md` | ready | keep | Open design. |
| `G7-spike6-headless-compute.md` | ready | keep | Names BAR 4's trigger (ADR-0010). |
| `G8-gpu-pcie-cost-models.md` | ready | keep | Sole record of the 'consume F5's views, do not invent units' coordination call. |
| `G9-spike7-design.md` | ready | keep | Allowlisted (L22); deleting it makes that entry stale and fails check_record.py. |
| `MD1-model-spec-debt-intake.md` | ready | keep | Sole record of a rejected DAG edge and the PageRank reason for rejecting it. |
| `MH1-semantic-memory-hook.md` | ready | keep (correct `status`) | Status `ready`; Memory.lean, X86_64Fault and 33 `memAccesses` sites all landed. |
| `MH2-memory-uop-centralization.md` | ready | keep | Genuinely open (`MemCostModel` absent from the tree). |
| `MH3-capability-authoring-surface.md` | ready | keep | Allowlisted (L37); deleting it makes that entry stale and fails check_record.py. |
| `MH4-fault-oracle-veh-capture.md` | ready | keep | Sole record of the EXCEPTION_RECORD offset map and the width-exclusion rationale. |
| `MT1-atomic-primitives.md` | blocked | keep | Cited by a code tripwire in Xchg.lean gating the memory-operand form. |
| `MT2-multithreaded-machine-state.md` | blocked | keep | Open design; MT4 names it in `after`. |
| `MT3-causal-trace-generalization.md` | ready | keep | Sole record of the MT3/G2 vocabulary-consumption coordination duty. |
| `MT4-litmus-battery.md` | blocked | keep | Sole record of the MT4/XM2 division of labour. |
| `MT5-spike8-windows-linux.md` | ready | keep | Sole record of the 'no futex in v1' debt decision. |
| `MT6-baremetal-smp-design.md` | ready | keep | Sole record of the Phase-C cost rationale and the owner go/no-go requirement. |
| `N1-win32-harness-design.md` | designing | keep | Active design; N2 names it in `after`. |
| `N2-os1-readfile-writefile-model.md` | ready | keep (correct `status`) | Status `ready`; `splitBytes` landed and four hooks carry 'N2 fix'. |
| `N3-real-socket-model.md` | ready | keep | Open; MODEL_DEBT C5 confirms sockets still invented. |
| `N4-socket-e2e-spike4.md` | ready | keep | Open. |
| `N5-spike4-reactive-verified.md` | ready | keep | Open. |
| `N6-networking-buildout.md` | ready | keep | Names BAR 3's trigger (ADR-0010). |
| `N7-constant-time-contract-class.md` | ready | keep | Open third contract shape (MODEL_DEBT F2). |
| `N8-spike4-stack-buffer-overflow.md` | ready | keep (correct `status`) | Status `ready`; fix applied and cited in past tense from five REF comments. |
| `PA1-crc32-pathfinder.md` | implementing | keep | Highest-fanout PA node; cited by ADR-0003/0018/0019. |
| `PA2-step-lemma-composition-design.md` | ready | keep | Allowlisted; five tasks name it in `after`. |
| `PA3-step-lemma-composition-impl.md` | ready | keep | Thin, but PA9 names it in `after`. |
| `PA4-capability-adoption.md` | ready | keep | Cited by ADR-0004 and by check_doc_facade.py's absent-mechanism list. |
| `PA5-canonicalize-trace.md` | ready | keep (correct `status`) | Status `ready`; `canonicalizeTrace` landed at CanonicalizeTrace.lean:149. |
| `PA6-read-binder-contract.md` | design-review | keep | Carries the gate evidence and the deliberate-deviation rationale. |
| `PA7-verified-reactive-program.md` | ready | keep | Load-bearing in the facade linter's absent-mechanism list; four `after` edges. |
| `PA8-law9-migration.md` | ready | keep | Open. |
| `PA9-verified-program-derived.md` | ready | keep | Open. |
| `PA10-png-filter-scanline-invertibility.md` | done | keep | Sole record of the `bpp >= 1` precondition discovery and allowlist 80->75. |
| `PA11-trivial-checksum-empty-facts.md` | ready | keep (correct `status`) | Status `ready`; both targets landed as `simp; decide`, allowlist entries gone. |
| `PA12-wasm-trap-guard-and-leb128-witness.md` | done | keep | Sole record of the `partial def`-is-opaque refutation with a minimal repro. |
| `PA13-crc32-bittrick-lemmas-without-sat.md` | ready | keep (correct `status`) | Status `ready`; all three lemmas landed structurally, annotated 'Per PA13'. |
| `PA14-crc32-table-identity-structural-closure.md` | ready | keep (correct `status`) | Status `ready`; `G8bf_table` proven structurally at CRC32Equivalence.lean:449. |
| `PA15-fibonacci-loop-invariant-induction.md` | ready | keep (correct `status`) | Status `ready`; Windows half landed, Wasm half open -> `implementing`. |
| `PA16-codec-roundtrip-universal-soundness.md` | ready | keep (correct `status`) | Twelve entries open; `design:` field stale (PA16_CODEC_SOUNDNESS.md exists). |
| `PA17-spike3-spike4-domain-honesty.md` | ready | keep | Cited by two Lean REF comments and six allowlist entries. |
| `PA18-small-domain-decide-migration.md` | ready | keep (correct `status`) | Status `ready`; all four allowlist entries gone, predicted fallback taken. |
| `TC1-hygiene-branch.md` | done | keep | Restates PLAN.md 465-575; isolated in DAG. Sole record post-flatten (ADR-0031). |
| `TC2-wasm-oracle-branch.md` | done | keep | B7 `after: [TC2]`. Pointer to a `trapShortCircuit` allowlist entry is dead. |
| `TC3-law10-gates.md` | done | keep | Restates PLAN.md; isolated. Sole record post-flatten (ADR-0031). |
| `TC4-decoder-registry-gate.md` | done | keep | Nine tasks name it in `after`; deleting breaks nine DAG edges. |
| `TC5-gate-runner.md` | done | keep | Cited from ci.yml, CI.md, two ADRs; allowlisted. Names a deleted script. |
| `TC6-ci-establishment.md` | implementing | keep | Sole record of the CI-location ruling and the Linux link-flag finding. |
| `TC7-tcb-ledger.md` | done | needs owner ruling | Frontmatter `done`; body states twice that its status is `designing`. |
| `TC8-trust-fuzzer-buildout.md` | ready | keep | Open work; TCB routing table. |
| `TC9-fail-open-audit.md` | done | keep | Sole fuller diagnosis of the GzipFuzzer stderr/binary read defect; allowlisted. |
| `TC10-continuous-fuzzing-corpus.md` | ready | keep | Open work. |
| `TC11-mutation-coverage-tooling.md` | ready | keep | Open work. |
| `TC12-connection-theorem-linter.md` | ready | keep | Sole record of the third-RNG triage question. Four pointers stale by file. |
| `TC13-task-dag-tooling.md` | ready | keep | Spec for the fix to the TASKS.md drift finding; deleting it is self-defeating. |
| `TC14-emitter-connection-theorem.md` | ready | keep | Open; `codeMatches` confirmed absent from the tree. |
| `TC15-axiom-gate-closure-coverage.md` | implementing | keep (correct `status`) | Status `implementing`; work appears landed and REVIEW.md still calls the gap open. |
| `TC16-references-integrity.md` | done | keep | Allowlisted; self-corrects its own stale script pointer. |
| `TC17-vacuity-floors.md` | done | keep | `TC17` is cited in-code at five fuzzer vacuity floors. |
| `TC18-fuel-and-environment-honesty.md` | ready | keep | Open; `rawEmitForFuzzing` still has zero call sites. |
| `TC19-harness-self-hosting.md` | ready | keep | Open; 95 hand-written byte literals still present. |
| `TC20-wasm-emission-roundtrip.md` | implementing | keep (correct `status`) | Status `implementing`; most deliverables landed in LEB128.lean/Linker.lean. |
| `TC21-doc-facade-linter.md` | done | keep | Sole record of the four seed drift instances that motivated the linter. |
| `TC22-doc-lean-fence-facade.md` | ready | keep | Densest unique record here: the measured fence-precision analysis at 27ab4ed. |

_79 task files._


### 6.2 `docs/adr/` — 41 files, 2,357 lines

No ADR is superseded by another, so no `mark superseded` disposition appears. Deleting
any of these erases a ruling; the two `needs owner ruling` rows are unreconciled
tensions, not candidates for removal.

| ADR | Disposition | Ruling and reason |
|---|---|---|
| `README.md` | keep | Directory charter. Its ratification-order and immutability claims need two corrections. |
| `0001-vision-and-insights.md` | keep | Vision and the Three Insights - Ruling stands; no later ADR reverses it. |
| `0002-native-decide-restricted-to-exhaustive-finite-domains.md` | needs owner ruling | `native_decide` Restricted to Exhaustive Finite Domains - Its own reserved open question (eliminate `native_decide` outright?) is unresolved while migration proceeds. |
| `0003-universal-equivalence-via-modular-decomposition.md` | keep | Universal Equivalence via Modular Decomposition - Ruling stands; no later ADR reverses it. |
| `0004-adopt-core-capability-machinery-for-memory-safety.md` | keep | Adopt Core Capability Machinery for Memory Safety - Ruling stands; no later ADR reverses it. |
| `0005-connection-theorems-for-duplication.md` | keep | Connection Theorems for Duplication - Ruling stands; its named twin-detection linter is unbuilt and honestly tracked as backlog. |
| `0006-performance-model-as-strategic-asset.md` | keep | Performance Model as a Strategic Asset - Ruling stands; no later ADR reverses it. |
| `0007-worktree-agent-workflow-and-adversarial-review.md` | keep | Worktree Agent Workflow and Adversarial Review - Ruling stands; no later ADR reverses it. |
| `0008-demand-driven-model-growth.md` | needs owner ruling | Demand-Driven Model Growth - ADR-0039 authorises an ISA expansion that this ADR's 'never in bulk' clause forbids; the exception is unrecorded here. |
| `0009-findings-become-gates.md` | keep | Findings Become Gates - Ruling stands; no later ADR reverses it. |
| `0010-bar-triggered-deep-re-reviews.md` | keep | Bar-Triggered Deep Re-Reviews - Ruling stands; no later ADR reverses it. |
| `0011-dsls-as-unit-of-proof-leverage.md` | keep | DSLs as the Unit of Proof Leverage - Ruling stands; no later ADR reverses it. |
| `0012-no-review-archive.md` | keep | No Review Archive - Ruling stands; no later ADR reverses it. |
| `0013-tcb-ledger-and-trust-implies-fuzzer.md` | keep | TCB Ledger: Everything Trusted-but-Unprovable Gets a Fuzzer - Ruling stands; no later ADR reverses it. |
| `0014-observation-standard.md` | keep | Observation Standard Ratified - Ruling stands; no later ADR reverses it. |
| `0015-read-as-universal-binder.md` | keep | `read` as the Universal Binder - Ruling stands; no later ADR reverses it. |
| `0016-target-systems-and-scale.md` | keep | Target Systems and Scale - Ruling stands; no later ADR reverses it. |
| `0017-task-dag-operating-mode.md` | keep | Task-DAG Operating Mode - Ruling stands; no later ADR reverses it. |
| `0018-task-notes-consolidate-to-design.md` | keep | Task Notes Consolidate to Design - Ruling stands; no later ADR reverses it. |
| `0019-review-model-and-spec-before-implementation.md` | keep | Review Model and Spec Before Implementation - Ruling stands; no later ADR reverses it. |
| `0020-coordinator-work-is-reviewed.md` | keep | Coordinator Work Is Reviewed - Ruling stands; no later ADR reverses it. |
| `0021-coordinator-role-executive-function-and-mandatory-delegation.md` | keep | Coordinator Role: Executive Function and Mandatory Delegation - Ruling stands; no later ADR reverses it. |
| `0022-graphics-and-networking-priority-deliverables.md` | keep | Graphics and Networking as Priority Deliverables - Ruling stands; no later ADR reverses it. |
| `0023-merge-discipline-everything-reaches-main.md` | keep | Merge Discipline: Everything Reaches Main - Ruling stands; no later ADR reverses it. |
| `0024-trajectory-grounded-record-review.md` | keep | Trajectory-Grounded Record Review - Amended after acceptance, outside the README remediation note's stated 0001-0020 window. |
| `0025-model-tiers.md` | keep | Model Tiers: Implementors, Reviewers, and Coordinator Tier by Phase - Ruling stands; no later ADR reverses it. |
| `0026-large-systems-planning-gate.md` | keep | Large-Systems-Planning Gate - Ruling stands; no later ADR reverses it. |
| `0027-planning-output-lives-under-docs.md` | keep | Planning Output Lives Under `docs/` - Ruling stands; no later ADR reverses it. |
| `0028-adr-and-task-directory-structure.md` | keep | The `docs/adr` and `docs/tasks` Directory Structure - Ruling stands; no later ADR reverses it. |
| `0029-build-performance-workstream.md` | keep | Build-Performance Workstream - Ruling stands; no later ADR reverses it. |
| `0030-model-debt-ledger-directive.md` | keep | Model-Debt Ledger Directive - Ruling stands; no later ADR reverses it. |
| `0031-flatten-not-history-scrub.md` | keep | Flatten the Repository Rather Than Scrub History - Ruling stands; no later ADR reverses it. |
| `0032-no-third-party-prose-in-published-tree.md` | keep | No Third-Party Prose in the Published Tree - Ruling stands; no later ADR reverses it. |
| `0033-autonomous-saturated-dispatch.md` | keep | Autonomous, Saturated Dispatch to a Trustable Base - Ruling stands; no later ADR reverses it. |
| `0034-commit-trailer-must-not-fabricate-authorship.md` | keep | Commit Trailer Must Not Fabricate Authorship - Ruling stands; no later ADR reverses it. |
| `0035-decision-record-integrity-gate.md` | keep | Decision-Record Integrity Gate - Ruling stands; no later ADR reverses it. |
| `0036-no-urgency-framing-in-agent-briefs.md` | keep | No Urgency Framing in Agent Briefs - Ruling stands; no later ADR reverses it. |
| `0037-ratify-bv-decide-trust-tier.md` | keep | Ratify `bv_decide` as Law 10's Fourth Trust Rung - Ruling stands; contains no link to ADR-0002, whose law it amends. |
| `0038-standards-are-earned-before-imposed.md` | keep | Standards Are Earned Before They Are Imposed - Ruling stands; defers Law 13 without citing ADR-0009, and resolves an ADR-0037 open item without citing it. |
| `0039-x86-isa-expansion-prerequisites.md` | keep | x86 ISA Expansion Prerequisites - Ruling stands; no later ADR reverses it. |
| `0040-memory-hook-approved.md` | keep | Memory Hook Design Approved - Ruling stands; no later ADR reverses it. |

_41 files (40 ADRs + the directory README)._

---

### 6.3 `docs/` (loose) — 33 files, 11,914 lines

"REF" is the count of `/- REF: -/` citations from `.lean` files naming that document.
A non-zero REF count means deletion or renaming fails `check_refs.py`.

| File | Lines | REF | Disposition | Reason |
|---|---|---|---|---|
| `REVIEW.md` | 278 | 143 | keep | The 14 Laws; most-cited document in the tree. Fix the §1.1 example's fabricated theorem name. |
| `STDLIB_ZLIB.md` | 191 | 269 | keep (add Status to §6.2, §6.3) | Highest REF density in the repo. Five displayed theorems exist only in `_inst` form; point the sections at PA16. |
| `STDLIB_HTTP11.md` | 195 | 146 | keep | 146 citations and zero inbound links — looks orphaned, is not. Add to the index. |
| `EQUIVALENCE_PROOFS.md` | 185 | 107 | keep (add Status to §4) | §1 alone is cited 103×. §4's three `memcpy` theorems are the largest fabricated-theorem instance found. |
| `STDLIB_PNG.md` | 245 | 97 | keep (delete §5; add Status to §6.2) | §5 duplicates `STDLIB_ZLIB.md` and has zero REF citations on any `#5*` anchor; already drifted. |
| `MEMORY_HOOK.md` | 619 | 86 | keep (correct §1–§3.4 Status lines) | The inverted-facade case: denies MH1 machinery that landed and that cites this file as its spec. |
| `SYSTEM_EFFECTS.md` | 245 | 66 | keep (correct §6.3) | Says `canonicalizeTrace` does not exist; it landed at `CanonicalizeTrace.lean:149`. |
| `SPIKES.md` | 111 | 47 | keep | Sole home of the spike methodology, the Spike 1 spec, and the 1–8 roadmap. Spikes 1, 2, 6, 7 exist only here. |
| `STDLIB_SMOLALLOC.md` | 97 | 44 | keep | 44 citations, invisible from every index. Add to the index. |
| `PATHFINDER_CRC32.md` | 1134 | 34 | keep (correct preamble; trim §0) | Preamble asserts no ADRs or task files exist; there are 41 and 79. ~40 lines of revision log are relocatable. |
| `READ_BINDER_CONTRACT.md` | 332 | 33 | keep (correct §1, §8, §9) | Says PA5 and the wiring are absent; both landed (`ReadBinderWiring.lean`). |
| `X86_ISA_EXPANSION_PREREQUISITES.md` | 511 | 128 | keep (correct P3, P4, §2, §7.2, §8) | Marks a landed prerequisite `BLOCKING`; P4 (cited 25×) says three landed mechanisms do not exist. |
| `OBLIGATIONS_AND_CAUSALITY.md` | 107 | 14 | keep (trim §2) | Third transcription of `CpuTerminator`; reduce to the constructors its anchors cite. |
| `API_STATE_MODELS.md` | 226 | 12 | keep | Canonical home of `ComposedState` and the terminator type. Correct `List Obligation` to match `Gasm/Core/State.lean`. |
| `PA16_CODEC_SOUNDNESS.md` | 807 | 8 | keep | Live working doc, kept current; its §4 L-numbers are cited from `gate_allowlist.txt` and two `Equivalence.lean` files. |
| `CALIBRATION_GOVERNANCE.md` | 938 | 7 | keep (correct §0, §1) | F2's `design:` target; §9 is cited from Lean source. §0 describes a deleted script as the current mechanism. |
| `PROOF_CARRYING_ASSEMBLY.md` | 106 | 6 | keep | §1 cited 5×. Its fenced sketches are design; add a file-level Status line. |
| `MEMORY_PROVENANCE.md` | 79 | 4 | keep | Small, cited, no overlap with anything. Add a file-level Status line. |
| `VISION.md` | 313 | 4 | keep | Primary onboarding document; cited from 11 ADRs and 25+ tasks. |
| `X86_MEMORY_MODEL.md` | 369 | 3 | keep | Best Status hygiene in the corpus. MT1/MT2 are blocked on it; a code tripwire points at it. |
| `STACK_DISCIPLINE.md` | 119 | 2 | keep (delete §1 and §3) | Only §2 is cited. §1 and §3 are uncited, already-drifted twins of `API_STATE_MODELS.md` §1/§4. |
| `CI.md` | 502 | 2 | keep (correct §2, §3, §7, §8, §11; relocate §8/§8a) | Gate-of-record, cited from `ci.yml` and two `.lean` files, but drifted from both `REVIEW.md` §4.1 and `ci.yml`. |
| `ARCHITECTURE.md` | 61 | 1 | keep | Small enough to look mergeable; `Gasm/Core/Callable.lean` cites §2 and two scripts name the file. |
| `REFERENCE_INDEX.md` | 1133 | 0 | keep (correct status banner) | The as-built spec for four scripts and an allowlist, presented as a pending proposal. |
| `ORACLE_DEBT.md` | 414 | 0 | keep (refresh counts; drop the Part 6 snapshot) | Cited by 23 task files; sole rationale for PA10–PA18. Its allowlist counts and frontier dump are stale. |
| `PRE_FLATTEN_CHECKLIST.md` | 488 | 0 | keep (mark Part 1 §1.3/§1.7 and Step 1 superseded) | Procedure for an irreversible operation; cited by ADR-0031 and two scripts. Front-page verdict is wrong. |
| `THIRD_PARTY_LICENSES.md` | 477 | 0 | keep | Deliberately retained historical record; the flatten will erase the history that would otherwise answer it. |
| `GRAPHICS_ARCHITECTURE.md` | 364 | 0 | keep (correct 7 `references/` claims) | Only briefing on graphics scope; §2.2 exists to stop ruled-out targets returning. |
| `BARE_METAL_VALIDATION.md` | 350 | 0 | keep | Sole record of a deliberate "not yet" plus the five triggers that reopen it. |
| `SOFTWARE_MODELING_SDLC.md` | 209 | 0 | keep (add file-level Status) | Onboarding methodology; complements REVIEW rather than duplicating it. Its 12 worked-example declarations need one disclosure line. |
| `README.md` | 126 | 0 | keep (extend the index) | The index reaches 11 of 33 documents; the cheapest high-value fix in this proposal. |
| `WORK_TRACKING.md` | 484 | 0 | needs owner ruling | Honest, wholly un-enacted proposal; zero inbound references. Ratify, fold into TC13, or retire. |
| `AUTHORING_ASM.md` | 99 | 0 | needs owner ruling | Fully orphaned, partly contradicted by the tree, but onboarding-shaped — the category to flag, not delete. |

_33 files._

### 6.4 `docs/TARGETS/` — 14 files, 2,810 lines

| File | Lines | REF | Disposition | Reason |
|---|---|---|---|---|
| `X86_64.md` | 332 | 338 | keep | Most-cited document in the repository; §3 is now the model of honest disclosure. |
| `LINUX.md` | 115 | 79 | keep (correct §2.3, §4) | The Linux team's sole consolidated spec. Names a typeclass that does not exist; §4's `native_decide` claims are stale. |
| `WINDOWS.md` | 94 | 43 | keep (add Status to §1.2, §2) | Names an enforcement discipline and unwind machinery absent from the tree. |
| `BARE_METAL.md` | 148 | 29 | keep (add Status to §5, §6; unify §3.1) | CI-load-bearing. Paging/IDT/vector-table claims absent from the tree; §3.1 is the ELF64 twin. |
| `WASI.md` | 62 | 28 | keep | Cited; no defects found. |
| `WASM.md` | 64 | 26 | keep | Cited; no defects found. |
| `WASM_ORACLE_HARNESS.md` | 278 | 17 | keep | Cited code exists; the Law 4 resolution for a first-party oracle. |
| `TARGET_MODEL.md` | 74 | 5 | needs owner ruling | §2/§3 describe a `Gasm.Common.*` family that does not exist; §1's directory scheme is wrong and cited 5×. |
| `ARM64.md` | 371 | 0 | keep — **do not delete** | Explicit external-team handoff; unreproducible experimental data. Zero inbound references of any kind. |
| `SPIRV_VULKAN.md` | 133 | 0 | keep | Exemplary honesty: carries a Status note marking one section SUPERSEDED and one claim UNSUBSTANTIATED. Anchors G1/G2/G5/G6. |
| `WIN32_DIFFERENTIAL_HARNESS.md` | 950 | 0 | keep (relocate 109 lines of review meta) | Self-declares unimplemented; governs N2/N3. Zero REF is the correct state for a Law 5 design. |
| `ARM.md` | 79 | 0 | keep (add Status to §4) | Only ARM spec; `ARM64.md`'s stated prerequisite. §4 describes restrictions with no ARM backend. |
| `X86_32.md` | 62 | 0 | keep | Design-only, and cited *as* design-only from SPIKE8 §6.3. |
| `X86_REALMODE.md` | 48 | 0 | keep (add file-level Status) | Design-only, cited as such from SPIKE8 §6.3 and MT6. |

_14 files._

### 6.5 `docs/SPIKES/` — 4 files, 795 lines

| File | Lines | REF | Disposition | Reason |
|---|---|---|---|---|
| `SPIKE8_MULTITHREADING.md` | 513 | 0 | keep | Textbook file-level Status marker; anchors MT1–MT6, all six of which exist as tasks. |
| `SPIKE5_GZIP.md` | 104 | 53 | keep (correct §5) | Displays a universal theorem the tree has only in pointwise `_inst` form, with a present-tense discharge claim. |
| `SPIKE4_HTTP_SERVER.md` | 95 | 55 | keep (correct §5) | Names two theorems that do not exist and asserts a property the gate allowlist records as falsified. |
| `SPIKE3_SORT_LINES.md` | 83 | 34 | keep (renumber) | Two sections are both numbered `## 5.`; anchors do not collide, so this is cosmetic. |

_4 files._

### 6.6 Repository root, `scripts/`, `.github/` — 11 files, 3,047 lines

| File | Lines | Disposition | Reason |
|---|---|---|---|
| `PLAN.md` | 1114 | keep (fix 6 broken ADR links; assign or retire D8) | The epic tracker; traversed by `check_record.py`. Every ADR link in it is broken. |
| `README.md` | 294 | keep | Public front page; the honest "what works today / what is designed" split is the corpus's best writing. |
| `CONTRIBUTING.md` | 252 | keep | Documents the `**Status**:` convention the whole proposal leans on. |
| `MODEL_DEBT.md` | 269 | keep (close §B1) | Still-open ledger, traversed by `check_record.py`. §B1 asks for a fix that landed in `f597a53`. |
| `TASKS.md` | 178 | keep (regenerate, or correct 35 rows) | Hand-maintained board; 20 tasks absent and 15 markers contradict frontmatter. TC13 is the filed fix. |
| `TCB.md` | 121 | keep | Open trust ledger; cited 4× from `REVIEW.md` and traversed by `check_record.py`. |
| `GRAPHICS_PREBUILD_AUDIT.md` | 82 | keep (add a closure column) | Dated audit; four §8 items are fixed in the tree but the file reads as entirely open. |
| `CODE_OF_CONDUCT.md` | 133 | keep | Community-health file; zero inbound references by design. |
| `SECURITY.md` | 102 | keep | Community-health file; zero inbound references by design. |
| `scripts/build_baseline.md` | 405 | keep (consider moving under `docs/`) | B1's before/after evidence baseline, cited from ADR-0029 and six task references. Placement is the only oddity. |
| `.github/PULL_REQUEST_TEMPLATE.md` | 97 | keep | The only markdown in `.github/`; maps the PR checklist to the three-pillar protocol. |

_11 files._

---

## 7. Line-count arithmetic

### Corpus as it stands

| Category | Files | Lines | Share |
|---|---:|---:|---:|
| `docs/tasks/` | 79 | 11,149 | 34.8% |
| `docs/` (loose) | 33 | 11,914 | 37.1% |
| `docs/TARGETS/` | 14 | 2,810 | 8.8% |
| `docs/adr/` | 41 | 2,357 | 7.3% |
| repository root | 9 | 2,545 | 7.9% |
| `docs/SPIKES/` | 4 | 795 | 2.5% |
| `scripts/` | 1 | 405 | 1.3% |
| `.github/` | 1 | 97 | 0.3% |
| **Total** | **182** | **32,072** | |

### After the proposal

**Whole files deleted: zero.** The reduction is section-level.

| Change | Lines | Category |
|---|---:|---|
| Delete `STDLIB_PNG.md` §5 — uncited twin of `STDLIB_ZLIB.md` | −24 | removed |
| Delete `STACK_DISCIPLINE.md` §1 — uncited twin of `API_STATE_MODELS.md` §1 | −32 | removed |
| Delete `STACK_DISCIPLINE.md` §3 — uncited twin of `API_STATE_MODELS.md` §4 | −40 | removed |
| Trim `OBLIGATIONS_AND_CAUSALITY.md` §2 to its cited constructors | −10 | removed |
| Unify the ELF64 header twin across `LINUX.md` §3.1 / `BARE_METAL.md` §3.1 | −15 | removed |
| **Subtotal: genuinely duplicated, uncited prose removed** | **−121** | |
| Relocate `CI.md` §8 + §8a into the owning task files | −81 | moved |
| Relocate `WIN32_DIFFERENTIAL_HARNESS.md` revision notes + §12 into `N1` | −109 | moved |
| Trim `PATHFINDER_CRC32.md` §0's revision log | −40 | moved |
| Drop `ORACLE_DEBT.md`'s dated frontier-tool dump (regenerable) | −38 | moved |
| **Subtotal: review meta-content relocated out of specifications** | **−268** | |
| De-duplicate task-file closing boilerplate across `G2`–`G9`, `N2`–`N7`, `PA1`–`PA9` | ~−140 | removed |
| **Total reduction** | **~−529** | |
| Additions: `**Status**:` markers, corrected Status lines, index entries, closure columns | ~+120 | added |
| **Net** | **~−409 (−1.3%)** | |

| | Files | Lines |
|---|---:|---:|
| Before | 182 | 32,072 |
| After | 183 (this proposal) | ~31,663 |

### The honest reading of these numbers

The owner's premise was that much of this should be deleted. **The measurement does not
support that.** The deletable-with-confidence volume is 121 lines — 0.4% of the corpus.
Even counting relocation and boilerplate de-duplication, the corpus shrinks by about
1.3%.

What the corpus has instead is roughly **1,200 lines that are wrong**: 18 fabricated or
drifted theorem statements, eight documents describing absent mechanisms, one document
denying present ones, thirteen staleness findings, and a status board wrong about 35 of
79 tasks. Correcting those costs more effort than deleting them would, and it is what
the corpus actually needs.

If the owner's intent was specifically volume reduction, the honest options are all
policy changes rather than cleanup findings, and each has a stated cost:

- **Reconsider ADR-0031's flatten.** Constraint 3 above — task files as sole surviving
  record — is what forces 79 of 79 to `keep`. If history is preserved instead, roughly
  15 completed task files become prunable, worth about 1,800 lines.
- **Split `docs/` into `spec/` and `record/`.** The audit ledgers, checklists, and
  dated assessments — `ORACLE_DEBT.md`, `PRE_FLATTEN_CHECKLIST.md`,
  `THIRD_PARTY_LICENSES.md`, `PA16_CODEC_SOUNDNESS.md`, `BARE_METAL_VALIDATION.md`,
  `build_baseline.md` — total ~3,400 lines and are a different kind of artifact from the
  specifications a newcomer reads. Moving them out of the specification namespace would
  shrink the apparent corpus without losing anything, at the cost of updating
  `check_publishable.py` and several allowlists.
- **Accept the review meta-content relocation above** as the routine hygiene it is.

I have not assumed any of these; each is an owner decision.

---

## 8. Things I was unsure about

Named rather than resolved by guessing.

1. **Whether `MEMORY_HOOK.md`'s Status lines are wholly or partly stale.** I verified
   `Memory.lean`, `MemoryCell.lean`, `MemoryFrame/`, the defaultless `memAccesses` field
   and 33 call sites. I did not verify MH1's full acceptance bar — the Law 13 negative
   control, the 14 frame lemmas, whether the raw memory field is actually sealed. Someone
   should diff MH1's completion evidence against §8's M0/M1 rows rather than take a
   blanket "stale" label.
2. **Whether `docs/AUTHORING_ASM.md` predates the current discipline or was abandoned.**
   No commit, ADR, or task mentions it — itself unusual — so I could not date its intent.
3. **`EQUIVALENCE_PROOFS.md` §2/§3/§5 have zero REF citations while §1 has 103.** §5's
   universal `VerifiedProgram` law does appear realized (the type occurs in 10 files), so
   this may be citations pointing at §1 that should point at §5, or genuine Law 3
   backlog. I did not sample enough of the 103 to tell.
4. **`ORACLE_DEBT.md`'s accuracy at row granularity.** I verified the aggregate counts
   moved and that PA13/PA18-shaped work landed. I did not re-derive its Part 2 matrix row
   by row, so I cannot say which specific entries closed.
5. **Whether the `related:` edges in task frontmatter are load-bearing enough to keep.**
   They carry weighted symmetric edges into the frontier tool's ranking and validation
   rejects unknown ids in them, so they are gate-relevant — but several look associative
   rather than structural. I did not evaluate any for removal.
6. **Whether `XM1`/`XM2` should exist as task files.** `MT1`, `MT2` and `MT4` are
   `blocked_on` them; no such files exist. This is legal, since `blocked_on` is not
   validated, and the files say so explicitly — but three tasks are gated on work with no
   file, no priority, and no frontier presence.
7. **Whether `ARM64.md`'s "second team" is the Linux team named in my brief.** If they are
   the same group, `ARM64.md` may be a pending handoff rather than a delivered one. I
   flagged both files either way.
8. **Whether `scripts/build_baseline.md`'s measurements are still valid.** It is dated,
   records 143 `.lean` files where the tree now has 251, and warns that its wall-clock
   numbers were taken under background load. I re-ran no timings.
9. **The ADR numbering-order question.** ADRs 0031–0034 record decisions D23, D25, D20,
   D21 — number order runs opposite to decision order across that block. Whether this
   violates the README's "ratification order" rule depends on whether ratification
   indexes the decision or the record. Genuinely ambiguous.
10. **I did not verify owner quotations against the session transcript**, which ADR-0024
    requires of a record review. Every attribution judgement in section S5 is
    internal-consistency reasoning over the ADR text alone. A compliant record review of
    this corpus would need the JSONL.
11. **The ~38-line cross-file duplication figure in `docs/TARGETS/`** is manual reading,
    not a mechanical diff. The 91%-unique conclusion is robust to a factor-of-two error
    in it; the specific number is not precise.

---

## 9. Method

- Corpus enumerated with `git ls-files`, never a filesystem walk, matching the
  convention the gate scripts use.
- `REF:` counts derived by grepping `docs/…\.md#anchor` patterns out of all 251 tracked
  `.lean` files.
- The fenced-block sweep tokenised all 251 `.lean` files with the same regex
  `check_doc_facade.py` uses, then matched declaration headers inside ` ```lean ` fences
  across all 182 markdown files, classifying each absent name as fabricated (absent even
  as a substring) or drifted (a real longer name contains it). The distinction changes
  the fix, so it is reported separately.
- Every absence claim in sections S1–S4 was re-verified by direct grep before being
  written down. Claims about mechanisms were checked against the tree, not against other
  documents.
- Four parallel readers covered `docs/adr/`, `docs/tasks/`, `docs/` loose, and
  `docs/TARGETS/` + `docs/SPIKES/` + root; their sharper findings were independently
  re-verified before inclusion here.
- Gates run at authoring time, all exit 0: `check_doc_facade.py`, `check_refs.py`,
  `check_record.py`, `task_frontier.py --validate`.
