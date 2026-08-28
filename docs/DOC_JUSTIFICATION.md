# Documentation justification — proposal

**Status**: this is a proposal, not a change. Nothing described here has been executed; no file
was added, edited, or deleted by the pass that produced it, other than this document. Every
disposition below is a recommendation awaiting the owner's ruling. Where this document names a
mechanism, count, or absence, it reports a measurement over the tree; it does not describe
machinery this pass built.

**Measurement pin**: every count is measured at commit `46b3a60`, where the corpus was 185 files
and 34,509 lines with 81 task files. **`main` moved continuously during the pass** — through
`938f4db`, `fc88dd2` and `c717eeb` — and by the time of writing `docs/tasks/` held **84** files,
three having landed after the audit began. A second agent is concurrently correcting factual
defects in several documents audited here. Re-verify any individual number before acting on it;
the three new task files are un-audited by this pass and are outside every count below. The
findings are about document *value* and do not depend on the exact tip.

**Relationship to the previous pass.** `docs/DOC_CLEANUP_PROPOSAL.md` asked *"what can we
delete?"*, answered *"nothing"*, and rested that answer on **cost of removal**: files were held
because `scripts/check_refs.py` resolves anchors into them, because `scripts/check_record.py`
hard-fails on a stale allowlist entry, because ADR-0031 makes task files the sole surviving
record. This pass inverts the burden and asks **"why does this deserve to exist?"**, ruling that
**"something cites it" is not a justification**. The previous pass's measurements are sound and
are reused here; its verdicts are not inherited.

---

## 1. Headline

The corpus is **185 tracked markdown files, 34,509 lines**. Every one is given an affirmative
justification and a form verdict below: `docs/tasks/` in §3, the model and specification cluster
in §4, targets/spikes/root in §5, the process and ledger cluster in §6, `docs/adr/` in §7.

Under the inverted burden, **25 files (4,655 lines) cannot be justified** and are proposed for
deletion, with ~370 lines of their content extracted into permanent homes first. Twenty are
completed task files; five are loose documents, including the previous audit itself. A further
~655 lines go at section level, nine consolidation groupings remove 13 more files, and ~1,269
lines move out of the specification namespace into a proposed `docs/record/`.

**Net: 185 → 148 files, 34,509 → ~29,900 lines (−13.4%).** The previous pass proposed −1.3% and
deleted no whole file. The corpus barely changed between the two passes; the difference is
entirely the burden of proof.

**The most important finding is not a file. It is that the mechanism the previous pass used as
its principal justification is itself the largest defect in the corpus.**

`docs/REVIEW.md` Law 1 states that "Un-cited code is strictly prohibited", and
`lake exe check_refs_coverage` fails the build on any Lean declaration lacking a `/- REF: -/`
annotation. Every declaration must therefore cite *some* markdown anchor. Law 2 then requires that
once an anchor is cited, the section behind it be **100% realized**.

Those two Laws together create a measurable — and here measured — incentive: **cite the emptiest
anchor that will resolve**, because an empty anchor is realized by anything and so carries no
Law 2 obligation. The observed citation distribution is precisely what that incentive predicts.
Citation counts therefore measure the pressure to cite, not the value of what is cited — which
means the previous pass's central evidence does not support the conclusion it was used for.
Section 2 quantifies this.

**A second finding reframes the owner's task-file criterion.** The owner's rule was that
"checklists for tasks that are complete are certainly not worth keeping". Measured: **only 1 of
the 81 task files (`B2`) contains checkbox syntax at all.** These files are not checklists. They
are forward-looking briefs — objective, acceptance bar, deliverables — with a `## Notes` section
where findings accumulate as work proceeds. The criterion still applies, but the operative test is
not "is the checklist ticked"; it is **"once the brief is spent, does the Notes section hold
anything a future reader needs?"** Section 3 applies exactly that test. It discriminates sharply:
Notes sections across the 81 files range from 0 lines to 113.

---

## 2. The circular-justification list

The previous pass could not produce this section by construction: it treated a resolving citation
as proof of worth, so it could not see a citation that exists only because a rule demanded one.
Five distinct shapes, each measured.

### 2.1 The citation sink — anchors that exist in order to be cited

**Corpus measurement.** 1,903 `REF:` citations across the `.lean` tree resolve to just **160
distinct anchors**, out of **1,802 markdown sections**. `scripts/check_refs.py`'s own summary
reports the same fact from the other side: *155/1670 design specification sections referenced
(9.3% coverage)*. **91% of the corpus is cited by nothing.** The twelve most-cited anchors absorb
**40% of all citations**.

**193 citations land on headings with at most one non-blank body line**; 145 of those on headings
with **zero** body — a bare heading above subsections, whose own content is nothing at all.

| Cited anchor | Citations | Own body |
|---|---:|---|
| `docs/TARGETS/X86_64.md#1-machine-state-model-sub-register-aliasing` | **57** | **zero lines** |
| `docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention` | **39** | one sentence |
| `docs/STDLIB_ZLIB.md#4-deflate-bitstream-engine-rfc-1951` | **31** | **zero lines** |
| `docs/STDLIB_SMOLALLOC.md#3-block-structure-freelist-state-model` | 16 | **zero lines** |
| `docs/TARGETS/WASI.md#2-syscall-signatures` | 12 | **zero lines** |
| `docs/REVIEW.md#42-pillar-2-semantic-integrity-adversarial-domain-gap-hunting` | 12 | one sentence |
| `docs/STDLIB_SMOLALLOC.md#4-linear-obligations-memory-invariants` | 7 | **zero lines** |
| `docs/STDLIB_HTTP11.md#3-parser-behavior` | 6 | **zero lines** |
| `docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications` | 3 | **zero lines** |
| `docs/STDLIB_ZLIB.md#6-formal-theorems-15-roundtrip-soundness` | 1 | **zero lines** |
| `docs/STDLIB_PNG.md#6-formal-theorems-15-roundtrip-soundness` | 1 | **zero lines** |

**The sharpest single instance.** `docs/TARGETS/X86_64.md#2-binary-instruction-encoding` is cited
by **127 declarations** — the most-cited anchor in the repository. Its entire content is one
sentence and a seven-line ASCII box diagram naming the fields of an x86-64 instruction. One
hundred and twenty-seven encoder declarations are, in Law 1's words, "completely defined and
motivated by" that box diagram.

Concentration is the general pattern. `docs/TARGETS/X86_64.md`'s 333 citations resolve to **5**
anchors; `docs/EQUIVALENCE_PROOFS.md`'s 104 resolve to **2**, with 103 on `#1`;
`docs/TARGETS/WINDOWS.md`'s 43 resolve to 3, with 39 on the one-sentence `#1`.

**Why this is circular rather than merely sloppy.** A declaration cannot be un-cited. When no
section specifies it, the author cites the nearest heading that resolves — and the *emptier* that
heading, the *safer* the citation, because Law 2 obligates full realization of whatever is cited.
An empty parent heading is the cheapest legal target. The heading is then kept alive by the
citation, and the citation exists only because Law 1 required one. Neither end justifies the other.

**The fix is in the citing code, not the document.** These sections should not be deleted —
`X86_64.md` §1's subsections hold the real sub-register aliasing table, and `WASI.md` §2's hold
the real syscall signatures. What is defective is 193 citations pointing at a parent heading
instead of the subsection that actually specifies the declaration. Retargeting them is a change to
`.lean` files, and it would make the citation graph mean something for the first time.

### 2.2 The transcription — sections whose body is the code that cites them

**356 citations (19% of all) land on anchors whose non-blank body is at least 50% fenced code or
ASCII art.** In these, the "specification" a declaration cites is a copy of the declaration.

| Anchor | Citations | Code share of body |
|---|---:|---:|
| `docs/TARGETS/LINUX.md#31-elf64-layout-header-structure` | 24 | **100%** — pure ASCII box art, no prose |
| `docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine` | 13 | **100%** |
| `docs/SYSTEM_EFFECTS.md#11-core-effect-typeclass-hierarchy-gasmeffects` | 12 | 95% |
| `docs/SPIKES/SPIKE4_HTTP_SERVER.md#1-high-level-architecture-protocol-state-machine` | 8 | **100%** |
| `docs/SYSTEM_EFFECTS.md#22-monadfilesystem-file-io-descriptor-typestates` | 6 | **100%** |
| `docs/SYSTEM_EFFECTS.md#23-monadprocess-lifecycle-environment` | 3 | **100%** |
| `docs/SYSTEM_EFFECTS.md#21-monadconsole-standard-io` | 2 | **100%** |
| `docs/MEMORY_PROVENANCE.md#1-core-principles-of-memory-provenance` | 2 | **100%** |
| `docs/STDLIB_SMOLALLOC.md#21-typeclass-definition` | 1 | **100%** |
| `docs/SPIKES.md#3-spike-progression-roadmap` | 26 | 90% |
| `docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture` | 25 | 75% |
| `docs/API_STATE_MODELS.md#3-the-callable-typeclass-automatic-derivation` | 1 | 96% |
| `docs/API_STATE_MODELS.md#4-basicblock-structure-target-parametric-terminators` | 3 | 95% |
| `docs/OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger` | 5 | 92% |
| `docs/STACK_DISCIPLINE.md#2-multi-abi-calling-conventions-stack-restoration-laws` | 2 | 92% |
| `docs/TARGETS/BARE_METAL.md#1-machine-model-in-freestanding-mode` | 4 | 92% |
| `docs/PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions` | 5 | 88% |
| `docs/MEMORY_HOOK.md#31-types-and-api` | 8 | 84% |

Law 1's stated purpose is that a declaration be "completely defined and motivated by its attached
`REF:` notes" and not "introduce concepts... not specified in the referenced markdown sections". A
section that is a transcription of the declaration satisfies the letter of that Law while
inverting its intent: the document is derived from the code, then cited as the code's source.

### 2.3 Code citing task files

**70 `REF:` citations in `.lean` files point at `docs/tasks/*.md`** — a work-tracking artifact,
not a specification.

| Cited task file | Citations from `.lean` |
|---|---:|
| `docs/tasks/PA1-crc32-pathfinder.md` | 29 |
| `docs/tasks/PA14-crc32-table-identity-structural-closure.md` | 18 |
| `docs/tasks/N8-spike4-stack-buffer-overflow.md` | 12 |
| `docs/tasks/PA17-spike3-spike4-domain-honesty.md` | 8 |
| `docs/tasks/PA13-crc32-bittrick-lemmas-without-sat.md` | 3 |

Citing sites: `Stdlib/Zlib/CRC32Equivalence.lean` (21),
`Spikes/Spike3SortLines/Windows/InstructionStepLemmas.lean` (20),
`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean` (9),
`Spikes/Spike4HttpServer/Equivalence.lean` (8),
`Spikes/Spike3SortLines/Windows/Equivalence.lean` (4), and three
`Spikes/Spike4HttpServer/*/Program.lean` files (8 between them).

**This is the purest instance of the closed loop.** A task file is a plan for work. Once code
cites it, `check_refs.py` makes it permanently undeletable — and four of the five (`PA13`, `PA14`,
`N8`, `PA17`) are exactly the completed task files section 3 proposes to retire. The citation
exists because Law 1 demanded one and no specification section was available to carry it; the file
survives because the citation exists.

**Fix the citation.** Each should point at the design document that owns the fact —
`docs/PATHFINDER_CRC32.md` for the CRC32 lemma work, `docs/SPIKES/SPIKE4_HTTP_SERVER.md` for the
Spike 4 fixes — or, where no such section exists, one should be written. Writing it is what Law 1
was for.

### 2.4 Frontmatter edges into completed work

24 surviving task files carry **28 edges** (19 `after:`, 9 `related:`) naming files this proposal
retires. The previous pass declined to delete `TC4` and `TC2` on exactly this basis: *"deleting
both produces 11 validation errors... Making that work would mean rewriting ten `after:` lists —
falsifying the DAG in order to delete a record."*

That reasoning inverts cause and effect. `after: [TC4]` means *"do not start until TC4 is done"*.
TC4 **is** done. The edge is a satisfied precondition — a scheduling constraint that has already
discharged, carrying no information a future reader acts on. Retaining a file so that a discharged
constraint still resolves is the closed loop; the edge is what should go. Section 7 lists all 28
edges with their disposition.

### 2.5 Allowlist entries naming files

`scripts/decision_record_allowlist.txt` names `F1`, `G1` (twice), `G2`, `G5`, `G9`, `MH3`, `PA2`,
`TC5`, `TC9`, `TC16`. `scripts/gate_allowlist.txt` names `PA17` six times, and names `MH1` only in
a comment recording that MH1's entries were **retired** (`gate_allowlist.txt:170`). Deleting a
named file makes its entry stale and hard-fails `scripts/check_record.py`.

This is coupling, not justification. Where the underlying gate debt is closed, the entry should be
removed together with the file; where it is open, the entry should name the document that records
the debt (`docs/ORACLE_DEBT.md`, `TCB.md`) rather than the task that filed it.

---

## 3. `docs/tasks/` — 81 files, 11,357 lines

### 3.1 The owner's criterion, corrected against the evidence

The owner's rule: *"checklists for tasks that are complete are certainly not worth keeping."*

**Measured: only 1 of the 81 files (`B2`) contains checkbox syntax.** These are not checklists.
Each is a brief — Context, Objective, Deliverables, Acceptance bar — plus a `## Notes` section
where dated findings accumulate as work proceeds. So the criterion applies, but the operative
question is:

> **Once the brief is spent, does the `## Notes` section hold anything a future reader needs?**

That test is measurable and it discriminates hard. Non-blank `## Notes` lines across the 81 files:
`B3` 97, `PA12` 75, `TC22` 56, `B7` 46, `PA6` 37, `TC6` 26 — and at the other end, **53 files
still carry the untouched placeholder** (*"none yet — first entries append here as work
begins"*), and six (`MT1`–`MT6`) have no Notes content at all.

Two consequences follow, and they cut in opposite directions:

1. **A file with an untouched Notes placeholder is not a completed checklist — it is an unspent
   brief.** It is the forward plan. Deleting it destroys work not yet done. This is why the
   deletion set below is much smaller than the raw count of `status: done` files might suggest.
2. **A completed file whose Notes never accumulated anything is pure residue.** The brief is
   spent, nothing was learned worth writing down, and the code plus the commit are the record.

### 3.2 Why the verdicts below are tiered

I found two errors while cross-checking a first cut of this list, and they are worth stating
because they show the failure mode:

- **`B4`** is `status: ready` and was initially classed as complete. Its deliverable — an
  instruction byte-offset index replacing the `O(M·N)` walk in
  `Gasm/Targets/X86_64/Semantics.lean` — **is not in the tree**; `instructionAtRip` still
  re-encodes on every step. Deleting it would have destroyed live work.
- **`TC15`** is `status: implementing` and was initially classed as complete. Its Notes read
  *"(none yet — first entries append here as work begins)"*. The work has not begun.

Both errors ran in the same direction: **trusting a status field, or a plausible inference, over
the tree.** The tiers below therefore separate what I verified from what I did not, and Tier C is
explicitly *not* a deletion recommendation.

### 3.3 Tier A — delete: complete, and nothing survives stripping (11 files, 1,350 lines)

Deliverable verified present in the tree; `## Notes` holds no finding, measurement, refutation or
handoff that is not recoverable from the code, the gate, or an ADR.

| Task | Lines | Notes | Verified deliverable | Why nothing survives |
|---|---:|---:|---|---|
| `TC1` | 111 | 5 | hygiene-branch work landed | Restates `PLAN.md`; isolated in the DAG; no finding recorded. |
| `TC2` | 114 | 5 | Wasm oracle branch landed | Same shape as TC1; its one pointer to a `trapShortCircuit` allowlist entry is already dead. |
| `TC3` | 124 | 6 | `scripts/check_gates.py` | The gate *is* the record; Notes adds nothing. |
| `TC4` | 158 | 7 | `allEncodableInstructions` in `Gasm/Targets/X86_64/Registry.lean` | The registry and its gate theorems are the record. Nine `after:` edges name it — all discharged (see §2.4). |
| `TC5` | 224 | 2 | `scripts/run_gates.py` (72 KB) | Two Notes lines. The runner is the record. Five `after:` edges, all discharged. |
| `TC16` | 89 | 7 | `scripts/check_references.py` | Self-corrects its own stale script pointer and nothing else. |
| `TC17` | 86 | 4 | `TC17` cited at five fuzzer vacuity floors | The in-code comments carry the rule; the task file restates it. |
| `G1` | 199 | 4 | graphics doc rework landed | Notes still carries only the pre-completion placeholder. Three `after:` edges, all discharged. |
| `MH1` | 93 | 3 | `Gasm/Targets/X86_64/Memory.lean`, `MemoryFrame/`; `scripts/gate_allowlist.txt:170` records MH1's entries **retired** | Five `after:` edges, all discharged. The design record is `docs/MEMORY_HOOK.md` and ADR-0040. |
| `PA11` | 68 | 3 | `crc32_empty` (`Stdlib/Zlib/CRC32.lean:66`), `adler32_empty` (`Adler32.lean:45`), both closed | Allowlist entries gone. The theorems are the record. |
| `PA18` | 84 | 3 | zero `PA18` entries remain in `scripts/gate_allowlist.txt` | The migration is visible in the allowlist's shrinkage. |

### 3.4 Tier B — extract, then delete the wrapper (9 files, 1,318 lines; ~250 lines relocated)

Complete, but `## Notes` carries something a future reader needs that exists nowhere else. The
verdict is **not** "keep the file": it is *move the finding to a permanent home, then delete the
wrapper*. A finding filed under a spent task is a finding nobody will find.

| Task | Lines | Notes | What survives | Proposed destination |
|---|---:|---:|---|---|
| `B3` | 295 | 97 | Measured rebuild cascade (39→14 modules), the +146 s finding that kept the exhaustive dispatch check off the hot path, a planted-mutation control | `docs/TARGETS/X86_64.md` §5 already narrates this work in detail — reconcile and fold in; measurements to `scripts/build_baseline.md` |
| `PA12` | 177 | 75 | Empirical refutation of the task's own premise (`partial def` is opaque) with a minimal repro | `docs/ORACLE_DEBT.md` |
| `TC22` | 146 | 56 | The measured fence-precision analysis that scoped the linter extension | `docs/CI.md`, or the header of `scripts/check_doc_facade.py` next to the check it justifies |
| `B7` | 114 | 46 | Full RED/GREEN control with the literal oracle divergence; a still-open `wasiHostCall` bypass recorded only here | `MODEL_DEBT.md` (the open bypass) and `TCB.md` |
| `PA10` | 97 | 20 | The `bpp >= 1` precondition discovery; allowlist 80→75 | `docs/STDLIB_PNG.md` (precondition), `docs/ORACLE_DEBT.md` (count) |
| `PA14` | 110 | 17 | Measured SAT wall-time and a genuine rejected-alternative analysis | `docs/PATHFINDER_CRC32.md` |
| `PA13` | 102 | 15 | The structural-closure route that avoided a SAT certificate | `docs/PATHFINDER_CRC32.md` |
| `TC21` | 109 | 15 | The four seed drift instances that motivated the facade linter | header of `scripts/check_doc_facade.py` |
| `TC9` | 168 | 8 | Fuller diagnosis of the `GzipFuzzer` stderr/binary-read defect, where `TCB.md` has only a one-liner | `TCB.md` |

**This is the category the previous pass got backwards.** It listed exactly these files as
`keep` *because* they hold unique content — and thereby left nine irreplaceable findings filed
under spent work items where no reader looking for them would think to look. The content is the
justification; the wrapper is not.

### 3.5 Tier C — do not delete without further verification (6 files, 743 lines)

Evidence ambiguous. Each *may* be complete, but I did not establish it to the standard that
justifies deletion. **These are listed as open questions, not recommendations.**

| Task | Lines | Status | The ambiguity |
|---|---:|---|---|
| `TC7` | 133 | done | Frontmatter says `done`; the body states twice that its status is `designing` and explains why it is not done. One of the two is wrong. `TC8` has `after: [TC7]`. |
| `B1` | 254 | implementing | Notes suggest iteration 2 complete, but the Notes also still carry a placeholder. Its evidence base is `scripts/build_baseline.md`, which would need to absorb the measurements. |
| `N8` | 82 | ready | Fix appears applied and is cited in the past tense, but **12 `REF:` citations from `.lean` point at this file** (§2.3). Those must be retargeted first; that is the real work item. |
| `PA15` | 83 | ready | `LoopInvariant.lean` exists for both Windows and Wasm; a prior audit recorded the Wasm half as open. Needs a direct check of both proofs. |
| `PA17` | 106 | ready | Six `gate_allowlist.txt` entries and 8 `.lean` `REF:` citations name it, which suggests live debt rather than completed work. |
| `TC20` | 85 | implementing | `LEB128.lean` exists; Notes still carry the untouched placeholder. Contradictory. |

**A correction to the brief I was given.** I was told `PA17` exemplified a handoff that earned its
keep — one agent recording a feasibility assessment, a later agent picking the task up from it.
**`PA17`'s `## Notes` section contains a single dated entry**, recording its priority and its
`after: [PA7, PA8]` sequencing rationale. It contains no feasibility assessment. Whatever handoff
occurred is not recorded there. I flag this rather than build on it.

### 3.6 Keep — live work (55 files, 7,946 lines)

Every one of these is an **unspent brief**: the work is not done, and the file is the plan. The
justification is uniform and it is affirmative — *a future implementer reads this to know what to
build, what the acceptance bar is, and why the approach was chosen* — so it is stated once here
rather than 55 times. Form verdict for all: **keep as-is**.

| Task | Lines | Status | Subject |
|---|---:|---|---|
| `B2` | 70 | design-review | Linux target foundation and strategy — ABI, ELF64 linker, syscall semantics |
| `B4` | 72 | ready | Pre-index instruction byte offsets to eliminate O(M·N) re-encoding — **verified not built** |
| `BR1` | 89 | ready | Borrow index — measurement first, then the context and the weaving DSL |
| `BR2` | 77 | blocked | Promote MH3's checked program from a fixed frame to a borrow index |
| `BR3` | 68 | blocked | Cross-thread capability partition and the no-unsynchronized-race theorem |
| `F1` | 230 | ready | RDTSC hardware harness — containment and rank criterion |
| `F2` | 182 | designing | Calibration-data governance (`MODEL_DEBT.md` E5) |
| `F3` | 205 | ready | Staged model calibration vs silicon |
| `F4` | 156 | ready | Parametric cost functions |
| `F5` | 161 | ready | Composable cost views |
| `F6` | 220 | ready | zlib-to-infinity epic — owner-named forcing function |
| `G2` | 164 | ready | Synchronization DSL design (Vulkan memory model, happens-before) |
| `G3` | 159 | ready | FP kernel DSL design (Deterministic Shader Profile) |
| `G4` | 163 | ready | GPU differential-validation harness design |
| `G5` | 158 | ready | SPIR-V emitter, Lean validator, registry-style shader gate |
| `G6` | 165 | ready | Vulkan host model and GPU capability mapping |
| `G7` | 195 | ready | Spike 6 — headless parametric compute to PNG |
| `G8` | 185 | ready | GPU/PCIe cost models and calibration |
| `G9` | 174 | ready | Spike 7 design — windowed swapchain, multi-loop reactive contracts |
| `MD1` | 163 | ready | Model/spec debt intake queue |
| `MH2` | 80 | ready | Memory uop centralization — one provenance-marked cost table |
| `MH3` | 97 | ready | Capability authoring surface v1 — checked programs, erasure, bypass ledger |
| `MT1` | 62 | blocked | Atomic primitives — `XCHG r64,[m64]`, `MFENCE` |
| `MT2` | 48 | blocked | Thread lifecycle and per-thread execution state |
| `MT3` | 59 | ready | Causal traces for threads — sync edges, causal ordering |
| `MT4` | 50 | blocked | Emitted-binary litmus battery — SB / MP / SB+MFENCE |
| `MT5` | 53 | ready | Spike 8 Phases A+B — Windows and Linux spinlock counter |
| `MT6` | 53 | ready | Bare-metal SMP bring-up — Stop-and-Design for Spike 8 Phase C |
| `N1` | 191 | designing | Win32 API differential harness design |
| `N2` | 227 | ready | OS1 — ReadFile/WriteFile/handle model rebuild vs real OS |
| `N3` | 212 | ready | Real socket model — replace invented hooks with harness-validated WinSock |
| `N4` | 137 | ready | End-to-end socket exercise of Spike 4 binaries |
| `N5` | 159 | ready | Spike 4 re-verified as a reactive verified program |
| `N6` | 215 | ready | Networking buildout — TCP semantics, HTTP/1.1 hardening, HTTP/2 framing |
| `N7` | 192 | ready | Constant-time / secrecy contract class design |
| `PA1` | 227 | implementing | crc32 pathfinder — the highest-fanout node in the PA graph |
| `PA2` | 181 | ready | Step-lemma library and composition calculus — design |
| `PA3` | 126 | ready | Step-lemma library and composition calculus — implementation |
| `PA4` | 179 | ready | Capability adoption (Law 11) |
| `PA5` | 223 | ready | `canonicalizeTrace` — causal-stamped observation normal form |
| `PA6` | 199 | design-review | Read-binder contract shape — 37 Notes lines of live design evidence |
| `PA7` | 184 | ready | Reactive verified programs — mandatory inner/outer proof pairs |
| `PA8` | 193 | ready | Law 9 migration — Spike 5 domain-shrinking, then Tier-1 quantification |
| `PA9` | 176 | ready | Verified program as derived theorem — routine contracts and linker facts |
| `PA16` | 109 | ready | Codec universal roundtrip soundness — twelve entries still open |
| `TC6` | 112 | implementing | CI establishment — 26 Notes lines of live findings |
| `TC8` | 146 | ready | Trust-implies-fuzzer buildout — one harness per TCB item |
| `TC10` | 132 | ready | Continuous fuzzing and regression corpus |
| `TC11` | 138 | ready | Mutation-coverage tooling for differential suites |
| `TC12` | 181 | ready | Connection-theorem linter and known twins |
| `TC13` | 141 | ready | Task-DAG checker — the filed fix for the `TASKS.md` drift |
| `TC14` | 121 | ready | Emitter last-mile connection theorem |
| `TC15` | 80 | implementing | Axiom gate closure coverage — **verified not started** |
| `TC18` | 105 | ready | Fuel-exhaustion honesty and `Environment` dead-field resolution |
| `TC19` | 102 | ready | Harness self-hosting — rebuild oracle machine code from the registry |

### 3.7 What `task_frontier.py --validate` would say

Today: `[+] 81 task files parsed and validated OK`, exit 0.

After **Tier A + Tier B** (20 files removed, 61 remaining), the tool would report
`[+] 61 task files parsed and validated OK`, exit 0 — **but only if the edge removals below land
in the same change.** `--validate` rejects unknown ids in `after:` and `related:`; it does not
validate `blocked_on:`.

**26 edges across 25 surviving files must be dropped** (20 `after:`, 6 `related:`):

| Surviving file | Edge to drop |
|---|---|
| `B1`, `B2`, `B4`, `F1`, `PA1`, `TC14`, `TC19` | `after: [TC4]` |
| `TC6`, `TC10`, `TC11`, `TC12`, `TC13` | `after: [TC5]` |
| `BR1`, `MH2`, `MH3`, `MT1`, `MT2` | `after: [MH1]` |
| `G2`, `G3`, `G4` | `after: [G1]` |
| `BR2` | `related: [MH1]` |
| `F1`, `MT4` | `related: [TC17]` |
| `PA8`, `PA15` | `related: [B7]` |
| `PA16` | `related: [PA10]` |

Every one of these is a **discharged precondition** (§2.4): the named task is complete, so the
constraint has already been satisfied and the edge records history, not scheduling. Dropping them
loses no scheduling information.

Also required in the same change: remove the `decision_record_allowlist.txt` entries naming `G1`
(two), `TC5`, `TC9`, `TC16`; and retarget the `.lean` `REF:` citations naming `PA13` (3) and
`PA14` (18) at `docs/PATHFINDER_CRC32.md`. Without the citation retarget, `check_refs.py` fails.

If Tier C were also deleted (26 files removed, 55 remaining), two further `related:` edges go
(`BR2`→`N8`, `MH3`→`N8`), one `related:` edge (`B4`→`B1`), one `after:` edge (`TC8`→`TC7`), the
six `gate_allowlist.txt` entries naming `PA17` become stale, and the 12 `.lean` citations naming
`N8` and 8 naming `PA17` need retargeting.

---

## 4. `docs/` — the model and specification cluster (17 files, 4,598 lines)

Measurements in this section were re-derived at `938f4db`, by which point `MEMORY_HOOK.md` had
grown 652→704 lines and `BORROW_MODEL.md` 887→1,129. Citation counts here count `/- REF: -/`
*lines*; §2's count distinct citing *declarations*. Rankings are identical either way.

| File | Who reads it, when, and what they cannot get elsewhere | Form verdict |
|---|---|---|
| `STDLIB_ZLIB.md` 246L | A proof engineer on the PA16 codec-soundness epic asking what is actually proven about compression. §6.2–§6.4 give the measured 55/108 dynamic-vs-fixed split and the exact hypothesis of the fixed-choice roundtrip theorem — the honest counterweight to five ground-instance names ending in `_soundness`. §1–§5 are RFC 1950/1951/1952 paraphrase. | **split, then merge**: §6 is the real document; §2–§5 → a `docs/STDLIB.md` chapter |
| `STDLIB_PNG.md` 255L | A Spike 6 / graphics author needing the PNG chunk grammar and filter algebra; §6.1's filter-roundtrip soundness with its `1 ≤ bpp` side condition and why the induction needs it. | **absorb into `STDLIB.md`; delete §5** |
| `STDLIB_HTTP11.md` 221L | Anyone routing untrusted network bytes. §1.2's *deliberate omissions* list — chunked, obs-fold, absolute-form each becoming an explicit parse error, never a hang — is a scope contract present in no `.lean` file. | **keep as-is** (chapter, if the merge happens) |
| `STDLIB_SMOLALLOC.md` 97L | An allocator implementer needing §3.1's byte-exact header offset table and the borrow discipline. | **merge into `STDLIB.md`** — too small to navigate to |
| `EQUIVALENCE_PROOFS.md` 191L | Every proof author, constantly. §1.1 is the canonical definition of "observable": deterministic equality vs refinement-plus-liveness, the reactive inner/outer pair, contract-trace vs audit-trace. Irreplaceable. | **absorb `SYSTEM_EFFECTS.md` §6** (see grouping D) |
| `MEMORY_HOOK.md` 704L | Instruction authors and the MH1–MH3 / PA4 implementers. §3.3's "one source, four consumers" argument; §3.2's correction block on why the structure seal does not privatize `casesOn`; §4.6's non-unification with the read binder. Reasoning, not transcription. | **keep as-is** |
| `SYSTEM_EFFECTS.md` 245L | Spec authors at SDLC stage 1 and PA5's implementer. §6 is the canonical observation algebra and per-effect coalescing table, cited from three other documents. | **split**: §6 → `EQUIVALENCE_PROOFS.md`; §1–§5 stay |
| `READ_BINDER_CONTRACT.md` 332L | PA5 / N2 / PA9 implementers and any reviewer applying Law 9. §5's argument for why the read quantifier must not be capped at buffer capacity — with Spike 4's 16-byte buffer against a 128-byte request as the worked case — is the most load-bearing reasoning in the effects cluster. | **keep as-is** — a design report, not a spec surface; a low citation count is *correct* for it |
| `API_STATE_MODELS.md` 226L | A newcomer to `Gasm/Core` wanting the composed state, the typestate monad and the callable class in one place. §5's transaction and UART case studies are the only motivating typestate examples in the repo. | **merge into `docs/CORE_SEMANTICS.md`** |
| `STACK_DISCIPLINE.md` 119L | Someone writing an ABI instance. §2.1's five-row matrix of callee-saved sets across SysV / MS x64 / cdecl / stdcall / **AAPCS64** is real content and is **ARM-team briefing material**. | **demote to a section** of `CORE_SEMANTICS.md`, keeping §2.1; drop §1 and §3 |
| `OBLIGATIONS_AND_CAUSALITY.md` 107L | Whoever implements PA5 / MT3 causality. §1.1's rationale for multiset subtraction (preventing double-free and ghost duplication) and §3.1's sequence diagram are the only non-Lean content. | **merge into `CORE_SEMANTICS.md`** |
| `PROOF_CARRYING_ASSEMBLY.md` 106L | A Law 11 reader wanting the permission vocabulary. §1.1's split/join inference rules are the only content the Lean does not carry. | **merge into `CORE_SEMANTICS.md`; delete §4** |
| `MEMORY_PROVENANCE.md` 79L | The Spike 3 / SmolAlloc author. §1.2's hierarchical-borrow rule is real design, which `BORROW_MODEL.md` §7.2 identifies as the pattern's first instance. | **merge** §1 into the memory cluster; §3 → `SPIKE3_SORT_LINES.md`; **delete §2** |
| `X86_MEMORY_MODEL.md` 369L, **0 REF** | The ARM team and the MT1–MT6 implementers. States x86-TSO once so MT1/MT2 cite rather than restate; §5's `XCHG` finding; §7's asymmetric falsification criterion; §8's rejected alternatives. | **keep as-is** |
| `BORROW_MODEL.md` 1,129L, **0 REF** | The owner (it answers seven verbatim directives), the ARM team (§13's architecture-neutrality analysis, cited from `TARGETS/ARM64.md`), and BR1–BR3. §1.1's 17-row verified-state table and §6's measured elaboration spike. | **keep as-is** |
| `ARCHITECTURE.md` 61L | **NONE FOUND.** | **delete** — see §4.3 |
| `SPIKES.md` 111L | Every spike author and both external teams: the roadmap plus §4's five-step verification protocol including the exit-code honesty rule. | **keep as-is** |

**`X86_MEMORY_MODEL.md` and `BORROW_MODEL.md` are the clean counterexamples to "citation equals
justification".** Both have zero `REF:` citations. Both are strongly justified — they are design
documents standing ahead of their consumers, and `X86_MEMORY_MODEL.md` says so in its own text.
Under the previous pass's framework they were held for the wrong reason; under a naive orphan
sweep they would be deleted. Neither framework sees them correctly. The affirmative question does.

### 4.1 Circular instances in this cluster

**The worst instance in the corpus: `docs/SYSTEM_EFFECTS.md#2-portable-effect-typeclass-specifications`.**
The heading has **zero body lines** — `## 2.` is immediately followed by `### 2.1`. Three
declarations cite it, including the network and clock effect instances:

- `Gasm/Effects/Network.lean:45`
- `Gasm/Effects/Trace.lean:83` — the `MonadNetwork` instance
- `Gasm/Effects/Trace.lean:77` — the `MonadClock` instance

**`MonadNetwork` — the effect typeclass Spike 4's entire HTTP server runs on — is specified
nowhere in `SYSTEM_EFFECTS.md`.** It appears only as rows in §6.1's coalescing table.
`MonadClock` appears only as a box in an ASCII diagram. Law 1 was satisfied by pointing at a
heading with nothing under it, and Law 2's "once referenced, must be 100% implemented" is
satisfied *vacuously*, because there is nothing to implement. This is the mechanism of §2.1
caught in a single instance, and the cost is real: the specification of a load-bearing typeclass
was never written, and the gate reports green.

**Transcriptions that have additionally gone stale.** These are worse than absent sections,
because `check_refs.py` passes over them:

| Anchor | Citing declarations | The drift |
|---|---|---|
| `OBLIGATIONS_AND_CAUSALITY.md#1-the-linear-obligation-ledger` | `Gasm/Core/Obligations.lean:22`, `:28` | Doc shows `inductive ObligationType` and `structure Obligation`. **Neither exists.** The tree has `IsObligation` and `ObligationToken`. |
| `OBLIGATIONS_AND_CAUSALITY.md#3-monotonic-causality-vector-clocks` | `Gasm/Core/Types.lean:41–64` (five declarations) | Byte-identical transcription of five declarations. Adds one sentence of framing. What a reader actually needs — that the memory model *generates* happens-before edges and the trace layer *projects* them — is in `X86_MEMORY_MODEL.md` §3, stated without a fence. |
| `STACK_DISCIPLINE.md#2-multi-abi-calling-conventions-stack-restoration-laws` | `Gasm/Core/ABI.lean:24` | Doc states the preservation law as `s_post.rsp = s_pre.rsp + wordWidth`. The tree states `s_post.stackDepth = 0`. **A different proposition.** |
| `PROOF_CARRYING_ASSEMBLY.md#1-capability-based-discrete-memory-permissions` | `Gasm/Core/Permissions.lean:30` (five declarations) | Same declaration, one bound written `2^64` in prose and `18446744073709551616` in code. |
| `MEMORY_PROVENANCE.md#2` | `Gasm/Core/Obligations.lean:41`, `:50` | Of four structures printed, only `ArenaPageToken` exists. |
| `STDLIB_SMOLALLOC.md#21-typeclass-definition` | `Stdlib/SmolAlloc/Spec.lean:194` | The doc block is the class declaration; the citer is an *instance*, not the class. |

**The `CpuTerminator` triple.** `API_STATE_MODELS.md` §4, `STACK_DISCIPLINE.md` §3 and
`OBLIGATIONS_AND_CAUSALITY.md` §2 each print the same inductive. **All three have drifted from
`Gasm/Core/CFG.lean:48–54`, in different directions** — the documents' `jmp`/`jcc` carry a type
parameter and proof fields; the tree has string labels, a depth, and one proof field. Three
markdown copies of one declaration, none of which matches it. This is Law 12's unlinked-twin
failure mode at document level, and the previous pass found two of the three but read them as a
size problem rather than a correctness one.

**Not circular, for the record** — checked and earning their anchors: `MEMORY_HOOK.md#31` (84%
fence, but explicitly labelled design sketches rather than transcriptions — a fence used as a
*proposal* is legitimate); `EQUIVALENCE_PROOFS.md#1`; `STDLIB_HTTP11.md` throughout;
`READ_BINDER_CONTRACT.md#2`.

### 4.2 Consolidation — does the boundary serve a reader, or did it serve a writer?

**A. `docs/STDLIB.md`, four chapters — recommend yes.**
*Reader need*: a stdlib author or external reviewer asking "what does the standard library
specify, and what is proven about it" today opens four files, one of which appears in no index and
is mentioned by no other document. They belong together because the codecs compose — PNG routes
through Zlib, and `STDLIB_PNG.md` §6.2 says so.
*Additional force*: this is where the previous pass's clean negative on duplication was wrong.
`STDLIB_PNG.md`'s title claims to cover Zlib, and its §5.1–§5.3 respecify Adler-32, CRC-32,
canonical Huffman and the block-type table already in `STDLIB_ZLIB.md` §2–§4, in a second and
slightly divergent voice. Two specifications of one library.
*Cost*: 48 anchors, ~619 citing `.lean` lines. The expensive merge, but mechanical — the file part
of each anchor path changes, fragments are unchanged if chapter headings keep their numbering. It
also sweeps up 9 already-malformed anchor variants.

**B. `docs/CORE_SEMANTICS.md`, absorbing `API_STATE_MODELS` + `STACK_DISCIPLINE` +
`OBLIGATIONS_AND_CAUSALITY` + `PROOF_CARRYING_ASSEMBLY` + `MEMORY_PROVENANCE` §1 — recommend yes,
strongly.**
*Reader need*: the composed state has seven fields, and five of them are documented in five
different files. A reader who opens any one of them cannot understand the structure it prints
without the other four. **This split is the clearest instance in the corpus of a boundary that
served a writer**: five parallel agents each needed a file.
*What it fixes*: three copies of `CpuTerminator`, two of the composed state, two ABI boxes, and
three independent drifts from `Gasm/Core/` collapse to one description each, with staleness
visible.
*Cost*: 16 anchors, 38 citing `.lean` lines. **The cheapest merge in the corpus relative to its
benefit** — two orders of magnitude less anchor churn than grouping A for a comparable gain.

**C. The memory cluster (`MEMORY_HOOK` / `X86_MEMORY_MODEL` / `BORROW_MODEL` / `MEMORY_PROVENANCE`),
~2,281 lines — recommend NOT merging the three large documents.**
Each answers a distinct question, carries a distinct verified-state table, and gates a distinct
task family (MH1–MH3 / MT1–MT6 / BR1–BR3). Critically, their `**Status**:` states differ:
`MEMORY_HOOK` §3 has landed while §4–§5 have not; the other two are entirely unbuilt. A merged
file would carry one preamble over three incompatible truth-states — which is precisely the defect
this corpus already suffers from. `BORROW_MODEL.md` §18 argues against splitting itself on
compatible grounds. **Narrow exception**: `MEMORY_PROVENANCE.md` §1 belongs with the cluster, §2
should be deleted, §3 belongs in `SPIKE3_SORT_LINES.md`. Cost: 4 citing lines.

**D. Fold `SYSTEM_EFFECTS.md` §6 into `EQUIVALENCE_PROOFS.md` — recommend yes.**
*Reader need*: the definition of "observable" is split across two files that cross-cite each other
in both directions — `EQUIVALENCE_PROOFS.md` §1.1 says the congruence "is defined once,
canonically, in `docs/SYSTEM_EFFECTS.md` §6", and `SYSTEM_EFFECTS.md` §6 opens by referring back.
**The documents themselves state that neither half can be read alone.**
*Direction matters*: moving §6 into `EQUIVALENCE_PROOFS.md` costs **12** citing lines; moving
§1.1 the other way costs 110. Move §6.

**E. `ARCHITECTURE.md` is not a document** — see below.

### 4.3 Deletion candidates in this cluster

**`docs/ARCHITECTURE.md` (61 lines) — delete. The only whole-file deletion outside `docs/tasks/`.**

- *Affirmative justification*: none found. §1's directory tree is factually wrong — it names
  `Gasm/Common/Memory.lean`, `Simulation.lean` and `ApiState.lean`, none of which exist; the real
  layout is `Gasm/Core/`, `Gasm/Effects/`, `Gasm/Targets/` — and is re-derivable by listing the
  directory. §2's flow diagram is a lower-fidelity copy of the one already in `docs/README.md`.
- *What breaks*: exactly one `REF:` line, `Gasm/Core/Callable.lean:25`, on the step relation.
  `check_refs.py` hard-fails.
- *The fix*: retarget that line to
  `docs/API_STATE_MODELS.md#3-the-callable-typeclass-automatic-derivation`, which is where the
  callable class is actually specified and which the *very next* citation
  (`Callable.lean:30`) already points at. The step relation is what the soundness field quantifies
  over, and §3 describes it. `ARCHITECTURE.md` §2 describes neither.
- *The 14 inbound `.md` mentions are all see-also links* from index-style documents. None depends
  on content. This is the shape the brief predicted: a file that looks connected and is not.

**Section-level deletions**: `MEMORY_PROVENANCE.md` §2 (three of its four structures exist
nowhere); `PROOF_CARRYING_ASSEMBLY.md` §4 (a worked `memcpy` example whose blocks appear in no
`.lean` file, and unlike `EQUIVALENCE_PROOFS.md` §4 it carries no disclosure); `STDLIB_PNG.md` §5
(the Zlib re-specification); the stale fences in `OBLIGATIONS_AND_CAUSALITY.md` §1/§2,
`STACK_DISCIPLINE.md` §1/§3 and `API_STATE_MODELS.md` §1/§4, which the grouping-B merge subsumes.

### 4.4 External-team constraint — flagged, not proposed for deletion

`X86_MEMORY_MODEL.md` (cited from `TARGETS/ARM64.md` and `SPIKE8_MULTITHREADING.md` — the ARM
team's only statement of what x86 settled and what ARM must decide); `BORROW_MODEL.md` §13 (the
AArch64 neutrality analysis); `STACK_DISCIPLINE.md` §2.1 (the AAPCS64 row); `STDLIB_SMOLALLOC.md`
§2.2 (the Linux page-source realization); `SPIKES.md` §4 (the protocol both teams follow).

### 4.5 Line arithmetic for this cluster

| | Files | Lines |
|---|---:|---:|
| Now (at `938f4db`) | 17 | 4,598 |
| After deletions (`ARCHITECTURE.md` 61; `MEMORY_PROVENANCE` §2 ≈30; `PCA` §4 ≈30; `PNG` §5 ≈25; stale fences ≈130 net) | 16 | ≈4,290 (−308, −7%) |
| After consolidation into `STDLIB.md`, `CORE_SEMANTICS.md`, `EQUIVALENCE_PROOFS.md`, `READ_BINDER_CONTRACT.md`, `SYSTEM_EFFECTS.md`, `SPIKES.md`, and the 3-file memory cluster | **9** | ≈4,355 |

**The line saving is small and is not the point.** The gain is 17 navigation targets reduced to 9,
three copies of one inductive reduced to one, and a specification a reader can finish. Note that
the memory cluster alone is 2,202 of the remaining 4,355 lines — half this cluster — and the
recommendation there is to leave it untouched.

---

## 5. `docs/TARGETS/`, `docs/SPIKES/`, and the repository root (28 files, 7,319 lines)

Re-measured at tip `fc88dd2`; `SPIKE4_HTTP_SERVER.md` grew 95→141 lines and `ARM64.md` 887→905
during the pass, both from the concurrent fixer, and both changes are improvements.

| File | Who reads it, when, and what they cannot get elsewhere | Form verdict |
|---|---|---|
| `TARGETS/X86_64.md` 332L | Two readers glued together. The registry-and-roundtrip-gate essay (238 of 332 lines) is read by anyone adding an x86 instruction: it explains why the roundtrip-case field has no default and what the registry audit does and does not cover. §3 is read by anyone about to believe the model has a memory-ordering story — it says plainly that it does not. §1–§2 (49L) serve no reader; the Intel SDM is vendored and cited directly two lines away. | **split** — the gate essay becomes its own document |
| `TARGETS/WIN32_DIFFERENTIAL_HARNESS.md` 950L | The N2/N3 implementer, before writing a line. Eight probe designs with witness-reachability arguments, and a reasoned *disagreement* with its own reviewer over an always-blocking pipe call that exists nowhere else. | **keep as-is** — best-justified document in the set |
| `TARGETS/ARM64.md` 905L | The ARM team, on day one. Hand-computed AArch64 instruction words, the exact QEMU invocation, observed serial output and exit code, and the finding that AArch64 needs no PVH note where x86 does. The generator was deliberately not committed. §13's "the memory-access surface is moving under you" is honest handoff content. | **keep as-is** |
| `TARGETS/WASM_ORACLE_HARNESS.md` 278L | Anyone touching the Wasm host oracle or semantics fuzzer. Its own preamble states the justification: first-party harness design with no W3C counterpart to cite, so Law 1 needs a real source and Law 4 forbids inventing one. | **absorb `WASM.md` + `WASI.md`**, renamed `WEBASSEMBLY.md` |
| `TARGETS/BARE_METAL.md` 148L | A bare-metal spike author and MT6's designer. The 16550 UART register map, the Xen PVH note fields, the ISA debug-exit encoding — operational facts that are tedious to re-derive and easy to get wrong. | **keep as-is**; §5/§6 (paging, IDT) are 10 lines of aspiration with zero citations and could go |
| `TARGETS/SPIRV_VULKAN.md` 133L | A G2/G3/G5 implementer. Post-G1 it is largely a **retraction register**: which claims were wrong, what replaced them, which task owns the replacement. | **keep as-is** — its value is negative space, which is legitimate |
| `TARGETS/LINUX.md` 115L | The external Linux team, and B2. §1.2's three-architecture syscall register table and §2.3's twelve intercepted syscall numbers are the only in-tree statement of the interception surface. | **keep as-is — FLAG, do not touch** |
| `TARGETS/WINDOWS.md` 94L | A Win64 spike author needing the shadow-space arithmetic. §1.2's two ASCII stack diagrams, with the derivation of why the reservation is 40 rather than 56 bytes, are genuinely load-bearing and easy to get wrong. | **keep as-is**; re-point §1's 39 citations at §1.1/§1.2 |
| `TARGETS/ARM.md` 79L | Nominally the ARM team — but `ARM64.md` §1 explicitly labels it design-only, and every fact in it is standard AArch64 the team already knows. Its Lean block describes a DSL that does not exist. | **merge into `ARM64.md`** as an appendix |
| `TARGETS/TARGET_MODEL.md` 74L | Anyone implementing a new target slice; §1 is the specification for the architecture typeclasses. | **keep as-is — do NOT merge** (see below) |
| `TARGETS/WASM.md` 64L | A Wasm emitter author needing the eleven section IDs. Correct and useful, but always opened alongside the other two Wasm documents. | **merge into `WEBASSEMBLY.md`** |
| `TARGETS/WASI.md` 62L | Same reader, same sitting. §3.1's vector layout and §4's errno values are the useful part. | **merge into `WEBASSEMBLY.md`** |
| `TARGETS/X86_32.md` 62L | **NONE FOUND.** No IA-32 code exists, and §3 describes an API that does not exist. | **merge into `docs/TARGETS/UNBUILT_TARGETS.md`** |
| `TARGETS/X86_REALMODE.md` 48L | Weak but non-zero: MT6 needs the real-mode trampoline story for SMP bring-up, and §2's segment-offset and A20 arithmetic is what that will build on. | **merge into `UNBUILT_TARGETS.md`**, keeping §2 verbatim |
| `SPIKES/SPIKE8_MULTITHREADING.md` 513L | MT1–MT6 implementers, and anyone deciding whether the memory model is demand-driven or speculative. §1 (why threads-and-join proves nothing) and §4's falsification table define what would *disprove* the model. | **keep as-is** — textbook Law 5 document |
| `SPIKES/SPIKE5_GZIP.md` 115L | A Spike 5 maintainer. §5, post-fix, is a genuine correction record: it names a theorem that never existed and says what is actually proved. | **keep as-is** |
| `SPIKES/SPIKE4_HTTP_SERVER.md` 141L | Same shape, and §4 as just rewritten is the best "what is actually proved versus what the theorem name suggests" writeup in the repository — including *why the universal claim is false*, not merely unproven. | **keep as-is** |
| `SPIKES/SPIKE3_SORT_LINES.md` 83L | Weakest of the four. §2.1 duplicates `WINDOWS.md` §1.1 applied to one call; a maintainer gets more from the Lean spec. | **demote to a section of `docs/SPIKES.md`** — also fixes its two sections both numbered `## 5` |
| `PLAN.md` 1114L | The coordinating session, every session. Its irreplaceable content is **D1–D31**, the ratified decision register gated by `check_record.py`, plus the workflow post-mortems in the header — expensive lessons recorded nowhere else. | **split** |
| `README.md` 294L | A first-time reader or external evaluator. The "what works today / what is designed / maturity, honestly" split is exactly right for a repository at this stage, and it is honest. | **keep as-is** |
| `MODEL_DEBT.md` 292L | Anyone asking "is the model good enough for X yet". 52 inbound mentions, and both `X86_64.md` §3 and `SPIRV_VULKAN.md` defer *to* it rather than restating. Each entry carries a file:line, a "when it bites" trigger, and a validation plan. | **keep as-is** — the deferral pattern is working |
| `CONTRIBUTING.md` 273L | A new contributor, and every agent dispatched into a worktree. Its `**Status**:` convention section is the specification `check_doc_facade.py` enforces. | **keep as-is** |
| `TASKS.md` 210L | The frontier reader. **The premise that this is hand-maintained is stale** — see below. Its real unique content is now the 96-line task-lifecycle specification. | **split** |
| `CODE_OF_CONDUCT.md` 133L | A prospective external contributor. Verbatim Contributor Covenant 2.1 — boilerplate whose *absence* is a signal. | **keep as-is** |
| `TCB.md` 121L | Anyone reasoning about what a green build actually proves. T2 — that the axiom gate sees 81% of the tree, with 32 of 170 modules invisible — is the single most load-bearing sentence in the repository's trust story. | **keep as-is** |
| `SECURITY.md` 102L | An external reporter. Its value is redefining "security" for this repository — a soundness bug, a gate that passes when it should fail, a model that diverges from silicon. That reframing is the content. | **keep as-is** |
| `GRAPHICS_PREBUILD_AUDIT.md` 82L | G2–G9 implementers. §8's items *are* all fixed, verified. But §1–§7 and §9 are the *rationale* for eight still-open tasks — G2 exists because §2 diagnosed a specific modelling error. | **keep until the G-track closes** |
| `scripts/build_baseline.md` 405L | **NONE FOUND for most of it.** §0–§6 are iteration-1 measurements superseded by §7's iteration 2, and the absolute numbers are self-declared contention-skewed and so not re-comparable. | **delete**; move §7.4's experiment note into `B1` |
| `.github/PULL_REQUEST_TEMPLATE.md` 97L | Every PR author, at the moment of writing. The domain-gap matrix is an *authoring instrument*, not documentation — it forces the adversarial question when it is cheapest to ask. | **keep as-is** |

### 5.1 Two premises in my own brief that the evidence overturned

**`TASKS.md` is no longer hand-maintained.** `scripts/task_frontier.py` gained
`--regenerate-board` and `--check-board` (verified at `task_frontier.py:342`, `:457`, `:459`), and
the file's header now states that frontmatter is the single source of truth. The "wrong about 35
of 79 tasks" finding is a fact about a state that has since been fixed. What remains in `TASKS.md`
is a 96-line task-lifecycle specification — frontmatter schema, status enum, design stages, the
priority-aging rule — which is *not* derived and lives nowhere else. **The verdict is split, not
delete**: move the lifecycle spec out, leave the generated board.

**`TARGET_MODEL.md` should not be merged into an unbuilt-targets file**, as I had suggested. Its 5
citations are among the healthiest in the corpus: `Gasm/Core/Arch.lean:21` cites it for the
architecture typeclass, and §1 specifies exactly the fields that typeclass carries. It is a built,
load-bearing specification. Folding it in with genuinely unbuilt targets would mislabel it.

### 5.2 Circular instances in this cluster

**`X86_64.md#2-binary-instruction-encoding` — 127 citations, 13 lines of content. The corpus's
single largest circular block.** A representative citer:

    Instructions/Add.lean:186: /- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
                               def add_r64 (dst src : Reg64) : AnyX86_64Instruction := ...

The box says nothing about `ADD`, nothing about opcode `0x01`, nothing about the sub-opcode
encoding. **The Lean docstring one line below carries strictly more information than the section
it cites.** The Intel SDM is vendored; these citations belong on per-opcode SDM anchors.

**`X86_64.md#1` — 57 citations onto a zero-body heading, and the citations are not even about
that topic.** The tell is what sits beside them. `Registers.lean:32` cites the SDM for the register
enumeration, then `Registers.lean:122` falls back to this anchor for the flags accessor — and §1
contains no flags content. Worse, `Core/Types.lean:29` and `:37` cite it for architecture-neutral
width aliases in `Core/`, which an x86-64 sub-register aliasing section does not mention at all.
The anchor is a catch-all for declarations that had nothing else to point at.

**`SPIKES.md#3-spike-progression-roadmap` — 26 citations, and the clearest instance in the
corpus.** There is no `SPIKE2` document. So the *entire* Spike 2 Lean corpus cites a single box in
an eight-box ASCII diagram:

    Spikes/Spike2Fibonacci/Spec.lean:29:            /- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
                                                    def fibNat : Nat -> Nat
    Spikes/Spike2Fibonacci/Windows/Program.lean:189: /- REF: docs/SPIKES.md#3-spike-progression-roadmap -/
                                                    def spike2Linked : LinkedWindowsProgram := ...

The definition of Fibonacci and the PE linking of Spike 2's binary are justified by the same box.
Law 1 satisfied, Law 2 vacuous.

**`WINDOWS.md#1` — 39 of the file's 43 citations onto a one-sentence body**, and four of them
(`Gasm/Core/Verification.lean:51,56,61,66`) are on an environment loader that has nothing to do
with the Microsoft x64 calling convention. The contrast is one line above: `Verification.lean:45`
cites `SYSTEM_EFFECTS.md#1` for the same class, correctly. The instances then fall back to the
Windows anchor because the author had run out of grounded anchors.

**`LINUX.md#31` — 24 citations onto pure ASCII box art.** Every citer is a constant re-export
(`ELFFormat.lean:30` on the ELF type constant); the box does not contain the value. **The markdown
is strictly less informative than the code citing it.**

**`WASI.md#2` — 12 citations onto a zero-body heading** whose subsections document two syscalls,
while `WASI/ABI.lean:39` cites it for a *third* that the document never mentions. That is a Law 2
gap hiding behind a citation gap.

**Non-instances, named so the framework does not over-fire**: `TARGET_MODEL.md#1` is genuinely
grounded; `SPIKE4_HTTP_SERVER.md#1`'s diagram does justify the router; `BARE_METAL.md#42` genuinely
specifies the debug-exit encoding; `WASM_ORACLE_HARNESS.md` is the model of how to do this
honestly. **Roughly 40% of citation *volume* is circular; well under 10% of *anchors* are.**

### 5.3 Consolidation in this cluster

1. **`X86_32.md` + `X86_REALMODE.md` → `docs/TARGETS/UNBUILT_TARGETS.md`.** *Reader need*: someone
   assessing what has actually been built should find the unbuilt ISAs in one clearly-labelled
   place, rather than discovering it file by file from a target table that lists them as peers of
   x86-64. *Anchor cost*: **zero**.
2. **`WASM.md` + `WASI.md` → `WASM_ORACLE_HARNESS.md`, renamed `WEBASSEMBLY.md`.** *Reader need*:
   the binary format, the WASI import ABI, and the differential oracle are consulted in a single
   sitting by a single person — and today the three files disagree about whether a syscall exists.
   *Anchor cost*: 41 citing lines need path rewriting; every anchor survives verbatim.
3. **`ARM.md` → appendix of `ARM64.md`.** *Reader need*: the ARM team must not have to reconcile a
   79-line file showing a DSL against a 905-line file stating no ARM code exists. *Anchor cost*:
   zero. **Timing is an owner call** — the merge is right, but the team is mid-dispatch.
4. **`SPIKE3_SORT_LINES.md` → `docs/SPIKES.md` §5**; keep 4, 5, 8 standalone; write `SPIKE2` or
   grant an explicit exemption. *Reader need*: a spike author should find their spike's document by
   a predictable rule, and "some spikes have one" is not a rule — which is exactly why Spike 2's
   whole corpus cites a roadmap box.
5. **Split `PLAN.md`; do not touch `TASKS.md`'s board or `docs/tasks/`.** The three-views
   redundancy is already mostly resolved: `docs/tasks/` is the source of truth, the board is
   generated, and `PLAN.md`'s phases are self-declared advisory. What remains is that `PLAN.md`
   mixes an authoritative, gated decision register with ~300 lines of dead phase checkboxes and
   ~330 lines of triage backlog. *Reader need*: someone looking up D20 should not scroll past 300
   lines of completed phases.

### 5.4 The framework mis-fire on `ARM64.md` — stated plainly

**Every mechanical metric marks `ARM64.md` deletable, and the framework in this proposal avoids
that conclusion only because the file was read.** That is worth admitting rather than claiming a
clean result.

Mechanically: 905 lines, **zero** inbound `REF:` citations, **two** inbound markdown mentions — one
of which is `DOC_CLEANUP_PROPOSAL.md`, another audit rather than a reader. By coupling it is the
most deletable file in the set. By content it is among the least.

Question 1 ("who reads it, when, what can they not get elsewhere") saves it with a crisp answer.
Every *proxy* for question 1 — citations, inbound links, whether it documents anything in the
tree — points the other way.

**The lesson generalizes, and it is the most important structural finding in this section.**
`SPIKE8_MULTITHREADING.md` (0 citations, 513 lines), `WIN32_DIFFERENTIAL_HARNESS.md` (0, 950),
`SPIRV_VULKAN.md` (0, 133), `X86_MEMORY_MODEL.md` (0, 369) and `BORROW_MODEL.md` (0, 1,129) are in
the same position. **In a repository governed by Law 5 — design before demand — zero inbound
citations correlates with *high* value, because the best documents are written before the code
that will cite them.** A framework keyed on coupling inverts the truth here. Both the previous
pass's framework and a naive orphan sweep would mishandle these five documents in opposite
directions; only the affirmative question handles them correctly.

---

## 6. `docs/` — the process, governance and ledger cluster (17 files, 9,269 lines)

This cluster is where the inverted burden bites hardest, because **most of these files have zero
`REF:` citations and zero cited sections — nothing in the code holds them up at all.** The
question is therefore unusually clean: *if this file vanished, which human or team would notice,
and what would they fail to do?*

| File | Who reads it, when, and what they cannot get elsewhere | Form verdict |
|---|---|---|
| `REVIEW.md` 324L | Every contributor and agent, before authoring or reviewing anything. The canonical normative statement of the 14 Laws and the three-pillar protocol; CODEOWNERS assigns it to the owner personally. | **keep as-is** — trim §4.1's body, never rename its headings |
| `X86_ISA_EXPANSION_PREREQUISITES.md` 511L | The owner deciding whether to green-light the ISA expansion, and any team dispatched to do it. Unique: the measured evidence base — 39 modules and 130 s per instruction edit, 50 of 88 forms unfuzzable against hardware, 0 of 88 cited coefficients. ADR-0039 was ratified out of it. | **keep as-is** |
| `PATHFINDER_CRC32.md` 1134L | The agent implementing PA1 (its `design:` target) and PA2's designer. Unique: the contract shape, the 14-instruction step-lemma inventory, two adopted assembly defects, and the axiom-footprint policy that `gate_allowlist.txt:129` cites. | **keep** (trim §0; correct the preamble) |
| `REFERENCE_INDEX.md` 1133L | Whoever modifies any of the four reference scripts — all four name it in their module docstrings as their design of record. Unique: the per-media-type anchor grammars, the drift policy, the exit-code semantics. **A script encodes policy; it does not justify it.** | **split** — §6 and §8 (~370L) are closed record |
| `CALIBRATION_GOVERNANCE.md` 938L | Whoever implements the calibration checker (F2's `design:` target), and F1/F3 authors. **The Lean-citation claim is verified and is stronger than reported** — see below. | **keep as-is** (correct §0/§1) |
| `PA16_CODEC_SOUNDNESS.md` 807L | Whoever picks up PA16 Phase 2. Its §4 proposition numbers are cited from **ten `gate_allowlist.txt` justification lines** as the map of what closes each entry. | **keep as-is** — the healthiest long document in the cluster |
| `CI.md` 502L | Whoever edits the workflows; cited from both, from the PR template, and from two `.lean` files. Unique: the platform-matrix rationale and its incident, and §5's carve-out — the sole written justification for a required gate that CI does not run. | **split** — §8/§8a are ~130L of past-incident tables |
| `PRE_FLATTEN_CHECKLIST.md` 488L | The owner or agent executing the flatten, once. Unique: Part 2's ordered irreversible-operation procedure and its post-flatten verification step. | **split** — Part 2 (~90L) is live, Part 1 (~340L) is closed record |
| `WORK_TRACKING.md` 484L | **NONE FOUND.** Zero citations; **one** inbound reference, and it is `DOC_CLEANUP_PROPOSAL.md` — an audit *of* it. Its own status line says nothing described has been enacted. The directory it specifies does not exist. | **convert to task** (fold into TC13) |
| `THIRD_PARTY_LICENSES.md` 477L | The owner or counsel, once, answering "was anything non-redistributable ever in this repository" after the flatten erases the history that would otherwise show it. `check_publishable.py:49` names it. | **keep as-is** → `docs/record/` |
| `ORACLE_DEBT.md` 414L | Any agent picking up a PA-track task; **27 inbound files**; the sole recorded rationale for PA10–PA18's existence and scoping. Unique: the four-shape taxonomy of the allowlist and the precision gap it found in the axiom gate. | **keep**; drop Part 6; **absorb** the PA-task extractions from §3.4 |
| `GRAPHICS_ARCHITECTURE.md` 364L | Whoever picks up G1–G9, and anyone asking why there is no DX12 or WebGPU target. Unique: §2.2 is a **negative** record — ruled-out targets written down so they are not silently reintroduced. | **keep as-is** |
| `VISION.md` 313L | Everyone, first. It states its own role: "when a design question is ambiguous, resolve it against this document." 63 inbound files, including 11 ADRs. | **keep as-is** — genuinely the root document |
| `SOFTWARE_MODELING_SDLC.md` 217L | A newcomer learning the four-stage pipeline. Durable unique content: the four stages plus the **Seams** concept, which `VISION.md` §4 gestures at but does not walk — about 40 lines' worth. | **demote to a section of `docs/README.md`** |
| `docs/README.md` 126L | Claimed: someone browsing `docs/`. **That audience is not real as constructed** — no document links here; the only path is a directory listing. | **reduce to index + targets table**, and link it from the root README |
| `AUTHORING_ASM.md` 99L | **NONE FOUND.** Zero citations; one inbound reference, again the previous audit. Absent from `docs/README.md`'s own index. No commit, ADR, or task mentions it. | **flag, do not delete** — see below |
| `DOC_CLEANUP_PROPOSAL.md` 938L | **NONE FOUND.** Zero citations, zero inbound references, no allowlist entry, no `design:` field, no `check_record.py` path citation. Its §5 asks for ten owner rulings; none was given. | **rescue §3/§5/§7, then delete** |

### 6.1 Applying the test to the previous audit itself

`docs/DOC_CLEANUP_PROPOSAL.md` fails its own standard, and the failure is instructive rather than
merely ironic.

**It renders verdicts on two files that do not exist on `main`.** Its inventory at line 738 gives
`docs/BARE_METAL_VALIDATION.md` (350 lines) a `keep`, and at line 590 gives
`docs/tasks/MH4-fault-oracle-veh-capture.md` a `keep`. It also names both in its "do not delete"
section as load-bearing cases. **Neither is tracked on `main`** — `BARE_METAL_VALIDATION.md` was
added by commit `5d41bde` on a branch that never merged, and no `MH4` task file exists among the
81.

The cause is recorded in the commit that landed it. `46b3a60`'s own message reads: *"Written and
committed on a worktree branch, never pushed — the proposal about stranded documentation was
itself stranded."* Its measurement pin is a merge commit on that branch, and its corpus totals
correspondingly do not match `main`: 182 files / 32,072 lines against 185 / 34,509; 79 task files
against 81; `REVIEW.md` at 278 lines / 143 citations against 324 / 136.

**This is the strongest possible argument for the owner's premise.** A 938-line audit, cited by
nothing, asking ten questions nobody answered, whose inventory would send a future reader to act
on files that are not there. Leaving it untouched is worse than either alternative: rescue its
four proposed gates (§3), its ten open questions (§5) and its two policy levers (§7) into task
files or an ADR, then delete it.

**It is also the only inbound reference for two other files in this cluster** —
`WORK_TRACKING.md` and `AUTHORING_ASM.md`. Once it goes, both are fully orphaned, which is the
honest state they were already in.

### 6.2 Circular and self-referential instances

**Whole files whose only reader is the process that produced them — 1,521 lines:**
`DOC_CLEANUP_PROPOSAL.md` (938), `WORK_TRACKING.md` (484, a proposal produced by an investigation,
whose sole inbound reference is the audit above), `AUTHORING_ASM.md` (99, no reader path exists to
it at all).

**Circular sections inside otherwise-justified documents — ~1,015 lines. This is where the volume
actually is:**

| Location | Lines | Why circular |
|---|---:|---|
| `CI.md` §8 + §8a | ~130 | "Verification performed, this task, on this machine" exit-code tables. The only reader was that task's reviewer. |
| `CI.md` §7, four bullets | ~25 | A known-gaps list in which four gaps carry "(Resolved; left here as the record.)". |
| `PATHFINDER_CRC32.md` §0 | ~50 | A revision log narrating point-by-point responses to two design reviews that signed off. |
| `CALIBRATION_GOVERNANCE.md` §16 + §17 | ~65 | "Disposition of the prior draft's design-review questions" and "review history across three cycles". |
| `ORACLE_DEBT.md` Part 6 | ~60 | A stale-status table and a pasted tool dump. Regenerable, and already wrong. |
| `PRE_FLATTEN_CHECKLIST.md` Part 1 | ~340 | Findings for an operation whose dominant blocker has since landed; three claims false today. |
| `REFERENCE_INDEX.md` §6 + §8 | ~370 | A migration plan for a migration that landed, plus amendment text marked "PROPOSED pending ratification" when `REVIEW.md` Law 6 already carries the amended mechanism as ratified law. |

**Aggregate: ~2,536 lines — 27% of this cluster — is either fully circular or superseded record
living in a specification namespace.** The previous pass's answer for the entire corpus was 121
lines, 0.4%.

**Explicitly NOT circular: `THIRD_PARTY_LICENSES.md`.** Every corpus it audits is deleted, but its
reader is a future owner or counsel answering a question ADR-0031 makes unanswerable any other
way. It is a record, and it says so.

**A verified claim, stronger than reported.** `CALIBRATION_GOVERNANCE.md` §9's licensing
determination is cited from shipped model code and from a gate tool — not via `REF:` anchors but
via prose doc-comments, which is why its measured citation count is zero:
`Gasm/Targets/X86_64/Instructions/Obligations.lean:39,70,75,77,80` names §9 as the reason external
timing tables are ruled out as a coefficient source, and `Tools/CheckX86Obligations.lean:71,343`
names the same determination as the reason the gate reports 0-of-88 cited coefficients as
*correct* rather than as a failure. **A gate's honest-state report rests on §9 — while §9 itself
says it does not contain an actual license reading and invites supersession.** That is defensible
but should be deliberate, and it is filed for ruling.

### 6.3 Consolidation in this cluster

**The gate list is encoded four times** — `REVIEW.md` §4.1, `CI.md` §2, `run_gates.py`'s table,
and `ci.yml` — and the first two have already drifted: `CI.md`'s table omits three gates that
`REVIEW.md` §4.1 requires. *Reader need*: **a reviewer must be able to answer "did every required
gate run, on a platform where it means anything" from one place, and today must reconcile four.**
Fix: `REVIEW.md` §4.1 keeps the policy statement and stops enumerating commands (`run_gates.py` is
already named there as the single entry point); `CI.md` §2 keeps only the platform column. Trimming
§4.1's body is safe; renaming its headings is not, as 136 citations resolve into the file.

**The three debt ledgers should NOT merge.** Read together, they are not three encodings of one
thing: `MODEL_DEBT.md` records where the model is wrong about the world; `ORACLE_DEBT.md` records
where the proof mechanism is an oracle rather than the kernel; `PA16_CODEC_SOUNDNESS.md`
decomposes ten of those entries into thirteen propositions — a roadmap, not a ledger. They
cross-cite correctly. If §3.4's extraction of PA-task findings into `ORACLE_DEBT.md` lands, that
file grows toward ~600 lines and the case for keeping PA16 separate gets *stronger*.

**The onboarding cluster has two real audiences, not four.** The previous pass's 7%-literal-overlap
measure is the wrong test — nobody copy-pastes, they re-state. Root `README.md` (a stranger on
GitHub) and `VISION.md` (anyone resolving a design ambiguity, 63 inbound) are real and should be
kept as-is. `docs/README.md` is **not** a real audience as constructed: nothing links to it, and
~85 of its 126 lines are one-line twins of four other documents — with ADR-0020 *already*
recording this file going stale on exactly those twins. `SOFTWARE_MODELING_SDLC.md` is partly
real: ~40 durable lines in 217. *Reader need*: a newcomer needs the four stages, the Seams cut, the
targets table and the index in one place, and no one of those is large enough to navigate to
separately.

**`docs/record/` — recommended, and it is the highest-leverage structural change in this
cluster.** Seven of these 17 files are dated ledgers, audits, checklists or proposals rather than
specifications — **4,459 lines, 48% of the cluster** — interleaved with the specs a newcomer
reads. This matters beyond tidiness: *a dated audit and a normative spec decay differently and
must be read differently, and nothing in the path tells a reader which one they are holding.* That
is precisely how `PRE_FLATTEN_CHECKLIST.md`'s front page stays wrong — it reads like a
specification. Move *closed* artifacts there; leave live ledgers with an update cadence where
they are.

**A real objection to `docs/record/`, stated plainly:** `check_doc_facade.py` scans `docs/*.md`
excluding `docs/adr/` and `docs/tasks/`. A new `docs/record/` falls outside that glob and would
**silently stop being linted** — a directory of stale claims, exempted from the stale-claim gate.
The linter's scope must extend in the same change, or the split buys tidiness at the cost of a
gate.

### 6.4 External-team constraint

Flagged rather than proposed for deletion: `GRAPHICS_ARCHITECTURE.md` (§2.2's negative record) and
**`AUTHORING_ASM.md`** — the only authoring-guide-shaped document in the tree, with an ARM team
being dispatched now, but **currently a misleading one**: it teaches the pre-capability authoring
path that Law 11 prohibits for new programs, and §1–§3's library-variant menu describes an
architecture the tree does not have. The ruling needed is whether an authoring on-ramp is meant to
exist; if so it must be rewritten against Law 11 *before* an incoming team reads it.

**One finding bears directly on the constraint and is the cheapest fix in this proposal.**
`docs/README.md` is unreachable except by directory browsing, and its index reaches 11 of 34 loose
documents. `docs/TARGETS/ARM64.md` — the ARM handoff — has zero inbound references of any kind.
**If the repository is the only channel to those teams, the channel currently depends on them
guessing which directory to open.** Extending the index to all 34 loose documents and linking it
from the root `README.md` costs a few dozen lines and directly serves the constraint.

---

## 7. `docs/adr/` — 41 files, 2,357 lines

Per the brief, this section is deliberately short. **The affirmative justification for every ADR
is the same and it is sufficient: it records an owner ruling, and the ruling is the only record
of why the project is shaped as it is.** ADR-0031 makes that record load-bearing — after the
flatten there is no commit history to fall back on.

The form is also right, and measurably so. The 40 ADRs run 35–161 lines (median ~52); all carry a
`## Provenance` section; numbering 0001–0040 is contiguous with no duplicates; and no ADR's ruling
is reversed by a later one. There is no supersession marking to add. **Verdict for all 41 files
(40 ADRs plus the directory README): keep as-is.**

Consolidating them into a single `docs/DECISIONS.md` was considered and is **not** recommended.
Three reasons, in order of weight: the directory's immutability rule means an amendment is a new
ADR rather than an edit, which a single file would silently invite breaking; `PLAN.md`'s D1–D31
register and many commit messages cite ADRs by number and path; and per-ADR provenance — which
words were the owner's and which were a coordinator's synthesis — is the corpus's best-maintained
discipline and depends on the one-ruling-per-file boundary. **This is the one cluster where the
split demonstrably serves a reader rather than a writer.**

Four unreconciled tensions the previous pass identified are carried forward unchanged into §11;
they are questions about the *content* of rulings, not about whether the files should exist.

---

## 8. The consolidation plan

Nine groupings. Each states the reader need, and none rests on duplication — the previous pass's
negative result on duplication stands, and consolidation is recommended anyway where the boundary
served the writer.

| # | Grouping | Reader need it serves | Cost |
|---|---|---|---|
| 1 | `API_STATE_MODELS` + `STACK_DISCIPLINE` + `OBLIGATIONS_AND_CAUSALITY` + `PROOF_CARRYING_ASSEMBLY` + `MEMORY_PROVENANCE` §1 → **`docs/CORE_SEMANTICS.md`** | The composed state has seven fields and five are documented in five different files; a reader who opens one cannot understand the structure it prints without the other four. | **38 citing lines.** Cheapest merge relative to benefit. Collapses 3 copies of one inductive to 1. |
| 2 | `STDLIB_ZLIB` + `STDLIB_PNG` + `STDLIB_HTTP11` + `STDLIB_SMOLALLOC` → **`docs/STDLIB.md`** | A stdlib author or external reviewer asking what the library specifies and what is proven about it opens four files, one of which is in no index. The codecs compose; PNG routes through Zlib and says so. | ~619 citing lines. The expensive one, but mechanical, and it sweeps up 9 malformed anchors. |
| 3 | `WASM` + `WASI` → `WASM_ORACLE_HARNESS`, renamed **`docs/TARGETS/WEBASSEMBLY.md`** | One person, one sitting, three files that currently disagree about whether a syscall exists. | 41 citing lines; anchors survive verbatim. |
| 4 | `X86_32` + `X86_REALMODE` → **`docs/TARGETS/UNBUILT_TARGETS.md`** | Someone assessing what has actually been built should find the unbuilt ISAs in one labelled place, not discover it file by file from a table that lists them as peers of x86-64. | **Zero.** |
| 5 | `ARM.md` → appendix of `ARM64.md` | The ARM team must not reconcile a 79-line file showing a DSL against a 905-line file stating no ARM code exists. | **Zero** — but see §11 on timing. |
| 6 | `SYSTEM_EFFECTS` §6 → `EQUIVALENCE_PROOFS` | The two halves of the definition of "observable" cross-cite each other and each says the other is canonical. Neither can be read alone; the documents say so. | **12 citing lines** in this direction; 110 in the other. Direction matters. |
| 7 | `SPIKE3_SORT_LINES` → `docs/SPIKES.md` §5 | A spike author should find their spike's document by a predictable rule. "Some spikes have one" is not a rule — which is why Spike 2's entire corpus cites a roadmap box. | Anchors move within one file; also fixes two sections both numbered `## 5`. |
| 8 | `SOFTWARE_MODELING_SDLC` (~40 durable lines) → `docs/README.md`; drop that file's ~85 lines of twins; **link it from the root `README.md`** | A newcomer needs the four stages, the Seams cut, the targets table and the index in one place, and none is large enough to navigate to alone. Today nothing links to `docs/README.md` at all. | Two link updates; zero anchors. |
| 9 | **`docs/record/`** — move closed artifacts (`THIRD_PARTY_LICENSES`, `PRE_FLATTEN_CHECKLIST` Part 1, `REFERENCE_INDEX` §6/§8, `GRAPHICS_PREBUILD_AUDIT`) out of the specification namespace | A dated audit and a normative spec decay differently and must be read differently, and nothing in the path tells a reader which one they hold. This is *how* a checklist's front page stays wrong for days. | ~1,269 lines moved. **Requires extending `check_doc_facade.py`'s glob in the same change** — see §11. |

**Explicitly NOT consolidated**, each after reading both sides:

- **The three memory documents** (`MEMORY_HOOK`, `X86_MEMORY_MODEL`, `BORROW_MODEL`, 2,202 lines).
  Their `**Status**:` states differ — one has partly landed, two are entirely unbuilt. A merged
  file would carry one preamble over three incompatible truth-states, which is the defect this
  corpus already has.
- **The three debt ledgers** (`MODEL_DEBT`, `ORACLE_DEBT`, `PA16_CODEC_SOUNDNESS`). Model-wrong,
  mechanism-wrong, and a proof roadmap respectively. They cross-cite correctly.
- **`docs/adr/`** — see §7.
- **`docs/TARGETS/` as a whole.** The previous pass's negative on duplication stands, and the
  per-target boundary tracks a real reader boundary.
- **`TARGET_MODEL.md`** — I had proposed folding it into `UNBUILT_TARGETS.md`; the evidence says
  no. It is a built, cited specification for the architecture typeclasses.

---

## 9. The deletion list, with what breaks and the fix

**25 whole files, 4,655 lines, of which ~370 lines are extracted to permanent homes first.**

| File(s) | Lines | Why it cannot be justified | What breaks | The fix |
|---|---:|---|---|---|
| **Tier A task files** — `TC1` `TC2` `TC3` `TC4` `TC5` `TC16` `TC17` `G1` `MH1` `PA11` `PA18` | 1,350 | Complete (deliverable verified in the tree); `## Notes` holds no finding not recoverable from the code, the gate, or an ADR. | 20 `after:` + 6 `related:` edges in 25 surviving files; 4 `decision_record_allowlist.txt` entries. | Drop the edges (all are discharged preconditions, §2.4); remove the allowlist entries. `task_frontier.py --validate` then reports 61 files, exit 0. |
| **Tier B task files** — `B3` `B7` `PA10` `PA12` `PA13` `PA14` `TC9` `TC21` `TC22` | 1,318 | Complete; the surviving content belongs in a permanent home, not under a spent work item. | As above, plus 21 `.lean` `REF:` citations naming `PA13`/`PA14`. | Extract ~250 lines to `ORACLE_DEBT`, `TCB`, `MODEL_DEBT`, `PATHFINDER_CRC32`, `STDLIB_PNG`, `check_doc_facade.py`'s header; retarget the citations at `docs/PATHFINDER_CRC32.md`. |
| `docs/DOC_CLEANUP_PROPOSAL.md` | 938 | Zero citations, zero inbound references, no allowlist entry, no `design:` field. Ten open questions nobody answered, and an inventory pinned to a tree that never existed on `main` (§6.1). | **Nothing.** | Rescue §3's four proposed gates, §5's ten questions and §7's two policy levers into task files or an ADR first. |
| `docs/WORK_TRACKING.md` | 484 | Zero citations; its sole inbound reference is the file above. Nothing it specifies was ever enacted; the directory it defines does not exist. | Nothing, once the above goes. | Fold §9's design and §6's argument into `docs/tasks/TC13-task-dag-tooling.md`. |
| `scripts/build_baseline.md` | 405 | §0–§6 are iteration-1 measurements superseded by §7; the absolute numbers are self-declared contention-skewed and so not re-comparable. Also in the wrong place under ADR-0027. | Nothing mechanical; 6 inbound mentions from `B1` and `PLAN.md`. | Move §7.4's experiment note into `B1`'s Notes (it is already in `TCB.md` §T3 and the registry module header); repoint the 6 mentions. |
| `docs/AUTHORING_ASM.md` | 99 | Zero citations; sole inbound reference is the previous audit; absent from the docs index; no commit, ADR or task mentions it. Actively misleading — it teaches the pre-capability path Law 11 prohibits. | Nothing. | **Flag, do not delete unilaterally** — §11 ruling 2. Its one unhomed asset (the port/uop authoring advice) goes to `docs/TARGETS/X86_64.md`. |
| `docs/ARCHITECTURE.md` | 61 | No affirmative justification found. §1's directory tree names three files that do not exist; §2's diagram is a lower-fidelity copy of one in `docs/README.md`. | **One** `REF:` line — `Gasm/Core/Callable.lean:25` — so `check_refs.py` hard-fails. | Retarget that line to `docs/API_STATE_MODELS.md#3-the-callable-typeclass-automatic-derivation`, which is where the class is actually specified and which the very next citation already points at. The 14 inbound markdown mentions are all see-also links. |

**Section-level deletions — ~655 lines**, detailed in §4.3, §5.2 and §6.2: the stale-fence
transcriptions subsumed by grouping 1; `MEMORY_PROVENANCE` §2; `PROOF_CARRYING_ASSEMBLY` §4;
`STDLIB_PNG` §5; `CI.md` §8/§8a and the four resolved §7 bullets; `PATHFINDER_CRC32` §0;
`CALIBRATION_GOVERNANCE` §16/§17; `ORACLE_DEBT` Part 6; `X86_64.md` §1's bare heading and §2's box
(after re-pointing); `docs/README.md`'s four twinned summary sections; `BARE_METAL` §5/§6.

**The 193 mis-targeted citations of §2.1 are NOT on this list.** They are a defect in the citing
`.lean` files. The sections they point at should stay; the citations should move to the
subsections that actually specify the declarations. That work is mechanical and it is the single
highest-value follow-on this proposal identifies.

---

## 10. Line-count arithmetic

| Stage | Files | Lines | vs now |
|---|---:|---:|---:|
| **Now** (at `46b3a60`) | **185** | **34,509** | — |
| After 25 whole-file deletions (4,655 removed, ~370 extracted back) | 160 | 30,224 | −12.4% |
| After ~655 lines of section-level deletion | 160 | 29,569 | −14.3% |
| After the nine consolidation groupings (13 fewer files, content preserved) | 147 | 29,569 | −14.3% |
| Plus this proposal | **148** | ~29,900 | **−13.4%** |

A further **1,269 lines move** into `docs/record/` — a relocation, not a reduction, but it removes
that volume from the namespace a newcomer reads.

**By category:**

| Category | Now (files/lines) | After |
|---|---|---|
| `docs/tasks/` | 81 / 11,357 | 61 / 8,689 |
| `docs/` loose | 34 / 13,572 | 24 / ~10,900 (3 of them under `docs/record/`) |
| `docs/TARGETS/` | 14 / 3,326 | 10 / ~3,270 |
| `docs/adr/` | 41 / 2,357 | **41 / 2,357 — unchanged** |
| repository root | 9 / 2,589 | 9 / ~2,500 |
| `docs/SPIKES/` | 4 / 806 | 3 / ~730 |
| `scripts/` | 1 / 405 | **0** |
| `.github/` | 1 / 97 | 1 / 97 |

**For comparison, the previous pass proposed 182 → 183 files and −409 lines (−1.3%), deleting
zero whole files.** The difference is not that this pass found more cruft; the corpus barely
changed. The difference is entirely the burden of proof.

**And the volume is still not the point.** The clearest evidence: `docs/adr/` is 2,357 lines and
loses nothing, while the single largest clean deletion is one 405-line file of superseded
measurements. What this pass actually found is that **roughly 40% of citation volume is
circular** — and no line count captures that, because the fix is in the `.lean` files.

---

## 11. Needs an owner ruling

Ordered by consequence. These are genuinely close calls or questions only the owner can answer; I
have not resolved them by guessing.

1. **Is a Lean declaration allowed to exist without a design section to cite?** This is the root
   cause of §2, not a symptom. Law 1 forbids un-cited code and provides no exemption class, so
   when nothing specifies a declaration the author cites the emptiest anchor that resolves. The
   Fibonacci definition and Spike 2's PE linking are both "justified" by the same box in an ASCII
   roadmap. **Either write the missing specifications — documentation for the gate's sake, which is
   the disease — or carve an explicit exemption category.** No amount of document editing fixes
   this structurally.
2. **`docs/AUTHORING_ASM.md`** — is an authoring on-ramp meant to exist? If yes, it must be
   rewritten against Law 11's capability path, which it predates and contradicts, *before* an
   incoming ARM team reads it. If no, delete. It is currently orphaned and misleading, which is
   the worst of the three states.
3. **`docs/DOC_CLEANUP_PROPOSAL.md`** — its §5 asks ten questions that were never answered, and
   its inventory is pinned to a tree that never existed on `main`, including `keep` verdicts on
   two files that are not there. Answer the ten and delete it, or re-pin it and strike the two
   phantom rows. Leaving it untouched is the worst of the three.
4. **Adopt `docs/record/`?** If yes, `check_doc_facade.py`'s glob must extend to it in the same
   change, or a directory of dated claims silently exits the stale-claim gate.
5. **Should `check_refs.py` reject a `REF:` anchor whose section body is empty?** 193 citations
   across 11 anchors would be caught by one predicate. This is exactly Law 13's shape — a finding
   becoming a gate — and it is the mechanical enforcement of this proposal's governing rule.
6. **Tier C task files (§3.5)** — `TC7` (frontmatter says `done`, body says `designing`, twice),
   `B1`, `N8`, `PA15`, `PA17`, `TC20`. Each may be complete; I did not establish it to the standard
   that justifies deletion. 743 lines hang on this.
7. **`docs/WORK_TRACKING.md`** — ratify it (and then actually tell the Linux and ARM teams it
   exists), fold it into `TC13`, or retire it? It cannot remain a 484-line unratified proposal
   whose only inbound reference is an audit of itself.
8. **`CALIBRATION_GOVERNANCE.md` §9** — is an explicitly-unverified licence posture allowed to
   remain the load-bearing justification for a gate's honest-state report? §9 says of itself that
   it does not contain an actual licence reading, and invites supersession; meanwhile
   `Tools/CheckX86Obligations.lean:71,343` rests on it.
9. **`REFERENCE_INDEX.md` §8** — it says "PROPOSED, pending the owner's ratification", while
   `REVIEW.md` Law 6 already carries the amended mechanism as ratified law. Did the owner ratify
   §8, or did the amendment land without it?
10. **Timing of the `ARM.md` → `ARM64.md` merge.** The merge is right; the ARM team is mid-dispatch.
    Merging a document under a team that is reading it is an owner call, not mine.
11. **`X86_64.md` §2's 127 citations** — is re-pointing them at per-opcode Intel SDM anchors worth
    the mechanical cost, or is the honest fix to *write* a real encoding section that earns them?
12. **`PLAN.md`'s Phases 0–6** (~300 lines, self-declared advisory) — archive or delete? Under
    ADR-0031's flattening rule, deletion may not be available.
13. **Carried forward from the previous pass, unchanged and still unresolved**: ADR-0002's reserved
    question on eliminating `native_decide` entirely, while migration proceeds on a coordinator's
    synthesis that ADR-0037 itself flags as not the owner's words; ADR-0008 versus ADR-0039 on
    whether the ISA expansion is a sanctioned exception to demand-driven growth; ADR-0024's
    amendment falling outside the README's stated remediation window; and the two divergent copies
    of the Intel SDM frontmatter JSON.

---

## 12. Things I was unsure of

Named rather than resolved by guessing.

1. **Two of my own first-cut verdicts were wrong, in the same direction.** `B4` (`status: ready`)
   and `TC15` (`status: implementing`) were initially classed as complete; the tree says otherwise
   — `B4`'s index does not exist and `TC15`'s Notes read "none yet". Both errors came from trusting
   a status field or a plausible inference over the tree. **I did not re-verify all 55 keep-live
   task files to the same standard**, so the reverse error — a file I kept that is actually
   complete — is possible. Tier C exists because of this.
2. **The task cohorts were read by four parallel agents whose per-file conclusions I could not
   fully retain** after a session interruption. The tiering in §3 is my own re-derivation from
   frontmatter, Notes size, DAG edges and direct tree verification — not a transcription of theirs.
   Where they differed from me I went with the tree.
3. **Citation counts differ between sections by 5–10%.** §2 counts distinct citing declarations;
   §4 and §5 count `/- REF: -/` lines, and one declaration can carry several. `main` also moved
   during the pass. Rankings and the concentration finding are identical either way and no
   conclusion turns on it, but individual numbers should be re-derived before acting.
4. **I did not verify whether `check_refs.py` resolves anchors by exact fragment or by prefix.**
   Every anchor-cost figure in §8 assumes exact-fragment matching. If resolution is looser, the
   `STDLIB.md` merge is substantially cheaper than the ~619 lines quoted.
5. **Long documents were read at outline-plus-sample depth, not line by line**:
   `PATHFINDER_CRC32.md` §2.2–§5, `REFERENCE_INDEX.md` §1.2–§5, `CALIBRATION_GOVERNANCE.md`
   §3–§8/§12, `PA16_CODEC_SOUNDNESS.md` §1–§6, `PLAN.md` L453–1114,
   `WIN32_DIFFERENTIAL_HARNESS.md` §1–§11, `SPIKE8_MULTITHREADING.md` interior. Form verdicts for
   these rest on heading structure plus the sections read in full. In particular I did **not**
   audit `SPIKE8` and `WIN32_DIFFERENTIAL_HARNESS` for the fabricated-theorem defect class the
   concurrent fixer found in `SPIKE4`/`SPIKE5` — and since both are pure design with no Lean, that
   class is *likelier* there, not less likely. Worth a dedicated pass.
6. **`ORACLE_DEBT.md`'s Part 2 matrix at row granularity.** Its aggregate is confirmed stale (it
   says 80 allowlist entries; `X86_ISA_EXPANSION_PREREQUISITES.md` §2 says 85 a day later) but I
   did not re-derive which specific rows closed.
7. **Whether `X86_ISA_EXPANSION_PREREQUISITES.md`'s P3/P4 are stale.** The previous pass claims B3
   landed and three P4 mechanisms exist. I did not re-derive its evidence table, and the
   concurrent fixer may already have corrected it.
8. **The `docs/record/` boundary is a judgement call I could not fully ground.** Which ledgers are
   "live with an update cadence" versus "closed record" is clear for the extremes
   (`THIRD_PARTY_LICENSES` closed; `MODEL_DEBT` live) and genuinely ambiguous in the middle
   (`PRE_FLATTEN_CHECKLIST` Part 2 is live for an operation that may never run).
9. **I did not verify owner quotations against the session transcript**, which ADR-0024 requires of
   a record review. Every attribution judgement carried forward in §11.13 is internal-consistency
   reasoning over ADR text alone.
10. **The corpus moved continuously under this pass** — `46b3a60` → `938f4db` → `fc88dd2` →
    `c717eeb`, with `SPIKE4_HTTP_SERVER.md` growing 95→141 lines, `ARM64.md` 887→905,
    `MEMORY_HOOK.md` 652→704, `BORROW_MODEL.md` 887→1,129, and `REVIEW.md` gaining a line. Every
    such change I saw was a correction and an improvement. Specific line references may not hold.

---

## 13. Method

- Corpus enumerated with `git ls-files`, never a filesystem walk, matching the gate scripts'
  convention. An early attempt double-counted build-directory copies by a large factor; all figures
  here are from tracked files only.
- Citation data built by scanning every tracked `.lean` file for `REF:` matches with the same
  plain regex `check_refs.py` uses, resolving each target against a heading index built from all
  185 markdown files with GitHub's anchor-slug rules, and recording the declaration following each
  citation. Section bodies were measured with fenced-code regions counted separately from prose,
  which is what produced the transcription analysis in §2.2.
- The task-file classification is mechanical where it can be — frontmatter, `## Notes` non-blank
  line count, presence of the unstarted-Notes placeholder, and the in-edge counts of the DAG — and
  verified against the tree per file for every deletion proposed.
- Deletion-set consequences (edges to drop, validator output, allowlist staleness) were computed
  programmatically over the frontmatter graph, not estimated.
- Four parallel agents read `docs/tasks/` in cohorts; three more read the model/spec, process/ledger
  and targets/spikes/root clusters. Their sharper findings were re-verified against the tree before
  inclusion — a discipline that caught two false completions (§12.1) and one stale premise in my
  own brief (`TASKS.md` is generated now, §5.1).
- Gates run at authoring time, each in its own invocation with its exit code read separately.
