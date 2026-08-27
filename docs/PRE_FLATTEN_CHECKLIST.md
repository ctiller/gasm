# Pre-Flatten Publication Checklist

This document governs the one-way transition of `gasm` from a private working
repository to a public, Apache-2.0-licensed open-source repository via a
**history flatten**: dropping all existing commits and replacing them with a
single initial commit of the working tree (D23, `PLAN.md`). After the
flatten, the old history is gone. Nothing recorded only in a commit message
survives it, and nothing that IS in the tree at flatten time can be
un-published once it has been pushed and mirrored/cloned/indexed elsewhere.

**Audit basis**: this checklist and its findings were produced against `main`
at commit `389d427` ("docs(plan): record D23 ... and D24 ..."), 2026-08-27.
Re-run every check in Part 2 against the actual commit you intend to flatten
- do not assume these findings still hold, especially for §1.3 below, which
this audit expects to change fast.

---

## VERDICT: NOT SAFE TO PUBLISH TODAY - ONE DOMINANT BLOCKER

Running `python scripts/check_publishable.py` at the audited commit exits
**1** with **1,108 blocking findings**. 1,096 of those are one thing:

**`references/` still contains all 1,049 files of vendored third-party
prose, and 47 first-party files still carry `REF:` citations into it.** The
owner's ruling (relayed mid-audit, superseding the redistributability
question this checklist originally answered): *"i don't want third party
prose in the repo by the time we publish."* This is broader than copyright
risk - it does not matter that `docs/THIRD_PARTY_LICENSES.md` already
classifies `wasi/`, `zlib/`, `png/`, and most of `windows/` as legitimately
redistributable-with-attribution. **None of `references/` may ship.** The
replacement design (`references.json` + slug citations, `docs/REFERENCE_INDEX.md`,
approved-with-changes as D24) is written but **not yet implemented** - this is
the single largest piece of remaining work before this repository can be
published, full stop. Everything else in this document is real but
secondary to it.

The remaining 12 findings are machine-local path leaks (§1.2) - small,
mechanical fixes.

---

## Part 1: Findings by Audit Category

### 1.1 Secrets and credentials

**Result: none found.** Swept every text-like file in the working tree
(`scripts/check_publishable.py`'s `SECRET_PATTERNS`: AWS credentials,
GitHub/Slack tokens, private key blocks, JWTs, password/secret assignments,
credentialed connection strings) - both tracked files and anything present
regardless of `.gitignore`, since a stale ignore rule must not hide a leak.
Zero hits. This is a point-in-time result, not a guarantee - the check is
mechanical and re-runs on every future change, but re-run it again
immediately before the actual flatten.

### 1.2 Machine-local and personal information

**12 findings, all low-severity documentation leaks** (no leak reaches
runtime code - the previously-flagged `Gasm/Targets/X86_64/NASM.lean`
hardcoded path and `docs/README.md`'s local `file://` links were
already fixed before this audit; D22's own text confirms this: *"a
since-removed hardcoded NASM path, and local `file://` doc links fixed only
in the working tree"*). What remains (paths below are redacted to the
generic pattern that leaked, per this section's own fix recommendation -
see **FIXED 2026-08-27** below for where the real fix landed):

| File | Issue |
|---|---|
| `PLAN.md` (D5 area) | Windows user path under `wsc` - predecessor project's local path, cited as provenance |
| ~~`docs/adr/OWNER_DIRECTIVES.md` line 42~~ | Windows user path under `wsc` - same predecessor-repo citation, **and now moot regardless**: the file itself was deleted in a later remediation pass (its content was a duplicate, hand-maintained transcription of owner quotes that drifted from the session trajectory; see [`0035`](adr/0035-decision-record-integrity-gate.md)), so this leak instance no longer exists anywhere in the tree, redacted or not. Left struck-through rather than removed, to keep this table an accurate record of what the audited commit (`389d427`) actually contained. |
| `docs/adr/0006-performance-model-as-strategic-asset.md` line 53 | Windows user path under `wsc` - same |
| `docs/adr/0008-demand-driven-model-growth.md` line 45 | Windows user path under `wsc` - same |
| `docs/tasks/F1-rdtsc-harness.md` lines 37, 220 | Windows user path under `wsc` - same, twice |
| `scripts/build_baseline.md` line 49 | A literal build-log example path under the owner's worktree directory |

Five of the six point at the same underlying pattern: the predecessor project `wsc`
lived at a path under the owner's Windows profile, and several design docs
cited that path directly as a provenance pointer (e.g. "Reference wsc repo at
&lt;the owner's Windows profile&gt;\wsc"). This was accidental machine-local
leakage, not attribution - a reader gained the owner's Windows username and
directory layout, for no documentation benefit the citation couldn't provide
without it. **FIXED 2026-08-27**: those five locations now read "the
predecessor `wsc` project (private, unpublished); see D5" or equivalent,
with no literal path; `scripts/build_baseline.md`'s worktree example now uses
a `<worktree>/.lake/build/ir/...` placeholder instead of a real path copied
from an actual build log. Verified via `python scripts/check_publishable.py`:
0 `MACHINE_PATH` findings remain for these five files. The sixth,
`docs/adr/OWNER_DIRECTIVES.md`, is not redacted-and-fixed like the other
five -- it is deleted outright (see the struck-through row above), which
closes the same leak by a different, later route.

**One additional item worth an explicit owner decision, not currently
flagged as a "leak" by the mechanical check because it's a schema example,
not committed data:** `docs/REFERENCE_INDEX.md`'s worked example for the
`references.json` entry schema (§1.2) uses `"reviewer": "craig.tiller@gmail.com"`
as the example value for the `reviewer` field, following the same
email-as-identity convention `scripts/license_allowlist.txt`'s `<added-by>`
field already uses. The difference in blast radius: once the registry is
populated, this field will likely repeat the owner's real personal email
address across every one of the (currently ~10, eventually more) entries in
a single public JSON file at the repository root - a much more prominent and
repeated exposure than a one-off git-author identity. This may be exactly
what the owner intends (their name is already the LICENSE copyright holder),
but it is a materially different kind of disclosure than a copyright line,
and should be a deliberate choice, not an inherited convention. Consider a
handle, initials, or "owner" instead before the registry is populated.

**No hits** for the owner's email in committed prose (only the one schema
example above), machine hostnames, local IPs (the `127.0.0.1` / `localhost`
literals in `Spikes/Spike4HttpServer/*.lean` and the WASI/Windows ABI trace
models are legitimate protocol literals, not leaked infrastructure), or temp
directories.

**Legitimate attribution, for contrast, not flagged as leakage:** `LICENSE`'s
and `NOTICE`'s `Copyright 2026 Craig Tiller` lines, and the first-name
references to "Craig" throughout `PLAN.md`/`docs/adr/*` as the decision-log's
record of the owner's own ruling (e.g. "D23 - ... (Craig, 2026-08-27)"). This
is exactly the intended kind of authorship record and must not be confused
with the path leaks above - the distinction is "does this reveal a machine's
local layout" (leak) vs. "does this attribute a decision to its author"
(fine, arguably required for an honest decision log).

### 1.3 Non-redistributable third-party content

**This section's own conclusion has been superseded by the owner's ruling**
(see Verdict above): it no longer matters which corpora are redistributable,
because none may ship. The classification work remains valuable for two
reasons the ruling explicitly preserved: (1) the `references.json` registry
entries that replace each corpus each carry a `license` token that must be
correct, and this classification is where that token comes from; (2) it
establishes, with evidence, that this repository *did* at one point contain
genuinely non-redistributable copyrighted material, which is relevant to how
urgently the flatten should happen relative to any further pushes of the
current history.

`docs/THIRD_PARTY_LICENSES.md` (471 lines, already in the tree) is a
thorough, well-evidenced per-corpus audit reaching the same bottom-line
verdicts I independently re-derived for the two highest-stakes corpora
before discovering that document:

- **`references/intel_sdm/` (928 files, 89% of the corpus) - NOT
  REDISTRIBUTABLE.** I independently confirmed Intel's SDM license text via
  web search (not by reading `THIRD_PARTY_LICENSES.md` first): Intel's grant
  is *"no rights are granted to create modifications or derivatives of this
  document"* with a narrow unmodified-copy exception. Reading
  `references/intel_sdm/vol_2_instruction_set_reference/instructions/ADD.md`
  directly confirms the corpus is a per-instruction Markdown re-derivation
  (reformatted opcode tables, added YAML frontmatter and BibTeX citation
  blocks not present in Intel's manual) - precisely the "derivative" Intel's
  license withholds permission for. This matches `THIRD_PARTY_LICENSES.md`
  §2.1's verdict and evidence independently.
- **`references/spirv/` (5 prose files) and `references/vulkan/` (72
  files) - NOT REDISTRIBUTABLE.** I independently found (web search against
  Khronos's own copyright page) that Khronos's Specification Copyright
  License permits reproducing only the *unmodified* Specification; this
  repository's corpus is HTML-to-Markdown-converted, split per chapter, with
  synthesized frontmatter - a modification. Matches `THIRD_PARTY_LICENSES.md`
  §2.2-2.3.
- The remaining corpora (`wasm/` genuine W3C files, `wasi/`, `zlib/`, `png/`,
  4 of 6 `windows/` files) are, per `THIRD_PARTY_LICENSES.md`, genuinely
  redistributable-with-attribution under their respective licenses (W3C
  Document License, Apache-2.0, permissive 1996-era RFC notices, zlib/MIT/
  public-domain, and CC-BY-4.0 respectively) - **and it no longer matters**,
  per the ruling. They ship out along with everything else in `references/`.
- `references/wasm/{binary,execution,structure,text}.md` (91 of 94 wasm
  citations) and `references/windows/{readfile,winsock2}.md` (14 of 37
  windows citations) are **not third-party material at all** -
  `THIRD_PARTY_LICENSES.md` §2.4/§2.8 confirms both open with an explicit
  "hand-authored summary, not the official text" disclaimer. These are
  first-party prose the project already owns the copyright on. They are
  *also* leaving `references/` under the ruling (the directory is deleted in
  its entirety, no exceptions - see §7 of `docs/REFERENCE_INDEX.md`), but if
  the owner ever wants to keep this specific content, it could legitimately
  move to `docs/` as first-party material with an Apache header rather than
  being deleted outright - a distinct question from the licensing one.

I did not re-derive every corpus's license text myself given the existing
audit's thoroughness and citation discipline; I independently verified the
two highest-consequence verdicts (intel_sdm, Khronos) and found them
correct, which is the load-bearing check this document owed the ruling.

**Citation impact of full deletion**, per `scripts/check_publishable.py`'s
`REF_CITES_BANNED_PROSE` check: **47 first-party files, ~260+ individual
`REF:` citations**, concentrated in `Gasm/Targets/X86_64/**` (intel_sdm),
`Gasm/Targets/Wasm/**` (wasm), and `Gasm/Targets/Windows/**` (windows/pe
format). None of this can be deleted safely until each citation is
re-pointed at the `references.json` slug registry design
(`docs/REFERENCE_INDEX.md`) - deleting `references/` first would silently
orphan the entire x86-64 encoder/decoder/registry/fuzzer/perf-model surface's
citation trail.

### 1.4 License and attribution completeness

Already substantially in place, unlike at an earlier snapshot of this
repository:

- **`LICENSE`** (Apache License 2.0, full text) - present at repo root. Good.
- **`NOTICE`** - present at repo root, with a "Third-Party Content" section
  attributing `references/`'s vendored material. **This section will become
  false once `references/` is deleted** (§1.3/§7) - it currently says the
  project "vendors third-party reference material... used as citation
  targets," which stops being true. Revise `NOTICE` as part of the
  `references/` migration, not as an afterthought; do not let it silently go
  stale (a `NOTICE` file that claims to vendor content that no longer exists
  is itself a small honesty defect in a legal document).
- **`docs/THIRD_PARTY_LICENSES.md`** - present, thorough, self-described as
  "not legal advice," correctly errs toward flagging. Once `references/` is
  deleted this document's per-corpus verdicts become historical record
  rather than a live compliance surface; consider a one-line status banner
  at the top noting the corpora it describes no longer ship, rather than
  deleting the document (it remains valuable as the answer to "was anything
  non-redistributable ever in this repository," which D23 flags as newly
  relevant precisely because the flatten will erase the commit history that
  otherwise would have shown this).
- **Attribution text for the corpora that would have needed it** (CC-BY-4.0
  `windows/`, Apache-2.0 `wasi/`) is already drafted, ready-to-paste, in
  `docs/THIRD_PARTY_LICENSES.md` §3 - moot once those files are deleted along
  with the rest of `references/`, but worth keeping as a template if the
  registry's `references.json` design ever needs equivalent NOTICE-style
  attribution text for entries marked `attribution-required`.

### 1.5 Apache header coverage

`scripts/check_licenses.py` already exists (480 lines) and is well-designed:
normalized (not byte-exact) header comparison tolerant of per-language
comment syntax, a `scripts/license_allowlist.txt` with the same 5-field
`::`-delimited discipline this task's brief asked for, hard-fails on stale
allowlist entries, and reports its `references/` exclusion count on every
run rather than silently excluding. I assessed its exclusion list and find
it honest:

- **`references/**` excluded** - correct and explicitly justified in the
  module docstring ("every file there is third-party vendored reference
  material... must NEVER receive our copyright header"). Once §1.3/§7's
  migration lands and `references/` no longer exists, this exclusion becomes
  vacuous (0 files) rather than wrong - no change needed to the script.
- **`.lake/`, `.git/`, `.system_generated/` excluded** - correct, build/VCS
  internals.
- **`docs/**` and root Markdown ledgers (`PLAN.md`, `TASKS.md`,
  `MODEL_DEBT.md`, `TCB.md`) excluded from header stamping** - a stated,
  reasoned judgment call (prose documentation is covered by the repository
  `LICENSE` as a whole; this project does not stamp per-file boilerplate onto
  prose the way it does onto compiled/executable source), not a silent gap.
  I agree this is a defensible, common convention (many Apache-2.0 projects
  do not header-stamp Markdown) and is not "quietly skipping real
  first-party code" - the exclusion is source-code-shaped, not
  documentation-shaped, i.e. it does not exempt anything that runs.
- Running `python scripts/check_licenses.py` at the audited commit: **183/183
  in-scope files compliant, 0 missing, 0 malformed, 0 allowlisted** (exit 0).
  `scripts/license_allowlist.txt` is seeded empty and stays empty - no
  first-party file needed an exception.

`scripts/check_publishable.py` (this task's deliverable) deliberately does
**not** re-implement this check; it shells out to `scripts/check_licenses.py`
in the foreground and folds its exit code into its own (see §2 below), the
same way `check_refs.py` is its own standalone tool rather than being merged
into something else.

### 1.6 What the flatten destroys

`PLAN.md`'s own D23 entry already states this checklist's §6 conclusion
precisely, dated the same day as this audit: *"anything recorded only in a
commit message is destroyed... `PLAN.md`, `docs/adr/`, and `docs/tasks/` are
the sole surviving decision history. Anything load-bearing must be written
INTO the tree before the flatten."* I confirm this independently: `docs/adr/`
holds ratified ADRs numbered sequentially in ratification order (not aligned
with `PLAN.md`'s independent `D`-numbering - the two are different sequences
for different things, and a document that describes one in terms of the
other's numbers, as an earlier draft of this checklist did, misstates both),
`docs/tasks/` holds 40+ task design documents, and `PLAN.md`/`TASKS.md` hold
the live coordination surface - this is a genuinely mature decision-record
apparatus, not merely commit-message subject lines. Coverage of `PLAN.md`'s
`D`-numbered decisions by a dedicated ADR is verified mechanically by
`scripts/check_record.py` (see [`0035`](adr/0035-decision-record-integrity-gate.md)),
not asserted in prose here. D19's migration (moving `MODEL_DEBT.md`, `TCB.md`,
`GRAPHICS_PREBUILD_AUDIT.md` under `docs/`) is recorded as "queued," not yet
executed as of this audit - low risk either way since those files are
already tracked in the working tree and would survive the flatten regardless
of which directory they live in, but tidy it before publish for
consistency with D19's own rationale.

One item D23 itself flags as **newly urgent because of the flatten,
specifically**: the Intel SDM frontmatter side-table (926 files' worth of
page ranges, order number, printed page labels) exists nowhere else on
earth once `references/intel_sdm/` is deleted and history is dropped.
This extraction is now DONE and committed as `docs/intel_sdm_frontmatter.json`
(926 files; census independently re-derived with zero discrepancies against the
design review's published numbers; 10 files carry an embedded newline inside the
quoted `manual_pages` scalar, joined with a space on extraction). Verify it is
present before deleting the corpus, not after - D24's own review already caught
one page-offset framing bug in this exact extraction (SDM volume-relative
vs. combined-manual-absolute page numbers), underscoring that this step is
easy to get subtly wrong and hard to redo once the source is gone.

#### Procedure: the commit-message-only content audit

This is the actionable half of this section, and it must be re-run immediately
before the flatten executes, since more commits land in the meantime.

Walk commit messages since the last time this audit ran (or, the first time, since the project's
start) for load-bearing findings, hazards, decisions, or numeric results that are **not**
duplicated anywhere in `PLAN.md`, `docs/adr/`, or `docs/tasks/`. Transcribe anything load-bearing
into the appropriate tracked file before the flatten.

Two concrete instances found during the `docs/REFERENCE_INDEX.md` design revision, neither yet
resolved:

- [ ] Commit `c2f5bae`'s finding — *"a checksum manifest can merge cleanly and still be wrong"*
      (two branches each validly modified `references/MANIFEST.sha256`; the merge was
      conflict-free and semantically wrong) — has no mechanical gate yet (Law 13). Either build
      the gate before the flatten, or at minimum record the finding itself in `TCB.md` or
      `PLAN.md`'s gaps register so it is not lost.
- [x] Commit `2fc3c3d`'s Wasm re-pointing record (90/93 citations moved, 3→99 genuine-citation
      ratio, `binary.md`/`execution.md` deleted, `structure.md`/`text.md` reduced to stubs) — now
      restated in `docs/REFERENCE_INDEX.md` §6.1/§6.4, so this specific instance is covered.

Re-run this audit again immediately before the flatten actually executes, since more commits will
have landed between when this checklist item was last checked and flatten time.

### 1.7 Build and tooling residue

- `.gitignore` (13 entries as of this audit, up from 5 at an earlier
  snapshot: adds `.tmp_*` and `*.tmp`) correctly covers Lean's build output,
  this project's WASM/NASM emission targets, and Python caches.
- `git status --ignored` is clean at audit time - no stray `.lake/`, build
  output, or OS/editor cruft (`.DS_Store`, `Thumbs.db`) sitting in the
  working tree.
- `git ls-files` contains **zero** tracked files matching build/binary
  extensions (`.exe .o .olean .ilean .dll .so .bin .zip` etc., per
  `scripts/check_publishable.py`'s `TRACKED_BINARY_EXTENSIONS`) - confirmed
  mechanically, not just by eyeballing `git status`.
- Residual gap: `.gitignore` still has no entries for editor/OS cruft
  (`.vscode/`, `.idea/`, `.DS_Store`, `Thumbs.db`, `*.swp`, `*.log`). None
  present today, but add these preemptively (Part 2, Step 4) since nothing
  stops an editor autosave from introducing one before the flatten.
- No CI configuration (`.github/workflows/`) exists yet - none of
  `scripts/check_*.py` currently runs automatically anywhere. Out of scope
  for this checklist (publishability, not CI setup), but worth the owner's
  attention separately: a public repo with mechanical gates that nothing
  ever runs is a maintenance risk the moment external contributors show up.

---

## Part 2: The Checklist

Run every step from the repository root. Steps 1-6 are non-destructive and
repeatable; re-run them as many times as needed until they're all clean.
**Step 7 is the irreversible gate.** Nothing after Step 6 should be attempted
until every earlier step passes cleanly on the actual commit being flattened.

### Step 1 - Land the references.json migration (THE dominant blocker)

This is design-complete (`docs/REFERENCE_INDEX.md`, D24 approve-with-changes,
11 mandatory corrections noted) but not yet implemented. In order:

1. Apply D24's 11 mandatory corrections to the design (notably: fix the
   SDM page-offset frame bug - combined-manual-absolute, not
   per-volume-relative - before it propagates into 267 citations).
2. Extract and commit the Intel SDM frontmatter side-table (page ranges,
   order number, printed labels) to `references.json` / its supporting
   data - the "newly urgent" item from §1.6. Do this before touching the
   corpus itself.
3. Build `references.json` at repository root (replacing
   `references/MANIFEST.sha256` and `references/MANIFEST.provenance.json`)
   and `scripts/check_references.py` (citation/anchor/hash validator against
   a local, gitignored cache - never against a committed copy). This is the
   sibling workstream `check_publishable.py`'s module docstring explicitly
   declines to duplicate.
4. Re-point every one of the 47 files / ~260+ citations
   `scripts/check_publishable.py`'s `REF_CITES_BANNED_PROSE` check currently
   flags from `references/<path>.md#<anchor>` to `<slug>#<anchor>`.
5. Only once `scripts/check_references.py` passes and
   `REF_CITES_BANNED_PROSE` is empty: `git rm -r references/`.
6. Revise `NOTICE` to drop the now-false "vendors third-party reference
   material" claim (§1.4). Add a status banner to
   `docs/THIRD_PARTY_LICENSES.md` noting its corpora no longer ship (§1.4) -
   keep the document; do not delete it (§1.6's "was anything
   non-redistributable ever here" question needs a durable answer once
   history is gone).

### Step 2 - Fix machine-local path leaks (§1.2)

**DONE 2026-08-27** - replaced the 6 files' literal Windows-user-profile
`wsc`-path / worktree-path citations with path-free provenance descriptions
(§1.2 above). Still open: decide the `references.json` `reviewer` field's
identity convention (email vs. handle) before the registry is populated at
scale (§1.2's schema-example note).

### Step 3 - Re-run the mechanical gates (dry run)

```
python scripts/check_publishable.py --list-only
python scripts/check_licenses.py
python scripts/check_refs.py
```

`--list-only` always exits 0 and prints every finding without stopping you,
so Steps 1-2 can be iterated against a full punch list.

### Step 4 - Harden `.gitignore`

Add editor/OS cruft entries (`.vscode/`, `.idea/`, `.DS_Store`, `Thumbs.db`,
`*.swp`, `*.log`) even though nothing currently trips them (§1.7).

### Step 5 - Enforce the gate

```
python scripts/check_publishable.py
echo "exit code: $?"
```

Capture the exit code directly (foreground, no pipe - masking a real exit
code through a pipe has produced false greens on this project before).
**Do not proceed past this point until this prints `exit code: 0`.** Any
remaining finding must be fixed, or - for the categories that permit it
(`SECRET`, `MACHINE_PATH`, `TRACKED_BINARY`, `ROOT_LICENSE_TEXT` only;
`THIRD_PARTY_PROSE` and `REF_CITES_BANNED_PROSE` have no override) -
explicitly recorded in `scripts/publish_allowlist.txt` with a real
justification.

Also re-run the citation/reference integrity tools this script intentionally
does not duplicate:

```
python scripts/check_refs.py
python scripts/check_references.py --verify   # once it exists (Step 1.3)
python scripts/check_gates.py
```

`check_refs.py` must report zero broken citations after Step 1's
`references/` deletion.

### Step 6 - GATE: confirm intent, then flatten (IRREVERSIBLE)

Everything above this line is reversible. This step is not: once the
flattened history is pushed and the old branch/history is deleted from the
remote, and especially once anyone has cloned, forked, or mirrored it, the
dropped commits are permanently gone from the public record (they may
persist in local clones/forks you don't control, but you cannot use force to
retract those).

**Before running anything below, get explicit human confirmation** (this
document is design-and-audit only - it does not authorize performing the
flatten) that:
- Step 5's gate exited 0 on the exact commit about to be flattened.
- Step 1's migration is genuinely complete - `references/` does not exist,
  `REF_CITES_BANNED_PROSE` is empty, and the Intel SDM frontmatter data
  survives independently of the deleted corpus.
- A backup of the pre-flatten repository (with full history) exists
  somewhere private, in case something in Part 1 was missed and needs to be
  recovered after the fact.

Only then, as a separate, explicitly authorized action performed by the
repository owner or an explicitly authorized agent - not inferred from this
document:

```
# Illustrative only.
git checkout --orphan publish-flat
git add -A
git commit -m "Initial public release"
```

### Step 7 - Post-flatten verification

Run against the **newly published** repository, from a fresh clone (not the
working directory that produced it - a fresh clone catches anything that was
only "clean" because of local ignored/untracked state):

```
git clone <new-public-remote-url> /tmp/gasm-publish-verify
cd /tmp/gasm-publish-verify
python scripts/check_publishable.py
echo "exit code: $?"
git log --oneline    # must show exactly one commit
git rev-parse HEAD~1  # must error - confirms no parent history survived
```

Confirm:
1. `check_publishable.py` exits 0 on the fresh clone.
2. Exactly one commit exists (`git log --oneline` prints one line).
3. `references/` does not exist in the clone at all.
4. `LICENSE` and `NOTICE` exist, `NOTICE` no longer claims to vendor
   third-party reference material, and `check_licenses.py` exits 0.
5. The tree matches what was intended - diff the fresh clone against the
   pre-flatten working tree (excluding `.git/`) and confirm the only
   differences are the Part 2 fixes deliberately made, nothing else was lost
   or accidentally added by the flatten mechanics themselves.
