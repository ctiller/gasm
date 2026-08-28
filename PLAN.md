# Repair Epic — Plan & Tracker

> **OPERATING MODE CHANGE (Craig, 2026-08-27): phases below are ADVISORY/historical.
> The live plan is TASKS.md — a happens-after task DAG with BARS marking fresh-agent
> deep-re-review points. Grind ready tasks; critical paths to graphics and networking
> are explicit there. EXIT CRITERION for repair: we trust the system enough that
> spec & model review is something we do, implementation review is something we trust
> mechanically.**
> **WORKFLOW FINDING (2026-08-27, surfaced by the N1 agent): uncommitted coordinator
> state does not reach worktree agents.** Isolated worktrees branch from committed
> history, so PLAN/TASKS/ledgers/docs-tasks that were uncommitted at dispatch time are
> invisible in the agent's own tree — agents must read them cross-worktree (works, but
> fragile) and CANNOT update their own task-file frontmatter (status/design fields),
> so the DAG's status data goes stale unless the coordinator maintains it centrally.
> Fixes: (a) commit planning artifacts BEFORE dispatching a wave; (b) coordinator owns
> frontmatter status transitions, or TC13's checker/regenerator does; (c) dispatch
> briefs state which worktree holds the planning files.
> FOURTH — THE EXPENSIVE ONE (2026-08-27): dispatching a wave from worktrees created
> BEFORE the integration state was committed cost real duplicate work. TC17 and TC9 each
> independently re-found and re-fixed bugs already fixed on the integration branch (the
> fail-open hardware harness; the Wasm oracle ignoring its error field), and TC17's
> `[SKIP]` labelling duplicates the hygiene branch's. Both then needed rebase-and-
> reconcile cycles. RULE: commit integration state and dispatch worktrees from the tip;
> state the expected base commit in every brief; when an agent reports a "new" finding,
> check it against the integration tip before acting on it.
> FIFTH: an agent can enter a degenerate wait-loop (TC15 stalled 3× at 250k tokens /
> 140 tool calls, consuming nudges and returning to the same wait). Kill and relaunch
> with an explicit no-background-jobs constraint rather than nudging repeatedly.
> THIRD (B1, 2026-08-27): an agent that backgrounds a long command and stops "waiting to
> be woken" STAYS STOPPED — nothing wakes it. The coordinator must nudge it via
> SendMessage (context survives). Dispatch briefs for long-build tasks should say:
> poll your own background job; do not stop expecting a wake-up.
> COMPOUNDING (found by the G1 agent): some isolated worktrees were branched from a
> STALE commit (`ca78469`, pre-dating VISION/PLAN/ledgers/Laws 10-13) rather than the
> integration tip — the agent detected it, verified ancestry, and fast-forwarded
> (`--ff-only`) itself. Dispatch briefs must state the expected base commit so agents
> can check; and agent branches that edit PLAN.md/SPIKES.md (G1 did, for housekeeping)
> will conflict with concurrent coordinator edits — sequence those merges deliberately.
> **D20 — operating mode (owner, 2026-08-27, verbatim): "autonomous mode, maximize
> saturation, let's get to a trustable base".** See
> [`0033`](adr/0033-autonomous-saturated-dispatch.md) for the full decision record. The
> coordinator dispatches to the
> practical capacity ceiling without waiting for turn-by-turn approval, sequencing
> against the task DAG's frontier, and stops only for the gates the owner has set
> (D18's scoping conversations, D17's fable authorization, law ratification).
> "Trustable base" is the repair epic's exit criterion restated: spec and model review
> is something we do; implementation review is something we trust mechanically.
> Practical ceiling observed on this machine: ~11 concurrent agents before dispatch
> rate-limiting and build contention dominate. (This directive went briefly unrecorded
> during the trajectory remediation pass before landing here as D20 — the gap was
> caught by re-reading the session transcript directly, not by a secondary index; see
> [`0035`](adr/0035-decision-record-integrity-gate.md) for why a hand-maintained index
> was rejected as the fix for that gap.)
> **D21 — commit trailer must not fabricate authorship (owner, 2026-08-27).** See
> [`0034`](adr/0034-commit-trailer-must-not-fabricate-authorship.md) for the full
> decision record. The
> coordinator had agents write `Co-Authored-By: Claude Fable 5` on commits whose work
> was done by Sonnet and Opus agents — a false attribution, and not the string the
> harness specifies either. Correct form going forward: `Co-Authored-By: Claude
> <noreply@anthropic.com>` — true without asserting a model that did not do the work.
> ~15 existing commits carry the false trailer; fix in the history scrub (D22).
> **D22 — history scrub before open-sourcing (owner, 2026-08-27; quiesce expected
> today).** Known items: (a) fabricated co-author trailers (D21); (b) machine-local
> absolute paths in history (a since-removed hardcoded NASM path, and local `file://`
> doc links fixed only in the working tree); (c) credential/token/private-path audit —
> verify, do not assume clean; (d) whether agent-branch noise and merge topology should
> be squashed or preserved — preserving it documents the review discipline honestly, so
> this is a judgment call, not automatic; (e) build artifacts if any were ever committed.
> The scrub runs AFTER the licensing verdict, since removing a `references/` corpus is
> itself a history rewrite.
> **D19 — planning output lives in `docs/` (owner, 2026-08-27).** Every planning task's
> deliverable — designs, architecture audits, model/trust ledgers — is written under
> `docs/`, not at the repo root. In-flight designs already comply
> (`docs/PATHFINDER_CRC32.md`, `docs/TARGETS/WIN32_DIFFERENTIAL_HARNESS.md`,
> `docs/CALIBRATION_GOVERNANCE.md`). MIGRATION QUEUED (execute when the tree is quiet —
> the fix agent currently holds these files): `MODEL_DEBT.md`, `TCB.md`,
> `GRAPHICS_PREBUILD_AUDIT.md` → `docs/`; `PLAN.md`/`TASKS.md` → `docs/` as the
> coordination surface. The root-placement rationale they carried (keeping process
> paperwork out of `check_refs.py`'s unreferenced-section backlog) is superseded by the
> backlog-exclusion mechanism being added for `docs/adr/` and `docs/tasks/` — extend it
> to cover the moved files rather than keeping them out of `docs/`. Update every
> in-repo path reference (task files, ADRs, briefs) as part of the move.
> **D18 — LARGE systems planning is never delegated cold (owner, 2026-08-27).**
> **Large := more than ~10 kLOC will be written under the design.** Such a design is
> NEVER dispatched to sonnet, and never dispatched at all before a scoping conversation:
> *we talk → we decide the scope → then the coordinator dispatches* (tier per D17 —
> opus by default, fable on the owner's say). The coordinator's job for these is to
> bring the question, the options and the tradeoffs to the owner, not to pre-empt them
> with a design brief. Small designs (a harness, a file format, one routine's contract)
> remain normal sonnet work.
> GATED ON A SCOPING CONVERSATION (not dispatchable): PA2 (step-lemma library +
> composition calculus — governs every routine proof), PA4 (Law 11 capability migration
> across the authoring surface + Zlib), PA9 (VerifiedProgram as derived theorem),
> the graphics subsystem G2/G3/G5/G6/G7 (DSLs, SPIR-V emitter, Vulkan host model,
> Spike 6), N6 (TCP/HTTP-2/protobuf/gRPC buildout), F6 (zlib optimization epic).
> Borderline, coordinator judgment, flag when reached: TC14 (PE parser + connection
> theorem), B3 (decoder modularization), PA5–PA7 (contract-layer reshaping).
> **D17 — model tiers (owner, 2026-08-27). Workforce: sonnets as implementors, opus as
> reviewers. Coordinator: fable for BOOTSTRAPPING (standing up the system — this
> session), opus for RUNNING THE QUEUE (dispatch/synthesis against an established DAG).
> Systems planning (what does the graphics subsystem look like; vision-scale
> architecture) MAY deploy fable — but only on the owner's explicit say, never at the
> coordinator's discretion.** Operational consequence: when the DAG surfaces a
> systems-planning design task, the coordinator names it as a fable candidate and
> proceeds on sonnet unless the owner says otherwise — it does not block the queue and
> it does not self-authorize. First candidates: PA2 (step-lemma/composition calculus),
> G2 (synchronization DSL), G3 (FP kernel DSL), later N6 (networking architecture),
> F4/F5 (cost-function shapes), G6/G9 (Vulkan host model, Spike 7).
> Design/spec AUTHORING counts as implementation (sonnet); opus is for review only.
> **Every Agent dispatch MUST pass `model` explicitly, and every dispatch brief MUST
> instruct the agent to pass `model: "sonnet"` explicitly on any sub-agents it spawns** —
> an omitted model parameter can inherit the session tier (Fable 5), which is how
> nested fan-outs (a sonnet agent spawning five writers) silently ran on the top tier.
> Incident 2026-08-27: 11 direct dispatches were correctly tiered; nested grandchildren
> from three fan-outs were not, because the briefs omitted the rule. PA1's design was
> launched on opus and re-launched on sonnet on correction.
> **D16** — decision-record reviews are grounded in the recorded trajectory: ADRs and
> governance docs are audited against the session's JSONL transcript (the owner's actual
> words), never only against derived artifacts like PLAN.md — a record backfilled from a
> summary and verified against the same summary is a closed loop that validates
> transcription, not truth. Transcript path pattern:
> ~/.claude/projects/<project>/<session-id>.jsonl.
> **D16-a (owner, 2026-08-27, welds D15+D16): the review discipline for ANYTHING the
> coordinator authors — the reviewing agent MUST also check the trajectory for the
> owner's words.** Every coordinator-work review verifies attribution and modality
> against the JSONL, not against coordinator summaries. Rationale (empirical, same day):
> the first trajectory audit found systematic one-directional drift — owner modality
> upgraded ("i think i like that"→ratified; "probably"→"from day one"; "my preferred
> vector"→"the universal binder"; "i'm imagining"→"mandated"), coordinator design filed
> under the owner's name, one invented owner-attributed fact in ADR-0020, and the
> owner's exact words altered inside quote formatting. ADR pending in remediation pass.
> **D15** — the coordinator's work is reviewed too: every substantive body of
> coordinator-authored changes (governance/doc text, merge-conflict resolutions,
> ledger transcriptions, plan restructures) gets a fresh adversarial reviewer before
> its merge train commits — no unreviewed writer in the system. (Evidence: one
> ratified-intent drift catch on 2026-08-27 — the BAR-scope narrowing against
> ADR-0010 — was coordinator text caught by the owner directly, not a reviewer.
> CORRECTED 2026-08-27 remediation pass: this line and ADR-0020 previously claimed a
> SECOND such catch, "a stale law count," also attributed to the owner; the transcript
> does not support that — the law-count/spike-list staleness was a reviewing agent's
> own finding in its deep-review report, not the owner reading coordinator text. See
> ADR-0020's Provenance section.) ADR-0020.
> **D14** — notes→design→REVIEW→implementation: working notes append to the task file;
> consolidated into a design before implementation; **the design (model/spec) is
> reviewed by fresh agents while context is small, BEFORE implementation dispatches**
> (Law 5-class mandatory; graphics pre-build audit = exemplar). ADRs 0018/0019.
> Further decisions: **D12** — no review archive (reviews are proof-of-work +
> falsifiability consumed at read time; instantly stale after). **D13** — TCB policy:
> everything trusted-but-unprovable (environment, hardware, APIs, tools) gets a
> differential fuzzer validating our model of it (TCB.md ledger — Opus research
> DONE, deliverable committed at repo root). CI will be established (location: Craig chasing down).
> **2026-08-27 update**: location decided — GitHub Actions (`windows-latest` primary,
> `ubuntu-latest` covering the portable gate subset today; vendor-supplied self-hosted Linux
> joins the same matrix later). See `docs/CI.md` and `docs/tasks/TC6-ci-establishment.md`. Linux hardware
> comes once the codebase is in better shape (cost a factor; Craig has ideas).

> Working tracker for the "repair" epic (build trust in the codebase → detect duplication →
> plan next spikes). Lives at repo root deliberately: `docs/` is the design-spec surface
> indexed by `check_refs.py`; this file is operational state, not specification.
> Keep statuses current — this file is the cross-session source of truth for the epic.

Vision anchor: `docs/VISION.md`. Governance: `docs/REVIEW.md` Laws 1–14.

## Decisions (ratified 2026-08-27)

- **D1 — native_decide**: allowed ONLY for propositions exhaustively quantified over their
  entire finite domain (Law 10). Single-instance checks are regression tests (`*_inst`,
  designated modules, never citable as verification).
- **D2 — Universality via modular decomposition**: ∀-correctness of the Lean model and
  ∀-equivalence model↔asm, made tractable by per-routine contracts + composition rules;
  agents co-author (contract, asm, proof) triples. Not fuzz-first, not whole-program
  monolithic proofs.
- **D3 — Memory safety**: adopt the dormant Core capability machinery
  (`MemoryPermissions`/`BlockM`/obligations) as the authoring surface; memory access
  without a capability proof must fail to assemble (Law 11).
- **D4 — Duplication**: connection theorems + linter, PLUS review-protocol audit on top
  (embedding-similarity triage as tooling extension) (Law 12).
- **D5 — Performance modeling is strategic**: static model → agents optimize without
  executing; needs its own differential validation (fuzzer vs real hardware — resurrect
  from the predecessor `wsc` project's `Tools/PerfFuzzer.lean` + `benchmarks/`). End-state: parametric
  cost functions with concrete coefficients (`5·N² + 3·N + 293` cycles under a named
  profile), never bare big-O. Cost functions live on routine contracts, regression-gated.
- **D6 — Workflow**: fan out sonnet agents in separate worktrees for implementation;
  adversarial review (three-pillar, REVIEW.md §4) before merge; agents' claimed results
  are unverified until re-run in the merged tree.
- **D9 — Findings become gates; check ∀, fix ∀ (Law 13, ratified 2026-08-27)**: every
  review/fuzz finding must terminate in a mechanical prevention of its whole class —
  preference: unrepresentable by construction > build-time theorem > build-failing
  linter > (world-sampling only) oracle control vectors. Reviewer catches are evidence
  of missing gates. Pointwise sentinels only where the world itself is sampled; artifact
  properties get ∀-shaped prevention (typecheckers + registry-exhaustive theorems,
  Except-typed oracle outcomes nothing can synthesize). Every dispatch I write must
  include the gate obligation, not just the fix. NORTH STAR (Craig): review's only
  irreplaceable question is "are we proving the right theorems" (spec adequacy, real
  domains, no shrunken stand-ins); every other review finding = a missing mechanical
  gate. Reviewer prompts should weight Pillar 2 accordingly as gates accumulate.
  Gate obligations from today's findings:
  decoder gaps → registry roundtrip gate (queued); Wasm vacuous modules → Lean Wasm
  validator + ∀-registered-case validity theorem (in fix cycle); both fail-open oracles →
  Except-typed outcomes, catch-synthesize deleted (in fix cycles); Law 9 debt → check_gates
  linter (done, in re-review); harness/engine sanity → positive+negative+trap controls.
- **D11 — DSLs as the unit of proof leverage (Craig, 2026-08-27; VISION §4)**: prove
  the language in total, apply to every inhabitant; DSLs compose (layered lemma
  libraries). Reach for a DSL wherever there's a population — even closed, even size
  one if it separates proofs. Operational consequences: Phase 4's step-lemma library +
  composition calculus ARE the total theorems of the assembly DSL (frame it that way in
  the design doc); the registry gate is the closed-population exemplar; Zlib's bit-
  reader/Huffman machinery should become mini-DSLs with their own lemma libraries
  before the optimization epic (one language-level proof, many optimized inhabitants);
  every new subsystem design starts by asking "what is the language here?"; DSL-level
  proving is the primary mechanism making proof cost sublinear at the D-scale (10M LOC).
- **D10 — Bar-triggered deep re-review (Craig, 2026-08-27; scope corrected same day)**:
  at each BAR, fresh OPUS agents re-do the deep codebase review FROM SCRATCH over the
  **entire codebase** — never scoped to the recent work (scoped review is what
  per-branch reviewers already did; the bar catches what scoped reviews structurally
  cannot: unknown-unknowns, cross-branch interactions, rot in untouched corners).
  Blinded to prior review conclusions; may read PLAN/TASKS/ledgers as the CLAIMED state
  to check against reality. Reports: (a) doc/law/ADR-vs-code drift anywhere, (b) whether
  merged work's claims hold, (c) new findings ranked tree-wide, (d) tracking verdict —
  on/off course, (e) convergence metric. Triggers are milestones (bars in TASKS.md);
  scope is always global. First bar: after trust-core lands on main. The review-quality metric to watch (per D9 north star): what
  fraction of findings are right-theorem questions vs mechanical catches — that ratio
  is the convergence meter for the whole epic.
- **D7 — Demand-driven model growth (wsc lesson)**: the predecessor (wsc/Lasm) died by
  building out too much ISA as code before the instruction model was right — repair cost
  exceeded rebuild cost. Therefore: models stay deliberately incomplete, grow only on
  spike demand (Law 5), and every increment is differentially validated in the change
  that introduces it, before anything depends on it. Never bulk-import ISA surface.
  (Also VISION.md §3.3.) This makes Phase 3 (validating the existing unvalidated half of
  the x86 model) the countermeasure to the exact wsc failure mode, and rules out
  "complete the ISA" as a goal.
- **D23 — The repository will be FLATTENED, not history-scrubbed (Craig, 2026-08-27)**:
  "we will flatten the repo as soon as the scrub is done - history will be dropped." See
  [ADR-0031](adr/0031-flatten-not-history-scrub.md) for the full decision record.
  This SUPERSEDES D22 (surgical history rewrite via `git filter-repo`). Consequences,
  which run in both directions:
  - *Cheaper*: no path-glob surgery across ~900 commits; the non-redistributable
    `references/intel_sdm/` corpus and the ~15 fabricated `Co-Authored-By: Claude Fable 5`
    trailers (D21) simply cease to exist rather than needing excision. The entire
    "purge from historical commits" workstream is cancelled.
  - *More dangerous*: *only the final working tree is published*. Every defect in the
    tree at flatten time becomes permanent public record, and **anything recorded only in
    a commit message is destroyed**. Commit messages are therefore no longer a durable
    record: `PLAN.md`, `docs/adr/`, and `docs/tasks/` are the sole surviving decision
    history. Anything load-bearing must be written INTO the tree before the flatten.
  - *Newly urgent*: the Intel SDM frontmatter side-table (926 files: page ranges,
    order number, printed page labels) exists nowhere else on earth. Once the corpus is
    deleted AND history dropped, it is unrecoverable. Extraction-to-JSON is now a
    prerequisite to both, not a nicety.
  - The flatten is irreversible and gated on a pre-flatten checklist
    (`docs/PRE_FLATTEN_CHECKLIST.md`) covering secrets, machine-local paths,
    redistributability of every retained corpus, and license/attribution completeness.
- **D24 — Reference index design: APPROVE-WITH-CHANGES, 11 mandatory corrections
  (2026-08-27)**: the adversarial review validated the architecture (uniform indexing,
  JSON over YAML, network-free `--offline` default, drift-as-finding, dead-URL-as-failure)
  and confirmed by full census that the frontmatter invariant the whole migration rests on
  is 100% complete on content files — no long tail. What failed was the layer between that
  data and the emitted locators. Two findings are worth remembering beyond this task:
  - **The page numbers were in the wrong frame.** `pp=` was to be emitted as an offset into
    per-volume PDFs, but the frontmatter records absolute offsets into Intel's *combined*
    5,363-page manual (uniform order number `325462-092US`; contiguous monotone ranges
    across volumes). All 267 SDM citations would have been silently mislocated — Vol 2 by
    ~614 pages, Vol 3 by ~3,201 — and the design's own worked example was wrong by 614.
    Nothing would have caught it, because the one check that could (a page-range bound) was
    left optional and the wrong number was still in range. *A locator that is plausibly
    wrong is worse than one that is obviously broken.*
  - **A count reached by subtraction hid a whole class.** The claimed 212/55 split was
    really 159/108: 53 citations target a chapter file that matched no branch of the
    migration script and would have fallen through. The corrected rule is that an
    unrecognized shape must fail closed rather than fall through.
- **D26 — Reference index landed: `references.json` + `scripts/check_references.py`,
  267 Intel SDM citations migrated, scope widened by D25 (Coordinator-implemented,
  2026-08-27)**: implements D24's corrections. ONE `intel-sdm` slug for the
  combined document (not four per-volume slugs); locator grammar
  `vol=V;(instr=M|sec=S);part=P;pp=A-B;mp=ENCODED` with `part=` carrying today's anchor
  through unchanged (fixes the Operation/Description collision) and `mp=` from
  `manual_pages` (drift-resistant printed-page coordinate); `page_count` required for every
  `pdf-locator` entry; `edition` required/non-empty; `--offline` recomputes SHA-256 of the
  cached bytes on every run (never compares two recorded numbers — the sidecar meta file
  was dropped as redundant); unrecognized citation shapes fail closed. Mid-task the owner
  widened the scope (see D25 for his verbatim words) from an Intel-only, licence-driven
  cleanup to the removal of all vendored prose regardless of redistributability — the
  preceding characterisation is the coordinator's paraphrase, not a quotation —
  `references.json` now also registers wasi, zlib (RFC 1950/51/
  52), png (RFC 2083 + lodepng/stb sources), spirv (grammar JSON + spec HTML), and vulkan
  (spec HTML), each with a genuinely fetched URL and hash; wasm and windows registry
  entries are left to the sibling agents already re-pointing those corpora's citations.
  **One finding worth carrying forward: the `intel-sdm` entry is pinned to a genuinely
  live, hash-verified URL (`cdrdv2-public.intel.com/671200/325462-sdm-vol-1-2abcd-3abcd.
  pdf`) whose content is Order Number 325462-078US, December 2022 — NOT the 325462-092US,
  December 2024 edition that `references/intel_sdm/`'s own frontmatter (and therefore
  every migrated `pp=`/`mp=` locator) was derived from.** A live copy of the exact -092US
  edition could not be located after a genuine search (Intel's post-2024 SDM PDFs belong to
  a restructured ten-volume scheme with different pagination); rather than fabricate a
  pin, the entry records what was actually fetched and flags the mismatch in its own
  `review_note`. Consequence: the mandatory `page_count` range check (pp end <= 5,060)
  still passes for all 267 citations today (max cited page_end is 3,201 — **CORRECTED
  2026-08-27: this number was never independently verified and was wrong; the actual
  maximum was 2,873**, still under 5,060, so the point it was illustrating is unaffected)
  — it cannot and does not catch this specific edition drift, only gross errors. This is
  precisely the "plausibly wrong locator" risk D24 named, recurring in a new form the
  range check alone cannot close; resolving it (source the true -092US PDF, or accept
  -078US and re-derive `pp=` from it) is unresolved backlog, not done here.
  `references/intel_sdm/` itself is untouched — deletion is a separate, later step per
  D24, not attempted here.
  **RESOLVED 2026-08-27 (adversarial review, references/-deletion task):** rather than
  leave the edition mismatch as an undetectable-by-range-check caveat indefinitely, `pp=`/
  `mp=` were stripped from all 267 citations (kept: `vol=`/`instr=`|`sec=`/`part=`, which
  resolve by lookup in any edition); `scripts/check_references.py`'s pdf-locator grammar
  now treats `pp=`/`mp=` as optional. The `-092US` page data survives in
  `docs/intel_sdm_frontmatter.json` (self-labelled per entry via `order_number`/`date`).
  `references/intel_sdm/` (and the rest of `references/`) is now deleted in its entirety —
  see the `references/`-deletion commits.

- **D25 — NO third-party prose in the published tree; `references/` goes to zero
  (Craig, 2026-08-27)**: "i don't want third party prose in the repo by the time we
  publish", doubling down on the earlier "once we have the reference index in place we
  delete the references/ tree." See
  [ADR-0032](adr/0032-no-third-party-prose-in-published-tree.md) for the full decision
  record. The coordinator initially under-read the earlier ruling as
  "delete what has been resolved"; it means the directory ceases to exist.
  - **Redistributability is irrelevant to this decision.** W3C specs, RFCs, and CC-BY
    MicrosoftDocs content are all licensed to ship and all leave anyway. Being *allowed*
    to vendor something was never the reason to vendor it.
  - This retroactively confirms the design review's Finding 5, which flagged a draft Law 4
    clause reading "where the upstream's license permits redistribution, the authoritative
    text SHOULD be vendored as before." That clause would have written a standing
    obligation to re-vendor into the law book on the same day the tree was emptied. Deleted.
  - **End state**: no `REF:` citation resolves to a path under `references/`; the directory
    does not exist at publication; `references.json` + `scripts/check_references.py` are the
    sole mechanism for referencing external documentation, uniformly across all corpora.
  - **Consequence for grounding claims**: with the prose gone, a registry entry is the ONLY
    evidence that a citation is grounded in anything real. A fabricated URL or hash would be
    undetectable from inside the repo and would silently void the grounding claim these
    citations exist to make. Hence: never invent a pin; an honestly-reported unresolved
    citation is a success, a plausible fake is the worst available outcome.
  - **Three things that must not be conflated**, since a gate that confuses them does harm:
    third-party PROSE (banned from the tree); third-party LICENSE TEXT required for
    compliance, e.g. `LICENSE`/`NOTICE` (a legal obligation, must ship); first-party writing
    that describes third-party systems (ours, stays).
  - Enforced mechanically by `scripts/check_publishable.py`: any content file under
    `references/`, or any citation resolving into it, is a hard failure.

- **D27 — No urgency framing in agent briefs (Craig, 2026-08-27)**: "i would
  discourage sending \"URGENT\" prompts to agents -- it will only encourage shoddy
  work / send them the task, but keep things clear for them if it's urgent."
  The coordinator had opened a brief with "URGENT AND BLOCKING". Pressure framing
  buys shortcuts, not speed, and the shortcuts it buys are precisely the ones this
  project cannot afford: skipping the root-cause investigation for the quick patch,
  narrowing a gate's coverage to make it pass, silencing a loud failure.
  - **What to do instead**: state the facts that make the task matter (CI is red for
    every pusher; a team that cannot reach us depends on it) and let the agent draw
    its own conclusion about priority. Facts inform; adjectives pressure.
  - Corollary: when a brief IS time-sensitive, the clarity that helps is a precise
    scope and an explicit statement of which corners may NOT be cut — not emphasis.

- **D28 — Ratify `bv_decide` as Law 10's fourth trust rung (Craig, 2026-08-27)**: the
  owner approved `TCB.md` T14's finding that `bv_decide` is trust-equivalent to
  `native_decide` (same `Lean.Meta.nativeEqTrue` axiom-emission path, larger surface —
  it additionally trusts the bitblaster and the external LRAT/CaDiCaL checker) with
  "ok, bv_decide seems fine then." See [ADR-0037](adr/0037-ratify-bv-decide-trust-tier.md)
  for the full decision record.
  - `docs/REVIEW.md` Law 10 now states an explicit four-rung trust-cost ordering —
    structural proof (no oracle) / `decide` (kernel-checked, no axiom, categorically
    different from the next two) / `native_decide` (trusted, not checked) / `bv_decide`
    (same trust class as `native_decide`, larger surface, reaches finite bitvector
    domains too large to enumerate) — rather than appending `bv_decide` to a flat list.
    The ordering itself is the coordinator's framing of T14's findings, assented to by
    the owner, not his own words (see the ADR's Provenance section).
  - `scripts/gate_allowlist.txt`'s four PA1 `finite-forall` entries
    (`and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`, `G8bf_table`) are unchanged, per
    T14's own recommendation.
  - Implements T14's first disclosure recommendation: `scripts/run_gates.py`'s new
    `detect_cadical()` records which SAT solver `bv_decide` actually resolves — the
    toolchain-bundled `cadical.exe` (pinned by `lean-toolchain`) or the unpinned PATH
    fallback — and its version, in the same oracle-version table T9 already
    maintains for `node`/`nasm`/`python`.
  - Does NOT build a ratchet gate counting oracle-dependent declarations; that idea
    is unapproved and out of scope here (see the ADR's Consequences).
  - **`bv_decide` is approved as a waypoint, not a destination**: the owner separately
    stated the target posture ("it's critical we get to a trustable state: no axioms,
    strong verification, checked models"), which does not reverse this approval but
    governs how it is recorded — the end state is zero `scripts/gate_allowlist.txt`
    entries (Lean's own `propext`/`Classical.choice`/`Quot.sound` are the only
    acceptable residue), and PA1's branch-free normalization (one `bv_decide`
    certificate instead of several) is the model for keeping pushing work back down
    the rung ordering rather than settling wherever a proof first closes. Full
    framing, and which parts are the owner's own words versus the coordinator's, is
    in the ADR's Consequences and Provenance sections.

- **D29 — Standards are earned before they are imposed (Craig, 2026-08-28)**: "we get to
  hold standards of others when we can hold them of ourselves." The coordinator proposed a
  ratchet gate (fail any change that raises the oracle-dependent declaration count) after
  the Linux/bare-metal team's merge took it 80 -> 84. Our own count was 80 at the time.
  - **Not built.** Reduce our own number first; propose the gate for enforcement once we
    demonstrably meet it. See docs/adr/0038-standards-are-earned-before-imposed.md.
  - Their four entries were not a lapse — they followed this codebase's established
    convention faithfully. The convention (pointwise native_decide equivalence proofs) is
    the defect, and it is ours. Gating them on a standard we do not meet would export our
    debt as their obstacle.
  - **A gate IS a message**, and with the repository as the only channel between teams it
    is the one message that arrives without being read and cannot be replied to. That
    asymmetry is why the bar for introducing one is demonstrated practice, not intention.
  - The target is unchanged: zero, with the count as the score. Only the order changes —
    reduce, demonstrate, then ratchet.

- **D30 — x86 ISA expansion prerequisites, owner rulings (Craig, 2026-08-28)**: responses to
  `docs/X86_ISA_EXPANSION_PREREQUISITES.md`, whose verdict was "not ready — but not where the
  hypothesis pointed" (the roundtrip proofs are the healthiest part of the pipeline; the gaps are
  in the instruction model, which is where wsc actually died).
  - **P1 machine-state schema (XMM/MXCSR/fault taxonomy) — NOT a prerequisite.** "machine state i
    expect to be expanded when we need them (spike/demand driven essentially)." This overrides the
    planning doc's BLOCKING call and applies Law 5 / D7 consistently: SIMD state arrives when a
    spike demands SIMD, not speculatively. The planner ranked it highest-stakes because SIMD
    instructions cannot be written against today's state type — which is true, and is exactly why
    it is not a prerequisite: those instructions are not being written yet.
  - **P2 memory contracts — design a memory hook.** "let's plan out a memory hook -- apis every
    instruction needs to go through to access memory, so we can do the perf and permissions in one
    place." One chokepoint, so Law 11's capability check and the performance model's latency/cache
    accounting are each implemented once rather than per instruction. Design: `docs/MEMORY_HOOK.md`.
  - **P3 decoder modularization — promoted to a prerequisite.** "happy to make those tasks prereqs."
    B3 raised 5.0 -> 9.0. Motivation is measured: one instruction edit rebuilds 39 modules in ~130s,
    and that cost scales with total ISA size rather than change size.
  - **P4 + P5 are one thing, and are being built now.** "p4/p5 are the same thing, let's build it
    now." Validation and calibration are the same obligation — an instruction lands, the build goes
    green, and nothing has established that what it claims is true. Evidence: a probe instruction
    with identity semantics, empty uops and zero fuzz states compiled cleanly; 50/88 forms silently
    opt out of silicon validation; 0/88 cost coefficients cite any source, so `toUops` produces
    numbers that are present, uniform, and unfalsifiable.
  - **Correction recorded**: the coordinator had framed ISA expansion as multiplying oracle debt.
    Measurement says otherwise — **0 allowlist entries per instruction** (`SyscallOp` added zero),
    ~24 per *target*. The debt mint is the pointwise spike-equivalence convention, not the ISA.

- **D31 — Memory hook design approved in full (Craig, 2026-08-28)**: "all yes" to
  `docs/MEMORY_HOOK.md` §10's three questions.
  - **Q1 accepted**: the v1 enforcement line counts as Law 11 compliance. Literal-displacement
    accesses discharge by `decide`/`omega`; no-citation accesses and literal overruns are
    unrepresentable; dynamic bounds are carried-but-semantically-discharged, with flow-sensitive
    typestate as the PA2/PA3 upgrade the shape is built to accept. The alternative — gating all
    enforcement behind full typestate — would have blocked the hook on two unstarted tasks.
  - **Q2 accepted**: `MemRef` becomes the operand convention for the expansion's new memory forms.
    This is the ruling with the longest reach: it collapses form count, changes roundtrip
    enumeration, and interacts with B3's decoder modularization — and it needed deciding before
    Wave B because it changes what gets written.
  - **Q3 accepted**: the mandatory no-default `memAccesses` field's cost is accepted — 88 one-line
    edits now, one line per form forever. This is the P4-style forcing function, deliberately the
    `roundtripCases` shape and deliberately the opposite of `canFuzzHardware`'s silent opt-out,
    which is how 50 of 88 forms escaped silicon validation unnoticed.
  - Implementation sequence: MH1 (sealed memory field, width API, access descriptors, fault
    plumbing) then MH2 (uop centralization) and MH3 (capability authoring surface) in parallel.
    Expansion Wave B requires MH1-MH3.

## Phase 0 — Governance docs ✅ (committed: 03eeece)

- [x] `docs/VISION.md` (new): insights 0–2, gate-is-the-product, two trust obligations,
      modular contracts, perf superpower incl. parametric costs.
- [x] `docs/REVIEW.md`: Laws 10–12 added; "Six Laws" heading fixed; Pillar 1 gains gate-policy item.
- [x] `docs/README.md`: vision section, real spike list (was fictional), 12-law summary,
      Wasm/WASI in targets table.
- [x] `docs/SPIKES.md`: points to REVIEW.md as canonical law list.
- [x] `scripts/check_refs.py`: UTF-8 stdout fix (crashed on ∀ under cp1252).

## Phase 1 — Mechanical trust fixes (worktree agents; all reviewed by Opus adversarial reviewers per D6)

- [x] **Decoder gaps + REGISTRY GATE** — branch `worktree-agent-afbbc6cd975969059`.
      Fix cycle DONE (4ff4970): ∀-rel8 theorems, rel32→_inst, 0xE8 decoded, 0x8B REX.W
      soundness fixed, 9 more decodes; tests 2981→3508. REGISTRY GATE DONE (b1e0c95):
      defaultless roundtripCases on the typeclass (79 instances forced), Registry.lean +
      run_cmd environment audit (build-fails on unregistered instance, mutation-verified),
      21 gate shards ALL by `decide` (zero native_decide), suites DERIVED from registry,
      ground theorems deleted. **Gate construction itself caught 2 more real encoder
      bugs: LeaRipRel REX.R/REX.B swap (r8-r15) and 0xC7 decoder ignoring REX.B** —
      Law 13 validated. Build +30.5s (55→85.5s Gasm lib). RE-REVIEW: MERGE-WITH-FIXES —
      gate architecture held (reviewer reproduced mutations + added their own), BUT:
      **coverage regression EXPLOITABLE** (0/1419 cases set REX.R+REX.B together —
      reviewer's M3 mutation miscompiles add r8,r15→writes RAX while all gates stay
      green; old 16×16 loops had all 64 both-extended pairs); audit import-closure hole
      mutation-confirmed (unimported instruction module invisible); 2 more REX.B decoder
      siblings (0x8D/0xC6 SIB-base-4); diagnostic weaker than gate (no toLean clause);
      empty roundtripCases legal (shrink-to-green escape hatch); intermittent
      std::bad_alloc under 21-way parallel decide; doc overclaims "not a pointwise
      sample". FIX CYCLE RUNNING (both-extended witnesses + boundary-imm×ext-reg,
      rexB class fix via codeToReg64, doc honesty, umbrella import + audit hole,
      decodesOk diagnostic, non-empty assertion, OOM mitigation). **MERGED** (bedd699
      closed the coverage regression + REX.B siblings; 1cf58d5 merge commit; 7194c2a
      further hardened `canFuzzHardware` instance-level post-merge).
- [x] **x86 hygiene** — branch `worktree-agent-a59c163e8b2e2896e` (e67275b). Review verdict:
      MERGE-WITH-FIXES with a CRITICAL discovery: **the x86 hardware semantics fuzzer has
      been a silent fail-open no-op** (bare relative spawn path fails on Windows; catch
      synthesizes faulted:=true for every vector — the oracle never executed; baseline was
      6/49 "passing"). Reviewer fixed locally + re-ran: 49/49 instances pass on real
      silicon, all 131 DIV states bit-exact — model correct, harness was a facade. Also:
      NASM change regressed encoding fuzzer (removed path was the only NASM on host);
      shift masks are dead code (CL variants not in suite, RCX never varied); DIV prepend
      displaced 14 grid vectors (divisor 5/7 coverage lost, >7 still untested); RAX/RDX
      aliasing trap in new vectors. Fix cycle DONE (b03b574): runHardwareBatch returns
      Except (no synthesizable results — type-level fail-closed), mandatory pos/neg
      control pair, both failure directions demonstrated live; NASM via LOCALAPPDATA +
      hard error (encoding_fuzzer 100/100 green); DIV write-order fixed; budget 50→150
      (DIV 131/131, CL shifts 134/134); **real oracle immediately found a genuine
      pre-existing model bug: `xor eax, ebx` SF mismatch (58/59, 4939 vectors)** —
      fix cycle 2 DONE (c578f52): setFlagsLogic width-parameterized (SF from bit
      width-1), Xor calls width 32, 64-bit callers untouched; r32 audit: XorR32R32 was
      the only sibling (Mov r32 flag-inert). **59/59, 4939 vectors bit-exact.**
      FINAL RE-REVIEW: **MERGE** (all blockers verified by execution; xor fix confirmed
      vs silicon; zero truncation suite-wide). Micro-cycle DONE (52f91b4): width-masked
      flags (64-bit path bit-identical, shift-by-64 trap handled), [SKIP] labels +
      honest summary (53 fuzzed + 6 skipped, 0 failed, 5008 vectors), sign boundaries
      moved into curated take-6 slice (xor-class caught by design, not random luck).
      ✅ **MERGE-READY** (with build-perf branch). DEFERRED (conflicts with registry work on same typeclass):
      undefinedFlagsMask should take machine state for exact CL-dependent masks;
      unreachable Inhabited HardwareExecutionResult fabricator contradicts the
      "no fabricating path" docstring — tighten at merge or in registry work.
      **MERGED** (8771604).
- [x] **Wasm control-flow fuzzing** — branch `worktree-agent-ad4389e032b10b3d9` (6b5914d).
      Review verdict: REJECT — second confirmed FAIL-OPEN ORACLE: V8 module-rejection
      laundered via TRAP: prefix into PASS; 3/9 cases (br depth 1/2, loop re-entry — the
      headline coverage) never executed; node-absent machine reports all-green; fixed
      temp path cross-contaminates concurrent runs (reproduced); stderr handle leak; no
      timeouts; comparator blind to memory/locals (stores assert nothing); local_tee has
      been a dead PASS all along. Reviewer hand-verified valid equivalents of the dead
      cases agree with the interpreter — model fine, harness architecture broken.
      Fix cycle DONE (f07692f): Except OracleFailure/WasmRunOutcome (type-level
      fail-closed, exhaustive match), INVALID: vs TRAP: split in node script, mandatory
      pos/neg/trap controls (node-absent aborts — demonstrated), pre-module stack/type
      assert, 3 dead cases fixed per V8's real errors + local_tee, +6 cases (loop-vs-
      block discriminator, br depth-2 from loop, nested trap, 3 store/load), DRY'd,
      unique temp paths + stderr drain + timeout. **65/65 cases, 2424 vectors, 0
      divergences, formerly-dead cases genuinely executing.** DEFERRED (same-branch
      follow-up): build-time Lean Wasm validator (references/wasm/valid).
      FINAL CYCLE DONE (59fb2f1): discriminating br-depth cases (mutation-apply-observe-
      revert on Semantics.lean, both mutations kill the right cases, byte-identical
      revert), endianness pin, structural controls guard inside verifyWasmDiffCase,
      trap-guard pin honestly named `trapShortCircuitGuard_inst` (decide verified
      impossible — partial def chain). **67/67 cases, 2524 vectors, 0 divergences.**
      ✅ MERGE-READY. ⚠ MERGE-TIME TODO: add `trapShortCircuitGuard_inst` allowlist
      entry (gate_allowlist.txt lives on linter branch). Earlier RE-REVIEW record:
      **MERGE-WITH-FIXES** — reviewer built a JS mirror of the interpreter + 14-mutation
      matrix: laundering closed, memory cases kill real off-by-ones, concurrency repro
      dead; BUT br-depth decrement mutations (Semantics.lean:381,415) invisible to ALL
      65 cases (stepWasm discards ControlSignal → need outer trailing code; fix shapes
      V8-validated by reviewer); endianness compensating-swap invisible (add store→
      load8_u); verifyWasmDiffCase bypassable by future callers. Validator deferral
      ACCEPTED with residual risk stated (external gate needs CI wiring; validity only
      checked for fuzzed states). FINAL FIX CYCLE RUNNING (incl. mutation-apply-observe-
      revert verification). **MERGED** (d69503a).
- [x] **Law 10 linter** — branch `worktree-agent-a883598f71cb88e93` (957c9a6). Review
      verdict: REJECT AS GATE (classification of all 41 occurrences verified honest, but
      reviewer bypassed enforcement 3 ways: `decide +native` invisible; `_inst`-in-
      Equivalence auto-pass rule; declaration-attribution inheritance via `example`/
      wrapped names). Fix cycle RUNNING (same agent): axiom-oriented detection, delete
      auto-pass rule, ambiguous attribution ⇒ fail, allowlist integrity (dup/stale ⇒ fail),
      finite-forall syntactic corroboration, category-keyed citation warnings.
      Fix cycle 1 DONE (24be5dd); re-review: MERGE-WITH-FIXES — original attacks dead,
      but 4 new bypasses (set_option-in prefix; comment-forged decl heads defeating stale
      detection; multiline/(native:=true) configs; corroboration satisfied by a `-- ∀`
      comment). Structural verdict: regex cannot hold this gate. Fix cycle 2 DONE
      (c842ecd): **axiom-level gate delivered** — Tools/CheckGatesAxioms.lean (lean_exe,
      collectAxioms per decl; v4.33.1 emits DISTINCT `._native.native_decide.ax*` vs
      `._native.decide.ax*` names — agent empirically corrected reviewer's substring
      spec; + ofReduceBool/Nat for other toolchains). **Found 13 decls transitively
      native-dependent via citation (VerifiedProgram wiring) — invisible to text
      scanning by construction** → new `axiom-only` allowlist category; 4965 decls /
      54 native-dependent / 0 unallowlisted; ~40s wall. Python regex hardened per N1-N4,
      demoted to secondary. ROUND 3: **MERGE-WITH-FIXES** — architecture accepted
      (opaque/implemented_by/internal-aux laundering verified closed; reviewer's own
      ofReduceBool spec confirmed WRONG, agent's empirical correction right). Final
      cycle RUNNING: FQN allowlist keys (bare-name collision attack demonstrated),
      module-based scoping via getModuleIdxFor? (namespace-prefix evadable), report ALL
      axioms outside propext/choice/Quot.sound incl. sorryAx + raw `axiom` (implements
      the previously-UNENFORCED zero-sorry/zero-axiom Pillar-1 requirement — a raw
      axiom currently sails through both tools), Lean tool honors categories + rejects
      malformed lines, axiom-only stale validation, search-path/deprecation fixes.
      Doc-wiring blocker (F4/F5, 3 rounds open) CLOSED on integration branch: REVIEW.md
      §4.1 item 4 + §4.4 Gate 1 now name both tools (uncommitted; commit with linter
      merge). Optional perf: thread CoreM seen-cache through collectAxioms.
      **MERGED** (940f4f0 merge commit; 82fb5c6 FQN/module-scoping fix cycle; 6ca8471
      cited the axiom-gate tool to Law 10 and allowlisted `trapShortCircuitGuard_inst`).
- [ ] Merge order note: Phase 0 docs (Law 10/11/12 text) must merge WITH the linter branch
      (linter cites Law 10; its worktree predates the docs). Wire check_gates.py into
      REVIEW.md §4.1/§4.4 Pillar 1 on the integration branch at merge time.
- [ ] **Gate runner**: `.github/workflows/` now exists (TC6, 2026-08-27 — GitHub Actions,
      see `docs/CI.md`) and invokes every gate as its own CI step; the *consolidated local
      entry point* this bullet describes (scripts/run_gates.ps1/.sh or lake script, with its
      own machine-parseable summary and oracle-version pinning) is still what's missing — see
      TC5. Once TC5 lands, `.github/workflows/ci.yml`/`scheduled.yml` should be simplified to
      call it instead of enumerating each gate inline. Invokes: lake build,
      check_refs.py, check_gates.py, lake exe check_gates_axioms, x86_fuzzer,
      encoding_fuzzer (NASM present), wasm_fuzzer (node present), test_roundtrip —
      fail-closed on any missing oracle prerequisite. REVIEW.md §4.1 updated at merge to
      enumerate it. (Reviewers repeatedly flagged: a gate nothing invokes binds nothing.)
- [ ] Merge all branches; re-run full build + test suite + both linters post-merge
      (agents' claimed results are unverified until re-run in merged tree, per D6).

## Ongoing workstream — build performance (Craig: critical to workflow)

Agent iteration speed = checker feedback latency; build times have been creeping.
Craig supports a STANDING sonnet background thread iterating on this through repair and
beyond. Hypothesis (Craig): most of the win is correct SHARDING — split modules so
incremental builds recompile only what changed.

- [x] Iteration 1 DONE — branch `worktree-agent-a5d16e59384569684` (b1742a1); light
      merge-time check only (scripts + baseline doc, no .lean changes, no gate claims).
      FINDINGS: (1) the 3m45s "no-op" was a PHANTOM — worktree-seeded .lake caches are
      path-invalid (absolute paths in artifacts/.rsp), so first build in a fresh worktree
      rebuilds all 315 jobs; steady-state no-op = 0.25s. WORKFLOW TAX: every fresh
      worktree agent pays ~5min cold build → batch tasks into existing worktrees where
      possible (fix cycles already do). (2) Cold baseline 5m03s / 315 jobs (47% CPU
      contention); slowest = Spike2 Windows Equivalence 198s + 12-way 135s cluster =
      native_decide-heavy files → Law 10 migration buys back cold-build time directly.
      (3) Cascade: any of the 21 instruction files invalidates a 56-module closure via
      Instructions.lean aggregator (TOP iteration-2 payoff, confirming Craig's sharding
      hypothesis); Zlib/Windows.lean has only 8 dependents — self-edit latency, NOT a
      cascade bottleneck; Gasm.Core.Types fan-in 120/146 but low-churn.
      Deliverables: scripts/build_baseline.md (diff target), dev_build.ps1/.sh (opt-in
      118-job library build; defaultTargets untouched).
- [x] Iteration 2 DONE — Instructions.lean aggregator restructuring. TC4's registry
      gate had landed (same files), so this proceeded as planned: import-graph surgery
      only, no `.lean` splits. `X86_64Instr`, the `TargetArch X86_64` instance, and
      `X86_64Instr.toBinary` moved out of `Instructions.lean` into `Instructions/Base.lean`
      (already imported by every instruction submodule, so zero new dependency edges);
      the umbrella is now a pure 21-submodule import manifest, kept solely for
      `Registry.lean`'s whole-environment audit (and left on `Decoder.lean`, which
      already imported every submodule directly regardless). ~30 direct umbrella
      importers retargeted to `Instructions.Base` + whatever specific families they
      already used. Base.lean fan-in (80/33) investigated: genuinely shared
      (typeclass + ~30 generic helpers every instruction needs) — not splitting this
      round. Core churn check: `Gasm/Core/Types.lean` 3 commits ever, `Core/Arch.lean` 4
      — confirms low churn, deferred as PLAN.md predicted. Zlib/Windows.lean untouched
      (out of scope, per plan). CASCADE (the number that matters): `touch Add.lean;
      lake build Gasm`, 2 runs each side — before 38/93 jobs (147.5s), after 32/93 jobs
      (76.6s, 70.9s) — a real, contention-independent -16% job-count reduction (the
      generic consumers Windows.ABI/Win32API/Semantics/Encoding/HardwareHarness/
      Core.Verification dropped out of the cascade entirely; the Decoder/RoundtripGate/
      Registry cluster remains coupled by design, since a roundtrip gate must see every
      instruction — that irreducible chokepoint is B3's decoder-modularization scope,
      not this task's). Cold `lake build Gasm` before/after (183s vs 332s) was heavily
      contention-skewed this run (14+ concurrent lean.exe processes from other agents;
      the Registry job alone went 10s→147s across runs with no code change) — reported
      but not treated as signal. Full `lake build` (375+ jobs), `test_roundtrip`,
      `check_refs.py`, `check_gates.py`, and `check_gates_axioms` all still pass.

## Phase 2 — Stop-and-design docs (Law 5 prerequisites; write before code)

- [ ] **Win32 API differential harness design**: validate `Win32API.lean` state-transition
      hooks against the real OS (harness invokes real ReadFile/WriteFile/VirtualAlloc/sockets,
      compares observable behavior). Symmetric with HardwareHarness. Include error paths
      (partial reads, error codes).
- [ ] **Step-lemma library + composition calculus design** (extends EQUIVALENCE_PROOFS.md):
      per-instruction step lemmas (simp-set); sequential/call/loop rules; capability tokens
      as frame conditions; trace algebra for event-emitting routines (the hard design item).
- [ ] **Capability adoption/migration plan** (Law 11): how SymbolicInstr authoring path
      acquires capability obligations; migration order (new code first, then
      Stdlib/Zlib/Windows.lean last/biggest).
- [ ] **Connection-theorem registry format** (Law 12) + twin-detection linter design.
- [ ] **Perf fuzzer design** (wsc recon complete 2026-08-27). Key findings from wsc:
      wsc's "PerfFuzzer" was self-consistency only (no hardware); actual hardware
      comparison was a MANUAL one-off — RDTSC medians from standalone Rust/C harnesses
      hand-transcribed as Nat literals into Main.lean (and visibly stale: scalar and SIMD
      Mandelbrot both "8 cycles"). Never wired into the build — the automation gap is the
      thing to fix, not just the code to port. What to carry over is the *technique*:
      CPUID+RDTSCP bracketing (serialized), median-of-N (not mean — SMI/interrupt
      outliers), separate timer-overhead calibration pass subtracted per-run, 5k-20k
      warmup iterations (turbo/cache ramp). Criterion: **range containment**
      (real ∈ [minCycles, maxCycles]) — wsc tried %-error first (commit 2ff06a9a) and
      replaced it with containment (0af86e9a); adopt containment + rank-order tracking of
      nominal across a kernel suite. Implementation shape: extend gasm's
      HardwareHarness.lean per-test block with timestamp brackets (extend the 136-byte
      result record), calibration PE, in-PE warmup+repetition loops, new
      PerfHardwareFuzzer that reuses Fuzzer.lean generators + computeCycleBounds, wired
      into PerfFuzzerCLI as --hardware. Do NOT port benchmarks/*.rs|*.c as artifacts
      (fold abi/store-drain experiments in as fuzzed kernel buckets later). TMAM %-splits
      are unvalidatable dashboard dressing in both repos — out of scope for validation;
      scope strictly to the [min,nominal,max] bounds contract. No core-pinning existed in
      wsc; containment + median makes that tolerable initially.
- [ ] **Parametric cost function design** (D5 end-state): loop annotations → cost
      recurrences → closed-form polynomials on contracts.

## Phase 3 — Model validation expansion

- [ ] **Fail-open audit**: the x86 harness fail-open (catch → synthesized results) hid a
      total oracle outage. Audit EVERY oracle/harness error path for the same class:
      Wasm HostOracle node-spawn handling, GzipFuzzer python subprocess handling,
      spike Test.lean external-runner fallbacks ("100% sound (in-Lean)" no-op path),
      NASM fuzzer. Rule: an oracle that cannot run must FAIL the run, never no-op or
      synthesize. Candidate Law/REVIEW addition.
- [ ] Win32 differential harness implementation (per design).
- [ ] x86 hardware fuzzing for the excluded ~half of ISA: memory-operand instructions via
      scratch-region support in HardwareHarness; branch instructions via landing pads.
      (Currently `canFuzzHardware := false` on all branches/calls/RET/PUSH/POP/RSP-relative/
      most MOV memory forms — semantics are unvalidated SDM transcription.)
- [ ] Perf fuzzer port from wsc; calibrate Uop.lean latency/throughput tables; replace
      heuristic TMAM formula or mark it non-load-bearing.
- [ ] **Mutation-coverage tooling for differential suites** (mechanize what the Wasm
      reviewer did by hand): automated harness that applies a catalog of model mutations
      (drop a decrement, swap a branch polarity, byte-swap, off-by-one) and requires the
      fuzz suite to go RED for each — "executes" ≠ "discriminates"; a suite's coverage
      claims are only as real as the mutations it kills. Law 13-shaped: converts
      case-quality review into a mechanical gate.
- [ ] Wasm: fuzz `Limits.max`/memory_grow bounds (currently dead — max never set, grow
      never checks); keep control-flow suite growing.

## Phase 4 — Universal proofs (Law 9/10 migration)

- [ ] Step-lemma library implementation (per-instruction; agent-friendly, parallelizable).
- [ ] Composition calculus implementation.
- [ ] **Pathfinder**: ∀-proof of `crc32SymbolicProgram` vs `Stdlib.Zlib.crc32` spec
      (small, loop-heavy, dual-implemented → connection theorem for free, no syscalls).
- [ ] Migrate pointwise `*_inst` equivalence checks module-by-module; shrink the
      grandfathered allowlist to zero. Priority: Spike5 (gzip), then Spike3, Spike4.
- [ ] **`read` as the universal binder (2026-08-27; now in Law 9)**: owner's own words —
      "`read` (in all its forms) is my preferred vector for forcing reasoning forall
      byte arrays" — the "universal binder"/exclusive-enforcement-vector framing below is
      the coordinator's generalization of that stated preference (see ADR-0015's
      Provenance). Contract shape for Phase 4 must thread ∀ read-results — every monadic
      input op in a spec binds an arbitrary ByteArray (any contents/length/partial/EOF)
      and the continuation is proven for all of them; pinning a read result is
      unrepresentable. This is the enforcement mechanism for Law 9 (kills canned outputs,
      domain-shrinking, pointwise eval structurally) AND forces input chunk-robustness
      (dual of output coalescing). Design the VerifiedProgram-successor contract
      around read-continuations as the ∀ entry points.
- [ ] Rebuild `VerifiedProgram` as derived theorem from routine contracts + linker facts.
- [ ] **Observation standard ratified (EQUIVALENCE_PROOFS.md §1.1, 2026-08-27)**: obs.
      equivalence both ways (equality for deterministic specs; refinement+liveness for
      nondeterministic); observables = syscall-boundary effects UP TO write-coalescing
      congruence + contract-footprint memory (capability frame = observability boundary);
      timing never observable; audit trace (VirtualAlloc etc.) ≠ contract trace; internal
      structures excluded. Craig-ratified refinements (2026-08-27): (a) infinite loops
      ENFORCED as inner/outer proof pairs — new `VerifiedReactiveProgram` contract type
      with mandatory fields: inner = deterministic both-ways per-iteration equality,
      outer = progress/liveness; reactive emit accepts only the pair (Spike4 = first
      target); (b) coalescing congruence lives in the LIBRARY spec — SYSTEM_EFFECTS.md
      §6 now defines the per-effect observation algebra (console/file concat, net
      message-boundary, exit terminal, clock excluded) + canonical form via
      `canonicalizeTrace` in Gasm.Effects; (c) audit obligations attach to PER-TARGET
      typeclass instances (VirtualAlloc = Windows PageSource instance requirement;
      Linux proves mmap of its instance; portable spec knows only fetchPages).
      IMPLEMENTATION GAP: current traceEquivalence uses raw `==` on uncoalesced traces —
      chunking accidentally observable. Build canonicalizeTrace + migrate obligations
      BEFORE the zlib optimization epic. Coordinator additions (2026-08-27; CORRECTED —
      previously mislabeled "Craig additions"; owner's own words on this point were only
      "we'll need to adjust when we build threading/multiprocessing -- we will have more
      than one infinite loop in a typical program" and, hedged, "we should probably have
      a happens-after tracking in the trace normalization" — the specifics below are the
      coordinator's elaboration, not owner-stated): (d) threading/
      multiprocessing ⇒ MULTIPLE reactive loops per program — contract generalizes to
      per-loop inner/outer pairs + composition obligations (deadlock/livelock freedom at
      declared sync points, explicit fairness), cross-loop interaction confined to the
      causal layer (dormant VectorClock machinery becomes load-bearing); (e)
      canonicalizeTrace carries HAPPENS-AFTER tracking from day one — canonical form is
      a causally-ordered event set (degenerates to a list single-threaded); coalescing
      only across causally-consecutive writes; equivalence = equality of causal orders
      (linearization-insensitive). Both doc'd (EQUIVALENCE_PROOFS §1.1, SYSTEM_EFFECTS
      §6.3); full concurrent semantics needs Law 5 design before first threaded spike.
      See ADR-0014's Provenance section for the full owner-vs-coordinator breakdown.

## Phase 5 — Duplication (Law 12 execution)

- [ ] Connection theorems for known twins:
      - RFC1951 length/distance logic ×3 (tables in Deflate.lean; closed-form
        encodeLength/encodeDistance; asm branch trees in Zlib/Windows.lean)
      - `compress` vs `compressFixed` (Deflate.lean)
      - gzip magic bytes ×3 (Gzip.lean / Zlib/Windows.lean / Zlib/Wasm.lean)
      - duplicated xorshift RNGs (Core.Rng vs X86_64/Fuzzer.lean)
      - clenOrder 19-way branch chain (Windows.lean ~1667) vs table (Deflate.lean)
- [ ] Twin-detection linter (`scripts/` sibling), wired to CI.
- [ ] Embedding-similarity review triage (later; deterministic prioritization).

## Phase 6 — Spike repair & next spikes

- [ ] Spike5 Wasm: currently a canned-stream stub (writes precomputed bytes; no dynamic
      compression, no Wasm gunzip at all). Implement for real over Stdlib.Zlib.Wasm
      primitives, or formally demote so it cannot claim to be a realization.
- [ ] Spike4: no test opens a real socket against the emitted binaries. Add end-to-end
      exercise (and for Wasm, note sock_* imports are invented non-WASI extensions).
- [ ] Shared test-runner helper (Node WASI glue is copy-pasted ×3 across spikes).
- [ ] Then: Spike 6 (graphics) — SUPERSEDED by the G1 rework: DX12/WGSL are demoted to
      the non-obligating futures appendix, so their design docs are NOT prerequisites.
      Spike 6's real Law 5 prerequisites are G2 (sync DSL), G3 (FP kernel DSL),
      G4 (differential harness), G5 (SPIR-V emitter/validator), G6 (Vulkan host model)
      — and the whole graphics subsystem is gated on a D18 scoping conversation.
      (only SPIRV_VULKAN.md exists).

## Gaps register (self-audit, 2026-08-27 — "what are we missing")

- ~~**Review artifacts are ephemeral**: all Opus review reports + dispatch briefs live
      in temp dirs. Commit a `reviews/` archive per merge train (three-pillar protocol
      requires review artifacts; they're also calibration material for future
      reviewers). Backfill today's ~10 reviews from session records.~~ **removed per D12**
      (no review archive — reviews are proof-of-work + falsifiability consumed at read
      time, instantly stale after; see ADR-0012).
- [ ] **TCB.md ledger** (trust chosen, not discovered): Lean kernel/toolchain; elab-time
      metaprograms (registry run_cmd audit = trusted code); both gate tools; **the PE
      emitter — everything past serializeInstructions is unverified, validated only by
      spike exes running** (last-mile gap; C6 IAT finding adjacent); oracle environment
      versions UNPINNED (node/python/NASM — drift silently changes gate results; pin +
      record versions in gate output); HardwareHarness's hand-written machine code;
      calibration data (E5).
- [ ] **Continuous fuzzing + regression corpus**: fuzzers only run at review time; any
      input that ever diverged should become a checked-in permanent vector (Law 13 for
      inputs). Scheduled background fuzzing once gate-runner exists.
- [ ] **Single-machine/single-OS epistemology**: all hardware truth from one i9-13900H;
      whole oracle stack is Windows-only; zen4/skylake profiles unvalidatable; Linux
      target doc'd but absent from PLAN. Perf model must state "validated on exactly N
      microarchitectures"; Linux runner story eventually gates fleet-scale agents.
- [ ] **Pull the crc32 pathfinder FORWARD** (start when decoder lands, parallel to
      Phase 2 docs): the Phase 4 proof architecture is untested hypothesis until one
      routine goes contract→asm→kernel-proof→composition end-to-end; it will find what
      the design is missing faster than more design will.
- [ ] **Epic exit criteria** (draft, to ratify): Phase 1 = all 5 branches merged + gate
      runner + all gates green in merged tree + D10 re-review verdict "on course"
      (review archive struck per D12 — no such artifact will ever exist to commit).
      Repair epic overall = Phases 1-3 complete + pathfinder proven
      + grandfathered allowlist shrinking (trend, not zero) + Spike5-Wasm honesty
      resolved.
- [ ] **CLAUDE.md onboarding surface** at repo root: fresh sessions self-orient from the
      repo (read PLAN → run gates → conventions), not from one session's memory.
- [ ] Small: calibration-source licensing check before vendoring (Agner/uops.info
      redistribution vs Law 4); prune/advance stale `master`/`owner` branches (owner =
      Craig's live checkout, needs his ok).

## FLAKY HARDWARE ORACLE — diagnosis and why it matters (TC5, 2026-08-27)

TC5's gate runner caught `x86_fuzzer` failing intermittently: same commit, same built
binaries, ten minutes apart — one run stopped silently mid-sequence right after the
`not r13` vector with no diagnostic; a standalone re-run immediately after passed clean
(53 fuzzed, 5008 vectors, 0 failed).

**Probable cause, and it is the same root as two earlier findings.** `runHardwareBatch`
spawns the harness PE and reads its piped stdout; the TC17 agent independently diagnosed
a *short read* on that pipe in the pre-fix code. The hygiene branch's fix made the
harness **fail-closed** (`Except`-typed, catch-synthesize deleted) — which converted the
old failure mode from *silent wrong pass* into *loud intermittent failure*. That is
strictly better and exactly what we asked for, but the underlying race is unfixed: a
one-shot read of a child's stdout is not reliable under load, and this machine currently
runs 14-28 concurrent `lean.exe` (B1 measured `Registry.lean` at 10s and 147s in two runs
with identical code). FIX: read the child's output to EOF in a loop rather than one shot;
add a length/checksum framing to the result record so a truncated read is diagnosable
rather than silent. TASK: fold into TC19 (harness self-hosting) or file standalone.

**Why it matters beyond a flake**: an oracle that fails intermittently under load makes
green runs weak evidence and trains people to re-run rather than read failures (the
precise anti-pattern TCB T4 warns about). It also contaminates any future timing work —
F1's calibration harness will measure this same contention, which is Law 14's
run-conditions block earning its keep earlier than expected.

**Credit where due**: `run_gates.py` propagated the real exit code and turned the whole
run red rather than masking it. The runner did its job on its first outing.

## Architectural finding: the correctness gate is the build-cascade bottleneck (B1, 2026-08-27)

B1's import surgery cut the single-instruction-edit cascade 38→32 jobs (-16%; wall time
roughly halved). The residual 32-job cluster is **Decoder + RoundtripGate + Registry**,
coupled *by design*: a roundtrip gate must see every instruction, so TC4's correctness
gate is now the dominant coupling in the build graph. This is not a conflict between
correctness and build speed — **B3 (Stage B decoder modularization) is the fix for both**:
per-instruction `tryDecode` co-located with `encode`, its roundtrip proof local to the
same file (mostly `rfl`/`decide`, kernel-checked), the global decoder reduced to a
registry-driven dispatcher, leaving only per-family dispatch-reachability and in-bucket
exclusivity as global obligations. Editing one instruction would then rebuild that file,
the dispatcher, and one lemma — the other families' proofs staying cached. Sequencing
note: B3 must not weaken the registry audit's guarantee that an unregistered instruction
fails the build; that property is the reason TC4 exists.
Measurement caveat worth keeping: cold-build wall times are currently unusable as a
metric — `Registry.lean` measured 10s and 147s in two runs with zero code change, purely
from concurrent-agent contention. Job counts are the contention-independent signal.

## EVIDENCE FOR THE PROOF ARCHITECTURE, from an unexpected direction (TC20, 2026-08-27)

TC20 (Wasm emission roundtrip) produced the first genuine universal-proof infrastructure
in the tree, and it matters for PA1/PA2 far beyond its own task:

- `decodeSLEB128_encodeSLEB128` is proved **∀ (val : Int), no width restriction**, by
  strong induction, with **no `native_decide` and no `sorry`**. Also universal: the
  ULEB128 roundtrips, the u32/i32/i64 width-bounded variants, and
  `findTypeIdx_eq_none_iff`. Context for how unusual this is: the precedent census taken
  hours earlier found the ENTIRE tree contained **one** `induction` and **zero**
  `by_cases`. The claim that universal proofs are intractable here was untested, not
  established — and it is now falsified for at least this class.
- **Technique worth generalizing (PA2 input):** the encoders were rewritten from bitwise
  (`&&&`/`|||`) to arithmetic (`%`/`/`/`+128`) form — behaviourally identical, verified
  byte-for-byte against the old implementation and an independent JS oracle across the
  i64 boundary, but **tractable for `omega`**. Choosing a definition's form for proof
  tractability, then proving the two forms agree, is exactly the Law 12 connection-theorem
  shape and is likely to recur in the Huffman/LZ77 bit-packers.
- **A coordinator claim was refuted by measurement.** The brief asserted
  `encodeI64SLEB128 := encodeI32SLEB128` was wrong for out-of-i32 values; the shared core
  is genuinely arbitrary-precision. The real defect is a missing *precondition*
  (`encodeI32SLEB128` accepts out-of-range input and can emit 6 bytes where a 5-byte
  `i32.const` budget is assumed), proved by witness rather than asserted. Latent, not
  live — current call sites pre-bound via `UInt32`/`UInt64`.
- **Negative-control finding:** a middle-byte flip does not reliably trip
  `WebAssembly.validate`, because LEB128/opcode encoding can absorb corruption and still
  parse. Corrupting the mandatory magic number is the sound negative control. Another
  instance of "executes ≠ discriminates".

## Defects & gate obligations found by the PA1 design review (2026-08-27)

Three real defects and two Law 13 gate obligations, all found while *designing a proof* —
before a line of proof was written. This is the front-loaded-review thesis (ADR-0019)
producing its strongest evidence so far.

- **DEFECT (live, Stdlib/Zlib): the gunzip path computes CRC-32 and discards it.**
  `Windows.lean:2210-2217` — `label "decompress_finish"` loads rcx/rdx, `call zlib_crc32`,
  then immediately `xor_r32 .eax .eax`. **The gzip trailer CRC is never verified on
  decompression**, under a section captioned "Finish & CRC Calculation" — a Law 8 facade.
  Structurally invisible to the Python-oracle differential fuzzer: a corrupted-CRC input
  still decompresses, so both sides agree. NEEDS A TASK (fix + a fuzz vector that
  corrupts the trailer and requires rejection).
- **DEFECT (systemic, 53 sites): signed `jge` used for unsigned index-vs-length tests.**
  `JgeRel32.step` branches on `sf == of_`; with `len ≥ 2^63` the loop exits immediately
  and returns the empty-buffer CRC. `jae`/`JaeRel32`/`.jaeNear`/`jae_near_label` ALL
  ALREADY EXIST — the fix is a one-token substitution that *deletes* a precondition.
  53 uses of `jge_near_label` vs 3 of `jae_near_label`; `adler32SymbolicProgram` has the
  identical shape. GATE (Law 13): a lint flagging a signed Jcc consuming a cmp of
  index-vs-length, or better a `boundedCountingLoop` DSL combinator emitting the unsigned
  form by construction — which is also PA2's reusable loop combinator. Same finding twice.
- **DEFECT (latent, verified): `not_r64 .rax` leaves RAX[63:32] = 0xFFFFFFFF.** EAX is
  correct and both real call sites are unaffected (gzip's extractions use `mov_mem8` =
  low 8 bits, shifts ≤ 24; gunzip discards the value). But WINDOWS.md:13 names **RAX**
  as the return register with no narrow-return rule, so against our own ABI doc the
  declared return value is `0xFFFFFFFF_<crc>`. Fix: one `mov_r32 .eax .eax`. GATE:
  "declared return width narrower than the last write to the return register" —
  mechanically checkable at DSL level.
- **RULING (Law 10, coordinator): `bv_decide` is admissible for exhaustive finite
  domains.** It emits `<decl>._native.bv_decide.ax_*` on v4.33.1 (LRAT replayed natively;
  `checkProofs := true` does not exist in this version), so the axiom gate flags it. But
  a SAT certificate over the *complete* domain is categorically not "evaluation at
  sampled points", which is what Law 10 targets — and Law 10 already admits native
  evaluation for exhaustive finite domains. Allowlist under `finite-forall` with a
  justification naming the certificate; small task to teach both gate tools the spelling.
  (Discovered because the reviewer typechecked the technique: a branch-free normalization
  plus `bv_decide` discharges the crc32 per-byte connection theorem over all 2³²
  accumulators in 2.3s. Most transferable technique found so far — it will matter more
  for the Huffman/LZ77 bit-packers than for crc32.)
- **MODEL_DEBT B6 amendment**: `instructionAtRip`'s linear re-encode is not only an
  O(n²) *runtime* wall — it is the **proof's cost model**. One machine step forces simp
  to disprove up to 60 rip disequalities and evaluate `encode` through the
  `AnyX86_64Instruction` existential at each position: ~3,700 encode reductions per
  loop-body step. Any step-lemma proof strategy must bypass the interpreter (decode
  lemma set or small-step relation), not simp through it.

## Model debt ledger (Craig, 2026-08-27)

- [x] Opus researcher DONE — deliverable: `MODEL_DEBT.md` (repo root). enumerate what the machine/OS models omit or simplify —
      performance lens (cache hierarchy, store buffer, branch prediction, fusion,
      alignment, TLB, frontend limits — what would mis-rank agent optimizations) and
      correctness lens (TSO/atomics, interrupts, FPU/SSE, FS/GS, partial/short reads
      and serial-IO semantics, error paths, Wasm floats/br_table/limits) plus
      graphics-forward debt. Deliverable: MODEL_DEBT.md at repo root (inventory, not
      spec — outside docs/ until items graduate to real design docs per Law 5), with
      per-item severity, forcing function, validation strategy, and reference-ingestion
      status; TOP-10 priority table. Debt should be chosen, not discovered (D7).
      SCOPE ADDITION (Craig): section E — system-level perf models for PLACEMENT
      questions ("CPU vs GPU, counting readback"): PCIe transfer model (bandwidth/
      latency/readback asymmetry/pinned-vs-pageable), GPU compute cost in a COMMON
      CURRENCY with CPU cycles (time under named device profiles), disk perf model
      (seq/random/queue depth), network perf model. Also asked: how a MEASURED/
      calibrated model is governed under Law 4 (checked-in regenerable calibration
      data, references/-style). Vision extension written to VISION.md §5
      ("optimizing compiler → optimizing system architect"). Graphics researcher
      also briefed on the placement lens.

## Scale directive (Craig, 2026-08-27 — now VISION §4)

Target systems are millions to tens of millions LOC (Rust-equivalent; more as
assembly). Consequence: correctness+perf modeling crucial; DECOMPOSITION methods more
so — everything (builds, proofs, gates, fuzz suites, reviews) must cost proportional to
the change, not the system. Decomposition machinery is a primary deliverable. Standing
design question for every piece of infra: "what does this cost at 10M LOC when one
module changes?" (The registry gate's decide-shards and the F4 OOM finding are the
first live test of this principle.)

## Merge train 2 (2026-08-27) — LANDED

Wasm (59fb2f1) + linter (82fb5c6) merged; merged-tree verification: build 327/327,
wasm_fuzzer 67/67 (2524 vectors), **both gates caught the cross-branch violation on day
one** (trapShortCircuitGuard_inst flagged by FQN by the axiom gate → allowlisted with
justification), check_refs caught 15 uncited decls in Tools/CheckGatesAxioms.lean
(linter agent's Lean tool predated its refs runs) → cited to Law 10 anchor. All gates
exit 0. NOTE (self-finding): my first verification script reported tools' exit codes
through a pipe (got tail's exit) — fail-open reporting; gate runner (Phase 1 item) must
capture exit codes directly. Linter final cycle (82fb5c6) closed all round-3 findings:
FQN keys, module scoping, FULL axiom totality (sorry + raw axioms now enforced — the
previously-unenforced Pillar-1 requirement), category enforcement in the Lean tool,
axiom-only stale validation, direct-invocation fix.

## Graphics-plan pre-build validation (Craig, 2026-08-27)

- [x] Opus researcher DONE — deliverable: `GRAPHICS_PREBUILD_AUDIT.md` (repo root). audit the unbuilt graphics plans (GRAPHICS_ARCHITECTURE,
      SPIRV_VULKAN, Spikes 6/7) against ALL current lenses — Law 5 stop-and-design
      backlog (DX12/WGSL/windowing docs), observation standard mapping (what are GPU
      observables; fences/semaphores AS happens-after edges; FP nondeterminism vs
      both-ways equality — likely forces refinement/tolerance equivalence, MAJOR open
      question), differential oracle story (spirv-val, lavapipe/SwiftShader/WARP/naga +
      Law 13 control vectors), read-binder analog (buffer contents = the ∀ binder;
      golden-image tests are pointwise and thus prohibited), parametric GPU perf costs,
      Spike 7 event loop under inner/outer reactive contracts, GPU memory under Law 11
      capabilities, and whether the 6-target matrix should shrink per D7. DONE —
      verdict: **NOT ready for Spike 6**; full audit at GRAPHICS_PREBUILD_AUDIT.md
      (top-10 pre-build doc fixes; headline: readbackPixels carries no pixel data,
      Vulkan forbids cross-driver bit-exactness, sync must be happens-after not a
      layout FSM, Wasm+Vulkan targets are fiction, shrink matrix to Win-Vulkan-compute,
      Spike 6 = parametric compute not gradient).
      TACTIC (Craig, per D11): structure the graphics designs as DSLs — a
      **synchronization DSL** (race-freedom/happens-before soundness proven in total
      over the language, applied to any command stream; replaces the layout FSM) and a
      **floating-point kernel DSL** (Deterministic Shader Profile AS a language —
      kernels inherit determinism + ULP-bound theorems proven once; this is the Law 9
      answer for shaders). Write both into the Phase 2 graphics design docs.

## Candidate post-repair epic — "zlib to infinity" (Craig, 2026-08-27)

Take the zlib implementation and optimize it as far as it will go versus the best
available today (zlib-ng, libdeflate, ISA-L class baselines). This is the proving ground
for the whole thesis: universal contracts hold correctness fixed, the calibrated perf
model ranks candidates without execution, agents run the superoptimization search =
"world's foremost optimizing compiler" made concrete and benchmarkable against the
state of the art. Prerequisites: Phase 4 pathfinder (crc32 ∀-proof — conveniently also
the first optimization target: table-driven/SIMD CRC vs current bitwise loop), perf
fuzzer calibrated (Phase 3), capability migration of Zlib/Windows.lean (Phase 2/D3).
Likely needs ISA growth on spike demand (SSE/PCLMULQDQ for CRC32, wider moves) — each
increment differentially validated per D7. External benchmark harness vs real zlib-ng/
libdeflate binaries would be the headline scoreboard.

## Findings ledger (from 2026-08-27 deep review; not yet scheduled above = triage)

- Dead Core machinery: ComposedState/BlockM/CpuTerminator/Callable/AbiDiscipline/
  obligations/permissions have zero call sites → being resurrected via D3/Phase 4.
- `AbiDiscipline` instantiated but never consulted; linker/Win32 hooks hardcode registers.
- IAT dispatch skips index 6 unexplained (Win32API.lean ~255).
- FileSystemEvent lacks open/read events; TraceM stubs them silently → PROMOTED
  (2026-08-27, Craig's protocol-causality rule, SYSTEM_EFFECTS §6.4): input events
  (recv/reads/accept) must be first-class contract-trace events — causal anchors and
  coalescing barriers; ack-after-read ≢ ack-before-read is only expressible if reads
  appear in the trace. Required for canonicalizeTrace and any protocol spike; fix with
  the trace-canonicalization work (Phase 4).
- Assembler: pass-1 `estimatedSize` must equal pass-2 encoded size; no mechanical link.
  → candidate finite-∀ consistency theorem (Phase 1.5/4).
- `instructionAtRip` O(n²) re-encoding per step — perf wall for larger programs.
- Zlib/Windows.lean: 4096-byte stack scratch with hand-computed offsets (+8-for-push
  corrections) in dynamic-Huffman path — most fragile code in repo; only guarded by
  external Python fuzzer. Fixed 8MB/8MB VirtualAlloc split, no bounds checks (→ Law 11).
- `adler32SymbolicProgram` dead code; no asm ZLIB container.
- Wasm `Linker.lean` misnamed (module emitter, no linking).
- PNG: 16-bit indexed silently no-ops instead of rejecting; `partial` inflate loops have
  no termination argument vs adversarial streams.
- GzipFuzzer.lean leaves `.tmp_*` files; oracle is Python only (no C zlib reference).
- README/SPIKES law-numbering duplication (partially fixed Phase 0).
- Structural drift: Spikes 1–3 vs 4–5 directory layouts differ.

### Added by Opus review wave (2026-08-27)

- ~~mov_r32 0x8B rexW misdecode (SOUNDNESS: silent wrong-width decode)~~ → in decoder fix cycle.
- ~~9 more undecodable-but-emitted instructions (0x81 /0,/5,/7; 0xD3 CL shifts; 0F B6; LEA mod=2)~~ → in decoder fix cycle.
- **Instruction registry → BUILD-FAILURE roundtrip gate** (Craig directive 2026-08-27:
  make decode gaps/misdecodes fail the build). DESIGN (ready to dispatch):
  (1) add defaultless `roundtripCases : List ι` field to the `X86_64Instruction`
  typeclass — every instruction instance must enumerate its finite roundtrip domain
  (16×16 regs, boundary imms) or it does not compile;
  (2) `allEncodableInstructions` registry + `@[x86_instr]` attribute + build-time elab
  command auditing the environment: any typeclass instance not in the registry ⇒
  compile error;
  (3) gate theorem: `decode (encode i) = i` exhaustively over the whole registry via
  native_decide (Law 10-compliant: exhaustive finite domain) ⇒ any gap or misdecode
  (incl. the 0x8B rexW class — wrong structure ≠ registered value) fails `lake build`;
  (4) re-derive SemanticsFuzzer suite + RoundtripTests from the registry (kills the
  three drifting hand-lists, F5); stretch: estimatedSize==encoded-size over the same
  registry (assembler pass-1/pass-2 consistency);
  (5) Law 5: design section authored in docs/TARGETS/X86_64.md inside the implementing
  branch (file untouched by Phase 0 edits — no conflict).
  (3-REVISED per Craig 2026-08-27): gate proofs SHARDED one-per-instruction-family in
  separate modules + thin aggregator (parallel elaboration, failure names the family;
  prefer decide/rfl over native_decide per shard where fast enough).
  STAGE B (design-doc'd now, implemented as separate reviewed change AFTER gate lands,
  protected by it): modularize the decoder — per-instruction `tryDecode` co-located with
  `encode`, local roundtrip proof in the same file (mostly rfl/decide, kernel-checked),
  global decoder = registry-driven dispatcher, per-family dispatch-reachability +
  in-bucket exclusivity lemmas. Result: editing one instruction rebuilds only its file +
  dispatcher + one lemma; other families' proofs stay cached. This is both the build-perf
  sharding win AND proof-architecture practice for Phase 4 composition.
  DISPATCH: queued to the decoder agent (same worktree) immediately after its current
  fix cycle lands — the work touches the same Instructions/*.lean files, must sequence.
- JBE/JL/JG have NO rel32 encoder structures → those conditions cannot branch >127 bytes
  at all; JO/JNO/JS/JNS/JP/JNP condition families entirely unmodelled (demand-driven per
  D7 — add when a spike needs them, but document the limitation).
- `DecodesTo` docstring claims "universal" but is per-instance (rename/redoc when touched).
- Decoder accepts REX prefix on Jcc (encode∘decode ≠ id on such input; decode∘encode still id).
- Spike2 fib theorems check List.range 91 but true UInt64 no-overflow domain is n=0..93 —
  extend theorems by 3 values (n=91..93 are exactly where carry bugs live).
- Complete Law 9 mock-verification census (from linter warnings + re-review triage of
  all 16): TIER 1 (constant fn ignores env — verbatim REVIEW.md violations): Spike1
  Win+Wasm, Spike2 Win+Wasm, Spike3 Wasm. TIER 2 (**domain-shrinking evasion** — NEW
  finding): Spike5's `inductive GzipOp | compress` / `GunzipOp | decompress` are
  SINGLE-CONSTRUCTOR types, so `∀ op` quantifies over one element while spec ignores the
  parameter (Spike5Gzip/Equivalence.lean:96-110,122-149) — passes linter and casual Law 9
  reading. TIER 3 (legit pattern): Spike4's HttpRoute (3 constructors, exhaustive cases)
  and Spike3-Windows' Bool — genuine finite-∀ composition; their constituent theorems
  arguably deserve a `finite-forall-component` category. → Phase 4 priority order:
  Tier 2 (Spike5) first (it's also the gzip epic bed), then Tier 1. Gate question for
  Phase 4 design: mechanical prevention for domain-shrinking = contracts must quantify
  over the CANONICAL Environment type, not spike-defined input enums.
  **PA17 correction (2026-08-27+, `docs/tasks/PA17-spike3-spike4-domain-honesty.md`):** the
  "Tier 3 — legit pattern" verdict above is right about the *outer composition* (`cases`
  over `HttpRoute`/`Bool` genuinely is an exhaustive finite-∀) and **wrong if read as "no
  further action needed"** — each inner constituent theorem is still one `native_decide`
  check against one literal byte string, not the real per-route/per-stdin domain
  (`∀ request : ByteArray` / `∀ stdin : ByteArray`). PA17's original pass found this false
  via the pre-fix routing bug (Windows/Linux's 5-byte `"/stat"` prefix, WASI's single-byte
  `'s'` prefix); `docs/tasks/N8-spike4-stack-buffer-overflow.md` fixed that bug on all three
  targets (now an exact 8-byte `"/status "` compare — see `Equivalence.lean`'s "FIXED (N8)"
  note, which superseded the old "KNOWN DIVERGENCE" note this paragraph used to cite).
  **The domain-honesty finding survives the fix, for an independent reason**: none of the
  three lowerings validate the HTTP method before routing — each assumes the first four
  bytes are literally `"GET "` and reads the path window at a fixed offset regardless of
  what actually precedes it. `witnessMethodNotValidatedDivergence` (`Equivalence.lean`,
  added retiring this epic's Spike-4 slice, 2026-08-28) is a checked witness: a request
  whose method is not one of `Stdlib.Http11.Method`'s 9 constructors (so the honest model
  answers 400 Bad Request) but whose method token plus delimiting space happens to also be
  4 bytes (`"FOO "`, same length as `"GET "`), so the fixed offset-4 read lands on a real
  `"/ "` path and every lowering answers 200 OK instead. So a genuinely universal `∀ (request : ByteArray)` claim remains **false** — not
  because routing bytes are wrong (they are now provably right, on every witness path this
  epic's regression suite exercises), but because method validation is a piece of the
  honest model's behavior no lowering implements. A future spike author should read "Tier 3"
  as "outer composition legitimate, inner domain still unverified and provably cannot be
  ∀-request-complete without a lowering-side method-validation fix, do not cite as
  ∀-request/∀-stdin coverage" — not as "legit, no action needed." The nine grandfathered
  `native_decide` entries this paragraph concerns (`scripts/gate_allowlist.txt`) are
  therefore still grandfathered, not retired: PA6's read-binder and the Http11 parser
  landing removed the *architectural* blockers to attempting a real ∀-domain theorem, but
  did not make one true, and the *structural* proof of a correctly-narrowed version (e.g.
  `∀ request, method = GET → ...`) — connecting `X86_64Instruction.step`'s per-instruction
  semantics to the recv/dispatch/send byte comparisons via the step-lemma technique
  `Spikes/Spike3SortLines/TraceStepLemmas.lean` supplies — was not attempted to completion
  in this pass; it remains open, unblocked, and is a plausible next slice.
