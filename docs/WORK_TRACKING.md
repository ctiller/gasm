# Work Tracking Across Independently-Directed Teams

**Status**: this entire document is a proposal produced by an investigation, not a
ratified process. Nothing described below has been enacted: `docs/tasks/*.md`'s
frontmatter schema, `TASKS.md`, and `scripts/task_frontier.py` are unmodified by this
document, and no `docs/handoffs/` directory, no GitHub Issue convention, and no scheduled
staleness-check workflow exists in the tree today. Every mechanism named here is a
recommendation for the owner to ratify, adjust, or reject — most naturally by folding the
accepted parts into `TC13` (`docs/tasks/TC13-task-dag-tooling.md`, already scoped to
"validate docs/tasks/, regenerate this board") rather than spawning a new task id, since a
second checker covering the same ground would itself be the Law 12 twin this document
argues against elsewhere.

## 0. Why this document exists

Until 2026-08-27 one coordinator directed all work in this repository and held enough
context to avoid duplicating effort by memory. That stopped being true the moment a second,
independently-directed team — working the Linux target under `docs/TARGETS/`, per
`scripts/check_doc_facade.py`'s own module docstring, which names it explicitly as ongoing,
legitimate, concurrent work — began pushing to this repository without any channel to this
session other than the repository itself. A third team is plausible; nothing below assumes
exactly two.

That second team has already demonstrated the shape of the problem, not a hypothetical
version of it. Branch `comprehensive_codebase_security_audit` ran a security audit and
pushed three fully-speced task files plus a `TASKS.md` edit; the owner merged it as PR #1
(commit `b7ec28b`, on top of `83b19e9`) and confirmed the team's role in exactly these
words, relayed via the coordinator: **"they're not working on anything: they found and
recorded."** Sections 1 and 8 below take that worked example apart in detail, because a
design that cannot explain a concrete instance that already happened is not trustworthy
about instances that haven't happened yet.

The owner has also settled, then partially re-opened, then re-settled the channel question
across this investigation. In order: "the only comms channel available will be the
repository i expect" (ruling out any synchronous contact); then a correction that GitHub
mechanisms reachable via `gh` are legitimately part of "the repository" for this purpose,
since both parties push to and can query the same GitHub-hosted project ("possibly things
available via `gh`"). Section 4 works through that trade-off explicitly rather than
picking a side by assumption. What stays ruled out in every version: chat, email, issue
trackers or dashboards hosted anywhere *other* than this GitHub project, and anything that
assumes a reply arrives faster than the next push.

## 1. The situation, concretely

Before designing anything, the worked example is worth reading as data. The security-audit
team's PR added, in one commit (`83b19e9`):

- `docs/tasks/N8-spike4-stack-buffer-overflow.md`, `B4-instruction-index-lookup.md`,
  `B7-wasm-oob-trap-and-limits.md` — three fully-schema-compliant task files: every
  required frontmatter field present (`id`, `title`, `status: ready`, `blocked_on: ""`,
  `after`, `related`, `bar: ""`, `track`, `priority`, `priority_set`,
  `design: inline`, `design_review: waived-mechanical`, `date`), a `## Context` section
  citing exact file:line evidence, a `## Deliverables & acceptance criteria` section, a
  `## Pointers` section, and a dated `## Notes` entry. This is not a rough sketch of a
  problem; it is a task file indistinguishable in form from one this session would have
  written itself.
- A `TASKS.md` edit inserting three new bullet lines at three different points inside the
  existing status board — after the N7 line, and after the B3 line (with `B7` on a fourth
  new line right after `B4`) — not appended at the end of the file.

Two things follow directly from this diff, and both recur through this whole document.
First, `docs/tasks/*.md` is already exactly the right shape for a channel between
uncoordinated teams: one file per unit of work, self-contained, no shared mutable region.
`python scripts/task_frontier.py --validate` was re-run against the merged tree during this
investigation and the three new files parsed and validated cleanly on the first attempt —
they cost this design nothing to absorb. Second, `TASKS.md` is not that shape: the same
commit had to find three separate insertion points inside a hand-maintained list, which is
exactly the merge-conflict-magnet shape Section 6 addresses, and it worked this time only
because nothing else touched those same lines in the same window. That is luck, not a
property of the file.

One more observation, offered as evidence rather than as a mechanism anyone should rely on:
every commit on `comprehensive_codebase_security_audit` (including `83b19e9`) carries
author `Craig Tiller <ctiller@google.com>`, while this session's own commits on `main` carry
`craig.tiller@gmail.com`. Git already distinguishes "which operator's tooling produced this
commit" today, incidentally, with zero new convention. It is not a claim of team *identity*
in any enforced sense — a committer can set `user.email` to anything — but it is a real,
already-present, zero-cost signal worth reading when triaging an unfamiliar commit, and it
is referenced again in Section 5's discussion of self-declared team slugs, which have the
same trust level and the same cost.

## 2. Design principles forced by the constraints

These follow directly from the owner's stated facts, not from this document's preference,
and every mechanism below is checked against them:

1. **No synchronous coordination, ever.** Latency between a message and its being seen is
   bounded below by push cadence — hours at best, observed to be on the order of a day
   between this repository's last few pushes. Nothing in this design may require a fast
   reply to function; where a "wait for an answer" pattern would be natural in a
   synchronous setting (e.g. "is anyone working on this?"), it must instead be a
   fail-closed default (assume nobody has claimed it unless a claim is visibly recorded)
   rather than a poll-and-block.
2. **Prefer fail-loud mechanical checks over goodwill conventions**, per this project's own
   Law 13 and the owner's explicit instruction for this task. Section 9 inventories, for
   every mechanism proposed, whether it can be gated and by what, and states plainly which
   parts cannot be and will therefore rot silently unless someone reads this document again.
3. **Append-only beats edited-in-place wherever two parties might write concurrently.**
   This project already has a documented instance of an edited-in-place shared artifact
   merging cleanly and wrong: commit `c2f5bae` ("re-derive manifest hashes lost to an
   auto-merged hash file"), recorded in `docs/PRE_FLATTEN_CHECKLIST.md` and
   `docs/REFERENCE_INDEX.md` §6, where two branches each validly modified
   `references/MANIFEST.sha256` and the merge was conflict-free and semantically wrong.
   `TASKS.md` is the same shape of artifact and the same risk, demonstrated live in Section
   1's worked example (it merely didn't collide this time). Every new mechanism this
   document proposes is checked against this principle specifically.
4. **The tree is the durable record; nothing else is, per D23.** `docs/adr/0031-flatten-not-history-scrub.md`
   records the owner's ruling in full — the repository will be flattened to a single
   commit, so `PLAN.md`, `docs/adr/`, and `docs/tasks/` become "the sole surviving decision
   history," and "anything load-bearing must be written into the tree itself... not left to
   a commit message to carry." This is the load-bearing fact behind Section 4's
   in-tree/GitHub-native split: it is not a style preference, it is the reason a
   GitHub-only artifact cannot be where this project's decision record lives.

## 3. Recommendation summary

The durable parts of a task's identity — that it exists, what it depends on, its design,
who found it and why it matters, and the append-only history of notes about it — belong in
`docs/tasks/*.md`, exactly as today, because Principle 4 leaves no other option once the
flatten happens. The one genuinely ephemeral piece of state this whole problem turns on —
*is someone working on this right now* — is recommended to move to a GitHub-native
mechanism (an Issue's assignee) specifically because that piece of state benefits from a
property files cannot offer: atomic, non-mergeable mutation. A cross-team message that
isn't about any existing task yet gets a new home, `docs/handoffs/`, structured
one-file-per-message for the same reason `docs/tasks/` already works and `TASKS.md`
doesn't. `TASKS.md` itself should stop being hand-edited once `TC13` lands, generated from
frontmatter instead — this document argues that finding should raise `TC13`'s priority, not
that this document should implement it.

| Concern | Lives in | Why |
|---|---|---|
| Task exists, `after`/`related` edges, design, provenance | `docs/tasks/<id>.md` frontmatter | Durable per D23; must survive the flatten and work from an offline clone. |
| Status board / frontier ranking | `TASKS.md` (until `TC13`), then generated | Same file today; recommend deriving it to remove the conflict hazard (§6). |
| "Is anyone working on this right now" | GitHub Issue assignee | Atomic, non-mergeable, actually notifiable — none of which a file can offer (§4). |
| History of who claimed what, when | `docs/tasks/<id>.md` `## Notes` (echo of the Issue event) | Durable per D23; survives the Issue being closed or, worst case, deleted. |
| A message not yet about any task | `docs/handoffs/<date>-<team>-<slug>.md` | One-file-per-message avoids the shared-region merge hazard entirely (§7). |

## 4. In-tree vs. GitHub-native: the split, and why (Q4)

This question was the one place in the brief where the answer changed mid-investigation,
and the reasoning for landing where it lands is worth stating in full rather than
compressed into the table above.

**The case for GitHub-native mechanisms, taken seriously.** An Issue's `assignee` field is
not a line in a text file; it is a row in GitHub's own database, mutated by an API call
that either succeeds or fails, with no merge step in between. Two teams racing to claim the
same task cannot both "win" the way two teams appending a `claimed_by:` line to the same
task file in parallel branches could both merge cleanly and leave the file claiming two
different owners — which is exactly `c2f5bae`'s manifest failure, transplanted from a hash
table to a claim field. An Issue is also the one artifact in this list that can actually
*notify* someone (a watcher, a mention, an assignment) without that someone first choosing
to open a directory and read files — which matters given Principle 1: there is no other way
to make a message louder than "it's sitting in the tree if anyone looks."

**The case against putting the record itself there.** Everything in Section 3's left column
is exactly what `docs/adr/0031` says must survive into the flattened tree or be permanently
lost. An Issue is neither: it is not present in a clone, it is not covered by
`scripts/check_record.py`'s cross-reference or provenance checks (which enumerate
`PLAN.md`, `docs/adr/*.md`, `docs/tasks/*.md`, `TCB.md`, `MODEL_DEBT.md`, and
`docs/REVIEW.md` — nothing outside that list), and it can be edited or deleted by anyone
with write access with no trace left in the tree. A task DAG that existed only in Issues
would be precisely the kind of record the owner flattened this repository's history to
avoid depending on.

**The line, stated precisely.** A fact belongs in the tree if losing it would mean losing
part of *why the codebase looks the way it does* — that a task exists, why, what it depends
on, who found it, what was decided about it. A fact belongs in a GitHub-native mechanism if
it is true only *for now* and its entire value is in being loud and atomic while it's true —
who is holding a task at this moment, whether anyone has looked at an open question yet.
The test this document applied at every mechanism below: **if this fact vanished the day
before the flatten, would anything about the project's history become inexplicable?** A
missing claim answers "no" (the task file still explains itself completely without it); a
missing design or dependency edge answers "yes."

**Labels and Projects, weighed and set aside.** A label mirroring `status` or `track` would
duplicate a fact the frontmatter already states — exactly the Law 12 "unlinked twins"
shape this project already prohibits for code, and there is no reason process metadata is
exempt. If a visual board is wanted, the principled version is a read-only view generated
*from* frontmatter (a CI step could sync labels outward, never inward) so there remains
exactly one place that fact is authored. This document does not propose building that sync;
it is a plausible future convenience, not part of the minimal design.

**PR review threads.** Each team already merges its own work via its own PRs against
`main` — that is pre-existing single-team practice, not a new inter-team channel, and nothing
here changes it. A PR thread shares every durability problem an Issue has with none of the
present advantage (nobody is reviewing the *other* team's PR, since there is no coordination
to prompt it), so it is not recommended as a coordination surface here.

## 5. Claiming (Q1)

**Mechanism.** Before starting implementation on a task whose `docs/tasks/<id>.md` status is
`ready`, a team opens (or reuses) a GitHub Issue for that task — recommended title
convention `<id>: <title>` so the task id is greppable in the Issues list — and
self-assigns it. Self-assignment is the claim. There is no separate "lock" file, and no
frontmatter field records live claim state, for the reason given in Section 4: a claim is
exactly the kind of fact whose entire value is being true *right now*, and a frontmatter
field recording it would reopen the merge hazard this design exists to close.

**The durable half.** In the same sitting, the claiming team appends one dated line to the
task file's own `## Notes` section (already schema'd as append-only, already documented as
"anyone may append" in `TASKS.md`'s task-lifecycle section): `<date>: claimed by
<team-slug> (issue #N)`. This is the half that survives the flatten and survives the Issue
itself later being closed or deleted — Section 4's durability test applied concretely: if
the Issue vanished tomorrow, the Notes line still tells a future reader that team X was
working this task as of a given date, which is exactly the kind of fact D23 says must live
in the tree.

**Team identity.** Nothing registers which teams exist; there is no channel to agree on
one. The recommendation is the cheapest thing that already works: each team picks a short,
stable, self-declared slug once (the security-audit team's own branch name,
`comprehensive_codebase_security_audit`, already demonstrates the instinct — a slug like
`security-audit` would have served the same purpose more concisely) and uses it consistently
in Issue assignments, Notes lines, and branch names. This is **not mechanically
enforceable** — nothing stops a team from being inconsistent or another from impersonating
one — and Section 9 says so plainly rather than implying otherwise. The git-author-email
signal from Section 1 is corroborating evidence when a slug and a commit's actual author
disagree, but it is evidence to read by hand, not a check anything runs.

**Staleness.** A claim that never expires is a lock that leaks, per the brief's own framing,
and this design does not want a claim to require the *same* team to release it — that would
reintroduce synchronous coordination by another name. The recommendation is a scheduled
check (this repository already runs `.github/workflows/scheduled.yml`, so this rides
existing infrastructure rather than inventing a new one) that lists assigned, open Issues
whose `updated_at` is older than a threshold — proposed at 7 days, chosen only as "visibly
longer than any single push gap observed so far" with no real data behind it (see Section
10) — and, at that threshold, posts a comment naming the stale claim and unassigns it,
rather than silently leaving it assigned forever. The comment is itself an append-only
record (GitHub does not let a comment be edited away without leaving an edit trail visible
to the thread), so the fact "team X claimed this and went quiet" is not lost by the
unassignment — it is exactly the kind of interesting-but-ephemeral fact Section 4 puts on
the GitHub side of the line, since losing it does not make the tree's own record
inexplicable.

**Status**: this staleness check (a new scheduled-workflow job invoking `gh issue list`)
is a proposal; no such job exists in `.github/workflows/scheduled.yml` today, and Section 11
recommends building it only after the manual claiming convention has actually been used a
few times.

## 6. The `TASKS.md` conflict hazard (Q2)

Section 1's worked example already shows the shape of the risk without yet showing the
failure — three inserted lines that happened not to collide. The `c2f5bae` manifest
precedent (Section 2, Principle 3) shows what it looks like when the same shape of edit
*does* collide silently: two individually-valid changes to the same shared, hand-edited
file merge without conflict markers and produce a result nobody wrote and nobody reviewed
as a whole.

`TASKS.md`'s own text already names the fix and already has a task number for it: "Once
`TC13` (task-DAG checker/regenerator) lands, the status board below becomes generated
output... regenerated mechanically from `docs/tasks/*.md` frontmatter rather than
hand-edited." This document's contribution is not a new mechanism but a reason to move
`TC13` up the queue: the multi-team reality means the risk `TC13` closes is no longer a
hypothetical about concurrent coordinator dispatches within one session — it is a
demonstrated cross-organization hazard between parties who cannot even negotiate who edits
which line. A generated `TASKS.md` is non-conflicting by construction for exactly the same
reason `docs/tasks/*.md` already is: each task's fact lives in exactly one file nobody else
touches, and the aggregate view is a pure function of those files, never itself a place
anyone writes.

**Interim mitigation, until `TC13` lands** (a process convention, not a schema or script
change, so within this document's "propose, don't enact" scope): a team adding a task to
`TASKS.md` by hand should append its new line at the *end* of the relevant BAR-section's
list rather than interleaving it in id order, the same append-at-a-fixed-anchor discipline
recommended for `docs/tasks/<id>.md` Notes sections. This reduces, but does not eliminate,
same-line collisions — it is exactly the "goodwill convention" Principle 2 says to be
suspicious of, offered only as a stopgap because `TC13` does not exist yet, not as a
substitute for building it.

## 7. Cross-team messages: a channel distinct from the task DAG

A task file's `## Notes` section is already the right place for a message *about that task*
— claim events (Section 5), a finding-in-progress, a reviewer's concern. Nothing new is
needed there. What has no home today is a message that isn't about any existing task yet:
a finding with no task file written for it, "we looked at this and stopped because X, and
it's not our track," a general status ping, a "this looks like your area, not ours"
handoff. `PLAN.md` is the closest existing candidate and is the wrong shape for it — it is
one long hand-edited narrative, the single-file hazard from Section 6 applied to prose
instead of a task list, and (per `PLAN.md`'s own text) already flagged as "exactly the kind
of artifact that gets compressed away for context reasons."

**Proposed mechanism: `docs/handoffs/`, one file per message.** Filename convention
`<date>-<team-slug>-<short-slug>.md`; minimal frontmatter (`date`, `from`, `to` — a team
slug or the literal value `any` — `about` — a task id if one already exists, otherwise
empty — and `status`, one of `open` / `acknowledged` / `superseded`); free-form prose body.
One file per message is the direct fix for the Section 2/Principle-3 hazard: two teams
writing two different handoff files in the same push window cannot collide, full stop —
there is no shared region for a merge to get wrong, unlike `TASKS.md` or a single running
log file. The cost, named plainly, is directory clutter over time; this document considers
that cost acceptable given what it buys, and notes `docs/tasks/` already made the same
trade for the same reason.

**Immutability discipline.** A handoff file is never edited in place by anyone but its own
author. A response supersedes rather than amends: a new handoff file names the one it
responds to and, if the original is now resolved, that original's own `status` moves to
`superseded` by its own author (or is left `open` if nobody has taken responsibility for
updating it, which is itself informative). This reuses a convention this project already
trusts rather than inventing one — `docs/adr/README.md`'s own immutability rule: an
accepted record is never rewritten, a changed decision gets a new record that states which
one it supersedes.

**Where to look, and when — because a convention nobody reads is not a channel.** A team is
expected to scan `docs/handoffs/` for files with `status: open` and a `to` of either its own
slug or `any` at the start of any session that touches this repository, the same way
`CONTRIBUTING.md` already tells a first-time contributor to read `PLAN.md` and
`docs/tasks/` before starting something that might already be underway. There is no read
receipt and no delivery guarantee — an unacknowledged handoff simply sits there, visibly,
until someone supersedes it. That is the honest state of a channel with no synchronous
mechanism, not a defect this design can paper over (Principle 1).

**Optional GitHub-native amplification.** A handoff file may name a companion Issue number
for visibility (comments, notifications) exactly on Section 4's live/durable split: the
file is what a bare clone or the flattened tree still has; the Issue, if one exists, is
pure loudness layered on top and is never required for the channel to function. A team with
no habit of using Issues, or a period where Issues are unavailable for any reason, still has
a fully working channel through the file alone.

## 8. Findings vs. commitments (Q3)

The worked example already answers most of this question by demonstration rather than by
needing a new field. N8, B4, and B7 were filed with `status: ready`, `design: inline`, and
`design_review: waived-mechanical` — using fields the schema already has, not inventing new
ones — and that combination already reads correctly as "found, specified, nobody has
claimed it," which is the existing documented meaning of `ready` in `TASKS.md`'s own status
enum (`blocked | ready | designing | design-review | implementing | done`). A task does not
need a special "finding-only" status distinct from `ready`; `ready` already means exactly
that, and adding a second field to say the same thing would itself be the Law 12 duplication
this whole project's discipline exists to prevent.

**Where the schema genuinely under-specifies today.** `PLAN.md` itself already recorded the
sharper version of this gap from direct experience: "uncommitted coordinator state does not
reach worktree agents... agents CANNOT update their own task-file frontmatter (status/design
fields), so the DAG's status data goes stale unless the coordinator maintains it centrally."
A task can be genuinely `implementing` on someone's branch while the shared tree's copy of
its frontmatter still says `ready`, because updating frontmatter requires a commit and a
commit lags real work by however long a push takes. That is not a distinct "found vs.
committed" problem — it is Section 5's claiming problem wearing the schema's clothes, and
the fix is the same one: the live "is someone on this" fact belongs in the GitHub Issue
assignee, not in a frontmatter value that can only ever be as fresh as the last push.

**A real, narrower gap this document does recommend closing: whose acceptance criteria are
they?** N8's `## Deliverables & acceptance criteria` prescribes specifics — "expand the
stack allocation... to at least 256 bytes," "verify the full 7-character string" — written
by a team that audited the defect but has no stake in, and may never see, the eventual fix.
That is reasonable engineering judgment from an outside finder, but it should read as a
*strong suggestion from the finder*, not a contract from an owner who will review the
result against its letter. Recommend handling this through provenance (Section 9) rather
than a new status value: a task whose `found_by` differs from whichever team eventually
claims it is itself the signal that its acceptance criteria are advisory, and an executing
team should feel free to close the underlying defect by a different mechanism than the one
prescribed, as long as it is closed.

**Should an unowned finding rank as ready-now work?** Yes, unchanged from today's behavior,
and this document verified it rather than assuming it: `python scripts/task_frontier.py`
was run against the merged tree during this investigation, and N8/B4/B7 appear in the
ranking exactly as any other `ready` task with satisfied `after` edges would, aged upward
over time by the same `AGING_RATE = 1.0`/hour rule as everything else. That aging rule is
correct here, not merely tolerated: a real, unclaimed defect *should* keep climbing the
frontier for as long as nobody addresses it, precisely so it cannot be permanently
outranked by a louder but less urgent task. What the frontier cannot and should not try to
do is distinguish "high-leverage and unclaimed, hurry" from "high-leverage and already
claimed elsewhere, don't duplicate" — that fact lives in the GitHub Issue (Section 5), and
Section 10 argues explicitly for keeping `task_frontier.py` ignorant of it rather than
adding a network dependency to an otherwise-offline tool.

## 9. Provenance (Q5)

`docs/adr/README.md` already distinguishes Owner-stated / Owner-assented / Mixed /
Coordinator-decided for *decisions*, and every ADR in this repository carries a
`## Provenance` section recording which. Tasks have no analogous field today, and the
worked example shows exactly why they need one: N8/B4/B7 were found by a team with no
representation anywhere in the task's own text — read the file cold and there is no way to
tell it came from an external audit rather than from this session's own review pipeline.

**Recommendation**: a new frontmatter field, `found_by`, permanent once set — never edited
after the fact, the same discipline `docs/adr/README.md` already applies to an ADR's
Context/Decision/Consequences — recording who identified the task, as distinct from who is
(or will be) executing it (which lives in the GitHub Issue assignee per Section 5, and is
transient by design). A small vocabulary rather than free text, mirroring the ADR
provenance categories: `self-found` (the norm today — the team that will do the work also
found it), `external-finding` (N8/B4/B7's actual shape, undeclared today), `owner-directed`
(the existing `PLAN.md`-quoted pattern for owner-stated priorities), `coordinator-derived`.
Existing tasks predating this field would be backfilled honestly using the same
`predates-discipline` convention already established for `design`/`design_review` on
old tasks, rather than inventing a plausible-sounding provenance after the fact for work
where the true provenance was never recorded.

**Status**: `found_by` does not exist in today's frontmatter schema; adding it is a small,
mechanical extension of `scripts/task_frontier.py`'s `REQUIRED_FIELDS` list and `validate()`
function (parallel to how `status` is already validated against `VALID_STATUSES`), not
attempted in this change, and most naturally folded into `TC13`'s planned checker rather
than built as a second, competing tool.

## 10. Mechanical enforcement inventory (Q6)

Per this project's Law 13 and the owner's explicit instruction, every mechanism above is
listed here as either gated or not, so any rot is visible rather than assumed away.

**Enforceable today, or by a small extension of an existing tool:**

- Duplicate task `id`; `after`/`related` referencing an unknown id; missing or malformed
  `priority`/`priority_set`/`status` — already checked, today, by
  `scripts/task_frontier.py`'s `validate()` (re-run against the merged tree during this
  investigation; N8/B4/B7 passed cleanly).
- A new `found_by` field's presence and enum-membership — a direct, same-shape addition to
  the same `validate()` function once the field is adopted.
- `TASKS.md` drifting from `docs/tasks/*.md` frontmatter — already `TC13`'s stated scope; this
  document's contribution is evidence for prioritizing it, not a new checker (a second
  checker covering the same drift would itself be an unlinked twin).
- A stale GitHub claim — mechanically detectable and *fixable* (auto-unassign) by a
  scheduled Action calling `gh issue list`, since this repository already runs a scheduled
  workflow. This is the one proposed mechanism that inherently requires network/API access
  to enforce, and it should live in CI, never be assumed by an offline tool like
  `task_frontier.py`.
- A `docs/handoffs/` entry that stays `open` past some age — mechanically *detectable* by
  the same kind of scheduled check, but not mechanically *resolvable* the way a stale claim
  is: unassigning a claim is a real, correct state change, while marking someone's attention
  as having happened when it hasn't would manufacture the appearance of acknowledgment that
  never occurred — precisely the "manufactures confidence" failure this project's own
  doc-facade linter exists to catch in prose. A scheduled check here should only ever warn
  (a comment, a non-blocking report), never auto-resolve.

**Not mechanically enforceable — named here so the rot is visible, not silent:**

- Whether a team actually reads `docs/handoffs/` or checks an Issue's assignee before
  starting `ready` work. No gate can force a read; this is the same trust `CONTRIBUTING.md`
  already places in "read this before sending a change," extended to a second audience.
- Whether a self-declared team slug is honest or consistent. Bounded only by the incidental
  git-author-email signal (Section 1), which is evidence to read by hand, not a check.
- Whether an externally-found task's acceptance criteria are honored to the letter or
  reasonably reinterpreted (Section 8). This is left to Pillar 2 review's existing
  judgment, deliberately — it is a "did we prove the right theorem" question, exactly the
  class of question this project's own review protocol already treats as irreducible to a
  gate.

## 11. What to build first, if this is accepted

Ordered by cost and by how much of the identified gap each step actually closes, cheapest
and most load-bearing first:

1. **Add `found_by` to the task frontmatter schema and to `task_frontier.py`'s
   `REQUIRED_FIELDS`/`validate()`.** Smallest possible change; closes the Section 8/9 gap
   immediately; naturally owned by whichever task ends up implementing `TC13`, since it is
   the same kind of schema-and-validator work.
2. **Backfill `found_by: external-finding`** (or the eventual confirmed slug) onto
   N8/B4/B7, rather than leaving the one concrete instance of this problem this repository
   has silently indistinguishable from self-found work.
3. **Start the Issue-per-task claiming convention manually, with no new tooling.** It costs
   nothing beyond `gh issue create`/`gh issue edit --add-assignee` to begin today, and
   using it a few times before automating anything tests the convention itself rather than
   a guess about it — the same demand-driven-growth discipline this project already applies
   to its instruction-set model (D7), applied here to process instead of ISA surface.
4. **Only after the manual convention has actually been exercised**, build the scheduled
   staleness-check workflow job (Section 5/10). Automating a convention nobody has used yet
   risks automating the wrong threshold or the wrong shape of "stale."
5. **Open `docs/handoffs/` immediately** (the directory plus a short README stating the
   convention in Section 7). It blocks on nothing else in this list and is the one gap here
   with no existing manual workaround — an unrouted finding with no task file yet has
   nowhere else to go today.
6. **Raise `TC13`'s priority.** Section 6's argument is that the multi-team reality makes
   the `TASKS.md` conflict hazard live now rather than hypothetical; this document
   recommends that be reflected in `TC13`'s `priority`/`priority_set` re-triage, not that
   this document re-triage it directly (out of scope per this task's "propose, do not
   enact" constraint).

## 12. Open uncertainties

Stated plainly rather than papered over, per this task's own instruction:

- This investigation could not observe how the other team(s) actually operate
  session-to-session — whether they will ever read `docs/handoffs/`, or check an Issue's
  assignee before starting `ready` work, is an assumption, not an observed fact. The only
  real defense against that assumption being wrong is Principle 2: assume any unchecked
  convention is sometimes ignored, and nothing above is silently upgraded to "solved"
  because a mechanism exists for it.
- Whether GitHub Issues are practically usable for this repository could not be verified
  from this environment (`gh` was not available to test against the live repository during
  this investigation). If Issues are ever unavailable for any reason, the design degrades
  to file-only claiming — a `## Notes`-only claim record with no atomic guarantee — and the
  double-claim hazard Section 5 was written to avoid returns. That fallback should be
  named explicitly if it is ever actually needed, not discovered by surprise.
- The 7-day staleness threshold (Section 5) is a guess calibrated only to "longer than any
  push gap observed so far," with no real data on the other team's cadence. It should be
  treated as a placeholder to be revisited once the claiming convention has actually
  produced a stale claim to learn from.
