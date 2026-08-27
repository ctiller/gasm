# Contributing to `gasm`

`gasm` is a formal framework, not a conventional codebase, and its process is
unusual on purpose. Read this document before sending a change — the review
discipline described below is not bureaucracy layered on top of "real" work;
it *is* the work. If you haven't yet, read
[`docs/VISION.md`](docs/VISION.md) first — it explains *why* the process
below is shaped the way it is.

## The one-sentence version

Every change to `Gasm/`, `Stdlib/`, or `Spikes/` is a formally verified
claim, backed by a citation to a design document, and every design document
must itself be fully realized once it is cited. Nothing here is trusted
because someone reviewed it and it looked right; it is trusted because a
gate mechanically checked it and could not have passed otherwise.

## The Laws

The repository is governed by fourteen ratified Laws, stated in full in
[`docs/REVIEW.md`](docs/REVIEW.md). Do not treat the summary below as a
substitute for reading them — several turn on precise wording that a
paraphrase loses. Briefly, they cover:

- **Citation & traceability (Laws 1–3)**: every Lean declaration is
  completely motivated by its `/- REF: ... -/` annotations (Law 1); once a
  design-doc section is cited, it must be 100% implemented (Law 2);
  unreferenced sections are an automatically tracked backlog (Law 3).
- **External grounding (Law 4)**: models cite authoritative external sources
  rather than self-authored approximations of them.
- **Stop-and-Design (Law 5)**: see below.
- **Reference reproducibility (Law 6)**: everything an authoritative
  citation depends on must be independently verifiable, not hand-maintained.
- **Authoring ergonomics (Law 7)**: the `Spec.lean` / `Program.lean` /
  `Equivalence.lean` trio stays clean; infrastructure lives in `Gasm` itself.
- **Anti-facade (Law 8)**: no dead typeclasses, no inert abstractions; ground
  instances are labeled `*_inst` and never presented as general theorems.
- **Anti-pointwise (Law 9)**: whole-program contracts are universally
  quantified over their real input domain — no single-hardcoded-vector
  "verification."
- **Kernel-checked gates (Law 10)**: `native_decide` is admissible only for
  propositions exhaustively quantified over their entire finite domain.
- **Memory capability mandate (Law 11)**: memory-touching instructions must
  carry capability proofs; programs that can't prove access are unbuildable.
- **Connection theorems (Law 12)**: two encodings of one fact may coexist
  only when a kernel-checked theorem proves them equal.
- **Findings become gates (Law 13)**: every defect found by review or
  fuzzing must terminate in a mechanical prevention of its entire class, not
  just a fix of the one instance.
- **Calibration data governance (Law 14)**: measured performance data is a
  third reference class — checked in, harness-regenerable, never hand-edited.

If a Law and any other document (including this one) ever disagree,
`docs/REVIEW.md` wins.

## Describing not-yet-built machinery: the `**Status**:` convention

Writing a design document for a target or subsystem that does not exist yet
is normal and expected here (see Law 5 below) — a new target's design doc
will necessarily describe machinery, ABI rules, and API contracts that have
no Lean implementation on the day it's written. That is not a defect. What
*is* a defect is a document that reads as though the machinery already
enforces something, with no way for a reader to tell design from reality.
`scripts/check_doc_facade.py` (TC21) mechanically checks for exactly that
gap: a backtick-quoted identifier cited inside a MUST/is-implemented-shaped
claim, absent from the whole `.lean` tree, with no disclosure nearby. It is
wired into CI as a **required, blocking** gate, so read this before writing
a design doc for new machinery (this applies to any new target, including
the Linux target currently in progress under `docs/TARGETS/`):

- If a claim in your design doc names a mechanism that isn't built yet,
  attach a `**Status**:` sentence next to it, stating plainly that it does
  not exist in the tree today and, if one exists, the tracking task that
  will build it (`PA#`/`TC#`/`N#`/`F#`/`G#`/...). `docs/REVIEW.md` Law 9 and
  Law 11 are the two ratified examples of this pattern.
- Any of these phrasings in the same paragraph as the claim also satisfies
  it: "ratified design", "not yet implemented", "does not yet exist",
  "design-only", "fully designed but dormant", "pending implementation", or
  "tracked as `PA#`/`TC#`/`N#`/...". Pick whichever reads most naturally.
- This costs one sentence and is cheap on purpose — the gate exists to make
  the *absence* of that sentence loud, not to slow down legitimate design
  work. A document that already says "this is a design, not yet built" is
  never flagged, no matter how many not-yet-existing identifiers it names.

## The Stop-and-Design Invariant (Law 5)

> Whenever a task demands any concept, instruction, ABI rule, binary header,
> or API contract that is not yet fully designed in the repository,
> implementation MUST STOP immediately.

Concretely: if you're writing assembly and discover you need an ABI detail,
a binary-format field, or an instruction encoding that isn't already
specified under `docs/`, you do not improvise it inline and cite yourself
later. You stop, write (or extend) the design document, get it reviewed, and
only then write the Lean. This is the mechanism that keeps Law 1 (no
invention) true by construction rather than by discipline alone — see
`docs/VISION.md` §3.3 for why this project treats "build the model first,
validate it, *then* build on it" as load-bearing rather than optional
process.

## The citation requirement

Every top-level Lean declaration (`inductive`, `structure`, `def`, `class`,
`instance`, `theorem`, `lemma`, `axiom`) needs one or more `/- REF: ... -/`
annotations pointing at the design-document section(s) that motivate it:

```lean
/- REF: docs/API_STATE_MODELS.md#1-the-composed-state-model--zero-cost-proof-erasure -/
structure ComposedState (Arch : Type) (ApiStateType : Type) where
  ...
```

`python scripts/check_refs.py` enforces this: it indexes every heading in
`docs/`, indexes every `REF:` citation in the tree, fails if a citation
points at a section that doesn't exist, and fails if any Lean declaration
has no citation at all. It also reports the **unreferenced backlog** — every
design-doc section not yet cited by any code — as the honest, mechanically
computed remainder of what's left to build.

**A note on where citations point, and where that's heading.** Citations
into this project's own design documents (`docs/*.md`) are permanent and
unaffected by anything below. Separately, citations that ground a model in
*external* authoritative material (hardware manuals, RFCs, format specs —
Law 4) are migrating from vendored copies stored in the repository to a
`references.json` registry of source URLs and content hashes, checked
against a local (gitignored) cache rather than a copy shipped in the tree —
see [`docs/REFERENCE_INDEX.md`](docs/REFERENCE_INDEX.md) for the design.
This repository does not ship third-party documentation prose; it cites it.
If you're grounding new work in an external spec, check that design doc for
the current state of the migration before adding a new citation shape.

## Spike discipline

Progress is driven by **Spikes**: minimal, fully vertical, end-to-end
executable artifacts that force integration across every layer at once —
see [`docs/SPIKES.md`](docs/SPIKES.md) for the roadmap and per-spike forced
capabilities. Each spike is authored as the trio Law 7 protects:

1. **`Spec.lean`** — a pure, idiomatic Lean model of the intended behavior,
   with no machine-specific baggage.
2. **`Program.lean`** — the hand-written proof-carrying assembly (or Wasm
   AST), authored as straightforwardly as the target's DSL allows.
3. **`Equivalence.lean`** — the proof that the two correspond, containing
   *only* the simulation argument — no ad-hoc interpreters, no manual
   jump/offset tables, no hardcoded machine-layout constants standing in for
   a target loader. If you find yourself writing one of those inside an
   `Equivalence.lean`, the missing capability belongs in `Gasm.Targets.*`,
   not in the proof file — that's Law 7's prohibited-anti-pattern list,
   verbatim.

A new spike (or a new target for an existing spike) is exactly the kind of
task Law 5 governs: if it needs an ABI rule, instruction, or API contract
that isn't modeled yet, design that first.

## The gates that must pass

Every one of these must exit `0` before a change is considered mergeable.
Run them from the repository root:

```sh
lake build                                          # zero errors, zero sorry, zero unauthorized axioms
python scripts/check_refs.py                        # 100% citation validity, zero un-cited declarations
python scripts/check_gates.py                       # fast source-level Law 10 pre-check
lake exe check_gates_axioms                          # the LOAD-BEARING Law 10 gate — building it is not running it
python scripts/check_licenses.py                    # Apache-2.0 header compliance on first-party source
```

If a `references/` reproducibility check exists in your checkout at the time
you read this (`python scripts/regenerate_references.py --verify`), run that
too — see `docs/REFERENCE_INDEX.md` for whether that step has been
superseded by the registry migration in your branch.

Two things worth internalizing about this list, because they're easy to get
backwards:

- **`lake exe check_gates_axioms` must be *run*, not just built.** It's a
  `lean_exe` target, which means plain `lake build` compiles it as a
  byproduct of building `defaultTargets` — that is not the same as
  executing it. The Python pre-check (`check_gates.py`) is fast
  defense-in-depth; the axiom-level Lean tool is what actually reads Lean's
  own kernel-recorded axiom-dependency graph and is immune to source-level
  disguise. Treat "I built it" and "I ran it and it exited 0" as two
  different claims.
- **A gate that a bad implementation can pass will eventually be passed by
  a bad implementation** (`docs/VISION.md` §2). If you find yourself wanting
  to special-case a gate to let a change through, that is very likely a sign
  the change is wrong, not the gate.

## Review discipline

Reviews follow the Three-Pillar Verification Protocol in
[`docs/REVIEW.md`](docs/REVIEW.md) §4. Qualitative "LGTM"-style review is
explicitly prohibited by that document. In order:

1. **Pillar 1 — Mechanical Truth.** Did every gate above pass? If not,
   reject immediately; nothing else matters yet.
2. **Pillar 2 — Semantic Integrity & Adversarial Domain-Gap Hunting.** This
   is the pillar that actually matters, and it is the one that cannot be
   automated away (yet): for every theorem under review, state the spec
   requirement being formalized, paste the exact Lean signature, and map one
   to the other step by step — do the hypotheses match the spec's
   preconditions exactly (not artificially stricter), does the conclusion
   guarantee everything the spec promises (not a weakened subset)? Reviewers
   must actively hunt for input configurations, edge cases, or spec-permitted
   behaviors the theorem quietly excludes, and record them in a **Domain Gap
   Matrix**. This is, in a mature `gasm`, review's *only* irreplaceable
   question — see `docs/VISION.md` §2: "are we proving the right theorems?"
   Everything else is meant to be progressively absorbed into mechanical
   gates (Law 13); a Pillar-1/3 finding a human catches by hand is
   simultaneously a bug report *and* a missing-gate report.
3. **Pillar 3 — Structured Architectural Health Audit.** Four axes, all
   explicit in the review artifact: target separation (does code live in the
   right domain — `Core/`, `Effects/`, `Targets/`, `Stdlib/` — without
   bleeding OS/hardware concepts across the boundary?), abstraction
   cleanliness, factoring/DRY, and diffusion-vs-concentration of critical
   invariants.

All three gates must evaluate TRUE for an approval. Note the asymmetry
deliberately built into this: implementation correctness is expected to be
*mechanical* (Pillar 1 either passes or it doesn't), and review attention
concentrates on whether the formalization itself is honest — whether the
theorem you wrote is the theorem the spec actually demands, not a
conveniently provable neighbor of it.

**Every finding closes a gap, not just an instance (Law 13).** If review or
fuzzing surfaces a defect, the fix is incomplete until it also lands the
mechanical prevention that would have caught the entire class automatically
— a stronger type, a new theorem, a build-failing check, or (for
world-facing harnesses that can't be theorems) a mandatory positive/negative
control vector. Sign-off must name the gate.

## Practical notes for a first contribution

- Read `docs/VISION.md`, `docs/REVIEW.md`, and `docs/SPIKES.md` in that
  order before writing any Lean.
- `docs/adr/` records the durable *why* behind major decisions;
  `docs/tasks/` tracks in-flight design and implementation work as a
  happens-after DAG. Check both before starting something that might
  already be underway or already decided against.
- `lake build` compiles and links every target listed in `lakefile.toml`'s
  `defaultTargets` — this includes every spike executable, every fuzzer, and
  every test binary, so a full build is the real CI gate. There is no
  opt-out for local iteration speed built into `defaultTargets` itself;
  check `scripts/` for any dev-convenience wrapper that builds a narrower
  target set, and always run the full `lake build` before proposing a
  change.
- Prefer small, spike-shaped, end-to-end changes over broad speculative
  model growth. Per `docs/VISION.md` §3.3, target models are deliberately
  incomplete — new surface enters the model only when a spike demands it,
  and every increment is differentially validated in the same change that
  introduces it. Building out ISA/API surface ahead of demand is exactly
  the failure mode this project's predecessor died from; don't repeat it.
