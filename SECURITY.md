# Security Policy

## What "security" means in this repository

`gasm` is a formal framework for hand-authored, proof-carrying assembly. It
is not a network service and does not (yet) run anyone's untrusted input in
production. The security-relevant surface here is narrower and stranger than
a typical application's, and it is worth naming precisely because a generic
report ("XSS", "SQL injection") almost never applies here.

The things that would actually matter, roughly in order of severity:

1. **A soundness bug in the proof system or its trusted base.** If a
   `VerifiedProgram` typechecks and `lake build` is green, this project
   claims the emitted binary genuinely satisfies its stated contract. A way
   to make the Lean kernel accept a false theorem, a hidden `sorry`, an
   unauthorized axiom that slips past `lake exe check_gates_axioms`, or a
   `native_decide` discharging a proposition that is not actually an
   exhaustive finite-∀ (see Law 10 in [`docs/REVIEW.md`](docs/REVIEW.md)) —
   any of these would mean every "verified" claim built on top of it is
   worthless. This is the single most serious class of finding this project
   can receive.
2. **A gate that passes when it should fail.** `scripts/check_refs.py`,
   `scripts/check_gates.py`, `lake exe check_gates_axioms`, and
   `scripts/check_licenses.py` exist specifically to make certain classes of
   defect mechanically unrepresentable or automatically caught (see Law 13,
   "Findings Become Gates"). A way to construct code that should be rejected
   by one of these gates but is accepted — an evasion of the citation
   checker, an allowlist bypass, a `native_decide` occurrence the Python
   pre-check can't see, a pointwise "verification" masquerading as universal
   (Law 9) — is a critical finding even though nothing crashes and no data
   is leaked in the conventional sense. The canonical historical example
   (recorded in [`docs/VISION.md`](docs/VISION.md) §2) is a target
   realization that emitted one hardcoded output stream and legitimately
   passed a pointwise equivalence theorem, because the theorem only ever
   examined the input the stream was precomputed from.
3. **A model that diverges from the real hardware/OS/engine it claims to
   describe.** The x86-64 semantics, the Wasm semantics, and the Windows
   API model are this project's axioms about the world (see
   [`docs/VISION.md`](docs/VISION.md) §3.2). If a differential-validation
   harness (the hardware fuzz harness, a host Wasm runtime oracle, a Win32
   API harness) can be shown to disagree with the model it's supposed to be
   checking, or — worse — can be shown to *not actually be checking what it
   claims to check* (an oracle that no-ops, a control vector that can't
   fail, a harness that never executes the artifact it's meant to validate),
   that is a report worth making. `TCB.md` documents several known,
   already-tracked gaps of this kind; a genuinely new one, or a
   demonstration that a *known* gap is worse than documented, is still worth
   reporting.
4. **Memory-safety bypasses in generated/hand-authored assembly.** Per Law
   11, memory-touching instructions are supposed to be unrepresentable
   without a valid capability proof. A construction that assembles a
   memory access without one — or a capability-token API that can be
   satisfied vacuously — is a real finding.
5. **Conventional issues** — a malicious input to one of the Python tooling
   scripts (`scripts/*.py`), a path-traversal or command-injection bug in
   the reference-fetching or NASM-invocation code, credentials or secrets
   accidentally committed to the tree — are also in scope and should be
   reported the normal way, but are not what makes this project's security
   posture unusual.

**Out of scope / not useful reports:** generic automated scanner output
against this repository's Markdown or Lean source with no specific,
demonstrated exploit; "this dependency has a CVE" reports — `gasm` has zero
external Lean package dependencies (see `lake-manifest.json`) and the only
runtime dependencies are the Lean/Lake toolchain itself and, for local
development, an assembler/NASM invocation; social-engineering or physical
security reports.

## Reporting a vulnerability

There is no dedicated security mailing list or bug-bounty program for this
project yet. To report a security-relevant finding of any of the above
kinds, email **craig.tiller@gmail.com** with:

- What the finding is and why it matters (which category above it falls
  under, or your reasoning if it doesn't fit any of them).
- A minimal reproduction: the Lean declaration, gate command, or harness
  invocation that demonstrates the issue.
- If it's a soundness or gate-evasion finding, the *class* of the defect —
  per Law 13, the goal is always a mechanical prevention of the whole class,
  not just a fix to the one instance you found. A report that identifies the
  generalizable shape of the problem is more valuable than one that only
  patches a symptom.

Please do not open a public GitHub issue for a soundness or gate-evasion
finding until there has been a chance to assess it and land a fix or a
mechanical prevention — the project's own Laws treat "found a bug but didn't
close the gap that let it in" as an incomplete fix, and a public issue
before that happens invites someone else to exploit the same gap in the
interim, in the spirit of standard responsible-disclosure practice.
Conventional low-severity issues (typos in error messages, non-security
tooling bugs) are fine as regular public issues.

## Response

This is a research/hobby project with a single maintainer at present, so
there is no formal SLA. Reports will be acknowledged as promptly as
possible, and a genuine soundness or gate-evasion finding will be treated as
the highest-priority work in the repository, consistent with how the
project's own Laws already rank "the gate is the product"
([`docs/VISION.md`](docs/VISION.md) §2) above everything else.
