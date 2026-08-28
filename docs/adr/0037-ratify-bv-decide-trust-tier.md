# 0037. Ratify `bv_decide` as Law 10's Fourth Trust Rung

## Status

Accepted, 2026-08-27. (PLAN.md D28.)

## Context

PA1 (the crc32 pathfinder) introduced this codebase's first `bv_decide` proofs
(`Stdlib/Zlib/CRC32Equivalence.lean`: `and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`,
`G8bf_table`, and the downstream `G8_eq_Gbf8`/`crc32ByteStep_eq_G8`). Law 10's text at
the time named only `native_decide`/`decide`; whether `bv_decide` belonged in the same
admissible category, a stronger kernel-checked one, or a restricted/separate one was an
open, owner-level call about the trust base, not a decision an implementation task
could make unilaterally.

A task-scoped investigation (`TCB.md` T14) established, empirically, that `bv_decide`
is **not** kernel-checked: `LratCert.toReflectionProof` builds a term applying the
LRAT-certificate checker to the goal's own reflected expression and certificate, and
passes it to `Lean.Meta.nativeEqTrue` — the identical routine `native_decide` itself
calls to compile, run, and axiomatize a computed result. The kernel never replays the
certificate. This toolchain (v4.33.1) has no `checkProofs`-style kernel-replay option
for `bv_decide` at all. `bv_decide` is therefore the same trust class as
`native_decide`, with a strictly larger trusted surface: it additionally trusts the
bitblaster and an external CaDiCaL-compatible SAT solver process (the external solver's
*search* is not trusted — a bad search merely fails to produce a certificate — but the
LRAT checker that verifies what it found runs the same compiled-and-axiomatized way
`native_decide`'s own decision procedure does).

T14 also found that the SAT solver's resolved path and version were not recorded or
asserted anywhere, unlike `node`/`nasm`/`python` under TCB T9's disclosure plan for
`scripts/run_gates.py`, and that `bv_decide`'s toolchain-bundled `cadical.exe` — unlike
T9's genuinely floating oracles — is pinned by `lean-toolchain` the same way
`lean.exe`/`lake.exe` are, except when it falls back to an unpinned bare `cadical` on
`PATH`.

`docs/REVIEW.md` carried a drafted amendment marked `**Status**: proposed` since the
task that produced T14, explicitly deferring ratification: "this is an owner-level call
... rather than one an implementation task should decide unilaterally." The owner was
shown the analysis and replied "ok, bv_decide seems fine then."

Separately, and after that approval, the owner stated the project's target posture in
his own words: "it's critical we get to a trustable state: no axioms, strong
verification, checked models." That statement does not reverse the `bv_decide`
approval — it stands — but it governs how this ADR must characterize it: not as a
destination the project is content to sit at, but as a currently-necessary waypoint
away from which further progress is expected. `bv_decide` introduces
`<decl>._native.bv_decide.ax_*` axioms (T14); a "no axioms" target makes every
`finite-forall` allowlist entry — the four PA1 entries included — recorded debt, not a
compliant resting place.

## Decision

`bv_decide` is admitted into Law 10 alongside `decide`/`native_decide`, under the same
restriction all three already share (exhaustive finite-∀ only; never a single ground
instance, never a sampled or infinite domain) — **as an approved waypoint, not a
permanent resting place**. It is admissible because it reaches finite bitvector domains
(`crc32ByteStep_eq_G8`'s `UInt32 × UInt8`, ~10^12 cases, foremost) far too large for
rungs 1–2 to reach today, and because it is strictly better than the pointwise
`native_decide`/ground-instance proof it would otherwise force: an oracle whose result
is *trusted* rather than *checked*, at a domain size where the alternative was no proof
at all, not a cheaper one.

`docs/REVIEW.md` Law 10 is rewritten to present an explicit ordering of proof
mechanisms by trust cost, rather than a flat list with `bv_decide` appended:

1. **Structural proof** (induction, algebraic rewriting) — no oracle at all, genuinely
   kernel-checked. Always preferred.
2. **`decide`** — the kernel itself performs the evaluation; no axiom is introduced, so
   it needs no `scripts/gate_allowlist.txt` entry. Categorically different from rungs 3
   and 4: genuinely checked, not merely trusted. Feasible only on small domains.
3. **`native_decide`** — trusted, not checked: the compiler and runtime evaluate, and
   the result enters via an axiom. Requires an enumerable domain.
4. **`bv_decide`** — same trust class as rung 3, larger surface (bitblaster + LRAT
   checker additionally trusted), but reaches finite bitvector domains far too large to
   enumerate. `crc32ByteStep_eq_G8` quantifies over `UInt32 × UInt8` (~10^12 cases),
   where enumeration is infeasible, not merely slow — for that theorem the real choice
   was `bv_decide` or no proof.

Rungs 3 and 4 both require an honest `scripts/gate_allowlist.txt` entry; rung 2 does
not. The existing `finite-forall` categorization for PA1's four `bv_decide` entries
(`and_one_cases`, `G_eq_Gbf`, `xor_byte_shr8`, `G8bf_table`) is unchanged — T14
recommended no change, since each is an ordinary theorem universally quantified over a
complete finite bitvector domain.

T14's first disclosure recommendation is also implemented: `scripts/run_gates.py` gains
`detect_cadical()`, which resolves the solver the same way `bv_decide`'s own
`determineSolver` does (toolchain-bundled `cadical.exe`/`cadical` under the running
`lean`'s own prefix, found via `lean --print-prefix`, falling back to a bare `cadical`
on `PATH`) and records its path, whether it was the pinned bundled binary or the
unpinned fallback, and its version — in the same oracle-version table T9 already
maintains for `node`/`nasm`/`python`.

## Consequences

Law 10 now makes explicit a distinction its prior text blurred: rung 2 (`decide`) is
genuinely kernel-checked and categorically different from rungs 3–4, which are trusted
compiled-execution results wearing an axiom, not kernel-verified proofs. Reviewers and
future contributors reading Law 10 no longer have to infer this from the allowlist
mechanics; the ordering states it.

`bv_decide` remains the only route to several already-landed PA1 theorems
(`crc32ByteStep_eq_G8` foremost) whose domain is too large for `decide`/`native_decide`
to reach and too large to prove structurally today. This ratification does not change
what those theorems establish — it makes explicit and owner-approved a trust cost that
was previously true of the tree but undisclosed in Law 10's own text.

The solver-version disclosure closes one concrete gap: a toolchain install missing the
bundled `cadical.exe` (or one where PATH resolves a different CaDiCaL build than the
toolchain ships) is now visible in gate output rather than silently substituting an
unpinned binary with no record of which one ran.

**The end state is zero allowlist entries.** The owner's stated target — "a trustable
state: no axioms, strong verification, checked models" — admits no permanent residue in
`scripts/gate_allowlist.txt` at all; the only acceptable axiom footprint for a finished
proof is Lean's own foundational three (`propext`, `Classical.choice`, `Quot.sound`).
Every `finite-forall`/`grandfathered`/`axiom-only` entry today, `bv_decide`'s four PA1
entries included, is recorded debt against that end state, not a compliant destination.
This ratification makes `bv_decide` an admissible waypoint on the way there; it does not
relax the target.

**Reducing the oracle surface is progress even short of zero.** PA1 demonstrated the
relevant technique without being separately asked for it: branch-free normalization
(design task M9(a)) collapsed what would otherwise have been several independent
`bv_decide` certificates into a shape closing on one, which is why
`crc32ByteStep_eq_G8` transitively depends on five `bv_decide`-family axioms rather than
dozens. Rung 4 is where a proof goes when rungs 1–2 cannot reach it *today* — the
standing expectation is to keep pushing work back down the ordering (fewer certificates,
smaller bit-blasted goals, eventual structural replacement) as the model and lemma
library mature, not to settle at whichever rung happens to close the goal first.

**Left unbuilt, deliberately, as unapproved scope**: a ratchet gate that counts
oracle-dependent (rung-3/rung-4) declarations tree-wide and fails on growth past some
threshold has been raised with the owner but not approved. It is not built here. If
approved later, it would be a natural extension of this Law's allowlist mechanism —
recorded here only as a possibility, not a commitment.

## Provenance

Mixed. Two things are Owner-stated, verbatim, and only these two:

- The approval of `bv_decide`'s admissibility: "ok, bv_decide seems fine then," in
  response to being shown T14's analysis.
- The project's target posture, stated separately: "it's critical we get to a
  trustable state: no axioms, strong verification, checked models."

Everything else in this ADR is the coordinator's construction from those two
statements plus T14's empirical findings, assented to by the owner but not his own
words, and must not be read as an owner quotation:
- The four-rung trust-cost ordering in the Decision section (including the framing
  that rung 2 is categorically different from rungs 3–4, and each rung's rationale)
  is the coordinator's structuring of T14's findings.
- The "approved waypoint, not a permanent resting place" characterization, the
  "end state is zero allowlist entries" framing, and the reading of PA1's branch-free
  normalization as evidence that reducing oracle surface counts as progress, are the
  coordinator's synthesis of the two owner statements above — the owner did not
  himself describe `bv_decide` as a waypoint or cite PA1's normalization technique.

This distinction is drawn deliberately: this repository has a recorded incident of a
paraphrase being presented inside quotation marks with an owner attribution, and this
ADR does not repeat it.
