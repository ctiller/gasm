# Cross-consumer proof-architecture dossier review

**Status:** BLOCKED pressure-test dossier; no design, implementation, API, migration, compression,
or integration authority.  Primary design and independent Reviewer assessed an uncommitted
`PROPOSED_PROOF_ARCHITECTURE.md` draft against canonical `5fa32fc2`.  The draft itself has no
archived commit, so this note records the review outcome, not a reproducible candidate.  The exact
reviewed file was
`<workspace>\docs\PROPOSED_PROOF_ARCHITECTURE.md`: 657 lines,
SHA-256 `615D25C28C9D0A8967294FF66CB636CB364F246A4EF1627093FC5EC14C19C93C`.
Findings remain **Reported** until that draft is committed or archived.  The accepted Trust rebuild
plan and the `MEMORY_MODEL.md` semantic baseline remain authoritative.

Evidence labels in this note are strict:

- **Proved:** exact theorem/file plus commit or reproducible archive provenance.
- **Reported:** an observation without complete reproducible provenance.
- **Required:** a design or proof obligation, not evidence that it is met.
- **Owner choice:** semantic product meaning that only Craig or the named owner may select.

## Valuable pressure-test structure

The draft usefully separates independent root meaning, specification-owned algorithm mathematics,
explicit staged lowering, and target/ABI/artifact closure.  It asks for canonical environments,
result-indexed partial effects, narrow relational ghost transport, seven materially different
consumers, evidence/hypothesis labels, and a falsification matrix.  These are useful dossier
questions.  They do not close the blockers below or make the dossier a canonical owner.

## Blocking corrections

### Evidence and status

Every **Proved** row must cite an exact theorem/file and commit or archive, and state its
model-relative scope.  Phrases such as “current source work” and “reviewed evidence” are not
auditable; downgrade them to **Reported** or **Required**.  In particular, Spike 4 parser recovery
does not prove connection/socket cleanup, and graphics evidence must identify its exact source.

The draft pressure-tests accepted Trust-plan principles and canonical tactic guidance, including
positive relational ghost transport and selected-feature irrelevance.  It must distinguish those
accepted principles from unresolved synthesis inherited from the blocked lowering lineage, such as
the proposed local-conservation and common-proof-edge packaging.  Each unresolved item remains a
hypothesis with its blocker recorded.  The dossier neither owns nor extends lowering semantics and
imports no API from blocked `2bc1c1ee`.

### Applicability and obligations

The mandatory obligation question applies to every **selected or conservatively applicable** result
edge, not every possible timeout, cancellation, overcommit, or termination family.  Closed selected
rows prove absent families irrelevant once.  Local applicability premises remain only for dynamic
or reflected operations.  Do not impose a global reachability or feature-tax proof.

Ghost evidence carries logical authority or obligation facts only with explicit origin and a
conservation theorem.  It cannot mint them.  Runtime-controlling selection, layout, or resource
facts are explicit lowering/artifact data with their own refinement, not erasable ghost payload.

### Memory and target ownership

The dossier consumes current `MEMORY_MODEL.md` semantics and may expose missing work; it cannot
split, weaken, duplicate, replace, or mark historical any accepted rule or gate without the
clause-level successor ledger.  Multi's source package owns an architecture-neutral workload and
behavior envelope parameterized by a selected model.  `MEMORY_MODEL.md`, ISA, and the selected
profile own x86 TSO, AArch64 consistency, and target-specific verdict derivation.  Expected tables
come from pinned model semantics independently of observed runs.

Caller-controlled `Environment` data contains admitted external inputs, outcomes, transcripts,
availability, and nondeterminism, not semantic provider selection, target capability, or sealed
admission evidence.  Provider/profile/handler selection is explicit sealed
lowering/artifact/certificate data, and target-minted certificates remain outside the environment.
Provider transcripts range over all admitted transcripts under pinned provider semantics, not
arbitrary impossible sequences; raw transcript bytes are oracle data and never authority.

### Graphics root

Unless Craig explicitly selects a Windows+Vulkan product root, the precious cube specification is
platform-neutral: window/input, graphics/device, shader, presentation, and consequence semantics.
Windows+Vulkan is one concrete profile; Linux Vulkan with Wayland/X11 and macOS Metal or MoltenVK
must remain possible without changing root meaning.  Exact SPIR-V is a peer-ISA implementation
unless the owner deliberately promotes it into the product contract.

A fixed capitalized projection list and `CleanupLedger` freeze candidate APIs and suggest a global
ledger.  Replace them with illustrative semantic responsibilities and a domain-local
cleanup/disposition projection.  **Owner choice:** select a graphics cancellation profile or prove
cancellation structurally absent for the selected product.

### Spike-specific corrections

- **Spike 3:** retry from a returned capability is result-indexed.  Cleanup failure, quarantine, or
  outstanding-obligation transfer may prevent a fresh retry.
- **Spike 4:** deterministic per-request behavior is relative to the complete selected environment;
  provider or concurrent nondeterminism is not erased.  Separate parser-buffer release, request
  scope, connection scope, unread bytes, response prefix, close/keep-alive, and recovery-owned
  cleanup.  Logical parser reset is not physical provider cleanup.
- **Spike 5:** short writes and partial provider/allocation outcomes are mandatory realization
  outcomes when present in the canonical environment, unless an exact selected-provider theorem
  excludes them.  Do not group them with optional source cancellation/timeout/forced termination.
  **Owner choice:** require exact deterministic gzip bytes or permit any conforming gzip stream.

## Proof-economy feedback

For each dossier, record one fallback-boundary row: approximate hand-authored assembly, the
program-specific lowering proof delta, excluded shared/spec proofs, evidence quality, whether a path
toward the informal ratio is plausible or unsupported, and whether the human feedback iteration
triggers.  One lightweight human analysis/change attempt is required for each triggering consumer
before owner review.  Success, adoption, reusable machinery, or repeated churn is not required; if
the correct result is no change or a direct one-shot proof, record that conclusion.

That feedback must decompose irreducible program-local delta from repeated structural, semantic,
transport, and composition burden.  For repeated burden, name the proper instruction, ISA, policy,
lowering, ABI, target, artifact, or composition owner and state the smallest candidate theorem or
interface that could own it.  This is an ownership diagnosis, not authorization to publish shared
machinery: a public abstraction still requires Craig's approval and materially different immediate
consumers.  Proof golfing, relabeling or moving lines without abstraction, weakening semantics or
the proved domain, and inflating generated-code denominators are invalid responses.

The following ratios are **Reported diagnostic counts**, not proof-budget measurements.  On exact
base `5fa32fc2`, each target includes immediate `*.lean` files only.  `ApproxTargetProofLOC` counts
nonblank physical lines except files named `Program.lean`, `Emit.lean`, `Test.lean`, or `Spec.lean`.
`AuthoredAsmEntries` counts `Program.lean` lines matching
`^\s*(instr\s|label\s|[a-zA-Z0-9_]+_label\s|call_import\s)`.  The method is nonrecursive and does
not distinguish generated code, include common/shared or source-spec proofs, count theorems, or
account for missing closure; it is intentionally coarse.

| Consumer | Reported ratio | Interpretation |
|---|---:|---|
| Spike 1 Linux / Windows | about 19.6 / 17.6 | plausibly within reach after shared output/exit transport |
| Spike 2 Linux / Windows | about 120.9 / 102.3 | no demonstrated path; human architecture iteration required |
| Spike 3 Linux / Windows | about 12.8 / 3.5 | incomplete closure and omitted common proofs make the result misleading |
| Spike 4 | apparent zero | platform equivalence proof absent; no evidence |
| Spike 5, graphics, multi | unavailable | no comparable complete fallback boundary |

Universal whole-product 10:1 is not a meaningful claim: syscall glue may be tiny while domain,
provider, and lifecycle proof is large, and generated instruction counts distort the denominator.
The ratio is useful only as an unvalidated human smell test for program-specific proof at a
hand-authored fallback boundary, excluding already-proved specification mathematics and reusable
owner proofs.  Never claim success from incomplete proof, moved proof LOC, generated instructions,
relabeling consumer-specific glue as shared, proof golfing, or semantic/domain weakening.

## Documentation disposition gate

Before this dossier can become canonical, record explicit keep/split/replace/link/historical
dispositions for `MEMORY_MODEL.md`, `REVIEW.md`, `PROOF_MACHINERY_INDEX.md`,
`TRUST_REBUILD_PLAN.md`, `SYSTEM_EFFECTS.md`, `ABI_CONTEXT.md`, graphics foundation documents, and
every affected spike plan.  The file may remain a non-normative pressure-test index.  It becomes a
canonical owner only through an explicit owner decision, never by silently coexisting with the
accepted plan.
