# Trust proof rebuild plan

**Status:** proposed architecture and active execution plan. MP owns design refinement; Reviewer
owns execution-plan falsification. Neither review blocks isolated experimentation, but no rebuilt
spike becomes canonical until both applicable findings are closed.

This plan replaces the existing spike proof architecture. It does not refactor, migrate, wrap, or
generalize the old `Equivalence.lean` chains. Git history preserves those chains as requirements,
counterexamples, and spare parts.

## 1. Outcome and quantitative target

Rebuild Spikes 1 through 5 so each emitted artifact obtains the sole universal
`Gasm.Core.Platform.VerifiedProgram` through reusable proof-producing libraries and a small local
refinement delta.

The program-authoring target is:

> **At most 10 lines of program-specific proof burden per authored line of assembly.**

For a four-instruction artifact, the default budget is therefore forty substantive proof lines.
Going over budget is an architecture failure requiring an explicit design review, not an invitation
to hide the proof in another spike-local file.

### 1.1 Measurement

- **Assembly denominator:** one authored target instruction, call, branch, or terminator statement
  counts as one line. A macro reports both source statements and expanded emitted instructions; the
  stricter source-statement ratio is the acceptance metric.
- **Proof numerator:** nonblank, noncomment Lean lines in the rebuilt spike that construct semantic
  premises, invariants, refinement theorems, platform certificates, or the final `VerifiedProgram`.
  Inline proof blocks count. Imports, namespace declarations, specifications, executable source,
  tests, and data literals do not count.
- **Library charging:** a new `Gasm` or `Stdlib` proof used by only one rebuilt spike is charged to
  that spike until a second materially different consumer uses it. This prevents relocation from
  masquerading as proof-economy improvement.
- **Generated certificates:** generated proof terms do not count as authored burden, but their
  generator/checker and total correctness theorem are ordinary library proof lines and must remain
  kernel checked.
- Every cutover records old and new proof lines, assembly statements, ratio, focused build time, and
  peak memory when available.

The ratio measures author burden, not soundness. Universal inputs, exact artifact identity,
production execution, outcomes, frames, authority, lifecycle, and cleanup remain mandatory even
when the budget is missed.

## 2. Replacement proof architecture — MP review surface

The required dependency direction is:

```text
independent logical specification
        ↓
proof-carrying source / typed blocks and terminators
        ↓
exact closed execution over the production instruction index
        ↓
target-owned load, linker, provider, frame, and admissibility adapters
        ↓
explicit execution-to-spec refinement
        ↓
ProgramArtifact / Provider / Entry / Admissibility / Behavior certificates
        ↓
VerifiedProgram.compose
```

`VerifiedProgram` is the derived root, never an input to the machinery intended to construct it.
The current post-hoc `VerifiedProgramCFGArtifactCertificate` direction is not the rebuild template.

### 2.1 Library ownership

- **Instruction families** own codec, decoder routing, operational step, fault, exact memory-access
  descriptors, and frame laws. Programs do not re-prove these for concrete operands.
- **Proof-carrying block/CFG libraries** own sequential composition, exact middle-state transfer,
  event accumulation, branches, calls, selected loops, and typed terminal transitions.
- **Linkers** return artifact identity, layout/index resolution, import/export realization, and
  provider-slot linkage as certificates of their construction.
- **Platforms** own loader relations, standard runtime realization, external-input framing,
  admissible outcome classification, and profile-specific physical grants.
- **Specifications remain independent.** A platform adapter accepts an externally authored spec and
  an explicit execution-to-spec refinement theorem. It may not define `spec` from `run`, a closed
  outcome, emitted bytes, or an evaluator.
- **Applicability remains selected.** Checked memory, input, resource, reactive, concurrency, and
  cleanup obligations arise only from reachable selected features. No catch-all typeclass or empty
  decorative evidence is permitted.

### 2.2 Shared exact execution object

Artifact, instruction index, environment, loaded state, runtime/interceptor, entry context, proof
budget, ghost world, and host state must agree through one indexed object or minimal named bridge.
Consumers must not reconstruct extensionally equal copies and then spend most of their proof on
`rfl`/transport plumbing.

The first accepted lower-layer candidate is `Gasm.Targets.X86_64.ClosedExecution`, which packages an
exact selected production prefix and typed process-exit step. It deliberately supplies no behavioral
specification. Platform adapters above it remain under review.

### 2.3 Clean-slate consumers

New work is authored in fresh namespaces:

```text
Spikes/Rebuilt/Spike1Hello/
Spikes/Rebuilt/Spike2Fibonacci/
Spikes/Rebuilt/Spike3SortLines/
Spikes/Rebuilt/Spike4HttpServer/
Spikes/Rebuilt/Spike5Gzip/
```

`Spikes/Rebuilt/CheckedMemoryWindows/` is a temporary template/pathfinder, not a sixth product spike.

Rebuilt proof modules import stable `Gasm`/`Stdlib` libraries, not old spike proof modules. A
temporary dependency on an old source/spec definition must be listed as cutover debt and removed
before acceptance. There are no compatibility aliases, dual verified emitters, or parallel proof
authorities.

### 2.4 Soundness rejection rules

Reject a candidate immediately if it uses or enables:

- `spec := run`, `spec := execution.outcome`, or any equivalent self-selected meaning;
- a narrowed caller-selected input domain in place of canonical `Environment` quantification;
- a detached evaluator, instruction list, artifact, provider map, or host state;
- `sorry`, new axioms, `native_decide`, allowlists, or computational grandfathering;
- total memory as evidence of mapping/writability;
- generic ghost ownership as physical or lifecycle authority;
- caller-forgeable provider, discharge, cleanup, or terminal evidence;
- proof relocation without a second materially different consumer.

## 3. Execution plan — Reviewer review surface

### Phase A — establish the template

1. Land the independently accepted exact closed-execution combinator.
2. Build target-owned Windows non-input adapters that:
   - derive provider linkage from the linker;
   - use the standard target-owned runtime/capability realization;
   - centralize external-input framing;
   - accept an independent specification and refinement theorem.
3. Build `Spikes/Rebuilt/CheckedMemoryWindows` from blank as the four-instruction pathfinder.
4. Require MP soundness review and Reviewer proof-economy review.
5. Validate the same shared path on rebuilt Spike 1 before declaring a template.

### Phase B — rebuild Spike 1

Reauthor the simple platform artifacts first. Required libraries are straight-line/terminal
composition, linker certificates, standard provider/runtime adapters, and independent trace/outcome
refinement. The local proof should mostly state the intended output and terminal result.

### Phase C — rebuild Spike 2

Build one parameterized Fibonacci row certificate and structural bounded iterator. Reuse decimal
schedule, exact prefix, frame, recurrence, event, and typed exit libraries; do not preserve the
old per-row proof forest. Linux is the first acceptance target, followed by Windows and Wasm through
the same logical iteration theorem and target-specific lowering adapters.

### Phase D — rebuild Spike 3

Build the arbitrary-finite-input theorem, not literal-vector regressions. Required layers are:
immutable line identities/content, streaming tokenizer/chunk composition, bounded storage/resource
outcomes, permutation/stability/sortedness, algorithm progress, target execution, and exact output
refinement. Pure `Stdlib` Vec/sort work may proceed independently; old Spike 3 proof roots remain
frozen.

### Phase E — rebuild Spike 4

Introduce the ratified reactive inner/outer contract before claiming completion: universal
per-request deterministic behavior plus outer progress/liveness. Required libraries cover byte
request domains, fragmented reads, handler CFG composition, resource/cleanup outcomes, and target
socket/provider realization. A finite route sample is regression evidence only.

### Phase F — rebuild Spike 5

Compose codec roundtrip/refinement, fallible streaming fold, capacity/resource refusal, chunk
independence, cleanup, and native/WASI adapters. Compression and decompression share the same
streaming capability algebra; platform proofs do not replay codec internals.

### Phase G — atomic cutover per spike

For each spike:

1. Independently review the rebuilt tree and burden measurement.
2. Delete the old spike directory and its obsolete targets/controls.
3. Promote the rebuilt tree to the canonical path/namespace.
4. Update umbrella imports, Lake targets, emitters, tests, docs, and citations.
5. Prove with repository search that no old proof authority, compatibility alias, or forbidden
   tactic remains.
6. Run focused builds first, then the coordinated full trust gates.

## 4. Worker and integration protocol

- Workers receive non-overlapping spike/library ownership and work from current `origin/main`.
- Commits are dependency ordered: shared mechanism, clean-slate consumer increment, deletion/cutover.
- Every handoff names exact parent/hash, semantic claim, files, old burden removed, focused commands,
  forbidden-token scan, `git diff --check`, resource observations, and known unrelated failures.
- MP reviews architecture/soundness; Reviewer falsifies execution, proof economy, and acceptance
  evidence. A soundness finding vetoes integration regardless of schedule.
- `Trust repair` alone integrates reviewed commits into the clean main staging worktree and pushes.
- Workers may continue on isolated follow-up commits while reviews run, but blocked commits cannot be
  used as templates or cut over.

## 5. Accountability ledger

| Slice | Owner | State | Integration condition |
|---|---|---|---|
| Exact x86 closed execution | trustrebuild1 | Reviewer accepted `1e47693c`; integration pending | Current-main rebase and integrator focused build |
| Windows certificate adapter | trustrebuild1 | `357b9640` blocked | Independent spec, linker-derived providers, minimal runtime bridge, re-review |
| Clean checked-memory pathfinder | trustrebuild1 | Not started | Corrected adapter accepted; ≤10:1 burden |
| Clean Spike 1 | trustrebuild1 | Not started | Pathfinder plus second-consumer validation |
| Clean Spike 2 Linux | trustrebuild2 | Active under `Spikes/Rebuilt` | Structural termination, no old proof imports, ≤10:1 burden |
| Clean Spikes 3–5 | Unassigned | Frozen pending workers/template | Explicit assignment and prerequisite library brief |

## 6. Governing references

This plan executes the composition direction in [VISION](VISION.md#4-tractability-modular-contracts-composed-proofs),
the whole-program boundary in [ARCHITECTURE](ARCHITECTURE.md#21-platform-neutral-whole-program-boundary),
the universal anti-facade laws in [REVIEW](REVIEW.md), and the burden-delta discipline in
[Practical proof tactics](PROOF_TACTICS.md#eliminate-the-burden-delta). Where those documents describe
an old spike as an exemplar, the clean-slate rebuild and measured cutover supersede the exemplar,
not the underlying soundness law.
