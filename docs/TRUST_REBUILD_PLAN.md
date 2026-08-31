# Trust proof rebuild plan

**Status:** proposed architecture and active execution plan. MP owns design refinement; Reviewer
owns execution-plan falsification. Neither review blocks isolated experimentation, but no rebuilt
spike becomes canonical until both applicable findings are closed.

This plan replaces the existing spike proof architecture. It does not refactor, migrate, wrap, or
generalize the old `Equivalence.lean` chains. Git history preserves those chains as requirements,
counterexamples, and spare parts.

## 1. Outcome and quantitative target

Rebuild Spikes 1 through 5 so authors begin with an independent specification and typed abstract
program, while proof-producing lowering derives the instructions, artifacts, and certificates
consumed by the sole universal `Gasm.Core.Platform.VerifiedProgram`. Program authors supply a small
source-level refinement delta, not an instruction trace proof.

The fallback assembly-authoring design target is:

> **At most 10 lines of program-specific proof burden per authored line of assembly.**

For a four-statement artifact, forty substantive proof lines is the design trigger. Going over it
requires architecture review and usually more library work; it is not a soundness rejection gate
and never licenses a weaker property, smaller input domain, or missing authority proof. Being under
budget is likewise not evidence of soundness. Complexity-aware review distinguishes straight-line
NOPs, read-modify-write memory operations, syscalls, bounded loops, and reactive handlers rather
than treating them as interchangeable proof units.

### 1.1 Burden heuristic

The 10:1 figure is deliberately a rough human review heuristic, not a machine metric, proof-budget
field, CI gate, integration condition, or accounting system. When useful, report an approximate
local ratio for a hand-authored assembly leaf and identify obviously relocated shared burden. Do not
build token/AST counters, manifests, charging/amortization machinery, or semantic-operation
accounting solely for this heuristic. Ordinary source-directed authoring has no assembly-ratio gate.

An unexpectedly large proof remains an important architectural signal: reviewers should look for a
missing composition theorem, overly concrete boundary, repeated transport, or misplaced authority.
They may also record elaboration time and memory already available from normal builds. None of these
observations blocks an otherwise sound proof or permits weakening soundness, applicability,
universality, authority, lifecycle, cleanup, or claimed behavior.

The initial ratio measures the fallback assembly-authoring boundary. The end-state source path
should require no instruction-level proof from an ordinary program author: instruction evidence is
derived by the selected lowering implementation. Universal inputs, exact artifact identity,
production execution, outcomes, frames, authority, lifecycle, and cleanup remain mandatory even
when the budget is missed.

Large-program development is deliberately iterative rather than a one-way compiler handoff:

```text
spec₀ → asm₀ → revised intermediate spec₁ → asm₁ → spec₂ → asm₂ → ...
```

Top-down lowering gets a complete first implementation. Bottom-up inspection of the generated
assembly then exposes missed abstractions, bad representations, unnecessary generality, poor block
boundaries, or performance contracts that the current source layer cannot express. The next round
revises the typed intermediate specification and proof architecture, then regenerates code. This
dance repeats until semantics, proof burden, and generated code quality converge.

## 2. Replacement proof architecture — MP review surface

The required authoring and dependency direction is:

```text
independent logical specification
        ↓
typed abstract blocks → explicit selected lowering dictionaries → certified target blocks/CFG
        ↓                                                        ↓
source-to-target refinement                         linker-owned Artifact/Layout/Slot certificate
                                                                 ↓
canonical ∀ env : Environment + platform-owned loader/runtime → ExecutionContext env
                                                                 ↓
target blocks/CFG + exact artifact/index + ExecutionContext env → ClosedExecution env
                                                                 ↓
ClosedExecution env + independent source refinement → Behavior/Admissibility env
                                                                 ↓
bundle the existing Artifact / Provider / Entry / Admissibility / Behavior certificates
                                                                 ↓
VerifiedProgram.compose
```

`VerifiedProgram` is the derived root, never an input to the machinery intended to construct it.
The current post-hoc `VerifiedProgramCFGArtifactCertificate` direction is not the rebuild template.
Likewise, an `instructions → VerifiedProgram` helper is a backend completion theorem, not the public
authoring architecture.

### 2.1 Abstract blocks and implementation selection

- A source block is defined over typeclasses describing the operations and contracts it requires,
  not over one target instruction vocabulary. Examples include word arithmetic, checked memory,
  formatted output, streaming reads, process termination, and calls to typed capabilities.
- An implementation dictionary supplies each required operation together with its refinement,
  effects, clobbers, frame, obligations, failure outcomes, and cost/bound contribution.
- Lowering is staged. One implementation may replace an operation with more abstract typed basic
  blocks; another may close it as a target straight-line instruction run. Both cases return the same
  composable block contract and preserve the source meaning.
- The selected dictionaries are explicit data in the compilation/artifact certificate. Lean
  typeclass search may synthesize a dictionary locally, but global instance search may not silently
  choose the platform, weaken a contract, or become hidden proof authority. The certificate records
  reproducible dictionary, target, profile, and version identities; distinct valid implementations
  remain distinguishable without a global uniqueness premise.
- Recursive lowering carries a checked stage/rank or another structural termination argument. It
  strictly decreases on every abstract-to-abstract step, cannot follow same-rank mutual dictionary
  cycles, and ends in a certified target leaf. This is separate from source-program loops or
  recursion, whose termination/progress is proved with program invariants.
- Direct hand-authored assembly remains a supported leaf/fallback. Its approximate local burden is
  reviewed against the advisory 10:1 smell test, and it produces the same certified
  straight-line-run interface as a compiler-selected leaf.
- The source-to-block and block-to-block lowering theorems compose transitively, so final behavior
  is refinement of the independent source spec rather than a specification reconstructed from the
  emitted instructions.
- Refinement means target observable behaviors are contained in the source contract for the same
  canonical input. Composition preserves values/traces, declared effects and failures, outstanding
  obligations and resource disposition, frames/clobbers, and cost bounds. A lowering may eliminate
  a permitted failure by proof, but may not add an unadvertised failure or effect.
- Source contracts expose source-visible state and effects. Registers, ABI frames, physical
  mappings, clobbers, and descriptor geometry live in lowering/leaf certificates so implementers
  may change algorithms or fuse several source operations. Fusion requires an explicit block-level
  refinement discharging every source demand and obligation; there is no one-operation/one-
  instruction requirement.
- Authority-bearing operations additionally consume target-minted evidence. A caller-constructible
  law dictionary establishes conditional refinement only; it cannot manufacture physical or
  lifecycle authority.

### 2.2 Iterative top-down and bottom-up refinement

The engineering process alternates directions, while the accepted correctness edge remains
specification-to-implementation in every round.

For round `i`:

1. A typed intermediate specification `Sᵢ` refines or implements the stable root behavior `S₀`.
2. The selected lowering generates assembly `Aᵢ` and proves `Aᵢ` implements `Sᵢ`.
3. Inspection, differential execution, cost modeling, and proof-burden measurement of `Aᵢ` produce
   design feedback—not proof authority.
4. A revised intermediate specification `Sᵢ₊₁` captures the better representation, operation,
   block boundary, or performance contract suggested by that feedback.
5. A named refinement/equivalence theorem connects `Sᵢ₊₁` to `Sᵢ` or directly to `S₀`; unchanged
   source/CFG proofs are transported rather than replayed.
6. Lowering regenerates `Aᵢ₊₁` with exact new artifact and execution certificates.

The root functional specification may remain stable while intermediate specifications evolve
aggressively. Performance, resource, layout, and target-specific guarantees may be strengthened in
later layers, but a generated assembly observation may not silently weaken functional behavior,
failure coverage, universal inputs, authority, or cleanup.

Recurring useful assembly motifs should feed bottom-up into new abstract operations only after they
are stated independently and proved as lowering implementations. A motif is not promoted merely
because one emitted artifact contains it. Differential replacement theorems should make one leaf or
block replaceable while retaining unaffected source, CFG, authority, and outcome proofs.

### 2.3 Library ownership

- **Source/abstract-block libraries** own typed operation contracts, source semantics, control-flow
  topology, and source-level composition independently of target layout.
- **Implementation/lowering libraries** own total source-operation refinement into another abstract
  block layer or a certified target straight-line run. Rebuilt spikes select implementations and
  prove only source-specific invariants or stronger advertised guarantees.
- **Instruction families** own architectural descriptors, codec/decoder routing, operational step,
  faults, exact access descriptions, and frame laws. Programs do not re-prove these for concrete
  operands.
- **Proof-carrying block/CFG libraries** own sequential composition, exact middle-state transfer,
  event accumulation, branches, calls, selected loops, and typed terminal transitions.
- **Linkers** return artifact identity, layout/index resolution, symbol/import/export identity, and
  slot certificates. They do not own semantic provider behavior.
- **Platforms** own loader relations, runtime/provider realization of linker slots, fault delivery,
  external-input framing, admissible outcome classification, and profile-specific physical grants.
- **Specifications remain independent.** A platform adapter accepts an externally authored spec and
  an explicit execution-to-spec refinement theorem. It may not define `spec` from `run`, a closed
  outcome, emitted bytes, or an evaluator.
- **Applicability remains selected.** Checked memory, input, resource, reactive, concurrency, and
  cleanup obligations arise only from reachable selected features. No catch-all typeclass or empty
  decorative evidence is permitted.

### 2.4 Small execution identity and named profile bridges

Keep a small indexed core for exact artifact/context/execution identity. Connect only selected
host, ghost, memory, resource, loader, and runtime facts through narrow named indexed bridges.
Burden heuristics and governance metadata never participate in semantic equality or the TCB.
The environment remains universally quantified (`∀ env : Environment`) or an explicitly justified
environment family; an outcome adapter may not choose the acceptable environment or result.
Consumers must not reconstruct extensionally equal copies and then spend their proof on transport.

The first accepted lower-layer candidate is `Gasm.Targets.X86_64.ClosedExecution`, which packages an
exact selected non-input production prefix and typed process-exit step. It is a narrow lower-layer
combinator, not a universal execution object, and deliberately supplies no behavioral specification.

### 2.5 Applicability and checked-access authority

- Applicability is mechanically derived from reachable operations in the admitted program and
  canonical environment family, never asserted by a caller annotation. Generic descriptor coverage
  is conditional evidence only and is never authority.
- Descriptor occurrences are indexed by program position (`Fin` or an equivalent dependent index).
  Access kind, width, address/range, and non-wrapping facts are derived from the exact production
  descriptor and pre-state, with production codec/decoder linkage and real `ReadsWithin` /
  `WritesWithin` obligations. Unselected forms contribute zero evidence.
- The sealed target/profile adapter alone combines live generation/binding with target-owned host,
  mapping, and physical grants. Generic x86 signatures and caller-supplied host/mapping/binding
  premises cannot discharge admission.
- The current `MemRef` is provisional: it does not yet faithfully exclude invalid scale/index
  states or resolve no-base SIB/absolute ambiguity, segments, address-size behavior, and atomicity.
  Abstract checked-memory contracts must not freeze this representation or expose Windows mapping
  and binding details.
- Hardware-memory validation remains disabled until typed vectors carry a rebased scratch-memory
  preimage and compare the observed postimage and exact footprint.

### 2.6 Clean-slate consumers

New work is authored in fresh namespaces:

```text
Spikes/Rebuilt/Spike1Hello/
Spikes/Rebuilt/Spike2Fibonacci/
Spikes/Rebuilt/Spike3SortLines/
Spikes/Rebuilt/Spike4HttpServer/
Spikes/Rebuilt/Spike5Gzip/
```

`Spikes/Rebuilt/CheckedMemoryWindows/` is a temporary template/pathfinder, not a sixth product spike.

Rebuilt consumers state their specification and abstract program before selecting target
implementations. Rebuilt proof modules import stable `Gasm`/`Stdlib` libraries, not old spike proof
modules, directly or transitively; production certificates may not import test modules. A temporary
copied definition or dependency on an old source/spec is recorded in an explicit cutover-debt list
and removed before acceptance. Search evidence must establish one emitter and one admission
authority before cutover. There are no compatibility aliases, dual verified emitters, or parallel
proof authorities.

### 2.7 Soundness rejection rules

Reject a candidate immediately if it uses or enables:

- `spec := run`, `spec := execution.outcome`, or any equivalent self-selected meaning;
- a narrowed caller-selected input domain in place of canonical `Environment` quantification;
- a detached evaluator, instruction list, artifact, provider map, or host state;
- `sorry`, new axioms, `native_decide`, allowlists, or computational grandfathering;
- total memory as evidence of mapping/writability;
- generic ghost ownership as physical or lifecycle authority;
- caller-forgeable provider, discharge, cleanup, or terminal evidence;
- a public authoring API whose primary input is an already emitted instruction list rather than an
  independent spec/abstract program, except for the explicit hand-assembly fallback;
- a typeclass instance that silently selects target semantics, invents authority, or lowers an
  operation without a named refinement theorem;
- an assembly-derived intermediate specification that weakens or replaces the stable root behavior
  without a checked refinement/equivalence theorem.

## 3. Execution plan — Reviewer review surface

### Phase A — establish the template through a non-circular DAG

The dependency order is mandatory:

```text
accepted backend leaf
    ↓
checked-access authority + abstract-block/dictionary/lowering interfaces
    ↓
clean checked-memory pathfinder + independent review
    ↓
clean Spike 1 as a materially different second consumer + independent review
    ↓
template declaration
    ↓
Spike 1 cutover, then Spike 2 target lowering/integration
```

1. Use the independently accepted exact closed-execution combinator and Windows adapter as backend
   leaves; neither defines the public authoring interface.
2. Define the smallest typed abstract-block interface and explicit implementation dictionary needed
   by the four-statement pathfinder. Its selected Windows implementation must produce the accepted
   closed-execution leaf; the author starts from the logical block, not its instruction list.
3. Before pathfinder implementation, accept a checked-access contract that requires:
   - descriptor occurrences indexed by exact program position;
   - address, range, kind, width, and non-wrapping derived from the production descriptor/pre-state;
   - generic coverage treated as conditional evidence, explicitly not authority;
   - live generation/binding plus target/profile-owned host, mapping, and physical realization;
   - one sealed target admission adapter, with no generic host/mapping/binding premise;
   - an abstract contract independent of the provisional current `MemRef` representation; and
   - no hardware-memory claim without rebased scratch preimage, observed postimage, and exact
     footprint.
4. Build target-owned Windows non-input adapters that:
   - derive provider linkage from the linker;
   - use the standard target-owned runtime/capability realization;
   - centralize external-input framing;
   - accept an independent specification and refinement theorem.
5. Build `Spikes/Rebuilt/CheckedMemoryWindows` from blank and review its soundness, proof economy,
   imports, and authority provenance.
6. Build Spike 1 once as the materially different second consumer and review it before declaring the
   shared interface a template. This is the Phase B rebuild increment, not a separate prior Spike 1.
7. Perform one measured feedback round: inspect the first generated pathfinder/Spike 1 assembly,
   improve one intermediate abstraction or lowering boundary, regenerate it, and demonstrate that
   unaffected proofs transport rather than being rewritten.
8. Declare the template only after MP and Reviewer accept both consumers and all shared-library
   identities. Until then, Spike 2 may develop only its independent spec/source and separately owned
   pure libraries; its target lowering cannot define a competing interface or integrate.

### Phase B — rebuild and then cut over Spike 1

Reauthor the simple platform artifacts first. Required libraries are a target-neutral output/exit
abstract block, target implementations that lower it to certified straight-line runs,
straight-line/terminal composition, linker certificates, standard provider/runtime adapters, and
independent trace/outcome refinement. The local proof should state the intended output and terminal
result, then select implementations.

### Phase C — rebuild Spike 2

Define Fibonacci as typed abstract loop blocks over formatting/output/exit operations. Build one
parameterized source-level row certificate and structural bounded iterator. Formatting and output
implementations lower into more abstract blocks or certified target runs. Reuse decimal schedule,
frame, recurrence, event, and typed exit libraries at their owning lowering stages; do not preserve
the old per-row proof forest. Linux is the first acceptance target, followed by Windows and Wasm
through the same logical iteration theorem and target-specific implementation dictionaries.

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

For each spike, prepare one recoverable deletion/promotion candidate commit:

1. Independently review the rebuilt tree and burden measurement.
2. Delete the old spike directory and its obsolete targets/controls.
3. Promote the rebuilt tree to the canonical path/namespace.
4. Update umbrella imports, Lake targets, emitters, tests, docs, and citations.
5. Prove with repository search that no old proof authority, compatibility alias, or forbidden
   tactic remains.
6. Run focused builds first, then the coordinated full trust gates.

The candidate remains unintegrated and unpushed until independent review, the forbidden-authority
and transitive-import searches, focused builds, and full trust gates all pass. Only `Trust repair`
may then integrate and push it.

## 4. Worker and integration protocol

- Workers receive non-overlapping spike/library ownership and work from current `origin/main`.
- Commits are dependency ordered: shared mechanism, clean-slate consumer increment, deletion/cutover.
- Every handoff names exact parent/hash, semantic claim, files, old burden removed, focused commands,
  forbidden-token scan, `git diff --check`, resource observations, and known unrelated failures.
- Optimization rounds additionally report the stable root spec, old/new intermediate spec, checked
  refinement edge, assembly/cost delta, proof-burden delta, and which proofs were transported
  unchanged.
- MP reviews architecture/soundness; Reviewer falsifies execution, proof economy, and acceptance
  evidence. A soundness finding vetoes integration regardless of schedule.
- `Trust repair` alone integrates reviewed commits into the clean main staging worktree and pushes.
- Workers may continue on isolated follow-up commits while reviews run, but blocked commits cannot be
  used as templates or cut over.
- Rebuild is the verb at every scale: begin from the required semantics and current accepted
  boundaries, construct a clean replacement top down, and mine earlier code only as reviewed spare
  parts. No worker is required to preserve an old module boundary, proof shape, intermediate
  representation, or generated program merely because it already exists.

## 5. Accountability ledger

| Slice / shared API | Owner | Accepted base / state | Integration condition |
|---|---|---|---|
| Exact x86 closed execution | trustrebuild1 | Canonical `ae22a008` | Backend leaf only |
| Windows certificate adapter | trustrebuild1 | Canonical `4574db1b` | Backend leaf; independent consumer refinement still required |
| Abstract block, dictionary, lowering identity | trustplan design; trustrebuild1 implementation | Design under MP/Reviewer amendment | Exact reviewed interface hash before any consumer integration |
| Checked-access authority/admission API | trustplan design; trustrebuild1 implementation | Not started on canonical `4574db1b` | Phase A authority checklist and MP acceptance |
| Output/exit abstract contract and Windows lowering | trustrebuild1 | Not started on canonical `4574db1b` | Pathfinder review, then materially different Spike 1 use |
| Clean checked-memory pathfinder | trustrebuild1 | Not started on canonical `4574db1b` | Soundness review; target ratio is advisory only |
| Clean Spike 1 | trustrebuild1 | Not started on canonical `4574db1b` | Second-consumer review, template declaration, recoverable cutover candidate |
| Fibonacci independent spec/source/iterator | trustrebuild2 | Active commit `84a52476`, parent `2f359da5` | May proceed independently; no competing lowering API |
| Spike 2 target formatting/output/exit lowering | Unassigned pending template | Gated | Accepted template hash; no old proof imports |
| Clean Spikes 3–5 | Unassigned | Frozen pending workers/template | Explicit assignment and prerequisite library brief |

## 6. Governing references

This plan executes the composition direction in [VISION](VISION.md#4-tractability-modular-contracts-composed-proofs),
the whole-program boundary in [ARCHITECTURE](ARCHITECTURE.md#21-platform-neutral-whole-program-boundary),
the universal anti-facade laws in [REVIEW](REVIEW.md), and the burden-delta discipline in
[Practical proof tactics](PROOF_TACTICS.md#eliminate-the-burden-delta). Where those documents describe
an old spike as an exemplar, the clean-slate rebuild and measured cutover supersede the exemplar,
not the underlying soundness law.
