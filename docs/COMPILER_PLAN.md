# Compiler and Macro-Assembler Plan

**Status:** living compiler-track plan. Update it whenever priorities, accepted evidence, or
architectural constraints change.

## Mission

Make ordinary Lean code insertable into Gasm programs while preserving Gasm's main advantage:
developers can freely choose generated code, reusable proved macros, or handwritten assembly at
each boundary. The compiler should generate the bulk surrounding performance-critical assembly;
it must not become a second proof, artifact, or emission authority.

The north star is a relatively performant, increasingly general Lean compiler whose selected
lowerings are kernel-connected to the named Lean declarations they implement. Generated baselines
must remain replaceable by deeply optimized handwritten target code through property-relative
proof transport.

## Non-negotiable completion gate

Every compiler mechanism advertised as delivered must be exercised by a runnable spike that:

1. starts from a named Lean declaration or an explicitly typed macro source;
2. retains exact source-to-IR, IR-to-instruction, and instruction-to-byte evidence;
3. connects the selected instructions to production target execution and the final artifact;
4. proves applicable entry, exit, frame, control-flow, exceptional, and host-boundary obligations;
5. constructs the sole platform `VerifiedProgram`; and
6. emits only through `emitVerifiedProgram`.

Local certificates and differential deltas are reusable premises, never authorities. A focused
build without this spike is development evidence, not feature completion.

## Delivered on main

| Capability | Evidence | Boundary |
|---|---|---|
| Composable x86-64 and AArch64 macro segments | Target-owned constructor classification, local semantics, clobber/frame laws, exact encodings | Local fragments only |
| Tiny Lean word reification | Named four-argument `UInt64` declaration to kernel-checked `Word.Function` | One atom or binary operation |
| Structured Lean reification | Typed lets, word operations, equality/unsigned comparison, Boolean negation, and `ite` | Source semantics only |
| Typed finite CFG authoring | Nominal blocks, recursive declarations, typed JMP/JCC, scoped control points | Structural CFG evidence only |
| Portable straight-line bulk IR | Temporary-safe code for word operations and structural lets | No target allocation or execution |
| AArch64 bounded backend | Seven creation-order temporaries, exact result/frame/clobber/instruction/byte evidence | Local non-calling body |
| AArch64 production prefix bridge | Exact indexed lookup, runtime silence, consumed fuel, and caller continuation | No terminal/admission claim by itself |
| Compiler-bulk Linux AArch64 spike | Named Lean function through compiler and production `exit(42)` ELF | Sole `VerifiedProgram` authority |
| Differential hand optimization | Nineteen-instruction baseline replaced by seven handwritten instructions | Transports only selected X0 functional output; regenerates placement and bytes |
| Microsoft x64 bounded entry backend | Seven creation-order temporaries, exact RAX result/frame/clobber/instruction/byte evidence | Local non-calling process-entry body |
| Compiler-bulk Windows x64 spike | Named Lean function through generated body and handwritten Win64 `ExitProcess(42)` tail | Production outcome, emitted PE, and sole `VerifiedProgram` authority |
| Differential Microsoft x64 hand optimization | Nine-instruction baseline replaced by one handwritten `mov rax, 42` | Transports only selected RAX result and memory frame; regenerates exact implementation, placement, runtime, bytes, and artifact evidence |

Canonical completion of this set is main commit `88edac5`. Commit hashes are provenance, not API
identity; declarations and current docs remain authoritative.

## Active slice: structured branches

The Microsoft x64 differential seam is now delivered: its runnable spike replaces a nine-instruction
generated body with one handwritten `mov rax, 42`, transports only the selected result and memory
frame, and regenerates its exact placement, bytes, runtime and artifact evidence. The next compiler
slice therefore realizes the existing portable `eq`/unsigned-`ult`/`not`/`ite` decision plans.

Selected design:

- stable source and topology identity remains the existing `StructuredCFG.Plan`; exact generated or
  handwritten blocks are a separately replaceable assignment;
- condition preparation begins with target-owned comparison macros whose flag predicates agree
  with the portable Boolean condition and whose frame/clobber claims are law-bearing;
- each branch retains the exact JCC definition, true/false polarity, both exact child definitions,
  layout and relocation, while only the runtime-selected edge activates its world-transfer premise;
- leaves continue to use the accepted bounded straight-line compiler or handwritten segments under
  the same selected logical contract;
- the first target is Microsoft x64; the symbolic source plan remains target-neutral so AArch64 and
  shader backends can reuse it without re-proving source topology;
- no loop, CALL, indirect edge, exception, cancellation, memory representation, or callable ABI
  claim is introduced by this finite acyclic branch slice.

The compiler-local prerequisite chain is now on main. It contains the exact x86 comparison macro
(`cc64f4df`), structured condition lowering (`53436971`), typed condition-block binding
(`f9223e5a`), replaceable generated/handwritten leaf binding (`f2adc350`), and finite compositional
plan assembly (`2bf7c69d`). The final assembler uses stable symbolic node roles as nominal block IDs,
derives implementation freshness from the plan, preserves true/false polarity and exact child
definitions, and finalizes only through the existing `StructuredCFG.Realizes.lower`. Its control
mixes a generated leaf with a one-instruction handwritten replacement under the same exact source
contract.

This chain still does not constitute completed branch compilation. The replacement proof-authoring
template now exists structurally, but TrustRebuild1 has not yet published a runnable all-gates-green
sole-`VerifiedProgram` exemplar or named the branch spike cutover. The next accepted compiler change
must therefore be part of that concrete runnable spike: consume its final `ClosedCFGLayout`, supply
each existing `EmittedBasicBlock.RealizesAt` from exact target prefix/terminator facts, feed the
existing `VerifiedProgramCFGArtifactCertificate`, prove the real observation/outcome, and compose
only the sole platform `VerifiedProgram`. Detached intermediate certificates or another generic
emitted-block prerequisite are explicitly out of scope. Until that spike lands, structured branching
remains active work and is not advertised as a completed compiler feature.

## Subsequent slices

Order may change when a spike exposes a more valuable prerequisite.

1. **Callable wrappers and register allocation.** Add target-owned save/restore or volatile-only
   allocation/spilling, then demonstrate a real callable export. Process-entry evidence must not be
   reused as callable evidence.
2. **Functions and calls.** Add a finite direct-call subset with ABI contexts, return
   continuations, obligation transfer, and closed targets. Exception and cancellation contracts
   are required only when the selected source/target behavior permits those outcomes.
3. **Memory and representations.** Introduce selected arrays, structures, references, and borrowing
   only through the canonical borrowing, binding, and obligation model, never compiler-local
   ownership. Representation, aliasing, bounds, and frame laws apply to the selected form;
   allocation-failure and cleanup obligations apply only to forms that allocate or own lifetime
   resources, not stack/static representations merely because they use memory.
4. **Loops and recursion.** Compile finite recursive graphs using declared nominal scopes; require
   explicit invariants. Ranking/termination evidence applies when finite completion is advertised;
   reactive or intentionally nonterminating loops instead prove their selected safety/progress
   contract. Resource bounds and cancellation are obligations only when selected or advertised.
5. **Broader Lean reification.** Extend the accepted Lean surface only after the source IR and every
   selected backend have honest semantics. Unsupported helpers remain rejected rather than broadly
   normalized.
6. **More targets and shader frontends.** Add SysV x86-64, broader AArch64 profiles, and SPIR-V as
   first-class target ISAs through target-owned instruction, layout, execution, and final-artifact
   connections. Selected shader source/micro-languages such as WGSL subsets are frontends;
   Vulkan/WebGPU are platform/API profiles whose synchronization and resource proofs remain
   separate from the target instruction proof.
7. **Optimization infrastructure.** Add liveness, register reuse, spilling, scheduling, instruction
   selection, and block replacement as property-relative certified deltas. Functional refinement
   alone never transports timing, memory ordering, ABI, cancellation, exception, or target-set
   claims.

All later proof obligations are feature-selected, not generic taxes. Unselected effects, outcomes,
resources, and performance properties impose no per-program premise merely because another source
or target feature could select them.

## Handwritten assembly is a first-class path

Source role, logical contract, and symbolic topology are stable across replacement. Exact selected
implementation identity is scoped to its artifact and certificates and must be regenerated whenever
selection changes. A generated block is a baseline, not a privileged implementation. Replacing it
should retain unchanged source and symbolic-CFG proofs while re-proving only properties observed by
the consumer and regenerating exact code, layout, relocation, and artifact evidence.

Macros remain usable independently of the compiler. Compiler output must have the same target
instruction types as handwritten Gasm code so generated and manual fragments can be composed at
the selected call site.

## Governance and accountability

- The compiler track owns this plan and advertises accepted advancements here and in
  `docs/MACRO_ASSEMBLER.md`; it does not own integration authority.
- MP and the primary design track own cross-cutting architecture and changes to this plan's
  semantic boundaries.
- Reviewer independently falsifies each candidate before integration.
- Trust Repair owns main integration and repository-green verification.
- Speedracer receives reproducible serious latency or memory incidents; proof boundaries are not
  weakened to hide build cost.
- Work from other tracks is accepted only when it directly advances these compiler goals. Useful
  but nonessential infrastructure is recorded for later rather than displacing the active slice.

For every completed slice, update the delivered table, active status, spike evidence, limitations,
review verdict, and canonical main hash. If a design changes, record the reason and the old claim's
new status rather than silently rewriting history.
