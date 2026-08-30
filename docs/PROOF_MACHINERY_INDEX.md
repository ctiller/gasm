# Proof machinery index

This index answers a practical question: **what is the shortest already-accepted path from a proof
need to reusable machinery?**  It complements [Practical proof tactics](PROOF_TACTICS.md), which
explains why the patterns work.  Entries here point to checked code, its owning layer, demonstrated
consumers, and the facts that deliberately remain local.

An entry is not permission to force a proof through the nearest abstraction.  Start with the exact
caller-visible theorem, compare it with the reusable result, and keep the semantic delta in the
layer that owns it.  If adapting the library costs as much as proving the local fact, record the
candidate rather than widening the library speculatively.

## Find machinery by proof need

| Proof need | Reusable machinery | Owning layer | Demonstrated use | Deliberate boundary |
|---|---|---|---|---|
| Execute a list of local steps and compose the result | `Gasm.Proof.LocalExecution.runSteps_append` | target-independent list algebra | x86-64 and AArch64 macro assemblers | fetch, faults, fuel, host effects, termination, instruction admission, and artifact identity stay target-owned |
| Lift a one-step frame fact over a list | `runSteps_preserves`, `runSteps_preservesOutside` | target-independent observation algebra | AArch64 memory, SP, flags, fault, termination, and GPR frames; x86-64 composed GPR frames | the target supplies the one-step theorem and clobber classification |
| Compose frame facts without clobber-order obligations | `preserves_comp`, `preservesOutside_comp`, `preservesOutside_comp_append` | target-independent observation algebra | x86-64 segment composition and the shared list-execution consumers | append is only a conservative union representation; uniqueness and order are irrelevant |
| Preserve an x86 64-bit read across a lower, non-wrapping write | `Gasm.Targets.X86_64.X86_64Mem.read64_write_below` | x86-64 memory semantics | Spike 2 decimal authority and Spike 5 native proofs | address arithmetic, write width, nowrap, and strict-below premises remain explicit; this is not a target-independent memory model |
| Show bounded finite exploration contains only normative reachable states | `Gasm.MemoryModel.FiniteSearch.Enumerator.search_sound` | memory-model presentation/search boundary | the checked incomplete-enumerator negative control exercises the one-way guarantee | completeness is separate and may not be inferred from bounded fuel or a finite result |
| Preserve dependent CFG identity through lowering or nominal remapping | `Gasm.Compiler.TypedCFG.ProgramPlan.loweredBlock`, `lower_ref_exact`, and `lowerDefinitions_mapBlockId_block` | compiler CFG authoring/lowering | typed CFG lowering and x86-64 control-point remapping | matching names or entries do not substitute for equality of the complete dependent definition |
| Turn bounded UInt64 decimal progress into a reusable certificate | `Stdlib.Fmt.UInt64DecimalScheduleCertificate` and `Gasm.Targets.X86_64.UInt64DecimalScheduleRealization` | pure formatting schedule, then x86 realization | Spike 2 native decimal loop | the pure layer owns digit/count bounds; the target owns machine effects and the final production connection |

## Proven composition patterns

- For an expensive exact execution proof, keep the complete certificate in its producer and export
  a separate typed boundary containing only the observations required by the successor.  The
  accepted Spike 2 Linux Row 8 proof uses `spike2_row8_selected_prefix` for the exact 64-transition
  execution and `spike2_row8_after_recurrence_boundary` for RIP, recurrence/ABI registers, stack,
  and fault transfer from Row 7 to Row 8.  Exact generator reproduction and output/event facts stay
  with the producer.  Clean builds measured roughly 24--37 seconds for boundary data/opening and
  about 1.6 seconds for final composition.  This is a proven proof-term caching and forward-boundary
  pattern, not yet a target-independent API.

## Admission record

Reusable extraction should leave a short audit trail.  Record:

1. the exact repeated local theorem or proof shape;
2. the lowest layer that owns the common semantics;
3. at least two real consumers, unless Trust explicitly requests the abstraction;
4. the before/after local proof burden;
5. focused build cost and dependency closure;
6. the negative boundary: tempting facts the abstraction does **not** prove; and
7. the canonical commit after independent review.

Two useful precedents are:

- `a7002a5` extracted local list execution and frame composition into
  `Gasm.Proof.LocalExecution`, migrated x86-64 and AArch64, and retained each target's established
  `runLocalSteps` reduction behavior through a small equality proof.
- `a65316a` extracted `X86_64Mem.read64_write_below`, migrated Spike 2 and Spike 5, and removed the
  duplicated local proofs without weakening their arbitrary-width or address-bound premises.

Commit identifiers are provenance, not API names.  Follow the declarations above on current main;
use the commits to inspect the reviewed extraction delta.

## Indexed candidates, not yet reusable machinery

The following code shapes have enough evidence to investigate but are not canonical generic APIs:

- Bidirectional contract derivation for typed CFGs is not yet present.
  `Gasm.Compiler.TypedCFG.SourceScope` permits contracts to be declared before bodies, but the
  author still supplies them;
  `Gasm.Core.CFG.Invariant.alongReachable` checks an invariant over already defined block steps, and
  `Gasm.Targets.X86_64.VerifiedProgramCFG` connects reached blocks to exact emitted realizations.
  A candidate derivation layer would start from a symbolic control-flow skeleton, propagate
  reachable facts forward from the entry, propagate required facts backward from terminal
  postconditions, demand an explicit invariant at every join or cycle, and expose their local
  intersection as each block's implementation obligation.  Failed inclusion at an edge should be
  reported at that edge, not rediscovered during whole-path replay.  Spike 2 Row 8 now demonstrates
  narrow forward fact transfer across one accepted typed boundary, but it does not derive contracts
  from a symbolic graph or propagate requirements backward.  A generic consumer must also add a
  progress measure or runtime-enforced bound: closed-graph typing alone proves neither functional
  correctness nor termination.  Spike 3 should wait for its streaming, relational ghost-state, and
  resource-recovery invariants.
  Keep generic worklist or dataflow iteration separate until the candidates in
  `docs/STDLIB_FACILITIES_PLAN.md` earn promotion; automatic invariant discovery is not implied.
- Bounded byte reads appear in ELF, x86-64, AArch64, PNG, Zlib, and Gzip.  A first cursor slice
  should validate against two consumers with the same offset/progress needs while keeping format
  errors and validation consumer-owned.
- Endian assembly is repeated across those formats, but read/write roundtrip laws should be
  extracted independently of cursor control flow.
- Variable-fuel production-prefix composition exists in x86-64 `EventfulSegment`; it stays
  target-owned until a second accepted consumer demonstrates the same algebra.
- Generic `ByteArray` facts in `Stdlib/Zlib/ByteArrayBridge.lean` are shared by PNG and Zlib but
  should move atomically so the neutral module does not inherit a codec dependency.

Candidate status is intentionally visible: it tells agents where the delta may be removable without
pretending the reusable contract has already been established.
