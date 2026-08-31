# Spike 1 rebuild seam

**Status:** owner-approval proposal. This document authorizes no shared/public Lean machinery. It
identifies the semantic seam required by the Spike 1 root selected on 2026-08-31 and the disposable
surface that must be rebuilt to realize it honestly.

## 1. Finding

The current native authority is deterministic in the wrong place:

- `Platform.run` returns one `Observation`;
- `ExternalCallInterceptor.interceptCall` returns at most one successor and event;
- the standard Windows hooks make `GetStdHandle` and `WriteFile` succeed unconditionally; and
- the existing Spike 1 performs one unchecked `WriteFile` and exits successfully.

That shape cannot prove the selected root. Real provider calls have result-indexed alternatives:
stdout may be absent, a write may accept a strict prefix, and a write may fail after earlier bytes
were committed. Adding a Spike-local outcome list, caller assertion, mock platform, or untyped field
to `Environment` would move the mismatch rather than fix it.

The correct seam is a relational target execution whose provider leaves refine typed owner
operations. Deterministic evaluators remain useful derived runners for closed profiles and tests;
they are not the universal behavior authority.

## 2. Preserved owners

The rebuild preserves these meanings, not current datatypes:

- Spike 1 root: full text before ordinary exit; every short write retries; missing stdout or an
  actual write failure is fatal; fatal write failure retains the exact committed prefix; missing
  stdout commits nothing.
- Console/provider owner: acquisition, write acceptance/failure, exact committed bytes and progress
  premises.
- Process owner: ordinary versus nonzero fatal terminal outcomes.
- ISA, memory, target and ABI owners: exact executed actions, architectural definedness, memory
  access, call transport, result decoding and live physical bindings.
- Artifact owner: exact instructions, bytes, imports, relocations and selected provider identity.

No result transcript, artifact fact or successful test mints source authority.

## 3. Source operation and continuation contract

The ergonomic source boundary is an abstract operation with a typed fatal continuation:

```text
writeAll text onFatal
```

`writeAll`, not Windows `WriteFile`, promises to absorb every short or zero write. `onFatal` is a
target-independent function/abstract block receiving the error and exact committed-prefix evidence;
its result type is terminal, so it cannot accidentally return into the success continuation. A
convenience surface may spell the common policy as `writeAll text orFatal`.

Conceptually:

```text
OutputFailure text =
  { error, committed, proof committed.IsPrefix text }

writeAll
  (text : Bytes)
  (onFatal : OutputFailure text -> Program Terminal)
  : Program Unit
```

The next lowering rung turns the success and fatal continuations into typed abstract basic blocks.
Only the selected Windows realization turns those into concrete target blocks. Spike 1 lowers this
result-indexed operation tree:

```text
acquireStdout
  absent(error)       -> fatalExit(error, committed = empty)
  acquired(handle)    -> writeAll(handle, message, committed = empty)

writeAll(handle, remaining, committed)
  accepted(n), n <= remaining.length
    n < remaining.length -> writeAll(handle, drop n remaining, committed ++ take n remaining)
    n = remaining.length -> successExit(committed ++ remaining)
  failed(error)       -> fatalExit(error, committed)
```

Zero acceptance is nonfatal. A termination/liveness claim therefore additionally names a provider
progress premise: while a write remains pending, the provider eventually accepts a positive prefix
or returns a fatal result. Safety—the prohibition on successful early exit—does not depend on that
premise.

The specification owns the split invariant
`committed ++ remaining = message`. The lowering consumes it; it does not replay string correctness
at instruction level.

## 4. Provider boundary

Each selected provider exposes an owner-defined sealed result family. For the first Windows profile:

- stdout acquisition returns `acquired(handle, generation, rights)` or `absent(error)`;
- write returns `accepted(n)` with `n <= requested`, or `failed(error)`;
- accepted bytes are exactly the requested prefix of length `n`;
- the returned count, success flag and target state agree with the ABI-visible result;
- handle generation, buffer authority and count-output memory remain target/provider obligations;
  and
- the provider states its conditional progress class separately from safety.

The common lowering core sees only the operation, its sealed result, exact occurrence and the
directional realization theorem. It does not define a universal provider-result enum.

## 5. Stronger relational `VerifiedProgram` authority

Moving from one deterministic evaluator result to relational execution must strengthen the final
gate, not replace equality by a permissive predicate. An empty execution relation, omitted result
branch, post-hoc root substitution or existentially selected convenient execution must be
unrepresentable as verified. Generic machinery cannot prove that an owner authored a meaningful
product specification; that remains an explicit reviewed trust boundary. For Spike 1 the accepted
root constructor is sealed around the exact output/fatal contract, so the implementation cannot
replace it with `fun _ => True`.

The information content is:

```text
RootContract.accepts root environment rootObservation : Prop
Platform.Executes runtime artifact initial execution : Prop
Platform.observation execution : targetObservation
ObservationRefines root targetObservation rootObservation : Prop
```

`RootContract` is an identity-indexed owner package, not a caller-supplied proposition. It carries
the independent source semantics, result/failure/cancellation/terminal distinctions, its applicable
nonvacuity/consistency laws, and the exact observable projection. A `VerifiedProgram` stores the
exact root identity as well as the exact selected artifact/profile.

The universal whole-program proof must establish all of the following:

1. **Exact closure:** artifact bytes/instructions, imports, relocations, providers, target profile,
   entry relation, ABI boundaries, callbacks/handlers and every reachable implementation are one
   sealed selected tree.
2. **Universal quantification:** every canonical environment, every admitted provider/scheduler
   behavior and every target execution from the exact loaded entry are covered. No transcript or
   execution is selected by the proof author after seeing the desired result.
3. **Execution nonvacuity:** for every admitted finite profile situation, at least one target
   execution exists. Reactive/divergent profiles instead provide the exact coinductive existence
   statement. False/empty `Executes` cannot prove a program.
4. **Provider completeness:** the selected provider realization proves that its target transition
   relation includes every result permitted by the pinned provider contract, including failure,
   short acceptance and zero acceptance. A deterministic-success subset is not an admitted provider
   realization.
5. **Origin and coverage:** every execution step originates in the exact artifact, selected provider,
   platform or admitted environment transition; every result branch, internal helper, cleanup path
   and terminal/fault path has a disposition.
6. **Architectural and policy safety:** every execution satisfies instruction definedness, memory
   safety/authority, selected memory consistency, ABI, provider admission, lifecycle and artifact
   requirements. Root unobservability discharges none of these.
7. **Total outcome classification:** every finite execution is continuing, ordinarily terminal,
   fatally terminal or explicitly stuck/faulted according to an owner-defined result. Fuel
   exhaustion, unclassified faults and missing branches are rejected rather than erased by an
   observable projection.
8. **Backward soundness:** every target execution refines some exact root observation accepted by
   the stored root contract, preserving committed effects and result identity.
9. **Required-behavior realization:** under the root's named implementability premises and the
   selected provider/profile, every root-required behavior class has the stated target witness. This
   is separate from backward soundness and does not claim completeness over arbitrary source
   overapproximation.
10. **Progress separation:** termination, reactive progress, fairness and bounded latency are proved
    only under their exact eligibility/environment premises and cannot be inferred from safety or a
    terminating test.

`Environment` continues to contain logical external inputs; it does not select providers, assert
admission or carry authority. `Executes` owns provider and scheduler nondeterminism. A target may
derive a deterministic runner and prove it sound and complete for one closed transcript/profile,
but that runner is a witness below the universal relation, never the behavior authority.

For a deterministic target, the old equality theorem is recovered as a special case from singleton
execution plus soundness and completeness. The rebuilt gate therefore loses no currently valid
fact and additionally prevents deterministic-success narrowing from hiding real provider branches.

### 5.1 Obligation discharge

The final gate composes certificates; it does not ask each program to replay their proofs.

| Obligation | Discharging owner/construction | Spike 1 residual |
|---|---|---|
| Exact closure | Linker, provider registry, ABI and artifact certificates | Select exact PE/provider/profile |
| Execution existence | Target relation constructors plus provider transition totality | None after selection |
| Provider-result soundness | Windows provider realization, target transition to one typed result | None |
| Provider conditional coverage | Windows provider realization under its exact environment premise | None |
| Instruction/access safety | ISA, memory and ABI libraries over the derived selected tree | Local representation relation only if unavoidable |
| Branch/path coverage | Proof-producing lowering of success, retry and fatal continuations | Supply the two continuations |
| Output split | Source `writeAll` invariant/combinator | Exact message/root mapping |
| Backward soundness | Structural lowering induction over actual states/results | Connect accepted results to sealed root |
| Required behavior | Selected implementation plus provider implementability theorem | Choose claimed behavior class |
| Progress | Separate provider/fairness theorem | Choose whether termination is claimed |

Provider realization has two distinct directions. Mandatory soundness classifies every concrete
target call transition as exactly one typed provider result and proves its source transition.
Conditional coverage says that each result enabled by the pinned provider/environment profile has a
corresponding target transition. It does not require Windows to realize impossible results, and it
does prevent a proof author from narrowing the profile to deterministic success.

## 6. Windows realization

The first artifact must:

1. call `GetStdHandle(STD_OUTPUT_HANDLE)`;
2. branch to a nonzero fatal exit on `NULL` or `INVALID_HANDLE_VALUE`;
3. retain `(pointer, remaining length, committed length)` as the write-loop state;
4. call `WriteFile` for the remaining suffix;
5. branch to fatal exit when its success result is false;
6. load the exact returned byte count and reject a provider result larger than requested;
7. advance pointer/count and retry on every incomplete acceptance, including zero;
8. call `ExitProcess(0)` only when the remaining length is zero; and
9. use a nonzero `ExitProcess` code on fatal branches.

The Windows provider relation connects the Win64 call frame, `BOOL`, count-output memory and handle
result to the sealed source result. It emits only the accepted prefix, not the requested buffer.

## 7. Rebuild radius

The following current shapes are disposable and may need replacement:

- functional `Platform.run` as the behavior authority;
- functional `ExternalCallInterceptor` as the universal host-call semantics;
- equality-only `ProgramBehaviorCertificate.traceEquivalence`;
- admissibility predicates that classify only one evaluator result;
- standard Windows hooks that unconditionally succeed;
- reusable certificates whose indices assume those deterministic functions; and
- every spike proof facade coupled to that authority path.

The current repository has direct `traceEquivalence` consumers in 21 Lean files and direct
`ProgramBehaviorCertificate` consumers in 18. This is a rebuild population, not a compatibility
argument. Development may occur in an isolated experimental namespace, but canonical cutover is
atomic: one `VerifiedProgram` authority remains, all retained consumers are rebuilt, and the old
authority path becomes unreachable.

## 8. Proof-producing lowering target

Program-specific proof should be limited to:

- the selected message/root theorem;
- the source split invariant and result mapping;
- the exact Windows implementation choice; and
- any genuinely local representation relation.

Libraries should derive the loop's instruction execution, branch coverage, pointer/count arithmetic,
frame/clobber facts, ABI result decoding, access descriptors, provider routing and artifact closure.
If the rebuilt Spike 1 is not plausibly near the fallback 10:1 target, perform the single required
ownership/spec/lowering review before proposing further shared machinery.

## 9. Acceptance sequence

1. Craig accepts or changes this seam and its rebuild radius.
2. Build the relational platform/provider experiment and rebuilt Windows Spike 1 in an isolated
   namespace; do not preserve old APIs.
3. Demonstrate positive paths for full and repeated short writes, plus fatal missing-stdout and
   fatal-after-prefix paths.
4. Demonstrate falsifiers: empty execution relation, substituted/overbroad root, existential
   execution selection, omitted provider branch, successful early exit, dropped/duplicated bytes, oversized
   returned count, requested-buffer rather than accepted-prefix event, unclassified fault/fuel, and
   deterministic-success narrowing.
5. Close the exact Windows artifact through the sole experimental universal root and emit/test it on
   this machine.
6. Perform the one proof-burden review. Any additional shared/public machinery returns to Craig.
7. Propose the atomic canonical cutover and full consumer rebuild separately.
