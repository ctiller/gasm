# Rebuilt Spike 1: first relational experiment

Status: isolated exact-artifact experiment; not shared machinery and not a canonical
`VerifiedProgram`. Emission is available only through the stronger private certificate.

## What is kernel checked

`Spec.lean` defines the precious target-independent root as `writeAll message orFatal`. A successful
terminal observation contains the complete message. Missing stdout is fatal before any byte is
committed. A provider write failure is fatal after an exact prefix. Short and zero writes are not
source outcomes.

`RelationalExperiment.lean` defines a nondeterministic lowering transition relation. Every finite
prefix preserves the source split `committed ++ remaining = message`; every reached terminal state
is accepted by the root; an accepted count larger than the requested range cannot construct a
transition. These are unconditional safety results. Provider-labelled executions retain the exact
response trace. Separate theorems prove both coverage for each eligible finite plan and universal
termination of every execution consuming that exact plan. Eligible successful writes are positive
and bounded, or the plan ends in failure. A negative control proves an acquisition-only response
cannot be ignored or reselected into a terminal path. Thus zero-write livelock remains safe but does
not satisfy the conditional progress premise.

`Windows/Program.lean` is the selected clean-slate assembly realization. It checks null and
`INVALID_HANDLE_VALUE` from `GetStdHandle`, checks `WriteFile` failure, loads and bounds-checks the
accepted count, advances by exactly that count, retries short and zero writes, and exits through the
selected success or fatal continuation. Its first provider profile is explicitly limited to a live,
writable synchronous stdout handle. An overlapped/asynchronous handle is ineligible; in particular,
`ERROR_IO_PENDING` may not be classified as source `writeFailure`.

`Windows/RelationalExecution.lean` fixes the linked instruction index and PE load state. Ordinary
steps use production x86 semantics. Provider steps include the exact call occurrence, ABI argument
and output slots, selected synchronous profile, actual memory bytes, returned count, emitted bytes,
and source ghost-state transition as one relation. Universal preservation and terminal-refinement
theorems quantify over every execution admitted by that relation.

`Windows/Witnesses.lean` connects closed traces through the exact artifact: complete output and
successful exit, missing stdout and fatal exit, synchronous write failure and fatal exit, and both
positive-short and zero writes returning to the WriteFile site with the correct residual slice.
`Windows/Certificate.lean` is the sole
private emission authority and requires the exact artifact, universal safety, universal terminal
refinement, source conditional progress, and those exact reachability witnesses.

## Falsifiers

The proposed seam is rejected if any later connection proof admits one of these cases:

- terminal success before `remaining = []`;
- missing stdout after a committed byte;
- `WriteFile` failure without preserving the exact committed prefix;
- provider acceptance greater than the requested byte count;
- an oversized-success provider fault laundered through the common fatal machine label into an
  accepted source write failure;
- a returned count, output-memory update, and emitted-prefix occurrence that disagree;
- a provider effect without the exact labelled boundary occurrence;
- a safety theorem that assumes positive provider progress;
- a termination theorem that omits its progress premise;
- a response plan that an execution can ignore or reselect;
- an asynchronous pending result classified as a synchronous write failure;
- an infinite zero-response execution classified as unsafe (it is safe but lacks progress);
- a symbolic block proof that is not connected to the exact linked instruction sequence, imports,
  entry point, ABI storage, memory image, and emitted artifact;
- a deterministic test interceptor presented as universal provider behavior;
- emission that bypasses either the canonical strengthened `VerifiedProgram` or this experiment's
  stronger private exact-artifact certificate.

## Burden measurement

The selected symbolic program has 29 machine instructions. Across the source relation, exact
x86/Win64 relation, concrete witnesses, certificate, and three small artifact facts there are 709
nonblank theorem-region physical lines: 24.4 proof lines per assembly instruction. The exact count is
a deliberately conservative smell test (it includes reusable relational framework proofs and
statement lines), but it misses the 10:1 target by more than twofold. Therefore this round is not a
successful proof-authoring architecture and must be rebuilt again before Spike 1 is called complete.
The dominant residual is repetitive closed-trace construction in `Windows/Witnesses.lean`; the next
round must replace it with a checked trace/plan derivation whose generic soundness theorem produces
the exact execution evidence. No shared machinery is proposed or extracted without Craig's explicit
approval.

## Review gate and next seam

MP must now review whether the exact relation and private certificate are strong enough, and whether
the proposed next rebuild seam—a checked provider-plan derivation with a generic soundness theorem—is
the correct abstraction. Existing deterministic runtime execution remains only a diagnostic. No
public record shape, shared proof machinery, or compatibility cutover occurs without Craig's explicit
approval.
