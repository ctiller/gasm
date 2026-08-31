# Rebuilt Spike 1: first relational experiment

Status: isolated experiment; not shared machinery, not an emission authority, and not a canonical
`VerifiedProgram`.

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
- emission through the experimental package before canonical `VerifiedProgram` is strengthened and
  the exact artifact/provider execution relation is discharged.

## Burden measurement

The selected symbolic program has 29 machine instructions. The first relational file was 246
physical lines including license, prose, definitions, provider-plan model, and proofs: 8.5 lines per
assembly instruction. This unstable physical-line ratio is only a one-round human smell test, never
an authority, denominator, or automated gate. The exact x86/Win64/artifact connection remains
deliberately unimplemented pending review and must be included in the next informal measurement.
Craig decides whether any burden warrants another rebuild; this experiment introduces no machinery
to enforce the ratio.

## Review gate and next seam

The next change should introduce the correct target-owned relational execution seam: a selected
provider profile relates an exact boundary occurrence and pre-state to one of its admitted
post-states and result classes; the initial Windows profile admits only synchronous stdout;
program execution is a relation over the exact artifact; `VerifiedProgram` quantifies over every
admitted execution. Existing deterministic execution remains, at most, a derived diagnostic for a
singleton provider transcript. No public record shape or compatibility cutover should occur until
MP reviews this experiment and Craig approves any machinery that would become shared.
