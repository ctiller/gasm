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
transition. These are unconditional safety results. A separate theorem establishes termination only
from a finite progress plan whose successful writes are positive and bounded, or which ends in a
write failure. Thus zero-write livelock does not get mislabeled as safety failure or silently assumed
away.

`Windows/Program.lean` is the selected clean-slate assembly realization. It checks null and
`INVALID_HANDLE_VALUE` from `GetStdHandle`, checks `WriteFile` failure, loads and bounds-checks the
accepted count, advances by exactly that count, retries short and zero writes, and exits through the
selected success or fatal continuation.

## Falsifiers

The proposed seam is rejected if any later connection proof admits one of these cases:

- terminal success before `remaining = []`;
- missing stdout after a committed byte;
- `WriteFile` failure without preserving the exact committed prefix;
- provider acceptance greater than the requested byte count;
- a safety theorem that assumes positive provider progress;
- a termination theorem that omits its progress premise;
- a symbolic block proof that is not connected to the exact linked instruction sequence, imports,
  entry point, ABI storage, memory image, and emitted artifact;
- a deterministic test interceptor presented as universal provider behavior;
- emission through the experimental package before canonical `VerifiedProgram` is strengthened and
  the exact artifact/provider execution relation is discharged.

## Burden measurement

The selected symbolic program has 29 machine instructions. The entire relational experiment is 246
physical lines including license, prose, definitions, provider-plan model, and proofs: 8.5 lines per
assembly instruction. This is an early architecture measurement, not the final proof-burden result,
because the exact x86/Win64/artifact connection remains deliberately unimplemented pending review.
The next measurement must include that connection. If the completed spike exceeds 10:1, the design
must be rebuilt rather than normalized as acceptable overhead.

## Review gate and next seam

The next change should introduce the correct target-owned relational execution seam: a selected
provider relates a boundary call and pre-state to one of its admitted post-states and result classes;
program execution is a relation over the exact artifact; `VerifiedProgram` quantifies over every
admitted execution. Existing deterministic execution remains, at most, a derived diagnostic for a
singleton provider transcript. No public record shape or compatibility cutover should occur until
MP reviews this experiment and Craig approves any machinery that would become shared.
