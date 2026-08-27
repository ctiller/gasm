# 0032. No Third-Party Prose in the Published Tree

## Status

Accepted, 2026-08-27. (PLAN.md D25.)

## Context

The reference-index work ([`0031`](0031-flatten-not-history-scrub.md); D24's
APPROVE-WITH-CHANGES review) had been scoped by the coordinator as an Intel-SDM-specific,
licensing-driven cleanup: migrate the citations that pointed at genuinely
non-redistributable vendored prose, leaving redistributable corpora (W3C specs, RFCs,
CC-BY Microsoft Docs content) in place under `references/` since nothing legally required
their removal. The owner's first statement on the reference index's end state — "once we
have the reference index in place we delete the references/ tree" — was read by the
coordinator as narrower than intended ("delete what has been resolved," not "the directory
ceases to exist"). The owner then corrected that under-reading directly.

## Decision

The owner's own words, in two parts. The original ruling on the reference index's end
state: "once we have the reference index in place we delete the references/ tree." And,
correcting the coordinator's narrower reading of it: "i thought i was clear, but let me
double down: i don't want third party prose in the repo by the time we publish."

## Consequences

Redistributability is irrelevant to this decision — W3C specs, RFCs, and CC-BY Microsoft
Docs content are all licensed to ship, and all leave anyway; being *allowed* to vendor
something was never the reason to vendor it. This retroactively voided a draft Law 4
clause that would have read "where the upstream's license permits redistribution, the
authoritative text SHOULD be vendored as before" — that clause would have written a
standing obligation to re-vendor into the law book on the same day the tree was emptied,
and was deleted rather than adopted. End state: no `REF:` citation resolves to a path
under `references/`; the directory does not exist at publication; `references.json` +
`scripts/check_references.py` are the sole mechanism for referencing external
documentation, uniformly across all corpora. With the prose gone, a `references.json`
registry entry becomes the *only* evidence that a citation is grounded in anything real —
a fabricated URL or hash would be undetectable from inside the repo and would silently
void the grounding claim these citations exist to make, so an honestly-reported unresolved
citation is a success and a plausible fake is the worst available outcome. Three things
must not be conflated, since a gate that confuses them does harm: third-party PROSE
(banned from the tree by this decision); third-party LICENSE TEXT required for compliance,
e.g. `LICENSE`/`NOTICE` (a legal obligation, must still ship); and first-party writing
*about* a third-party spec (permitted — this decision bans vendored prose, not discussion
of external systems).

## Provenance

Owner-stated. Both quotes above are the owner's own words.
