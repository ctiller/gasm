# Stdlib.Http11 — A Proof-Carrying HTTP/1.1 Message Parser and Writer

## 1. Overview & Scope

`Stdlib/Http11/` is a small, total, proof-carrying HTTP/1.1 message library: a structured
request/response type, a byte-string parser (`Except Http11.Error _`), and a canonical byte
writer, together with a machine-checked roundtrip theorem connecting them. It exists to close a
real defect class: `Spikes/Spike4HttpServer`'s per-target assembly lowerings performed ad-hoc,
inline byte comparisons to route requests (a fixed-offset 5-byte immediate compare against
`"/stat"` on Windows/Linux x86_64, a single-byte compare against `'s'` on Wasm), so `GET /static`
matched the `/status` route and returned its 200 response instead of a 404. No parser, no
structured request-target, and no theorem meant that class of bug had no proof obligation to
violate. This library gives request/response parsing a real type and a real theorem so a
transposed offset or a truncated prefix comparison becomes a proof failure, not a silent
misroute.

### 1.1 What This Library Models

Request-line and status-line parsing/writing, header-field parsing/writing, and a
`Content-Length`-declared message body, for the origin-form request-target shape (`"/" path
["?" query]`) and a fixed `HTTP/1.1` version token. `Method` is a closed enumeration of the nine
registered HTTP methods (`GET`, `HEAD`, `POST`, `PUT`, `DELETE`, `CONNECT`, `OPTIONS`, `TRACE`,
`PATCH`) — sufficient for a routing server, and closed so the roundtrip theorem needs no token
grammar for it. Header field names and values are restricted to the `tchar` token grammar and
visible-US-ASCII field-content respectively (§2.4) — a conservative, decidable subset of what
RFC 9112 permits.

### 1.2 Deliberate Omissions

Not modeled, and rejected rather than silently mishandled: `Transfer-Encoding: chunked` (only a
declared `Content-Length` body is supported — a request/response with no body has an implicit
zero-length body, i.e. the writer always emits `Content-Length`, never omits it), HTTP/1.0 and
HTTP/2, absolute-form / authority-form / asterisk-form request-targets (origin-form only),
obs-fold header continuation lines, obs-text (bytes 0x80–0xFF) in field values, and trailers.
Each of these is an explicit parse error (`Http11.Error`, §3.1), never a hang and never a silent
accept — the honest posture for code that parses untrusted network input. This is a real, named
scope limit, not a hidden gap: a future extension that adds any of these needs new grammar and a
re-proof of the roundtrip theorem, not a loosening of an existing check.

## 2. Wire Grammar

### 2.1 Request Line

`method SP request-target SP "HTTP/1.1" CRLF`. `request-target` is origin-form: a non-empty byte
sequence whose first byte is `'/'` and whose every byte is visible US-ASCII (§2.4) — this
excludes the space and CR/LF bytes that would otherwise make the request-line ambiguous to split,
so target validity is exactly what makes splitting the line on single space bytes total and
unambiguous.

### 2.2 Status Line

`"HTTP/1.1" SP status-code SP reason-phrase CRLF`. `status-code` is exactly three decimal digits,
100–599. `reason-phrase` is a (possibly empty) run of visible-US-ASCII-or-space bytes with no
leading/trailing whitespace, same grammar as a header field-value (§2.4).

### 2.3 Header Fields

Zero or more `field-name ":" SP field-value CRLF` lines, each written and parsed independently
(no header-value list folding, no combining of repeated field names), followed by the header
section terminator `CRLF` (the "blank line"). `field-name` is a `tchar` token (§2.4);
`field-value` has no leading/trailing space or horizontal tab and contains no CR or LF byte.

### 2.4 Token And Field-Value Character Classes

`tchar` (used for `Method` names and header field names): `DIGIT`, `ALPHA`, and
`` !#$%&'*+-.^_`|~ ``. Visible US-ASCII (used for the request-target and, together with SP/HTAB,
header field-values): bytes 0x21–0x7E inclusive. Header field-values additionally permit internal
SP (0x20) and HTAB (0x09) bytes, but never as the first or last byte of the value — the same "no
leading/trailing OWS in the canonical form" rule a writer needs to make its output re-parse to
itself.

### 2.5 Message Body And Content-Length

The writer always synthesizes exactly one `Content-Length` header from the structured value's own
`body : ByteArray` field — it is never supplied by the caller as an ordinary header (a structured
`Request`/`Response` value's header list is invariant-checked to contain no `content-length`
header, case-insensitively), so there is exactly one source of truth for body length and no
possibility of a mismatched or duplicated `Content-Length`. The parser reads headers until the
blank line, extracts and removes the (exactly one, required) `content-length` header from the
parsed list to recover the declared length `n`, then requires exactly `n` bytes to remain after
the blank line — not fewer (truncated body), not more (trailing garbage past a declared length is
rejected, not silently accepted as part of the next message).

## 3. Parser Behavior

### 3.1 Error Taxonomy

`Http11.Error` names each rejection reason precisely: `headersNotTerminated` (no `CRLF CRLF` blank
line found — includes a request truncated mid-headers), `malformedRequestLine` /
`malformedStatusLine` (wrong field count when splitting on space), `unknownMethod`,
`invalidTarget`, `unsupportedVersion`, `malformedHeaderLine` (no `": "` separator),
`invalidHeaderName`, `invalidHeaderValue`, `missingContentLength`, `duplicateContentLength`,
`malformedContentLength` (non-digit or empty value), `bodyLengthMismatch` (declared length does
not match the bytes actually remaining), `invalidStatusCode`, `invalidReasonPhrase`. Every
rejection is total and immediate — the parser is built entirely from structurally recursive
functions over `List UInt8` (never `partial def`), so it terminates on every input, well-formed or
adversarial, with no possibility of a hang.

### 3.2 Rejected Input

Concretely, and non-exhaustively: a request line with the wrong number of space-separated fields
(`"GET / HTTP/1.1 extra\r\n..."`, `"GET /\r\n..."`); a method outside the nine registered tokens;
a request-target that is empty, does not start with `/`, or contains a space/CR/LF; any version
token other than the literal `HTTP/1.1`; a header line with no `": "` separator or an empty name;
a header value with leading/trailing whitespace embedded improperly; two headers both named
`content-length` (case-insensitively); a missing `Content-Length` header; a non-numeric or empty
`Content-Length` value; a body shorter or longer than the declared `Content-Length`; input with no
`CRLF CRLF` blank line at all. See `Stdlib/Http11/Test.lean` for a concrete regression vector per
case.

## 4. Writer / Canonical Serialization

`writeRequest` / `writeResponse` produce exactly one canonical byte string per structured value:
start line, each header field in list order as `name ": " value CRLF`, the synthesized
`Content-Length` header, the blank line, then the body bytes verbatim. There is no other
serialization this library ever produces for a given structured value — "canonical" here means
literally deterministic, not merely RFC-conformant.

## 5. Formal Theorems

### 5.1 Write-Then-Parse Roundtrip Theorems

`Stdlib.Http11.request_roundtrip : ∀ (r : Request), parseRequest (writeRequest r) = .ok r` and
the corresponding `response_roundtrip` for `Response`, universally quantified over every
structured value the (proof-carrying) `Request`/`Response` types can express — not a
`native_decide` check over sample literals. This is the honest direction: writing produces
canonical bytes, and parsing recovers exactly the value that produced them.
`write (parse b) = b` is not claimed and is false in general for HTTP (header case, optional
whitespace, and header order all admit multiple byte-strings for one structured value) — see
`docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems` for the same distinction drawn
for the zlib/gzip codecs this library's proof style follows.

### 5.2 Parse-Reencode Stability Theorems

`Stdlib.Http11.request_parse_reencode_stable : ∀ (b : List UInt8) (r₁ r₂ : Request), parseRequest b
= .ok r₁ → parseRequest (writeRequest r₁) = .ok r₂ → r₁ = r₂` (`Roundtrip.lean:342`), and
`response_parse_reencode_stable` (`:480`) with the identical shape. The `b` binder ranges over
*every* byte string, not just ones the writer produces.

**What the `b` binder does and does not carry (corrected 2026-08-28).** This section previously
claimed the theorem "would catch a lossy parser: one that accepts `b`, discards information the
writer cannot reproduce, and so reparses its own canonical rewrite into a different value". That
was wrong on the mechanics. In both theorems `b` and the first hypothesis (`_h1`, underscored in
the source for exactly this reason) are **bound and never used**: the entire proof is
`rw [request_roundtrip r1] at h2; exact Except.ok.inj h2`. No fact about `b` can reach the
conclusion, because the conclusion `r₁ = r₂` mentions only `Request` values.

**Why that is a strength, not a shortfall.** The reason no fact about `b` is needed is that §5.1
already gives something *stronger*: `∀ r : Request, parseRequest (writeRequest r) = .ok r` is an
unconditional inverse law over every inhabitant of the type, which makes the 1.5-roundtrip shape a
corollary rather than an independent obligation. A property one rewrite away from an existing
universal law is a property you already had. The same statement has real force in a **fuzzer**,
which cannot quantify over `Request` and must sample `b` instead; it has little independent force
as a theorem sitting beside §5.1. Both are kept and proved: the property was asked for, and its
being a corollary is information a reader should have rather than something to hide by deleting
the theorem.

**Byte-level losslessness is the wrong standard here, deliberately.** HTTP requires *semantic*
round-tripping, not byte round-tripping, and canonicalization is the parser's job. `Content-Length:
007` and `Content-Length: 7` denote the same message and parse to the same `Request`
(`digitBytesToNat?` accepts leading zeros; `natToDigitBytes` re-emits the minimal form). That is
correct behaviour, not lossiness to be engineered away. What was genuinely missing is that this
canonicalization was *implicit* — discoverable only by reading `Basic.lean` — so it is now pinned
by regression vectors in `Stdlib/Http11/Test.lean` (§3): `007`/`7` parse equal, and
`content-length:`/`Content-Length:` parse equal (the name match is case-insensitive and the header
is writer-synthesized, never carried in `Request.headers`). The boundary vector matters as much as
the two positive ones: an **ordinary** header's name case is *preserved*, not folded, so `host:`
and `Host:` parse to **different** `Request`s. A future "helpful" normalization of ordinary header
names would break `request_roundtrip`, and that vector is what would catch it.

**Non-vacuity floor (unchanged, and correct).** On its own §5.2 would be satisfiable by a parser
that always returns `.error` — the hypothesis `parseRequest b = .ok r₁` would simply never fire.
§5.1 independently forbids that parser, since it requires `writeRequest r` to parse successfully
for every `r`. Both are stated and proved, never one without the other.

## 6. Spike4 Migration

### 6.1 The Routing Defect This Library Makes Unrepresentable

The defect (§1) was a byte-offset assumption baked directly into hand-written assembly with no
structured request-target to check against and no proof that the comparison implemented "does the
target equal `/status`" rather than "do the target's first five bytes equal `/stat`". Routing
through `Stdlib.Http11.parseRequest` and matching on the resulting `Request.target` (a validated,
whole-value comparison, not a fixed-width prefix load) makes the transposed-length/truncated-match
shape of bug impossible to reintroduce at the call site that uses this library: there is no
"compare N bytes at a fixed offset" step left to get wrong, because the target is already a
complete, parsed value by the time routing logic runs.

### 6.2 Migration Status And Remaining Work

**Model layer (done).** `Spikes/Spike4HttpServer/Spec.lean`'s `parseRequestLine` delegates
request-line field-splitting to `Stdlib.Http11.parseRequestLine` (`Stdlib/Http11/Parser.lean`)
rather than re-implementing it via `String.splitOn`. This is the request-*line*-level parser, not
the full `parseRequest`: the full parser additionally requires exactly one `Content-Length` header
and a body of exactly that length, and Spike4's request vectors and its own `formatResponse` wire
format carry neither — `parseRequestLine` only ever needed the first line, so using the full
parser here would reject every request this spike sends for a reason unrelated to routing.
`routeRequest` itself is unchanged (still matches on the resulting `HttpRequest.path : String`);
what moved to the library is exactly the field-splitting step where the original defect's
byte-offset-vs-full-value confusion could occur. This was verified behavior-preserving before
landing — a standalone comparison confirmed the migrated implementation agrees with the prior
hand-rolled one on every existing request vector and every witness path named in §6.1, and
`Spikes/Spike4HttpServer/Equivalence.lean`'s full six-theorem trace-equivalence suite still
verifies unchanged against the migrated model.

**Assembly layer (fixed independently, not via this library).** The per-target lowerings
(`Spikes/Spike4HttpServer/{Windows,Linux,Wasm}/Program.lean`) hand-emit their own instruction
stream with no mechanism today for that code generation to call into a Lean-level parser at proof
time the way `Stdlib/Zlib`'s per-target `Equivalence.lean` files establish trace equivalence
between a spec function and an emitted program — building that bridge for `Http11` remains
comparable in scope to the existing Zlib per-target equivalence proofs (each several hundred to
low-thousands of lines) and is not attempted here. The routing defect itself, however, is already
fixed at the assembly level: a concurrent task (`docs/tasks/N8-spike4-stack-buffer-overflow.md`)
replaced each target's fixed-width prefix compare (`"/stat"` on Windows/Linux, a single `'s'` byte
on WASI) with a full 8-byte `"/status "` comparison, independently of this library, and added its
own regression suite (`Spikes/Spike4HttpServer/Equivalence.lean`'s
`spike4RouteFixedOnAllTargets`, `#guard`-checked against `GET /static`, `GET /search`, and six
other witness paths on Windows, Linux, and WASM). Building the trace/byte equivalence bridge that
would let the assembly be verified *against this library's parser* (rather than merely alongside
an independently-fixed comparison) is the concrete remaining step, tracked as future work at the
same scope as a Zlib-style per-target equivalence proof.
