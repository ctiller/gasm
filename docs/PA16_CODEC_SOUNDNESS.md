# PA16: DEFLATE/ZLIB/GZIP/PNG codec universal roundtrip soundness — decomposition

**Status**: this is a Phase 1 design document (`docs/tasks/PA16-codec-roundtrip-universal-soundness.md`).
No proof code for the decomposition below has landed. One illustrative corollary (§3, item L12) was
mechanically verified in a scratch file against the real `Stdlib.Zlib`/`Stdlib.Png` declarations
during this investigation (`lake env lean`, exit 0) to confirm its proof shape is sound, but it is
**not committed** to the tree — it is reproduced here as evidence, not as landed machinery. Every
sub-lemma named below that is not yet in `Stdlib/Zlib/` or `Stdlib/Png/` is prospective.
`Stdlib/Zlib/Deflate.lean`/`Stdlib/Png/Streaming.lean` were **not** edited by this pass (P0's
`partial def` conversion, §4, remains prospective). This pass did make two small, immediate fixes
while investigating (both cited by full diff below, not asserted): it tightened a vacuity hole in
four of the ten pointwise `_inst` checks (§0.1, §1) in `Stdlib/Zlib/Equivalence.lean` and
`Stdlib/Png/Equivalence.lean`, and recorded a previously-unflagged, currently-zero-coverage
decoder code path in `MODEL_DEBT.md` (new entry B10, §0.2).

**On "narrowing the theorem" — read this before the rest of the document.** An earlier draft of
this investigation's summary could be misread as claiming the roundtrip theorem needs less than
genuine LZ77-match and canonical-Huffman-decode correctness. That is **not** the claim, and it would
be the wrong kind of finding if it were: `Stdlib/Zlib/Deflate.lean:393`'s `compress` is a real LZ77
compressor (32768-byte sliding window, 128-deep match chains, genuine back-references — not a
stored/uncompressed-block stub), and `∀ data, decompress (compress data) = .ok data` genuinely
requires proving LZ77 match/copy and canonical Huffman encode/decode are mutual inverses, over
*all* inputs, with no precondition narrowing that claim. §4's decomposition proves exactly that,
including the fully-worked-out self-overlapping back-reference induction (L4) — the single hardest
piece in the whole document. The only scope-narrowing finding in this document (§2) is about *which
decoder code paths a specific composition exercises* — `decompress`'s dynamic-Huffman table
construction is never reached when decoding `compress`'s own output, because `compress` never
writes a dynamic-Huffman block — which is a fact about the target of L7's proof obligation, not a
weakening of it, and it does **not** excuse the decoder's own unverified generality from honest
recording (§0.2, §2.5, `MODEL_DEBT.md` B10).

Covers the 10 entries in this task's scope: `Stdlib/Zlib/Equivalence.lean`'s 8
(`deflate_roundtrip_{empty,soundness,repetitive}_inst`, `zlib_roundtrip_soundness_inst`,
`gzip_roundtrip_soundness_inst`, `{deflate,zlib,gzip}_idempotent_canonical_roundtrip_inst`) and
`Stdlib/Png/Equivalence.lean`'s 2 (`png_roundtrip_soundness_inst`,
`png_idempotent_canonical_roundtrip_inst`). `Spikes/Spike5Gzip/Equivalence.lean`'s near-duplicate
pair is explicitly out of scope for this document (per the assigning task's own scoping) but
§6 notes what transfers to it for free.

Related: `docs/STDLIB_ZLIB.md#62-deflate-zlib-roundtrip-soundness-theorems`,
`docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems`,
`docs/STDLIB_PNG.md#62-canonical-15-roundtrip-soundness-theorem`, `docs/ORACLE_DEBT.md` Part 4,
`docs/tasks/PA16-codec-roundtrip-universal-soundness.md`, `docs/tasks/PA10-png-filter-scanline-invertibility.md`,
`docs/tasks/PA14-crc32-table-identity-structural-closure.md`, `docs/tasks/PA1-crc32-pathfinder.md`,
`MODEL_DEBT.md` §B (new entry B10, decoder-conformance coverage gap — see §0.2 below).

---

## 0. Headline finding

### 0.1 A vacuity hole, found and fixed immediately (not part of the big proof)

Four of the ten entries — `{deflate,zlib,gzip}_idempotent_canonical_roundtrip_inst` and
`png_idempotent_canonical_roundtrip_inst` — had an outer `match ... | Except.error _ => true | ...`
branch (`Stdlib/Zlib/Equivalence.lean:163,175,187`, `Stdlib/Png/Equivalence.lean:428`, before this
pass). Since each checks one fixed, already-known-good literal stream, that branch made the
theorem dischargeable by a `decompress`/`decodeImageRGBA8` that always fails — a regression that
broke decompression entirely would make these four *pass*, not fail, exactly the same class of gate
weakness `docs/tasks/TC17-*.md`'s vacuity floors exist to catch. This is now fixed (`Except.error
_ => false`), verified by `lake build` (§ verification below) to still close via `native_decide`,
confirming today's implementation does genuinely decompress its own test vectors — the four
theorems now actually establish that fact instead of assuming it. This fix is independent of, and
does not require, the universal proof discussed below; see §1 for the per-entry vacuity table and
the diff. The other 6 entries were checked for the same shape and do not have it — see §1.

**This does not extend to the universal target.** The universal 1.5-roundtrip theorems
(`docs/STDLIB_ZLIB.md#63-canonical-15-roundtrip-soundness-theorems`'s own stated form,
`∀ bytes, match decompress bytes with | none => True | some data => ...`) *should* keep `error =>
True` in the outer branch — quantified over literally every `ByteArray`, most of which are not
valid compressed streams at all, requiring `decompress` to succeed on all of them would make the
theorem false. The vacuity problem is specific to pinning that pattern to one hand-picked literal
already known to succeed; §3/L12 states and (as a verified proof shape) discharges the universal
form correctly.

### 0.2 Two distinct theorems, not one — do not let the narrower stand in for the broader

`Deflate.compress`/`compressFixed` never emit a dynamic-Huffman (BTYPE=10) or stored (BTYPE=00)
block (§2) — a real fact about which code paths this project's own compress-then-decompress
composition exercises, established by reading `compress`'s 40-line body, not by the compressor
being trivial (it is a genuine 32768-window, 128-chain LZ77 encoder — see the note at the top of
this document). Two theorems follow from this, and they must be named and tracked separately:

1. **Roundtrip against this codebase's own compressor**: `∀ data, decompress (compress data) =
   .ok data`. This is what closes the 10 entries in scope (§1, §4) and is *not* weakened by the
   above fact — L1 through L6 prove genuine LZ77 back-reference and genuine canonical-Huffman
   decode correctness in full generality, because `decodeHuffmanStream`'s Fixed-Huffman path (which
   `compress`'s output always uses) still has to correctly decode arbitrary LZ77 token streams over
   arbitrary `data`. What the "single block type" fact buys is narrower and honest: `decompress`'s
   *other* two block-type branches (`decodeStoredBlock`, `decodeDynamicTables`) are never invoked
   by this composition, so this proof says nothing about them.
2. **Decoder conformance to RFC 1951**: does `decompress` correctly decode *any* valid DEFLATE
   stream, including ones a different encoder produced with dynamic Huffman tables or stored
   blocks? **Grep-confirmed during this investigation: `decodeDynamicTables` and
   `decodeStoredBlock` are referenced nowhere outside their own definitions in
   `Stdlib/Zlib/Deflate.lean` — no test, no fuzzer, no proof, not even a `native_decide` ground
   check exercises either function.** This is a real, currently totally-unvalidated surface, not a
   consequence of anything this document narrows — it was already true before this investigation
   and remains true after it. Recorded as `MODEL_DEBT.md` new entry B10 (same "unvalidated surface
   is where debt hides" class as B7's Wasm OOB-trap gap) rather than left implicit. **Proving
   theorem 1 (this task's actual scope) provides zero evidence about theorem 2**, and this document
   does not claim otherwise anywhere in §4's decomposition — P0/L1-L11 target theorem 1 only.
   Theorem 2 is out of scope for PA16 as assigned (none of the 10 entries need it) but is
   independently real debt someone should eventually pick up, most likely by differentially fuzzing
   `decompress` against a real zlib/libdeflate or decoding real-world PNGs (which routinely use
   dynamic Huffman), per `MODEL_DEBT.md` B10's forcing function.

### 0.3 The rest of the headline: what actually determines feasibility

Reading the 10 theorems (not their names) collapses the *closure* question (theorem 1 above) into
**4 genuinely distinct universal theorems, one prerequisite engineering task, and one previously-
unflagged hard technical blocker**:

1. **6 of the 10 entries are free corollaries once a general theorem lands** — no new proof content
   at all (§1, §3). `deflate_roundtrip_{empty,repetitive}_inst` are literal instantiations of the
   general `deflate_roundtrip_soundness` claim at two concrete `ByteArray`s; all three
   `*_idempotent_canonical_roundtrip_inst` (Zlib) plus PNG's idempotent entry are one-line
   corollaries of the corresponding `*_roundtrip_soundness` theorem, **regardless of what block
   types or containers the input `bytes` used** — verified as an actual compiling Lean proof
   against the real types (§3). This is unaffected by, and independent of, §0.1's vacuity fix to
   their pointwise instances.
2. The 4 real theorems (`deflate_roundtrip_soundness`, `zlib_roundtrip_soundness`,
   `gzip_roundtrip_soundness`, `png_roundtrip_soundness`, all `∀`-quantified, and all requiring the
   full LZ77+Huffman argument per §0.2) never need `decompress`'s dynamic-Huffman or stored-block
   branches, or multi-block framing, to close — see §0.2 for exactly what that does and does not
   mean.
3. **A previously-unidentified hard blocker, confirmed empirically against the pinned toolchain
   (Lean 4.33.1)**: `decompress`, `decodeHuffmanStream`, `decodeHuffmanSymbol`, `decodeDynamicTables`,
   and `ensureBits` (`Stdlib/Zlib/Deflate.lean`) are all declared `partial def`. In this Lean
   version, `partial def`s compile to **kernel-opaque constants with zero exposed reduction
   behavior** — confirmed directly on the real declarations (§5): `#print ensureBits.loop` prints
   `opaque Stdlib.Zlib.ensureBits.loop : Nat → BitReader → BitReader`, and `unfold` on it fails
   outright. **No structural or inductive proof about these five functions is possible as they are
   currently written** — not "harder than expected," but literally not statable, because there is
   no equation to rewrite with. `Stdlib/Png/Streaming.lean`'s `readPngStream` has the same problem.
   This must be fixed (by converting these to well-founded-recursive `def`s with an explicit
   termination measure) *before* any of Phase 2's proof work can begin, and it is not mentioned in
   `docs/tasks/PA16-codec-roundtrip-universal-soundness.md` or `docs/ORACLE_DEBT.md` Part 4 at all.
   The fix itself is ordinary Lean engineering (confirmed working on a representative example,
   §5) — not new mathematics, not a tooling gap outside the project's control (unlike PA14's
   `bv_decide`-kernel-replay situation) — but it is real, mandatory, and touches
   `Stdlib/Zlib/Deflate.lean`/`Stdlib/Png/Streaming.lean` themselves, not just a new proof file.
4. Given (1)-(3), the genuinely hard, novel mathematical content is concentrated entirely in **one**
   sub-theorem: the LZ77 self-overlapping back-reference copy invariant (§4, L4) — the substance
   §0.2 confirms is genuinely required, not sidestepped. It is provable — this document works the
   induction through by hand in §4 — but it is the one piece that needed a real argument rather than
   bookkeeping, confirming the task's own guess (its author's guess was also "(b)," the LZ77 piece,
   for the same underlying reason: decoder state depends on unbounded history).

**Verdict** (detailed in §7): closing theorem 1 (the 10 entries in scope) is reachable on a bounded
timeline, but only after the `partial def` prerequisite (item 3) is fixed first, and it requires the
genuine LZ77/Huffman argument in full (§0.2), not a narrowed version of it. It is not the multi-week
research-risk item `docs/ORACLE_DEBT.md` Part 4 provisionally classified it as; it is one
nontrivial-but-standard bitstream formalization (§4, L1) plus one genuinely delicate but
fully-worked-out induction (§4, L4) plus a large amount of mechanical bookkeeping that PA10/PA1's
existing techniques cover directly (§6). Theorem 2 (decoder conformance) is separate, unaddressed,
and recorded as debt (§0.2, `MODEL_DEBT.md` B10) rather than left implicit or conflated with theorem 1.

---

## 1. What each of the 10 entries currently proves

Read directly from `Stdlib/Zlib/Equivalence.lean:114-192` and `Stdlib/Png/Equivalence.lean:404-433`
(not inferred from names):

| Entry | Currently proves (via `native_decide`) | Universal version must prove |
|---|---|---|
| `deflate_roundtrip_empty_inst` | `decompress (compress ByteArray.empty)` matches `.ok ByteArray.empty` | Instance of `∀ data, decompress (compress data) = .ok data` at `data = ∅` |
| `deflate_roundtrip_soundness_inst` | Same, for one fixed 42-byte ASCII string | Instance of the same `∀ data` claim |
| `deflate_roundtrip_repetitive_inst` | Same, for one fixed 16-byte repeated-`42` array | Instance of the same `∀ data` claim |
| `zlib_roundtrip_soundness_inst` | `zlibDecompress (zlibCompress data)` matches `.ok data`, one fixed 61-byte string | `∀ data, zlibDecompress (zlibCompress data) = .ok data` |
| `gzip_roundtrip_soundness_inst` | `gzipDecompress (gzipCompress data)` matches `.ok data`, one fixed 61-byte string | `∀ data, gzipDecompress (gzipCompress data) = .ok data` |
| `deflate_idempotent_canonical_roundtrip_inst` | For ONE fixed compressed stream (`compress` of one fixed string): if `decompress` of it succeeds, re-`compress`ing and re-`decompress`ing the result matches | `∀ bytes, match decompress bytes with \| error _ => True \| ok data => decompress (compress data) = ok data` |
| `zlib_idempotent_canonical_roundtrip_inst` | Same pattern, zlib container | `∀ bytes, ...` analogous, zlib |
| `gzip_idempotent_canonical_roundtrip_inst` | Same pattern, gzip container | `∀ bytes, ...` analogous, gzip |
| `png_roundtrip_soundness_inst` | `decodeImageRGBA8 (encodeImageRGBA8 sample2x2Image)` matches the fixed 2×2 RGBA image | `∀ img : ImageRGBA8, decodeImageRGBA8 (encodeImageRGBA8 img) = .ok img` (well-formedness side conditions TBD, see §4 L11) |
| `png_idempotent_canonical_roundtrip_inst` | Same idempotent pattern, one fixed 2×2 image's encoded stream | `∀ bytes, ...` analogous, PNG |

The **idempotent** entries are *not* independently-general claims distinct from the plain roundtrip
claims — see §3.

**Vacuity check, per entry** (§0.1 — every entry in scope was checked for a branch dischargeable by
a failing implementation):

| Entry | Outer failure branch | Vacuous? |
|---|---|---|
| `deflate_roundtrip_{empty,soundness,repetitive}_inst` | `Except.error _ => false` | No — requires actual success + exact equality |
| `zlib_roundtrip_soundness_inst`, `gzip_roundtrip_soundness_inst` | `Except.error _ => false` | No |
| `png_roundtrip_soundness_inst` | `Except.error _ => false` | No |
| `{deflate,zlib,gzip}_idempotent_canonical_roundtrip_inst` | was `Except.error _ => true` | **Yes, before this pass** — fixed to `=> false` (§0.1); `lake build` confirms `native_decide` still closes, i.e. today's implementation genuinely succeeds on these vectors |
| `png_idempotent_canonical_roundtrip_inst` | was `Except.error _ => true` | **Yes, before this pass** — same fix |

---

## 2. What the implementation actually does (read, not assumed)

This matters because it is smaller in scope than the task doc assumed:

- `Deflate.compress` (`Stdlib/Zlib/Deflate.lean:393-433`) writes exactly one block: `BFINAL=1`,
  `BTYPE=01` (3 bits, fixed at the top of the function), an LZ77-tokenized literal/match stream
  encoded via `fixedLitLenTable`/`fixedDistTable` (canonical codes from `buildHuffmanTable`,
  bit-reversed via `reverseBits` for LSB-first packing), an EOB symbol (`reverseBits 0 7`, 7 zero
  bits — hardcoded, not looked up from the table), then `flushBitWriter`. **It never emits BTYPE=00
  or BTYPE=10, and never emits more than one block.**
- `Deflate.compressFixed` (`:437-487`, used only by `Gzip.gzipCompress`) does the *same* thing but
  hand-inlines the RFC 1951 §3.2.6 literal-code bit patterns and length/distance arithmetic directly
  (matching, per its own doc comment, "the assembly machine code engine") instead of consulting
  `fixedLitLenTable`/`fixedDistTable`. It is a second encoder for the identical wire format, not a
  variant format.
- `Deflate.decompress` (`:265-290`) is fully general: it handles all three block types and multiple
  blocks, because it must also decode streams it did not itself produce (any valid DEFLATE stream).
  But **when its input is `compress`'s or `compressFixed`'s own output, its outer `while !isFinal`
  loop runs exactly once and always takes the `btype = 1` branch** (`decodeHuffmanStream ...
  fixedLitLenTable fixedDistTable`). `decodeDynamicTables` (dynamic-Huffman table construction,
  BTYPE=10) and the multi-block case are never exercised by any of the four real theorems in §0 —
  see §3 for why the idempotent theorems don't need them either, despite quantifying over arbitrary
  `bytes`. **This is not the same claim as "the decoder is correct for those cases" — it is
  currently neither proven correct nor known incorrect; it is simply untested and unexercised.
  See §0.2 and `MODEL_DEBT.md` B10.**
- Container wrapping (`Stdlib/Zlib/Gzip.lean`'s `zlibCompress`/`zlibDecompress`,
  `gzipCompress`/`gzipDecompress`) is fixed-layout byte concatenation plus a checksum computed by
  calling the *same* `adler32`/`crc32` function on the *same* recovered data on both the write and
  read side — see §4 L8 for why this makes the checksum-agreement part of container correctness
  free once the DEFLATE-level roundtrip holds (no checksum mathematics needed at all).
- `Stdlib.Png.encodeImageRGBA8`/`decodeImageRGBA8` (`Stdlib/Png/Streaming.lean:229-434`) wrap the
  Zlib container around filtered, chunk-framed scanlines. The per-scanline filter/unfilter step is
  **already proven fully generally** by `Stdlib/Png/Equivalence.lean`'s `filter_unfilter_soundness`
  (PA10, landed 2026-08-27) — see §6.

---

## 3. The idempotent entries are free corollaries — verified, not asserted

For any of the four codecs, once `X_roundtrip_soundness : ∀ data, decompress (compress data) =
.ok data` is proved, the corresponding idempotent theorem needs no reasoning about `decompress`'s
generality over block types, containers, or malformed input at all — it needs one `cases` and one
`exact`:

```lean
-- Verified 2026-08-27 against the real Stdlib.Zlib.decompress/compress signatures
-- (lake env lean, exit 0) — NOT committed to the tree; reproduced here as evidence.
example (deflate_roundtrip_soundness : ∀ data : ByteArray, decompress (compress data) = Except.ok data)
    (bytes : ByteArray) :
    match decompress bytes with
    | Except.error _ => True
    | Except.ok data => decompress (compress data) = Except.ok data := by
  cases h : decompress bytes with
  | error _ => trivial
  | ok data => exact deflate_roundtrip_soundness data
```

The hypothesis on `bytes` (`decompress bytes = .ok data` for *some* `data`, produced by *any* mix of
block types) is never inspected — the proof obligation collapses to `decompress (compress data) =
.ok data`, which is exactly `deflate_roundtrip_soundness` applied at that `data`. The same shape
closes `zlib_idempotent_canonical_roundtrip`, `gzip_idempotent_canonical_roundtrip`, and
`png_idempotent_canonical_roundtrip` from `zlib_roundtrip_soundness`/`gzip_roundtrip_soundness`/
`png_roundtrip_soundness` respectively. Combined with `deflate_roundtrip_{empty,repetitive}_inst`
being direct instantiations of `deflate_roundtrip_soundness` at two literals, **6 of the 10 entries
require zero independent proof effort once the 4 general theorems in the row below exist**:

| General theorem needed (∀-quantified) | Closes directly | Closes as free corollary |
|---|---|---|
| `deflate_roundtrip_soundness` | `deflate_roundtrip_soundness_inst` | `deflate_roundtrip_{empty,repetitive}_inst`, `deflate_idempotent_canonical_roundtrip_inst` |
| `zlib_roundtrip_soundness` | `zlib_roundtrip_soundness_inst` | `zlib_idempotent_canonical_roundtrip_inst` |
| `gzip_roundtrip_soundness` | `gzip_roundtrip_soundness_inst` | `gzip_idempotent_canonical_roundtrip_inst` |
| `png_roundtrip_soundness` | `png_roundtrip_soundness_inst` | `png_idempotent_canonical_roundtrip_inst` |

---

## 4. The decomposition — dependency-ordered propositions

Numbered `P0` (prerequisite, not a theorem) then `L1`–`L13` in landing order. Each depends only on
propositions with a lower number (plus, where noted, an existing theorem already in the tree).

### P0 — De-opacify the decoder (prerequisite; not optional; see §5 for proof)

Convert `ensureBits`, `decodeHuffmanSymbol`, `decodeHuffmanStream`, `decodeDynamicTables`,
`decompress` (`Stdlib/Zlib/Deflate.lean`) and `readPngStream` (`Stdlib/Png/Streaming.lean`) from
`partial def` to `def ... termination_by ... decreasing_by ...` (or an equivalent well-founded
formulation) with an explicit decreasing measure. Per-function measure sketch:

- `ensureBits`: `bytes.size - bytePos` (strictly decreases; loop condition already guarantees
  `bytePos < bytes.size` on each recursive call). **Easiest of the five.**
- `decodeHuffmanSymbol`/`.step`: recursion is *already structural* on the `HuffmanNode` argument
  (`step nextR n` where `n` is a strict child of the current `node`) — likely convertible with no
  measure at all, just dropping `partial`. **Easiest of the five; may not even need
  `termination_by`.**
- `decodeDynamicTables`: `totalLengths + 138 - lengths.size` (generous fixed slack covers the
  largest single repeat-code overshoot, 138 elements from a `sym == 18` run).
- `decodeHuffmanStream`, `decompress`: remaining-bits measure (`8 * (bytes.size - bytePos) -
  bitCount`, or equivalent), relying on every loop iteration that doesn't `throw` consuming at
  least 1 bit (true: every Huffman code has length ≥ 1, and `readBits`/`decodeHuffmanSymbol`
  either consume ≥1 bit or return `.error`, which exits without recursing).
- `readPngStream`: remaining-height measure (`header.height - rowIdx`), same shape as PNG's own
  already-`for`-loop-based `encodeImageRGBA8`.

**Difficulty**: moderate, bounded engineering. No new mathematics — every measure above is a
standard "remaining input" argument for a hand-rolled parser loop, and Lean does generate a real
equation lemma (`.eq_1`, usable by `rw`/`unfold`/`simp`) for a `termination_by`-proved `def`,
confirmed in §5. The risk is entirely in getting `decreasing_by` proofs to go through for the two
`while`-loop cases (`decodeHuffmanStream`, `decompress`), which need a small helper lemma each
("a successful `readBits`/`decodeHuffmanSymbol` call strictly shrinks the remaining-bits measure").
**This is a required edit to `Stdlib/Zlib/Deflate.lean`/`Stdlib/Png/Streaming.lean` themselves**,
not just new proof-file content — flag this to whoever reviews the Phase 2 design, since it changes
the file this task touches beyond `Equivalence.lean`.

### L1 — Bitstream reader/writer roundtrip (RFC 1951 §4.1; `docs/STDLIB_ZLIB.md#41-bitstream-reader-writer`)

No such spec-level lemma exists yet. Needs a new ghost/spec function and two lemmas:

```
def writerBits (w : BitWriter) : List Bool  -- LSB-first bit sequence w has emitted so far
def readerBits (r : BitReader) : List Bool  -- LSB-first bit sequence r has yet to consume

L1a (write-append):  writerBits (writeBits w v n) = writerBits w ++ lsbBits v n
                      -- given w.bitCount + n < 32 (no UInt32 overflow in bitBuf;
                      -- true at every actual call site: bitCount < 8 between calls,
                      -- n ≤ 13 at every writeBits call site in compress/compressFixed)
L1b (read-consume):  (readerBits r).length ≥ n →
                      readBits r n = .ok (r', v)  with  v = lsbVal (readerBits r).take n
                                                   and  readerBits r' = (readerBits r).drop n
L1c (writer↔reader):  readerBits (mkBitReader (flushBitWriter w)) = writerBits w ++ padding
                      -- padding: zero bits added by byte-alignment; never read because
                      -- decoding always stops at the EOB symbol before reaching it
```

**Difficulty**: moderate-high. This is the one place a genuinely new piece of machinery (the
`List Bool` ghost bit-sequence and its algebra) has to be built from nothing — it doesn't exist
anywhere in this codebase today. It is, however, "previously-formalized-elsewhere territory"
(`docs/ORACLE_DEBT.md` Part 4's own framing): every from-scratch DEFLATE/bitstream formalization
needs exactly this, it is standard, and nothing about `BitReader`/`BitWriter`'s definitions
(`Stdlib/Zlib/Deflate.lean:36-119`) is unusual or resists this treatment — `writeBits`'s `flushBytes`
inner loop is itself structurally recursive (decreasing on `cnt`), so P0 does not even apply to it.

### L2 — Fixed-Huffman decode-is-inverse-of-encode, for the two closed tables only

**Key scope point**: `docs/tasks/PA16-codec-roundtrip-universal-soundness.md`'s sub-lemma (a) asks
for Huffman correctness "for any symbol-frequency distribution the encoder can produce." That
generality is not needed here: `compress`/`compressFixed` only ever use the two *fixed, compile-time
closed* tables `fixedLitLenTable`/`fixedDistTable` (`Stdlib/Zlib/Huffman.lean:115-121`) — RFC 1951's
canonical fixed alphabet, never a dynamically-built one. `decodeDynamicTables` (the general,
data-dependent Huffman construction) is never exercised by any of the four real theorems (§2).

```
L2 : ∀ (bits : List Bool) (sym : Nat), sym < 288 →
       fixedLitLenTable.codes[sym]! = some (code, len) →
       (bits.take len corresponds, LSB-first-reversed, to code) →
       decodeHuffmanSymbol (readerFromBits bits) fixedLitLenTable
         = .ok (readerFromBits (bits.drop len), sym)
     -- and the analogous statement for fixedDistTable (32 symbols)
```

Because the domain here is the *fixed alphabet size* (288 + 32 symbols, a closed constant of the
DEFLATE format, not a property of arbitrary input `ByteArray` content), this is a finite/decidable
proposition once `decodeHuffmanSymbol` is de-opacified (P0) — closeable either by a genuine
prefix-tree argument (structural induction on `HuffmanNode` depth, since `decodeHuffmanSymbol.step`
is already structurally recursive per P0) or, for the resynchronization/no-missing-branch part
specifically, by `decide` over the finite, closed `insertCode` construction — the same "closed fact
about a fixed definition" category already used for `crc32Table_size`
(`Stdlib/Zlib/CRC32Equivalence.lean:97-99`), not a Law 9/10 violation since there is no unbounded
`ByteArray` quantification involved.

**Difficulty**: low-moderate. Finite domain, no missing lemma category, directly analogous to
already-solved sub-lemmas in this same file (`encode_length_bounds_inst`,
`encode_distance_bounds_inst`).

### L3 — `findLongestMatch`'s match-validity certificate

```
L3 : ∀ data pos, let (len, dist) := findLongestMatch data pos maxLookback maxTries
     len ≥ 3 →
       1 ≤ dist ∧ dist ≤ pos ∧ dist ≤ maxLookback ∧
       ∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j)
```

`findLongestMatch` (`Stdlib/Zlib/Deflate.lean:363-389`) is *not* `partial` — it terminates via a
`tries < maxTries` counter, so it is not blocked by P0 — but it is a `while`/`return`-shaped loop
(not a `for`-range loop), so it needs its own loop-invariant argument rather than reuse of
`Std.Legacy.Range.forIn_eq_forIn_range'` (which only applies to `for x in [a:b]` loops; this is a
genuinely different bridging lemma from the one PA1/PA10 already built, even though the technique
— state the loop as an explicit recursive/fold form, then induct — is the same in spirit).

**Difficulty**: moderate. The claim itself (the search only ever advances `len` while the
byte-by-byte comparison passes) is directly readable off the loop body; the work is in restating
the `while` loop in a form Lean can induct on, not in inventing new reasoning.

### L4 — LZ77 back-reference copy correctness (the hardest piece)

Given the induction invariant "decoded output so far equals `data[0:pos]`" and a valid match
`(len, dist)` from L3:

```
L4 : ∀ data pos len dist curOut,
       curOut.size = pos → (∀ i, i < pos → curOut.get! i = data.get! i) →
       1 ≤ dist → dist ≤ pos → (∀ j, j < len → data.get! (pos - dist + j) = data.get! (pos + j)) →
       let curOut' := copyLoop curOut dist len  -- the decoder's `for _ in [0:matchLen] do ...` body
       curOut'.size = pos + len ∧ ∀ j, j < len → curOut'.get! (pos + j) = data.get! (pos + j)
```

This is the delicate case because `dist` can be *less than* `len` (RLE-style self-overlapping
copies, e.g. `(candidate="42", pos, dist=1, len=16)`), meaning some of the bytes the copy loop reads
were written earlier in the *same* copy loop, not in the pre-match prefix. **Worked by hand in full
here** because the task explicitly asks for grounded difficulty, not a guess:

By strong induction on the copy step `j` (`0 ≤ j < len`). At step `j`, `curOut.size = pos + j`
(invariant maintained by the loop), so `srcIdx = curOut.size - dist = pos + j - dist`. Since
`dist = pos - candidate` where `candidate` is the match source position, `pos + j - dist = candidate
+ j` — a plain arithmetic identity, no case split needed for it. Two cases:

- **`j < dist`** (equivalently `candidate + j < pos`): `srcIdx` falls inside the *outer* invariant's
  already-verified prefix (`i < pos`), so `curOut.get! srcIdx = data.get! srcIdx = data.get!
  (candidate + j)`. The match certificate from L3, instantiated at this same `j` (`j < len` since
  `j < dist ≤ len` is not generally true — but the certificate holds for `j < len` regardless of
  the `dist` comparison, and this case only needs it at the current `j < len`), gives `data.get!
  (candidate + j) = data.get! (pos + j)` directly. Done — no recursion into the IH needed for this
  case.
- **`j ≥ dist`**: `srcIdx = pos + (j - dist) ≥ pos`, i.e. `srcIdx` is a position *this same copy
  loop* already wrote, at step `j - dist < j`. By the strong induction hypothesis (already
  established for all steps `< j`), `curOut.get! (pos + (j - dist)) = data.get! (pos + (j - dist))`.
  Separately, the match certificate at index `j` (the *same* `j`, not `j - dist`) gives
  `data.get! (candidate + j) = data.get! (pos + j)`, and `candidate + j = pos + j - dist` (the same
  arithmetic identity as above), so `data.get! (pos + (j - dist)) = data.get! (pos + j)`. Chaining:
  `curOut.get! srcIdx = data.get! (pos + (j-dist)) = data.get! (pos+j)`. Done.

Both cases close using the match certificate instantiated **at the current `j`** — the periodicity
that makes overlapping copies correct falls out of the *single* per-position match equality L3
already supplies, with no separate periodicity lemma needed. This is the one place in the whole
decomposition that needed a real argument rather than restating existing structure — confirming
the task doc's own guess that this is the hardest piece, for the reason it guessed (decoder state
depending on unbounded history), but it is fully worked out above, not merely flagged as risky.

**Difficulty**: moderate — a careful strong induction with one non-obvious case split, but every
step above is elementary arithmetic and lookup-chasing once stated correctly; no missing
mathematical machinery, no open question.

### L5 — Token-stream correctness (the main induction)

Ties L2 (per-symbol decode), L3+L4 (per-match decode), and the loop structure of
`compress`/`decodeHuffmanStream` together: by induction on `pos` (equivalently, on the list of
literal/match tokens `compress`'s main loop emits), `decodeHuffmanStream` applied to the bitstream
`compress` wrote for `data[pos:]`, starting from an output accumulator equal to `data[0:pos]`,
terminates at the EOB symbol having produced exactly `data`. Depends on L1 (bitstream position
bookkeeping) to know each iteration's remaining bits are exactly the encoding of the remaining
tokens, and needs P0 for `decodeHuffmanStream` to be inductable on at all.

**Difficulty**: moderate. This is "assembly," not new content — every fact it needs (L1-L4) is
already available; the work is a single well-founded induction correlating two loops (encoder's
`while pos < total`, decoder's `while !done`) step by step. Comparable in shape to PA10's
`unfilterFold_filterFold_get` (`Stdlib/Png/Equivalence.lean:353-382`), which already does exactly
this kind of "encoder loop / decoder loop, correlated by an induction on position" argument, just
for a per-byte filter step instead of a per-token LZ77/Huffman step.

### L6 — `compress` / `compressFixed` code-table bridging

`compressFixed` (used only by `gzipCompress`) hardcodes RFC 1951's literal/length/distance bit
patterns directly instead of consulting `fixedLitLenTable`/`fixedDistTable`. To reuse L2/L5 for both
encoders (rather than proving the whole chain twice), a finite bridging lemma per code class:

```
L6a : ∀ b < 256, fixedLitLenTable.codes[b]! = some (compressFixed's literal code for b, its bitLen)
L6b : ∀ len, 3 ≤ len → len ≤ 258 → compressFixed's lenSymbol formula = (encodeLength len).1
L6c : (analogous for the 5-bit fixed distance code, trivial: compressFixed's dCode is literally
       `reverseBits distCode 5` where distCode = (encodeDistance dist).1, already the same value
       `compress`'s path uses via `fixedDistTable.codes[distCode]!` — needs only
       fixedDistTable.codes[c]! = some (c, 5) for c < 32, a one-line closed fact)
```

Each is a finite/decidable proposition over a fixed alphabet or bounded numeric range (256 byte
values, 256 match lengths), directly analogous to the already-proven `encodeDistance_code_le_29`
(`Stdlib/Zlib/Equivalence.lean:73-76`, closed via `ite_fst_le`+`omega` band-peeling) and
`encode_length_bounds_inst`/`encode_distance_bounds_inst`'s pattern.

**Difficulty**: low. Same proof technique as sub-lemmas already landed in this exact file.

### L7 — `deflate_roundtrip_soundness` (∀ data)

Assembles: 3-bit header round-trip (trivial given L1), L5 (or L5+L6 for the `compressFixed` path
used by gzip), and the base case `data.size = 0` (the loop body never executes; only the header +
EOB are written/read — a direct instance of L1+L2 with no L3/L4/L5 needed at all).

**Difficulty**: mechanical, given L1-L6 — this is where everything else composes, not new content.

### L8 — Container-level checksum/index bookkeeping

For zlib: CMF/FLG header bytes are literal constants (`0x78`/`0x01`); `(0x78*256+0x01) % 31 = 0`
closes by `decide`/`rfl` on closed numerals (30721 = 31 × 991 exactly). Given `decompress
(compress data) = .ok data` (L7), `zlibDecompress`'s `uncompressed` variable IS `data`, so
`computedAdler := adler32 uncompressed` and the written `adler32 data` are *the same function call
on the same value* — **no Adler-32 mathematics is needed at all**, only that the byte-slicing
(`dataStart`/`dataEnd` arithmetic in `Stdlib/Zlib/Gzip.lean:46-69`) recovers exactly the bytes
`zlibCompress` wrote at that offset. Same argument for gzip's CRC-32/ISIZE trailer (`gzipCompress`/
`gzipDecompress`, `Stdlib/Zlib/Gzip.lean:25-160`) — the FEXTRA/FNAME/FCOMMENT/FHCRC branches are all
dead code for `gzipCompress`'s own output since it always writes `FLG=0x00`, each closing by a
closed-numeral `&&&` check.

**Difficulty**: low. Pure `ByteArray.extract`/`.push`/`.size` index arithmetic — exactly the
category PA10's `.get!`/`.push` bridge lemmas (`Stdlib/Png/Equivalence.lean:38-82`) already handle;
those lemmas are directly reusable here (see §6).

### L9 — `zlib_roundtrip_soundness`, `gzip_roundtrip_soundness` (∀ data)

L7 + L8, direct composition.

### L10 — PNG chunk/scanline bookkeeping

`mkChunk`/`parseChunk` roundtrip (`Stdlib/Png/Spec.lean:132-193`): given the same CRC-32 function
called on the same `type ++ data` bytes on both sides (no CRC mathematics, same argument as L8),
this is length-prefix/type-tag/CRC-suffix slicing arithmetic — mechanical, same category as L8.
Row-splitting (`encodeImageRGBA8`'s `for y in [0:img.height]` / `readPngStream`'s row loop) is a
`for`-range loop on the encode side already (directly PA10-style inductable) and, after P0's
`readPngStream` conversion, the same shape on the decode side.

**Difficulty**: low-moderate. Requires P0's `readPngStream` fix but otherwise pure bookkeeping.

### L11 — `png_roundtrip_soundness` (∀ img : ImageRGBA8)

L9 (zlib roundtrip closes IDAT recovery) + L10 (chunk/row bookkeeping) + **`Stdlib.Png.
filter_unfilter_soundness`, already proven and in the tree** (`Stdlib/Png/Equivalence.lean:394-402`,
requires `bpp ≥ 1`, satisfied since RGBA8 has `bpp = 4`). This is the one theorem in the whole
decomposition that gets a major existing dependency for free — see §6.

**Difficulty**: mechanical, given L9+L10 and the already-proven filter lemma. May need a
side-condition on `img` (e.g. `pixels.size = width * height * 4`) that the current bare
`ImageRGBA8` structure doesn't enforce as a type-level invariant — worth flagging to whoever lands
this, since `chooseBestFilter`'s row extraction (`img.pixels.extract (y*rowStride) ((y+1)*rowStride)`
in `Stdlib/Png/Streaming.lean:240`) silently produces a truncated/garbage slice if the invariant is
violated, which would make the theorem statement need an explicit hypothesis Law 9 requires be
stated, not silently assumed (exactly the PA10 precedent's own note about `bpp ≥ 1`).

### L12 — Idempotent-is-a-free-corollary (generic pattern)

See §3. One-line proof per instance, fully verified.

### L13 — `deflate_roundtrip_{empty,repetitive}_inst`

Direct instantiation of L7 at two concrete `ByteArray` literals.

---

## 5. The `partial def` obstacle — empirical evidence

Verified directly against the pinned toolchain (`leanprover/lean4:v4.33.1`, `lean-toolchain`) with
`lake env lean` on minimal standalone examples and, separately, directly on the real
`Stdlib.Zlib.Deflate` declarations (both runs done in the foreground during this investigation,
exit 0 each time; no scratch file was committed):

```
partial def countDown (n : Nat) : Nat := if n == 0 then 0 else 1 + countDown (n - 1)
#print countDown        --  opaque countDown : Nat → Nat
unfold countDown         --  error: Tactic `unfold` failed to unfold `countDown`
#check @countDown.eq_1   --  error: Unknown constant `countDown.eq_1`
```

And on the real code, after `lake build Stdlib.Zlib.Equivalence` (all 8 modules build clean, exit 0):

```
#print ensureBits.loop           -- opaque Stdlib.Zlib.ensureBits.loop : Nat → BitReader → BitReader
#print decodeHuffmanSymbol.step  -- opaque Stdlib.Zlib.decodeHuffmanSymbol.step : BitReader → HuffmanNode → Except ZlibError (BitReader × Nat)
unfold ensureBits.loop            -- error: Tactic `unfold` failed to unfold `ensureBits.loop`
```

`decompress` itself prints as a `forIn`-desugared `while` loop one level down, but that `forIn`
bottoms out in the same opaque `.loop`/`.step`-style auxiliary the other four functions do — the
outer function is not the opaque atom, but the actual recursive core underneath it is, for all five.

The fix (`termination_by`/`decreasing_by`, converting to well-founded recursion) was verified to
work and to produce a real, `rw`/`unfold`-usable equation lemma:

```
def countDownWF (n : Nat) : Nat := if h : n = 0 then 0 else 1 + countDownWF (n - 1)
termination_by n
decreasing_by omega

#print countDownWF        -- @[irreducible] def countDownWF : Nat → Nat := WellFounded.Nat.fix ...
#check @countDownWF.eq_1  -- countDownWF.eq_1 : ∀ (n : Nat), countDownWF n = if h : n = 0 then 0 else 1 + countDownWF (n - 1)
theorem countDownWF_zero : countDownWF 0 = 0 := by unfold countDownWF; simp   -- succeeds
```

This is the evidentiary basis for P0 in §4: the obstacle is real and total (nothing beyond
`native_decide`/`decide` on closed ground instances works today), and the fix is a known, working
Lean pattern, not a research question.

---

## 6. What's reusable

- **PA10's fold-normalization technique** (`Stdlib/Png/Equivalence.lean:151-238`, restating an
  `Id.run`/`for`/`push` loop as an explicit `List.foldl` via `Std.Legacy.Range.forIn_eq_forIn_range'`
  + `List.forIn_pure_yield_eq_foldl`) transfers **directly** to every genuine `for i in [a:b]` loop
  in the Zlib/PNG codec: `decodeStoredBlock`'s copy loop, `compress`'s/`compressFixed`'s literal
  emission when *not* matching, `encodeImageRGBA8`'s row loop, `unpackScanlinesToRGBA8`'s per-pixel
  loops. It does **not** directly transfer to `findLongestMatch` (a `while`/`return`-shaped loop,
  L3) or to any of the five P0 functions (not `for`-range loops, and opaque besides) — new bridging
  lemmas are needed there, though the *technique* (restate as an explicit recursive form, then
  induct) is the same in spirit.
- **PA10's four `.get!`/`.push` bridge lemmas** (`ByteArray.get!_eq_getElem_bang`,
  `get!_push_lt`, `get!_push_eq`, `ext_get!`, `Stdlib/Png/Equivalence.lean:38-82`) are
  general-purpose (not PNG-specific, per that file's own header comment) and directly reusable by
  every accumulator-growing loop in `Deflate.lean`/`Gzip.lean` (`decodeStoredBlock`'s `newOut`,
  `decodeHuffmanStream`'s `curOut`, `compress`'s/`zlibCompress`'s/`gzipCompress`'s `out`).
- **`Stdlib.Png.filter_unfilter_soundness`** (`Stdlib/Png/Equivalence.lean:394-402`) is consumed
  wholesale by L11 — zero new proof content for PNG's per-scanline correctness.
- **`CRC32Equivalence.lean`'s XOR-linearity technique** (PA14, `Gbf_additive`/`Gbf8_additive`,
  `Stdlib/Zlib/CRC32Equivalence.lean:283-297`) does **not** transfer to this task's core content —
  it is specific to CRC-32's bit-recurrence algebra, and per L8 above, no checksum algebra is
  needed for the roundtrip theorems at all (the checksum-agreement argument is definitional, not
  algebraic, once L7/L9 hold). It would, however, transfer to a *future* task that wants to prove
  the CRC-32/Adler-32 *values themselves* match an independent reference implementation — out of
  scope here.
- **`encodeDistance_code_le_29`/`encode_length_bounds_inst`/`encode_distance_bounds_inst`**
  (`Stdlib/Zlib/Equivalence.lean:41-112`, once migrated per PA18 to non-`native_decide` form) are
  directly reusable in L3/L6 to bound the code ranges `findLongestMatch`'s output can produce.
- **Spike5's near-duplicate pair** (`Spikes/Spike5Gzip/Equivalence.lean`, out of this task's scope
  but noted per the assigning task): once `gzip_roundtrip_soundness` (L9) lands here, Spike5's
  identical-shape theorems over its own `canonicalSampleData` close by the exact same L12 corollary
  pattern, provided Spike5's gzip compress/decompress are the same `Stdlib.Zlib` functions (worth
  confirming when that task is picked up) rather than a re-implementation.

---

## 7. Honest verdict

**Reachable, not a multi-week research-risk item, but not "cheap" either — closer in shape to
PA1's pathfinder than to PA14's SAT-replacement problem.** Grounding this against the task's own
calibration note (PA14 was the other item flagged possibly-unreachable, and closed in a single pass
with fifteen structural helper lemmas and no specialized library):

- **Nothing in this decomposition needs new mathematics or missing Lean machinery, and nothing in
  it is made easier by proving less than the honest target.** The hardest single piece (L4, the
  LZ77 self-overlap induction) is fully worked out by hand in §4 above and closes with an ordinary
  strong induction plus one arithmetic identity — no periodicity lemma, no external library,
  comparable in difficulty to PA14's own case-split-and-chase style, not to PA14's genuinely-blocked
  "GF(2) polynomial ring from scratch" alternative branch. L7's target is the full, unweakened
  `∀ data, decompress (compress data) = .ok data`, and L1-L6 prove genuine LZ77 back-reference and
  genuine canonical-Huffman decode/encode inversion to get there (§0.2) — the decomposition's only
  scope reduction is which of `decompress`'s three block-type branches this specific composition
  exercises, not a reduction in what's proven about the branch it does exercise.
- **Two immediate, independent fixes landed alongside this design pass** (§0.1, §0.2): the four
  vacuous `_inst` idempotent checks now require actual decompression success rather than accepting
  a permanently-failing decoder, and the `decodeDynamicTables`/`decodeStoredBlock` zero-coverage gap
  is now recorded as `MODEL_DEBT.md` B10 rather than left implicit. Neither required or anticipated
  the universal proof; both were cheap once found.
- **The one real correction to the task's own Phase 1 framing**: `docs/tasks/
  PA16-codec-roundtrip-universal-soundness.md`'s sub-lemma (a) (general Huffman correctness "for
  any symbol-frequency distribution") and (c) (general multi-block framing) are both *not needed*
  for any of the 10 entries in scope, because `compress`/`compressFixed` only ever emit a single
  Fixed-Huffman block (§2). This shrinks the decomposition's real content relative to the task
  doc's own estimate.
- **The one genuinely new prerequisite the task doc did not anticipate at all** is P0 (§4, §5): five
  `partial def`s are kernel-opaque in this Lean version, empirically confirmed, and nothing short of
  converting them to well-founded recursion unblocks any of L2 through L11. This is not optional and
  not previously flagged anywhere in `docs/ORACLE_DEBT.md` or the PA16 task file. It is bounded,
  known-working engineering (§5 demonstrates the fix pattern compiling), but it means Phase 2 must
  start by editing `Stdlib/Zlib/Deflate.lean` and `Stdlib/Png/Streaming.lean` themselves, not only
  adding a new proof file — a different shape of first step than PA1/PA10/PA14 needed (none of
  those tasks' target functions were `partial`).
- **Effort shape**: L1 (bitstream ghost-state algebra) and L4 (the overlap induction, already
  worked out) are the two pieces needing real proof-authoring skill; L2, L3, L5, L6, L8, L10 are
  mechanical given L1/L4 and PA10's existing bridge lemmas; L7, L9, L11, L12, L13 are composition.
  Realistic estimate: comparable to one PA1-class pathfinder effort (P0 + L1 + L4, the three pieces
  with real content) plus roughly PA10-class effort for everything else (bookkeeping, reusing
  existing lemmas). Not a single clean afternoon, but not the "multi-week, no clean strategy" framing
  `docs/ORACLE_DEBT.md` Part 4 used either — that framing was written without having read that
  `compress` is single-block-only or that the idempotent entries are free corollaries, both of
  which are visible directly in the 30 lines of `Equivalence.lean` this document read in §1.
- **Recommended landing order for whoever picks up Phase 2**: P0 first (nothing else compiles as a
  proof target without it) → L1 (bitstream algebra, needed by everything downstream) → L2/L3/L6
  (mechanical, can be parallelized against each other once L1 lands) → L4 (the hard one, worked out
  above, do it once L3 exists) → L5 (assembles L1-L4) → L7 (closes `deflate_roundtrip_soundness`,
  the first real entry) → L8/L9 (zlib/gzip, mechanical) → L10/L11 (PNG, sequenced last per the task
  doc's own correct instinct, since it depends on L9) → L12/L13/L9-closure (free corollaries, do
  last, trivially fast once their dependencies exist).
- **What would change this verdict**: if L1's bitstream algebra turns out to need a stronger
  invariant than sketched here once actually attempted (e.g. if `ensureBits`'s `UInt32` bit-buffer
  arithmetic has an overflow edge case at some call site not checked by this document's read),
  effort would grow but would still not cross into "new mathematics" territory — it would still be
  bookkeeping, just more of it.

**Bottom line**: assign this to landing P0+L1+L4 as a first pathfinder pass (highest-uncertainty,
highest-leverage content, same shape as PA1's role for CRC32), then the rest is well-scoped
follow-on work with no identified research risk remaining. This closes theorem 1 (§0.2) — this
codebase's compressor round-trips through this codebase's decompressor — and only that. It says
nothing about, and must never be cited as evidence for, theorem 2 (decoder conformance to arbitrary
valid RFC 1951 streams), which remains completely unverified and is tracked separately as
`MODEL_DEBT.md` B10.
