# Stdlib.Fmt — A Proof-Carrying Decimal Digit Formatter and Parser

## 1. Overview & Scope

`Stdlib/Fmt/` is a small, total, proof-carrying decimal-digit formatting library: a `Nat → List
UInt8` encoder (`formatDecimal`), a `List UInt8 → Except Fmt.Error Nat` decoder (`parseDecimal`),
and a machine-checked roundtrip theorem connecting them. It exists to close a real defect class in
`Spikes/Spike2Fibonacci`: the spike's Windows/Linux assembly (`Spikes/Spike2Fibonacci/{Windows,
Linux}/Program.lean`) hand-writes its own decimal itoa directly in x86-64 -- a hardware
division/modulo digit-extraction loop (`digit_extract_loop`) that pushes each digit onto the
stack, followed by a digit-pop-and-write loop (`digit_write_loop`) that copies them back out in
the correct order -- with no specification anywhere in the tree of what "correct decimal
formatting" even means, let alone a proof that this two-loop, variable-trip-count assembly
sequence computes it. The spike's whole-program trace-equivalence theorem
(`spike2_canonical_effect_trace_equivalence`, `Spikes/Spike2Fibonacci/Windows/Equivalence.lean`)
is consequently discharged by `native_decide` on a single concrete input trace, not a genuine
structural argument -- exactly the oracle-dependence Law 10 (`scripts/gate_allowlist.txt`) exists
to track down and retire. This library gives "the decimal representation of `n`" a real,
structurally-recursive definition and a real correctness theorem, so a future connection proof
between it and the assembly's itoa loops has something honest to be checked against, in the same
role `Stdlib/Http11` now plays for `Spikes/Spike4HttpServer`'s request routing
(`docs/STDLIB_HTTP11.md#1-overview-scope`).

### 1.1 What This Library Models

The decimal (base-10) representation of an arbitrary `Nat`, as a most-significant-digit-first
sequence of digit values `0..9` (`digits`), and its ASCII byte encoding (`formatDecimal`, one
byte `0x30 + d` per digit `d`). The representation is minimal: no leading zeros, and exactly `[0]`
/ `"0"` for zero. The companion decoder (`parseDecimal`) accepts any non-empty run of ASCII digit
bytes -- including ones with leading zeros, since rejecting those is a canonicalization policy a
caller can layer on top, not a grammar this library enforces (`digits`/`formatDecimal` alone are
responsible for never producing one).

### 1.2 Deliberate Omissions

Not modeled: negative numbers (`Nat` only -- callers formatting a signed quantity supply their own
sign handling), non-decimal radixes, locale-specific digit grouping (thousands separators), and
leading/trailing whitespace tolerance in the parser (a byte string with anything other than digit
bytes, including surrounding whitespace, is rejected as `Error.invalidDigit`, never silently
trimmed). Each of these is a real, named scope limit: a future extension needs new grammar and a
re-proof of the roundtrip theorem, not a loosening of an existing check.

## 2. Digit Grammar

A digit byte is ASCII `'0'..'9'` (`0x30..0x39`); `digitOfByte?`/`byteOfDigit` convert between a
digit byte and its numeric value `0..9`. `digits n : List Nat` is the most-significant-digit-first
decimal digit sequence for `n`: `digits n = [n]` when `n < 10`, and `digits n = digits (n / 10) ++
[n % 10]` otherwise -- well-founded recursion on `n` (`n / 10 < n` whenever `n ≥ 10`), not
`partial def`. `formatDecimal n := (digits n).map byteOfDigit` is its ASCII byte encoding.

## 3. Decoder (Parser) Behavior

### 3.1 Error Taxonomy

`Fmt.Error` names each rejection reason precisely: `empty` (a zero-length byte string -- an empty
field is a parse error, not a silent zero) and `invalidDigit` (any byte in the input that is not
an ASCII decimal digit, anywhere in the run, including a leading sign or embedded whitespace).
Every rejection is total and immediate -- `parseDecimal`/`parseDecimalAux` are built entirely from
structurally recursive functions over `List UInt8` (never `partial def`), so parsing terminates on
every input, well-formed or adversarial, with no possibility of a hang. See `Stdlib/Fmt/Test.lean`
for a concrete regression vector per rejection reason.

## 4. Encoder (Formatter) / Canonical Serialization

`formatDecimal` produces exactly one canonical byte string per `Nat`: its minimal digit sequence,
most-significant digit first, with no leading zeros (`"0"` for zero, never `""`). There is no other
serialization this library ever produces for a given `Nat`.

## 5. Formal Theorems

### 5.1 Digit-List Correctness

`Stdlib.Fmt.digits_foldl_eq : ∀ (n : Nat), (digits n).foldl (fun acc d => 10 * acc + d) 0 = n` --
folding `digits n` back together with the standard positional-notation accumulator recovers
exactly `n`, the checkable statement that `digits n` really is "the decimal representation of
`n`" and not merely some list of small numbers. Paired with `Stdlib.Fmt.digits_lt_ten : ∀ (n :
Nat) (d : Nat), d ∈ digits n → d < 10` (every entry actually is a digit) and
`Stdlib.Fmt.digits_ne_nil : ∀ (n : Nat), digits n ≠ []` (every `Nat`, including `0`, has at least
one digit).

### 5.2 Write-Then-Parse Roundtrip Theorem

`Stdlib.Fmt.parseDecimal_formatDecimal : ∀ (n : Nat), parseDecimal (formatDecimal n) = .ok n`,
universally quantified over every `Nat` -- not a `native_decide` check over sample literals. This
is the honest direction: formatting produces canonical bytes, and parsing recovers exactly the
value that produced them. `formatDecimal (parseDecimal b) = b` is deliberately **not** claimed and
is false in general (a leading-zero input such as `"007"` parses to `7`, whose canonical
`formatDecimal` re-encoding is `"7"`, not `"007"`) -- see
`docs/STDLIB_HTTP11.md#51-write-then-parse-roundtrip-theorems` for the same asymmetry drawn for
this library's HTTP counterpart.

### 5.3 Parse-Reencode Stability Theorem

`Stdlib.Fmt.parseDecimal_reencode_stable : ∀ (b : List UInt8) (n₁ n₂ : Nat), parseDecimal b = .ok
n₁ → parseDecimal (formatDecimal n₁) = .ok n₂ → n₁ = n₂` ranges over *every* byte string, not just
ones `formatDecimal` produces -- including malformed, adversarial, or non-canonical (leading-zero)
input. This is the theorem that would catch a lossy parser: one that accepts `b`, discards
information the formatter cannot reproduce, and so reparses its own canonical rewrite into a
different value. It is proved as a direct corollary of §5.2's universal roundtrip theorem plus the
parser's own determinism: instantiating §5.2 at `n₁` gives `parseDecimal (formatDecimal n₁) = .ok
n₁` unconditionally, which the second hypothesis (`... = .ok n₂`) then forces to equal `.ok n₂` by
injectivity of `Except.ok`. §5.2 is therefore this theorem's non-vacuity floor: on its own, §5.3
would be satisfiable by a parser that always returns `.error` (the hypothesis `parseDecimal b =
.ok n₁` would simply never fire), but §5.2 independently forbids that parser. Both are stated and
proved, never one without the other -- the shape the owner specified for parsers generally: "take
an arbitrary bytestream; if it fails, fail; if it parses, re-encode and parse; assert the first
parse matches the second."

### 5.4 Length And Buffer-Fit Bounds

`Stdlib.Fmt.digits_length_le : ∀ (n k : Nat), 0 < k → n < 10 ^ k → (digits n).length ≤ k` (and its
byte-level corollary `formatDecimal_length_le`) -- if `n` fits in `k` decimal digits, its digit
sequence is at most `k` entries long, the fact a stack-buffer itoa needs to know its write never
overruns a `k`-byte reservation. Specialized to the register width `Spikes/Spike2Fibonacci`
actually uses: `Stdlib.Fmt.digits_length_le_UInt64 : ∀ (n : UInt64), (digits n.toNat).length ≤
20` (and `formatDecimal_length_le_UInt64`), since `n.toNat < 2 ^ 64 < 10 ^ 20` for every `UInt64`.
Two exact-length facts cover the spike's other formatting site, the `1..90` loop index: `digits_
single : ∀ (n : Nat), n < 10 → digits n = [n]` and `digits_length_two : ∀ (n : Nat), 10 ≤ n → n <
100 → (digits n).length = 2` -- exactly the two cases
`Spikes/Spike2Fibonacci/Windows/Program.lean`'s `main_loop` branches on (`cmp r13, 10` / `jge
two_digits_i`) to decide one-digit versus two-digit index formatting.

### 5.5 Bounded UInt64 Decimal Contract

`Stdlib.Fmt.UInt64Decimal` is the callable result/capacity contract. Its `decimalDigitCount` has
an explicit zero case and is proved equal to the canonical digit-list length, so every `UInt64`
has between one and twenty decimal digits. `Stdlib.Fmt.UInt64DecimalSchedule` is a separate,
optional implementation certificate: `extractDecimalReversed` is a total division/modulo schedule
that produces the least-significant digit first, and `reverseWriteDecimal_extract` proves that
reversing and byte-writing that extraction is exactly `formatDecimal` for every input value.

`writeUInt64Decimal capacity value` makes finite memory a normal result: it returns the complete
canonical byte string only when the exact required length fits, otherwise
`insufficientCapacity required capacity`; it never truncates. The callable contract publishes the
exact required length only. The separate schedule certificate publishes its own affine work count
(`3 + 2 * digitCount`) and logical scratch clobbers; neither is a production instruction-fuel
claim. These scratch names deliberately do not choose registers, stack slots, or an ABI: a target
realization must separately prove its physical frame, clobbers, writes, faults, resource budget,
and calling boundary against the callable contract.

## 6. Spike 2 Migration Status

### 6.1 The itoa Defect Class This Library Makes Provable

Before this library, "the assembly formats a Fibonacci value as decimal" was not a statement with
a truth value anywhere in the tree: `Spikes/Spike2Fibonacci/Spec.lean`'s `fibonacciSpec` produces
its per-line strings via Lean's own `s!"..."` interpolation (`Nat.repr`/`toString`), and the
assembly's `digit_extract_loop`/`digit_write_loop` reimplement decimal itoa from scratch in
hardware division/modulo with no shared specification between the two -- so the single
`native_decide` trace-equivalence check (`spike2_canonical_effect_trace_equivalence`) is the
*only* place in the tree that ever compares them, and only for one concrete run (all 90 lines of
one fixed program), not a structural argument that the assembly's itoa is correct for every input
value. `Stdlib.Fmt` gives "the decimal representation of `n`" (§5.1) and "the assembly's actual
job, formatting a value into a byte buffer" (§5.2-§5.4) real, general theorems for the first time,
so a connection proof between them (§6.2) would close that gap for every input, not one sample.

### 6.2 Migration Status And Remaining Work

**Library layer (bounded contract done; target realization open).** The canonical codec and the
finite-resource UInt64 extraction/reverse-write contract (§5.1-§5.5) are proved without `sorry`,
axioms, `native_decide`, or `bv_decide`. The separate remaining task is to connect the exact
x86-64 division/push/pop instruction stream, its physical frame, and its selected outcome policy
to that contract; the library does not claim that connection has happened.

**Spec layer (not started).** `Spikes/Spike2Fibonacci/Spec.lean`'s `fibonacciSpec`/
`formattedFibonacciWindowsOutput` do not call `Stdlib.Fmt.formatDecimal` -- they still go through
Lean's own `s!"..."` string interpolation. Routing the model layer through `formatDecimal` first
(mirroring `docs/STDLIB_HTTP11.md#62-migration-status-and-remaining-work`'s "model layer" step)
would need a lemma that `Nat.repr`/`toString`'s digit sequence agrees with `Stdlib.Fmt.digits` --
not attempted here, since the spec's own output is not what `spike2_canonical_effect_trace_
equivalence` needs to change to retire its `native_decide`; the assembly side (below) is the
actual gap.

**Assembly layer (not started; the concrete remaining work).** Retiring
`spike2_canonical_effect_trace_equivalence`'s `native_decide` (`scripts/gate_allowlist.txt`'s
`Spikes/Spike2Fibonacci/Windows/Equivalence.lean::spike2_canonical_effect_trace_equivalence`
entry) needs a loop-invariant induction, in PA15's style
(`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`), over `spike2Instructions`' `digit_extract_
loop`/`digit_write_loop` pair specifically -- proving that pair's effect on the stack buffer,
starting from an arbitrary `UInt64` value in `r14`, equals `formatDecimal` applied to that value
(reversed appropriately for the push-based extraction order), for *every* value, not a sample.
Concretely, this needs:

1. A loop invariant for `digit_extract_loop` relating the stack's pushed-digit sequence after `j`
   iterations to `(digits (n / 10 ^ j)).reverse` (or an equivalent per-iteration characterization)
   and the loop's own `rcx` counter to `(digits n).length - j` -- proved by induction on the
   iteration count, the same shape `fibLoop_iteration`/`fibLoop_done` use for the Fibonacci
   recurrence loop, but over a *variable* trip count (`digits n`'s length depends on `n`, unlike
   the fixed `90`-iteration outer loop `Spikes 3/4/5` inherited) rather than a caller-supplied
   fixed iteration count -- the loop invariant's own `m` (remaining iterations) needs to be tied
   to `(digits (n / 10 ^ k)).length` for the current dividend, not passed in as an independent
   parameter the way `fibLoopInvariant`'s `m` is.
2. A matching invariant for `digit_write_loop` (the pop-and-write pass) showing it reconstructs
   `formatDecimal n` in the buffer in the correct (most-significant-first) order from the
   extraction loop's stack-pushed (least-significant-first) sequence.
3. Composing (1) and (2) with the two other formatting sites in `main_loop` (the fixed `"Fib("`/`")
   = "` literal bytes, and the one/two-digit index formatting `digits_single`/`digits_length_two`
   already cover exactly) and the existing PA15 Fibonacci-recurrence facts
   (`Spikes/Spike2Fibonacci/Windows/LoopInvariant.lean`) into a whole-line, then whole-program,
   trace fact -- comparable in scope to a Zlib-style per-target equivalence proof
   (`docs/STDLIB_HTTP11.md#62-migration-status-and-remaining-work` names the same scope estimate
   for `Http11`'s own still-open assembly connection).

None of this is attempted in this change: it is a genuine, multi-loop, variable-trip-count
induction (item 1 in particular has no direct PA15 precedent, since every prior loop-invariant
proof in this tree closes over a fixed or externally-supplied iteration count, not one derived
from the *value being processed*), estimated at PA15-or-greater scope on its own. **No allowlist
entry is retired by this change.** What this change delivers is the proven target (§5) that a
future connection proof would check the assembly against, plus this precise statement of what
remains -- not an overstated claim that the connection itself is done.
