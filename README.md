# gasm

**Proof-carrying assembly in Lean 4.** `gasm` is a framework for hand-authoring
machine code — real x86-64 instructions, real WebAssembly modules — annotated
with formal invariants, and mechanically proving that the assembly is
equivalent to a pure, high-level specification of what it's supposed to do.
The proof and the binary come from the same source tree; nothing is trusted
that a build didn't check.

This README is written to be read cold. It tells you what this project
claims, what it has actually verified today, and where the two diverge.

---

## Why proof-carrying assembly, not a compiler

`gasm` does not compile a high-level language down to machine code. There is
no lowering pass, no register allocator, no optimizer to trust. Instead, for
every routine, three things are authored side by side and checked against
each other by the Lean kernel:

1. A **specification** — a pure Lean function or state-transition system
   describing the intended behavior, with no machine-specific detail in it.
2. A **program** — the actual x86-64 instructions or WebAssembly AST, hand-
   written in `gasm`'s typed assembly DSL, carrying explicit proof
   obligations for every memory access and every ABI-sensitive register.
3. An **equivalence proof** — a Lean theorem stating that executing the
   program produces exactly the behavior the specification demands, checked
   by the Lean kernel, not by a test suite.

The project's stated reasoning for this shape (the full argument is in
[`docs/VISION.md`](docs/VISION.md), and is worth reading before you form an
opinion of the approach):

- **Implementation text is disposable.** Hand-written or agent-generated
  assembly, C, Rust — none of it is the durable artifact. The specification
  and the proof are. Code can be regenerated at will as long as the
  boundary it must satisfy is fixed and checked.
- **A "program" is a formal boundary on what must be true**, not a sequence
  of instructions to be trusted because a human wrote them carefully.
- **AI agents can generate low-level code fast, and cheaply explore many
  variants — but only if something mechanical and sound tells them when
  they're wrong.** The validation gate — not the generated assembly — is
  what this repository actually exists to build.

The corollary the project takes seriously: **a gate that an incomplete or
incorrect implementation can pass will eventually be passed by one.** Several
of the Laws in [`docs/REVIEW.md`](docs/REVIEW.md) — universal quantification
over real input domains (Law 9), the restriction on `native_decide` to
genuinely exhaustive finite checks (Law 10), the prohibition on dead
abstractions and pointwise "verification" (Law 8) — exist because this
project has, in its own history, watched a hollow gate get exploited by an
implementation specialized to pass it (`docs/VISION.md` §2 tells that story).

---

## What actually works today

Read this section skeptically; every claim here was re-verified against this
exact commit while writing this document, and the commands to reproduce each
one are given.

**The build is green.** `lake build` compiles and links the full project —
170 Lean modules (~26,000 lines), all five spikes for both targets, four
differential fuzzers, and the gate tooling — with zero errors, zero `sorry`,
and zero unauthorized axioms.

**Five spikes are implemented, proved, and (for the Windows target) executed
on real hardware as part of this verification pass:**

| Spike | What it does | Verified this session |
|---|---|---|
| 1 — Hello World | Prints `Hello, World!` and exits 0 | Emitted a real PE32+ binary, ran it on this Windows host, byte-exact stdout match |
| 2 — Fibonacci | Loop-based sequence printer with hand-proved loop invariants | Built; in-Lean equivalence proof checked by `lake build` |
| 3 — Sort Lines | Streaming stdin sort using `Stdlib.SmolAlloc`'s dynamic allocator | Built; in-Lean equivalence proof checked |
| 4 — HTTP 1.1 server | WinSock2 / WASI socket server, per-route equivalence proofs | Built; in-Lean equivalence proof checked |
| 5 — GZIP / GUNZIP | RFC 1950/1951/1952 DEFLATE, hand-written in x86-64 | Emitted real PE32+ binaries; ran `spike5_gzip.exe` on a real input string, decompressed the output with **Python's standard `gzip` module** to confirm it is a genuine, standards-conformant gzip stream (not a stub); then fed that file back into the emitted `spike5_gunzip.exe` and got the exact original bytes back |

Reproduce the Spike 5 round-trip yourself after building (Windows):

```sh
lake exe spike5_gzip_windows      # emits spike5_gzip.exe in the cwd
echo -n "some real text" | ./spike5_gzip.exe > out.gz
python -c "import gzip; print(gzip.open('out.gz','rb').read())"   # decodes correctly
lake exe spike5_gunzip_windows    # emits spike5_gunzip.exe
./spike5_gunzip.exe < out.gz      # prints the original text back
```

**The differential test suites pass.** `lake exe test_roundtrip` — the
encoder/decoder round-trip gate over the x86-64 instruction registry —
reports **1594/1594 tests passed** on this commit. Four fuzzers
(`x86_fuzzer`, `wasm_fuzzer`, `perf_fuzzer`, `encoding_fuzzer`,
`gzip_fuzzer`) build and are wired to differential oracles (real silicon for
the hardware fuzzer, a Python `gzip` oracle for the GZIP fuzzer, host Wasm
runtimes for the Wasm fuzzer) — see `docs/VISION.md` §3.2 for why
differential validation against reality, not just internal consistency, is
treated as load-bearing here.

**The citation/traceability gate holds.** `python scripts/check_refs.py`
confirms every Lean declaration in the tree cites a real design-document
section and every citation resolves — the mechanism behind Law 1
("no invention"). At the time of writing it reports **179 of 1,022 design
sections (17.5%) referenced by code** — the remaining 82.5% is the honestly
computed, mechanically tracked backlog of designed-but-unimplemented
specification (Law 3), not a hidden gap.

**The Law 10 gates hold.** Both the fast source-level pre-check
(`scripts/check_gates.py`) and the load-bearing kernel-level check
(`lake exe check_gates_axioms`, which reads Lean's own axiom-dependency graph
rather than source text) report zero un-allowlisted `native_decide` or
non-standard-axiom occurrences across the 5,088 declarations the axiom-level
tool scans.

## What is designed but not yet built

`gasm` currently implements exactly two ISA/format families end to end:
**x86-64** (encoder, decoder, disassembler, semantics, PE32+ emission for
Windows) and **WebAssembly** (AST, binary encoding, LEB128, a WASI
Preview 1 binding). Design documents exist under `docs/TARGETS/` for ARM
(AArch64/AArch32), x86-32, x86 real mode, SPIR-V/Vulkan, Linux (SysV/ELF),
and bare-metal/freestanding execution — **none of these have any
corresponding code in `Gasm/Targets/` yet.** A design document under
`docs/` is a specification the project intends to implement against, not a
claim that the implementation exists; if you're evaluating this project,
check `Gasm/Targets/` directly rather than the design-doc table of contents.

Spike 6 (a headless SPIR-V/Vulkan compute pipeline) and Spike 7 (an
interactive windowed swapchain) are planned in
[`docs/SPIKES.md`](docs/SPIKES.md) but not started.

## The stated destination — and why the gap is wide on purpose

The systems this project exists to eventually build are, verbatim from the
owner's own scope statement: **game engines, operating systems, web/gRPC
servers, and databases.** That is a genuinely large target and the current
codebase — two ISA targets, five small spikes, a partial x86-64 instruction
set — covers a small fraction of it. This is a deliberate consequence of the
project's own stated methodology, not an oversight:
[`docs/VISION.md`](docs/VISION.md) §3.3 explicitly rejects building out ISA
or API surface ahead of demand, citing this project's own predecessor
(`wsc`), which failed by doing exactly that — building a large instruction
model before the model was validated, then discovering the model was wrong
after too much depended on it. `gasm`'s target models are deliberately
incomplete; new surface enters only when a spike forces it, and is
differentially validated against real hardware/engines/OS in the same
change that introduces it. Treat the size of the gap between "five spikes"
and "operating systems and databases" as evidence the discipline is being
followed, not as a project running behind an unmet promise — and treat any
future claim that a target is "supported" with the same skepticism this
document is trying to model: check `Gasm/Targets/` for code, not `docs/` for
intent.

## Maturity, honestly

This is a young, single-maintainer-plus-AI-agents research project, not
production infrastructure, and it says so about itself in its own tree:

- **No CI is checked in.** Every gate above is run manually (or by an
  orchestrating agent) today; there is no `.github/workflows` or equivalent
  yet enforcing them on every change.
- **The project keeps its own ledgers of known gaps.** `TCB.md` (trusted
  computing base — what's assumed but not proven) and `MODEL_DEBT.md` (what
  the machine/OS models simplify or omit) are checked into the repository
  root and are worth reading before trusting any specific claim this project
  makes about a specific routine or model. They are unusually candid by the
  standards of most READMEs — e.g. `TCB.md` documents that the axiom-level
  gate's own import closure misses roughly a fifth of the project's modules
  (tracked, prioritized, not hidden).
- **Law 10's `native_decide` restriction is a target, not yet a completed
  migration.** `docs/REVIEW.md` Law 10 records that a majority of existing
  `native_decide` occurrences are "grandfathered" — pointwise checks that
  predate the law and are tracked migration backlog, not compliant
  instances. The gate correctly reports this every run rather than hiding
  it.
- **Memory-capability enforcement (Law 11) binds new code, not existing
  code.** `docs/REVIEW.md` states plainly that zero modules are currently
  migrated to the capability-authoring path; this is recorded as backlog,
  not silently overstated.

If you are deciding whether to depend on this project for anything, read
`TCB.md` and `MODEL_DEBT.md` directly rather than taking this README's word
for the state of any one model or routine.

---

## Repository layout

```
Gasm/                   The framework itself
├── Core/                 State, types, permissions, obligations, the BlockM
│                         typestate monad, the CFG/verification machinery
├── Effects/               Portable effect typeclasses (Console, FileSystem,
│                         Network, Clock, Process, Trace) — the vocabulary
│                         specs are written against
└── Targets/
    ├── X86_64/            Registers, encoding, decoding, disassembly,
    │                       semantics, the instruction registry, hardware
    │                       fuzzing, performance model
    ├── Windows/            PE/COFF format, Win32 API model, linker, emitter
    ├── Wasm/               AST, binary/text encoding, LEB128, semantics,
    │                       linker, host-oracle differential fuzzing
    └── WASI/               WASI Preview 1 ABI binding

Stdlib/                  Verified library routines built on Gasm
├── Zlib/                  RFC 1950/1951/1952 (zlib/DEFLATE/gzip), CRC32,
│                         Adler-32, Huffman coding, LZ77
├── Png/                   Streaming PNG scanline codec, filters
└── SmolAlloc/              A small dynamic memory allocator

Spikes/                  Minimal vertical end-to-end proofs (Spec + Program
                         + Equivalence + a real emitted binary), per
                         docs/SPIKES.md's roadmap

Tools/                   Gate tooling (the axiom-level Law 10 checker)
scripts/                 Python/shell gate scripts, CI-equivalent checks
docs/                    Design specifications, laws, ADRs, task tracking
```

Every routine in `Gasm/`, `Stdlib/`, and `Spikes/` follows the same
three-file shape wherever it's meaningful to: `Spec.lean` (pure model),
`Program.lean` (hand-written assembly/AST), `Equivalence.lean` (the proof
connecting them). See [`CONTRIBUTING.md`](CONTRIBUTING.md) for why this
shape is treated as load-bearing rather than a style preference.

---

## Building and running

**Prerequisites:** the Lean/Lake toolchain pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.33.1`) — install via [`elan`](https://github.com/leanprover/elan).
Nothing else is required to build and run the library, the spikes, or the
test suites; NASM is only needed if you run the x86-64 encoding fuzzer's
NASM cross-check. The Wasm spikes' host-runtime verification step (as
opposed to the in-Lean check) additionally looks for `node`, `wasmtime`,
`wasmer`, or `deno` on `PATH`; none are required to build.

```sh
# Full build: every library, every spike (both targets), every fuzzer and
# test binary, and the gate tooling. This is the real CI gate — there is no
# narrower default target set. Several minutes on a cold cache; the actual
# elapsed time in this session's own cold-build run varied with concurrent
# machine load, so no single number here is asserted as typical.
lake build

# Run the gates, in the order docs/REVIEW.md Pillar 1 lists them:
python scripts/check_refs.py         # citation/traceability
python scripts/check_gates.py        # fast Law 10 source-level pre-check
lake exe check_gates_axioms          # the load-bearing Law 10 gate — run it, don't just build it
python scripts/check_licenses.py     # Apache-2.0 header compliance

# Build and run one spike end to end (Windows):
lake exe spike1_hello_windows        # emits hello.exe into the cwd
./hello.exe                          # prints "Hello, World!" and exits 0

# Or use a spike's own self-test, which builds, runs, and checks output for you:
lake exe test_spike1_windows

# The x86-64 encoder/decoder round-trip gate:
lake exe test_roundtrip
```

All of the above were run against this exact commit while writing this
document; none are aspirational.

---

## Governance: the Laws, gates, and review discipline

`gasm` is governed by fourteen ratified Laws (citation discipline, the
Stop-and-Design invariant, universal quantification, kernel-checked gates,
memory-capability enforcement, and more), stated in full in
[`docs/REVIEW.md`](docs/REVIEW.md), and a Three-Pillar review protocol whose
one irreplaceable question is *"are we proving the right theorems?"* — see
[`CONTRIBUTING.md`](CONTRIBUTING.md) for a working summary of both, and
[`docs/VISION.md`](docs/VISION.md) for the reasoning behind them.

### Citations and external references

Every Lean declaration cites the design-document section that motivates it
(`/- REF: docs/SOME_DOC.md#some-section -/`), and `scripts/check_refs.py`
mechanically enforces that every citation resolves and every declaration
has one. This repository does not vendor or redistribute third-party
documentation prose (manuals, RFCs, specifications) to ground those models —
external grounding is by citation to canonical source URLs and content
hashes (see [`docs/REFERENCE_INDEX.md`](docs/REFERENCE_INDEX.md) for the
registry design), not by storing third-party text in the tree.

---

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). Copyright notices and
third-party attribution (for the small amount of third-party material, if
any, that actually ships in a given release) are in [`NOTICE`](NOTICE).
