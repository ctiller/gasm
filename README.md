# gasm

**Proof-carrying assembly in Lean 4.**

gasm is a framework for authoring native machine code (x86-64, AArch64, WebAssembly, SPIR-V/DXIL/WGSL) annotated with formal invariants, and mechanically proving that the lowered code is computationally equivalent to a pure, high-level monadic specification.

---

## Core Architecture

For every routine and system component, three artifacts are authored and verified together:

1. **Specification** (Spec.lean): A pure Lean function or effectful monadic model (MonadConsole, MonadNetwork, MonadGraphics, etc.) defining the required semantic behavior.
2. **Program** (Program.lean): Concrete machine instructions or AST nodes in gasm's typed assembly DSL, tracking registers, memory permissions, and ABI calling conventions.
3. **Equivalence Theorem** (Equivalence.lean): A kernel-checked Lean theorem proving that evaluating the program produces identical execution traces to the specification.

Across all gasm proof domains, obligations follow the selected program/profile's applicability
closure: every reachable safety and platform duty is mandatory, while unused targets, APIs and
stronger unclaimed guarantees impose no proof burden. Reusable abstract theorems are proved once;
each implementation proves only its refinement delta and the stronger properties it advertises.
See `docs/VISION.md` and the proof-applicability audit in `docs/REVIEW.md`.

`
       ┌──────────────────────────────────────────────┐
       │     High-Level Monadic Specification         │
       │   (Spec.lean: pure mathematical model)       │
       └──────────────────────┬───────────────────────┘
                              │
                    Equivalence Proof
                 (Equivalence.lean: Lean 4)
                              │
       ┌──────────────────────▼───────────────────────┐
       │         Typed Assembly Program               │
       │ (Program.lean: x86-64, AArch64, WASM, SPIR-V)│
       └──────────────────────┬───────────────────────┘
                              │
                    Binary Emission
                              │
       ┌──────────────────────▼───────────────────────┐
       │   Native Executable (PE32+, ELF64, WASM)     │
       └──────────────────────────────────────────────┘
`

---

## Targets & Platform Support

* **x86-64**: Full binary encoding/decoding engine, instruction semantics, roundtrip fuzzers, PE32+ (Windows), ELF64 (Linux), and Bare Metal (QEMU).
* **AArch64**: General-purpose registers, addressing modes, 15 instruction families, AAPCS64 ABI, static ELF64 (Linux), and Bare Metal UART (QEMU irt).
* **WebAssembly**: Binary & text encoding, LEB128 codecs, linear memory simulation, and WASI Preview 1 integration.
* **Graphics & Shaders**: Multi-target graphics architecture across Windows (Vulkan+SPIR-V, DX12+DXIL) and WASM (Vulkan+SPIR-V, WebGPU+WGSL).

---

## Standard Library & Codecs

* **Stdlib.SmolAlloc**: Compact, bump-pointer dynamic memory allocator with payload obligations and a legacy value-level exit marker for retained backing pages.
* **Stdlib.Zlib**: Verified RFC 1950 (ZLIB), RFC 1951 (DEFLATE), and RFC 1952 (GZIP) compression/decompression with output-size bounds.
* **Stdlib.Png**: Fully verified PNG encoder/decoder with RGBA8 roundtrip soundness proofs.
* **Stdlib.Http11**: HTTP/1.1 request/response parser and routing engine.
* **Stdlib.Fmt**: Zero-allocation numeric and string formatters.

---

## Getting Started

### Prerequisites

* [Lean 4 & Lake](https://github.com/leanprover/elan) (pinned via [lean-toolchain](lean-toolchain))
* Python 3.12+ (for CI gate scripts)
* Optional: 
asm (for differential x86 encoding fuzzing), qemu-system-aarch64 (for bare-metal AArch64 tests)

### Build & Test

`sh
# Build the entire workspace (all libraries, spikes, and test binaries)
lake build

# Run citation and gate checks
python scripts/check_refs.py
python scripts/check_gates.py
lake exe check_gates_axioms

# Run target test suites and spikes
lake exe test_roundtrip
lake exe test_smolalloc
lake exe test_zlib
lake exe test_png
lake exe test_spike1_windows
lake exe test_spike4
`

---

## Documentation

* **[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)**: System design, memory models, and compilation pipeline.
* **[docs/MACRO_ASSEMBLER.md](docs/MACRO_ASSEMBLER.md)**: Composable proved fragments and the portable word-function compiler.
* **[docs/GRAPHICS_ARCHITECTURE.md](docs/GRAPHICS_ARCHITECTURE.md)**: Multi-target Vulkan/DX12/WebGPU architecture.
* **[docs/DECISIONS.md](docs/DECISIONS.md)**: Ratified architectural decisions and principles.
* **[docs/TECHNICAL_NOTES.md](docs/TECHNICAL_NOTES.md)**: Formal verification notes, TCB boundaries, and model debts.
* **[docs/ROADMAP.md](docs/ROADMAP.md)**: Future technical roadmap and planned spikes.
