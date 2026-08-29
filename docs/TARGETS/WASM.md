# WebAssembly Target Architecture Specification

This document defines the architecture model, instruction representation, binary encoding, and text formatting for the WebAssembly (Wasm) target in `gasm`.

The implemented target is currently single-agent WebAssembly with unshared linear memory. Threads,
shared memories, atomic instructions, `memory.atomic.wait`/`memory.atomic.notify`, and host thread
creation are not implemented or claimed. A future threads profile must pin Core Wasm semantics
separately from its embedding: browser main agents, browser workers, Node, and WASI may expose
different blocking and lifecycle contracts. A synchronous parking implementation is eligible only
for an agent whose embedding proves it may block; a non-blocking main agent instead needs a
try-acquire, asynchronous continuation, or worker-offload contract rather than a fake blocking wait.
JavaScript `Atomics.wait`/`Atomics.waitAsync` are embedding APIs distinct from Wasm
`memory.atomic.wait32`/`memory.atomic.wait64`; a browser main-agent restriction must not be
presented as a Core Wasm rule.

That future profile must preserve the pinned Core threads model rather than map it through the CPU
v1 vocabulary by analogy. In particular it must represent Core Wasm's sequentially consistent-only
atomic operations, its specified racy non-atomic/tearing outcomes rather than importing C/C++ data-
race undefined behavior, both 32- and 64-bit wait comparisons, and notify's own result/visibility
rules. With multi-memory, a reference/location includes the store/module memory instance and memory
index plus offset; one flat numeric offset is not a global address or alias proof. Each admitted
engine/embedding profile separately proves shared-memory creation, agent lifecycle, blocking
eligibility and differential-validation coverage.

Shared `memory.grow` is also part of the threads intake rather than an ordinary allocator footnote.
The selected threads snapshot must pin the required maximum, successful sequentially consistent
length RMW and returned old size, and failed growth's sequentially consistent length read, `-1`
result and unchanged extent. Any two successful concurrent grows whose deltas are both nonzero must
return distinct old extents and establish nonoverlapping newly zero-initialized ranges. A successful
zero-delta grow allocates no range and may return the same old extent as another concurrent grow. The
profile also states the event and bounds observation that permit another agent to address each newly
allocated range. The embedding intake separately pins
`SharedArrayBuffer` identity/refresh behavior, fixed or resizable buffer lengths, and what existing
typed views can address after another agent grows the memory. A successful or failed grow result does
not manufacture exclusive authority; allocation and subdivision still require the checked
provenance/authority protocol.

The Core 3.0 pages currently registered in `references.json` do not pin the separate threads
proposal, so the preceding paragraph is a future intake checklist, not an implemented semantic
claim. That intake must choose whether gasm exposes the full defined-racy model or verifies a DRF
subset and proves its refinement into the full model. It must also pin unshared-memory trap/zero
outcomes, the proposal's non-spurious suspended-wait behavior, waiter-queue/SC ordering, host-call
reentrancy, traps and termination, and embedding interruption/cancellation. Wasm wait/notify receives
its own adapter: it does not inherit Linux futex's scheduler-only/no-memory-edge theorem merely
because both APIs wait on an address.

If the selected snapshot retains a transitive Wasm happens-before relation, a relation-specific
clock may cache it only after the profile proof; that does not make the same clock universal for
SPIR-V/Vulkan or other nontransitive relations.

---

## 1. WebAssembly Machine Model

WebAssembly is a stack-based virtual machine operating over typed values:
- `i32`: 32-bit integer
- `i64`: 64-bit integer
- `f32`: 32-bit IEEE 754 floating point
- `f64`: 64-bit IEEE 754 floating point

The machine state consists of:
- **Operand Stack**: Evaluates expression values in LIFO order.
- **Locals**: Function-local storage indexed by zero-based integer index, initialized to parameters and zero.
- **Linear Memory**: Continuous byte array addressable by 32-bit byte offsets, organized in 64 KiB pages.
- **Globals**: Module-level mutable or immutable typed state variables.
- **Control Stack**: Structured labels corresponding to `block`, `loop`, and `if` blocks.

---

## 2. Structured AST & Control Flow

WebAssembly enforces structured control flow with well-nested blocks:
- `block bt instrs`: Introduces a forward branch target at the end of the block.
- `loop bt instrs`: Introduces a backward branch target at the start of the loop.
- `if_else bt then_instrs else_instrs`: Evaluates condition on stack and branches to either sequence.
- `br depth`: Unconditional branch out of `depth` enclosing blocks/loops.
- `br_if depth`: Conditional branch if stack top is non-zero.
- `return`: Returns immediately from the current function.
- `call func_idx`: Invokes a function by index.

---

## 3. Binary Module Structure

A valid WebAssembly binary module starts with a 4-byte magic number `\0asm` (`0x00 0x61 0x73 0x6D`) followed by a 4-byte version `0x01 0x00 0x00 0x00`.

Sections are encoded with 1-byte section ID followed by LEB128 payload length:
1. **Type Section (ID 1)**: Function signatures (`FuncType`).
2. **Import Section (ID 2)**: Imported functions, tables, memories, and globals.
3. **Function Section (ID 3)**: Signature indices for functions defined in the module.
4. **Table Section (ID 4)**: Indirect function call tables.
5. **Memory Section (ID 5)**: Linear memory limits (min, max pages).
6. **Global Section (ID 6)**: Global definitions and initializers.
7. **Export Section (ID 7)**: Named exported items.
8. **Start Section (ID 8)**: Optional start function index.
9. **Element Section (ID 9)**: Table initializers.
10. **Code Section (ID 10)**: Function bodies (locals count + bytecode stream terminated with `0x0B`).
11. **Data Section (ID 11)**: Active memory segment data payloads with offset expressions.

---

## 4. Text Format (WAT) Formatting

The WebAssembly text format (`.wat`) uses S-expressions with indentation:
- Module wrapper: `(module ...)`
- Imports: `(import "mod" "name" (func $name (param ...) (result ...)))`
- Memory: `(memory (export "memory") 1)`
- Data segments: `(data (i32.const offset) "string\00")`
- Functions: `(func $name (export "name") (param ...) (result ...) (local ...) ...)`
- Instructions: Formatted in indented tree or linear S-expressions.
