# WebAssembly Target Architecture Specification

This document defines the architecture model, instruction representation, binary encoding, and text formatting for the WebAssembly (Wasm) target in `gasm`.

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
