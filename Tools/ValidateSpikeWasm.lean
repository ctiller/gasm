/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Gasm.Targets.WASI.ABI
import Spikes.Spike1Hello.Wasm.Equivalence
import Spikes.Spike2Fibonacci.Wasm.Equivalence
import Spikes.Spike3SortLines.Wasm.Equivalence
import Spikes.Spike4HttpServer.Equivalence
import Spikes.Spike5Gzip.Equivalence

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-!
  # Spike Wasm validator differential (the Wasm fail-closed emission contract)

  the adversarial review's finding: the Wasm control-flow fuzzer's V8/Node differential oracle validates only
  fuzzer-synthesized modules -- it has never validated a single spike-emitted `.wasm` module.
  This tool closes that gap: it emits every spike's `VerifiedWasmProgram` through the same
  `emitVerifiedWasmBinary` path the `spikeN_*_wasm` executables use, feeds each result through
  Node's `WebAssembly.validate`, and applies a byte-flip negative control to every module checked
  -- Law 13(4)'s mandatory positive-and-negative control-vector discipline for harnesses that
  interact with the world (an engine, here) and therefore cannot themselves be theorems -- to
  demonstrate the validator is not failing open.

  Exit code is nonzero if any spike's emission fails, any spike's emitted module is REJECTED by
  the validator, or any byte-flip control is (wrongly) ACCEPTED.
-/

open Gasm.Targets.WASI
open Gasm.Targets.Wasm

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Runs `node -e "... WebAssembly.validate(...) ..."` on `bytes` (via a temp file) and reports
    whether the engine accepted it as a well-formed, type-correct Wasm module. `WebAssembly.validate`
    is synchronous and does not require resolving imports (unlike `instantiate`), so it applies
    uniformly to every spike's module regardless of its WASI import surface. -/
def runValidate (bytes : ByteArray) (tmpPath : String) : IO Bool := do
  IO.FS.writeBinFile tmpPath bytes
  let escapedPath := tmpPath.replace "\\" "\\\\"
  let nodeScript :=
    "const fs = require('fs'); const b = fs.readFileSync('" ++ escapedPath ++
    "'); process.stdout.write(WebAssembly.validate(b) ? 'VALID' : 'INVALID');"
  let child ← IO.Process.spawn {
    cmd := "node"
    args := #["-e", nodeScript]
    stdout := .piped
    stderr := .piped
  }
  let stdout ← child.stdout.readToEnd
  let _ ← child.wait
  return stdout.trimAscii.toString == "VALID"

/- REF: wasm-binary-modules#modules-1 -/
/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Negative control (Law 13(4): a harness that interacts with the world must demonstrably
    reject a known-bad input, not merely claim to): flips one byte of an otherwise-valid module.

    Empirically (see TC20 completion notes), flipping an arbitrary *middle* byte is NOT a
    reliable corruption strategy for Wasm binaries: a flip landing inside a UTF-8 data
    segment, an LEB128 operand, or certain opcode positions can still parse as a *different but
    structurally well-formed* module, so `WebAssembly.validate` legitimately accepts it -- this
    was observed directly on spike2's module during development of this gate. That is a
    property of Wasm's binary format, not a validator bug. To get an unconditional negative
    control, this flips byte 0 of the mandatory 4-byte magic number (`\0asm`, REF
    wasm-binary-modules#modules-1) instead: every conformant engine
    checks the magic number before anything else, so corrupting it is guaranteed-rejected
    regardless of a module's internal content. -/
def byteFlip (bytes : ByteArray) : ByteArray :=
  if bytes.size == 0 then bytes
  else bytes.set! 0 (bytes.get! 0 ^^^ 0xFF)

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Runs the byte-flip negative control against one already-validated module's bytes and
    returns whether the control held (i.e. the corrupted module was correctly rejected). -/
def checkNegativeControl (name : String) (bytes : ByteArray) : IO Bool := do
  let corruptPath := s!".tmp_validate_{name}_corrupt.wasm"
  let corruptOk ← runValidate (byteFlip bytes) corruptPath
  if corruptOk then
    IO.eprintln s!"[!] {name}: byte-flip negative control was ACCEPTED -- validator failed open, FAIL"
    return false
  else
    IO.println s!"[+] {name}: byte-flip negative control correctly REJECTED -- PASS"
    return true

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Emits, writes, and validates one spike's module, then immediately runs the byte-flip
    negative control against that same module's bytes. Returns whether both the positive
    validation and the negative control passed. -/
def checkModule (name : String) (bytesE : Except String ByteArray) : IO Bool := do
  match bytesE with
  | .error e =>
    IO.eprintln s!"[!] {name}: emission FAILED ({e}) -- treating as a gate failure"
    return false
  | .ok bytes =>
    let validPath := s!".tmp_validate_{name}.wasm"
    let ok ← runValidate bytes validPath
    if ok then
      IO.println s!"[+] {name}: WebAssembly.validate ACCEPTED ({bytes.size} bytes) -- PASS"
    else
      IO.eprintln s!"[!] {name}: WebAssembly.validate REJECTED a spike-emitted module -- FAIL"
    let controlOk ← checkNegativeControl name bytes
    return ok && controlOk

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Hand-assembles a minimal single-function `() -> i32` module whose body is exactly
    `i32.const <opBytes>; end`, bypassing the normal `WasmInstr`/`encodeInstr` pipeline (whose
    `.i32_const` case only ever carries a `UInt32` operand and so can never itself produce an
    out-of-i32-range encoding). This directly exercises what `encodeI32SLEB128` emits when handed
    a value outside the i32 range -- the scenario `encodeI32SLEB128_exceeds_i32_budget_inst` in
    `Gasm/Targets/Wasm/LEB128.lean` proves produces a 6-byte sequence. -/
def malformedI32ConstModule (opBytes : ByteArray) : ByteArray :=
  let typeSec := encodeSection 1
    (encodeULEB128 1 ++ encodeFuncType { params := [], results := [ValType.i32] })
  let funcSec := encodeSection 3 (encodeULEB128 1 ++ encodeULEB128 0)
  let body := encodeULEB128 0 ++ ByteArray.mk #[0x41] ++ opBytes ++ ByteArray.mk #[0x0B]
  let codeSec := encodeSection 10 (encodeULEB128 1 ++ (encodeULEB128 body.size ++ body))
  wasmMagic ++ wasmVersion ++ typeSec ++ funcSec ++ codeSec

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- Ties the `encodeI32SLEB128_exceeds_i32_budget_inst` witness (LEB128.lean) to a real
    validator run: embeds the actual 6-byte `encodeI32SLEB128 (2 ^ 40)` output as an `i32.const`
    operand and confirms `WebAssembly.validate` rejects it, while a normal, in-range `i32.const`
    in the same module shape validates fine (so the rejection is specifically about the
    out-of-range operand, not some unrelated defect in the hand-assembled module). -/
def checkI32OverflowWitness : IO Bool := do
  let overLongOperand := encodeI32SLEB128 (2 ^ 40 : Int)
  let malformed := malformedI32ConstModule overLongOperand
  let malformedOk ← runValidate malformed ".tmp_validate_i32_overflow_witness.wasm"

  let normalOperand := encodeI32SLEB128 (100 : Int)
  let normal := malformedI32ConstModule normalOperand
  let normalOk ← runValidate normal ".tmp_validate_i32_overflow_control.wasm"

  if malformedOk then
    IO.eprintln "[!] i32-overflow witness: WebAssembly.validate WRONGLY ACCEPTED an \
      out-of-i32-range i32.const operand (encodeI32SLEB128 (2^40), 6 bytes) -- FAIL"
  else
    IO.println "[+] i32-overflow witness: WebAssembly.validate correctly REJECTED an \
      out-of-i32-range i32.const operand (encodeI32SLEB128 (2^40), 6 bytes) -- PASS"
  if !normalOk then
    IO.eprintln "[!] i32-overflow witness: sanity control (i32.const 100, in-range) was \
      REJECTED -- the hand-assembled module shape itself is broken, witness is inconclusive -- FAIL"
  else
    IO.println "[+] i32-overflow witness: sanity control (i32.const 100, in-range) validated -- PASS"
  return (!malformedOk) && normalOk

/- REF: docs/REVIEW.md#law-13-findings-become-gates-the-ratchet-law -/
/-- CLI entry point: runs the full validator differential (5 spike modules, positive +
    byte-flip-negative, plus the i32-overflow witness) and exits nonzero on any failure so this
    is wireable as a real gate. -/
def main : IO UInt32 := do
  IO.println "================================================================================"
  IO.println "  Spike Wasm Validator Differential (WebAssembly.validate vs every spike module)"
  IO.println "================================================================================"

  let r1 ← checkModule "spike1_hello"
    (emitVerifiedWasmBinary Spikes.Spike1Hello.Wasm.spike1VerifiedWasmProgram)
  let r2 ← checkModule "spike2_fibonacci"
    (emitVerifiedWasmBinary Spikes.Spike2Fibonacci.Wasm.spike2VerifiedWasmProgram)
  let r3 ← checkModule "spike3_sort_lines"
    (emitVerifiedWasmBinary Spikes.Spike3SortLines.Wasm.spike3VerifiedWasmProgram)
  let r4 ← checkModule "spike4_http_server"
    (emitVerifiedWasmBinary Spikes.Spike4HttpServer.spike4WasmVerifiedProgram)
  let r5 ← checkModule "spike5_gzip"
    (emitVerifiedWasmBinary Spikes.Spike5Gzip.spike5WasmVerifiedProgram)
  let r6 ← checkI32OverflowWitness

  let allOk := r1 && r2 && r3 && r4 && r5 && r6
  IO.println "--------------------------------------------------------------------------------"
  if allOk then
    IO.println "Summary: ALL spike Wasm modules validated; every byte-flip negative control held. PASS"
    return 0
  else
    IO.eprintln "Summary: at least one spike module failed validation, or the negative control \
      did not hold. FAIL"
    return 1
