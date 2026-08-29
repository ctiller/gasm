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

import Lean
import Gasm.Core.Types
import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.LEB128
import Gasm.Targets.Wasm.Binary
import Gasm.Targets.Wasm.Text

namespace Gasm.Targets.Wasm

open Gasm.Core

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- High-level function definition in a WebAssembly module. -/
structure WasmFunction where
  name       : String
  params     : List ValType     := []
  results    : List ValType    := []
  locals     : List ValType    := []
  body       : List WasmInstr  := []
  exportName : Option String   := none
  deriving Repr, Inhabited

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Initialized data segment placed at a static memory offset. -/
structure WasmDataSegment where
  offset : UInt32
  data   : ByteArray
  deriving Inhabited

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Complete WebAssembly module artifact ready for linking and serialization. -/
structure WasmModule where
  imports      : List Import          := []
  functions    : List WasmFunction    := []
  memoryPages  : Option UInt32        := some 1
  -- REF: wasm-syntax-types#limits -- the declared maximum (in pages) of this module's memory
  -- `Limits`, i.e. `Limits.max` (`Types.lean`). B8: previously this was always encoded as `none`
  -- (`encodeLimits { min := pages }`, no `max` field at all), so no module `emitWasmBinary`
  -- produced could ever exercise the "memory.grow fails because it would exceed the declared
  -- maximum" path on a real host engine -- the differential fuzzer's OOB/limit vectors
  -- (`Gasm/Targets/Wasm/SemanticsFuzzer.lean`) need the host module and the Lean model
  -- (`WasmMachineState.memMax`, `Semantics.lean`) to agree on the same declared maximum for that
  -- comparison to be meaningful at all. `none` (the default) preserves the previous no-max
  -- encoding exactly, so every existing caller (which never sets this field) is unaffected.
  memoryMaxPages : Option UInt32      := none
  dataSegments : List WasmDataSegment := []
  exports      : List Export          := []
  deriving Inhabited

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Serializes a group of local variables into code section local-entry format. -/
def encodeLocals (locals : List ValType) : ByteArray := Id.run do
  if locals.isEmpty then
    return encodeULEB128 0
  else
    let entries := locals.map (fun t => Prod.mk 1 t)
    let mut countBytes := encodeULEB128 entries.length
    for (cnt, t) in entries do
      countBytes := countBytes ++ encodeULEB128 cnt ++ ByteArray.mk #[encodeValType t]
    return countBytes

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Serializes a complete function code payload (locals + body + end byte 0x0B). -/
def encodeFunctionCode (fn : WasmFunction) : ByteArray :=
  let localsBytes := encodeLocals fn.locals
  let bodyBytes := encodeInstrList fn.body ++ ByteArray.mk #[0x0B]
  let payload := localsBytes ++ bodyBytes
  encodeULEB128 payload.size ++ payload

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Finds the index of a `FuncType` in a list of signatures. Fails closed: a not-found lookup
    returns `none` rather than silently defaulting to index `0` (the Wasm fail-closed emission contract -- a type-index
    mismatch previously encoded as a reference to type `0` instead of erroring, which is exactly
    the "wrong type, wrong index, no diagnostic" shape of bug this guards against). Callers
    (`emitWasmBinary`) must handle the failure explicitly; see `findTypeIdx_eq_none_iff` below
    for the theorem characterizing exactly when this happens. -/
def findTypeIdx (ft : FuncType) (sigs : List FuncType) : Option Nat :=
  let rec loop (i : Nat) (l : List FuncType) : Option Nat :=
    match l with
    | [] => none
    | x :: xs => if x = ft then some i else loop (i + 1) xs
  loop 0 sigs

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- **Fail-closed characterization** (Law 9: universal over every `FuncType`/list pair, not a
    pinned sample): `findTypeIdx` returns `none` exactly when `ft` is not a member of `sigs`,
    and `some i` only for an `i` that is a genuine, in-bounds occurrence of `ft` in `sigs`. In
    particular `ft ∉ sigs → findTypeIdx ft sigs = none` -- the not-found case can no longer
    silently produce `some 0`. -/
theorem findTypeIdx_eq_none_iff (ft : FuncType) (sigs : List FuncType) :
    findTypeIdx ft sigs = none ↔ ft ∉ sigs := by
  unfold findTypeIdx
  suffices h : ∀ (i : Nat) (l : List FuncType),
      findTypeIdx.loop ft i l = none ↔ ft ∉ l by
    exact h 0 sigs
  intro i l
  induction l generalizing i with
  | nil => simp [findTypeIdx.loop]
  | cons x xs ih =>
    unfold findTypeIdx.loop
    by_cases hxeq : x = ft
    · simp [hxeq]
    · simp only [hxeq, if_neg, not_false_iff]
      rw [ih (i + 1)]
      have hxeq' : ft ≠ x := Ne.symm hxeq
      simp [hxeq']

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Deduplicates function types and returns array of unique signatures. -/
def collectTypeSignatures (m : WasmModule) : List FuncType := Id.run do
  let funcTypes := m.functions.map (fun fn => { params := fn.params, results := fn.results : FuncType })
  let mut result : List FuncType := []
  for ft in funcTypes do
    if !result.contains ft then
      result := result ++ [ft]
  return result

/- REF: docs/TARGETS/WASM.md#3-binary-module-structure -/
/-- Serializes a high-level WasmModule into binary WebAssembly format (.wasm). Fails closed
    (`Except String ByteArray`, the Wasm fail-closed emission contract) if any function's signature has no matching
    entry in `typeSignatures` -- previously `findTypeIdx`'s `0`-default let such a mismatch
    silently encode a reference to the wrong function type instead of erroring. -/
def emitWasmBinary (m : WasmModule) (typeSignatures : List FuncType) : Except String ByteArray := do
  let mut bytes := wasmMagic ++ wasmVersion

  -- 1. Type Section (ID 1)
  if !typeSignatures.isEmpty then
    let mut typePayload := encodeULEB128 typeSignatures.length
    for ft in typeSignatures do
      typePayload := typePayload ++ encodeFuncType ft
    bytes := bytes ++ encodeSection 1 typePayload

  -- 2. Import Section (ID 2)
  if !m.imports.isEmpty then
    let mut impPayload := encodeULEB128 m.imports.length
    for imp in m.imports do
      impPayload := impPayload ++ encodeVectorString imp.module ++ encodeVectorString imp.name
      match imp.desc with
      | .func typeIdx =>
        impPayload := impPayload ++ ByteArray.mk #[0x00] ++ encodeULEB128 typeIdx
      | .mem memType =>
        impPayload := impPayload ++ ByteArray.mk #[0x02] ++ encodeMemType memType
    bytes := bytes ++ encodeSection 2 impPayload

  -- 3. Function Section (ID 3)
  if !m.functions.isEmpty then
    let mut funcPayload := encodeULEB128 m.functions.length
    for fn in m.functions do
      let ft : FuncType := { params := fn.params, results := fn.results }
      let typeIdx ←
        match findTypeIdx ft typeSignatures with
        | some idx => pure idx
        | none =>
          throw s!"emitWasmBinary: function '{fn.name}' has signature {repr ft} with no \
            matching entry in typeSignatures ({typeSignatures.length} candidates) -- refusing \
            to silently encode type index 0"
      funcPayload := funcPayload ++ encodeULEB128 typeIdx
    bytes := bytes ++ encodeSection 3 funcPayload

  -- 5. Memory Section (ID 5)
  if let some pages := m.memoryPages then
    let memPayload := encodeULEB128 1 ++ encodeLimits { min := pages, max := m.memoryMaxPages }
    bytes := bytes ++ encodeSection 5 memPayload

  -- 7. Export Section (ID 7)
  let numImportFuncs := m.imports.filter (fun imp => match imp.desc with | .func _ => true | _ => false) |>.length
  let mut allExports := m.exports
  let mut funcIdx := 0
  for fn in m.functions do
    if let some expName := fn.exportName then
      allExports := allExports ++ [{ name := expName, desc := .func (numImportFuncs + funcIdx) }]
    funcIdx := funcIdx + 1

  if m.memoryPages.isSome && !allExports.any (fun e => match e.desc with | .mem _ => true | _ => false) then
    allExports := allExports ++ [{ name := "memory", desc := .mem 0 }]

  if !allExports.isEmpty then
    let mut expPayload := encodeULEB128 allExports.length
    for exp in allExports do
      expPayload := expPayload ++ encodeVectorString exp.name
      match exp.desc with
      | .func fIdx =>
        expPayload := expPayload ++ ByteArray.mk #[0x00] ++ encodeULEB128 fIdx
      | .mem mIdx =>
        expPayload := expPayload ++ ByteArray.mk #[0x02] ++ encodeULEB128 mIdx
    bytes := bytes ++ encodeSection 7 expPayload

  -- 10. Code Section (ID 10)
  if !m.functions.isEmpty then
    let mut codePayload := encodeULEB128 m.functions.length
    for fn in m.functions do
      codePayload := codePayload ++ encodeFunctionCode fn
    bytes := bytes ++ encodeSection 10 codePayload

  -- 11. Data Section (ID 11)
  if !m.dataSegments.isEmpty then
    let mut dataPayload := encodeULEB128 m.dataSegments.length
    for seg in m.dataSegments do
      let offsetExpr := ByteArray.mk #[0x41] ++ encodeI32SLEB128 (Int.ofNat seg.offset.toNat) ++ ByteArray.mk #[0x0B]
      dataPayload := dataPayload ++ ByteArray.mk #[0x00] ++ offsetExpr ++ encodeULEB128 seg.data.size ++ seg.data
    bytes := bytes ++ encodeSection 11 dataPayload

  return bytes

/- REF: docs/TARGETS/WASM.md#4-text-format-wat-formatting -/
/-- Pretty-prints a WasmModule into WebAssembly Text format (.wat). -/
def emitWasmText (m : WasmModule) (typeSignatures : List FuncType := []) : String := Id.run do
  let mut lines : List String := ["(module"]

  -- Imports
  for imp in m.imports do
    match imp.desc with
    | .func typeIdx =>
      let sigStr :=
        if let some sig := typeSignatures[typeIdx]? then
          let p := sig.params.foldl (fun acc t => acc ++ s!" (param {formatValType t})") ""
          let r := sig.results.foldl (fun acc t => acc ++ s!" (result {formatValType t})") ""
          p ++ r
        else ""
      lines := lines ++ [indent 1 s!"(import \"{imp.module}\" \"{imp.name}\" (func ${imp.name}{sigStr}))"]
    | .mem _ =>
      lines := lines ++ [indent 1 s!"(import \"{imp.module}\" \"{imp.name}\" (memory 1))"]

  -- Memory
  if let some pages := m.memoryPages then
    let maxStr := match m.memoryMaxPages with | some mx => s!" {mx}" | none => ""
    lines := lines ++ [indent 1 s!"(memory (export \"memory\") {pages}{maxStr})"]

  -- Data segments
  for seg in m.dataSegments do
    let escaped := formatWatDataString seg.data
    lines := lines ++ [indent 1 s!"(data (i32.const {seg.offset}) \"{escaped}\")"]

  -- Functions
  for fn in m.functions do
    let expStr := match fn.exportName with | some e => s!" (export \"{e}\")" | none => ""
    let paramStr := fn.params.foldl (fun acc t => acc ++ s!" (param {formatValType t})") ""
    let resStr := fn.results.foldl (fun acc t => acc ++ s!" (result {formatValType t})") ""
    let localStr := fn.locals.foldl (fun acc t => acc ++ s!" (local {formatValType t})") ""
    lines := lines ++ [indent 1 s!"(func ${fn.name}{expStr}{paramStr}{resStr}{localStr}"]
    lines := lines ++ formatInstrList 2 fn.body
    lines := lines ++ [indent 1 ")"]

  lines := lines ++ [")\n"]
  return String.intercalate "\n" lines

end Gasm.Targets.Wasm
