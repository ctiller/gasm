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

namespace Spikes.GraphicsFoundation.Spirv

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Phantom roles prevent accidental interchange of SPIR-V identifiers. -/
inductive IdRole where
  | type | function | value | block
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- A generative frontend scope. The nonce is logical identity, not a serialized SPIR-V word. -/
structure ModuleScope where
  nonce : Nat
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- A scoped, role-indexed SPIR-V identifier. -/
structure Id (scope : ModuleScope) (role : IdRole) where
  word : UInt32
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
abbrev TypeId (s : ModuleScope) := Id s .type

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
abbrev FunctionId (s : ModuleScope) := Id s .function

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
abbrev ValueId (s : ModuleScope) := Id s .value

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
abbrev BlockId (s : ModuleScope) := Id s .block

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- The deliberately small compute-only instruction grammar. -/
inductive Instruction (s : ModuleScope) where
  | capabilityShader
  | memoryModelLogicalGlsl450
  | entryPointCompute (fn : FunctionId s) (name : String)
  | executionModeLocalSize (fn : FunctionId s) (x y z : UInt32)
  | typeVoid (result : TypeId s)
  | typeFunction (result returnType : TypeId s) (params : List (TypeId s))
  | functionBegin (returnType : TypeId s) (result : FunctionId s) (fnType : TypeId s)
  | functionEnd
  | label (result : BlockId s)
  | selectionMerge (merge : BlockId s)
  | branch (target : BlockId s)
  | branchConditional (condition : ValueId s) (onTrue onFalse : BlockId s)
  | returnVoid
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- A scoped module. `bound` is the first invalid serialized identifier. -/
structure Module (s : ModuleScope) where
  bound : UInt32
  instructions : List (Instruction s)
  deriving Repr, DecidableEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Validation failures are local structural findings, not Vulkan or semantic-shader errors. -/
inductive ValidationError where
  | zeroOrOutOfBoundId
  | duplicateResultId
  | undefinedBranchTarget
  | undefinedValue
  | missingComputeEntryPoint
  | missingLocalSize
  | malformedFunctionOrBlock
  | unstructuredSelection
  deriving Repr, DecidableEq, BEq

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def instructionResultId : Instruction s → Option UInt32
  | .typeVoid i => some i.word
  | .typeFunction i _ _ => some i.word
  | .functionBegin _ i _ => some i.word
  | .label i => some i.word
  | _ => none

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def instructionIds : Instruction s → List UInt32
  | .entryPointCompute f _ => [f.word]
  | .executionModeLocalSize f _ _ _ => [f.word]
  | .typeVoid i => [i.word]
  | .typeFunction i r ps => i.word :: r.word :: ps.map (fun p => p.word)
  | .functionBegin r f t => [r.word, f.word, t.word]
  | .label b => [b.word]
  | .selectionMerge b => [b.word]
  | .branch b => [b.word]
  | .branchConditional c t f => [c.word, t.word, f.word]
  | _ => []

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def blockDefinitions (xs : List (Instruction s)) : List UInt32 :=
  xs.filterMap (fun i => match i with | .label b => some b.word | _ => none)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def branchTargets (xs : List (Instruction s)) : List UInt32 :=
  xs.flatMap (fun i => match i with
    | .selectionMerge b => [b.word]
    | .branch b => [b.word]
    | .branchConditional _ t f => [t.word, f.word]
    | _ => [])

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def conditionValues (xs : List (Instruction s)) : List UInt32 :=
  xs.filterMap (fun i => match i with | .branchConditional c _ _ => some c.word | _ => none)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def isTerminator : Instruction s → Bool
  | .branch _ | .branchConditional _ _ _ | .returnVoid => true
  | _ => false

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def functionAndBlockShape (xs : List (Instruction s)) : Bool :=
  let rec go (inFunction inBlock terminated : Bool) : List (Instruction s) → Bool
    | [] => !inFunction && !inBlock
    | i :: rest =>
      match i with
      | .functionBegin _ _ _ => !inFunction && go true false false rest
      | .functionEnd => inFunction && inBlock && terminated && go false false false rest
      | .label _ => inFunction && (!inBlock || terminated) && go true true false rest
      | _ =>
        if inBlock then
          if terminated then false else go inFunction inBlock (isTerminator i) rest
        else if inFunction then false else go inFunction inBlock terminated rest
  go false false false xs

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def structuredSelections : List (Instruction s) → Bool
  | [] => true
  | .branchConditional _ _ _ :: _ => false
  | .selectionMerge _ :: .branchConditional _ _ _ :: rest => structuredSelections rest
  | _ :: rest => structuredSelections rest

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def entryFunctions (xs : List (Instruction s)) : List UInt32 :=
  xs.filterMap (fun i => match i with | .entryPointCompute f _ => some f.word | _ => none)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def definedFunctions (xs : List (Instruction s)) : List UInt32 :=
  xs.filterMap (fun i => match i with | .functionBegin _ f _ => some f.word | _ => none)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def localSizeFunctions (xs : List (Instruction s)) : List UInt32 :=
  xs.filterMap (fun i => match i with | .executionModeLocalSize f _ _ _ => some f.word | _ => none)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Validates only the explicitly selected compute grammar. -/
def validate (m : Module s) : List ValidationError :=
  let ids := m.instructions.flatMap instructionIds
  let results := m.instructions.filterMap instructionResultId
  let blocks := blockDefinitions m.instructions
  let targets := branchTargets m.instructions
  let conditions := conditionValues m.instructions
  let entries := entryFunctions m.instructions
  let functions := definedFunctions m.instructions
  let localSizes := localSizeFunctions m.instructions
  let errors := if !(ids.all (fun i => i != 0 && i < m.bound)) then [.zeroOrOutOfBoundId] else []
  let errors := if results.eraseDups.length != results.length then errors ++ [.duplicateResultId] else errors
  let errors := if !(targets.all (fun i => blocks.contains i)) then errors ++ [.undefinedBranchTarget] else errors
  -- The current grammar has no value-producing instruction. Conditional control flow therefore
  -- remains representable for frontend evolution but cannot yet receive a structural certificate.
  let errors := if !conditions.isEmpty then errors ++ [.undefinedValue] else errors
  let errors := if entries.isEmpty || !(entries.all (fun i => functions.contains i)) then errors ++ [.missingComputeEntryPoint] else errors
  let errors := if !(entries.all (fun i => localSizes.contains i)) then errors ++ [.missingLocalSize] else errors
  let errors := if !(functionAndBlockShape m.instructions) then errors ++ [.malformedFunctionOrBlock] else errors
  let errors := if !(structuredSelections m.instructions) then errors ++ [.unstructuredSelection] else errors
  errors

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- A local structural certificate. It carries no verified-emission authority. -/
structure ValidatedModule (s : ModuleScope) where
  module : Module s
  valid : validate module = []

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Attempts to construct the local structural certificate. -/
def certify (m : Module s) : Except (List ValidationError) (ValidatedModule s) :=
  match h : validate m with
  | [] => .ok { module := m, valid := h }
  | errors => .error errors

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def instructionHeader (wordCount opcode : Nat) : UInt32 :=
  (wordCount.toUInt32 <<< 16) ||| opcode.toUInt32

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
private def encodeStringWords (text : String) : List UInt32 :=
  let bytes := text.toUTF8.push 0
  let wordCount := (bytes.size + 3) / 4
  (List.range wordCount).map fun wi =>
    let base := wi * 4
    let byteAt (i : Nat) : UInt8 := if i < bytes.size then bytes.get! i else 0
    let b0 := (byteAt base).toUInt32
    let b1 := (byteAt (base + 1)).toUInt32
    let b2 := (byteAt (base + 2)).toUInt32
    let b3 := (byteAt (base + 3)).toUInt32
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Serializes one selected instruction using the hash-verified grammar opcode values. -/
def encodeInstruction : Instruction s → List UInt32
  | .capabilityShader => [instructionHeader 2 17, 1]
  | .memoryModelLogicalGlsl450 => [instructionHeader 3 14, 0, 1]
  | .entryPointCompute fn name =>
      let nameWords := encodeStringWords name
      instructionHeader (3 + nameWords.length) 15 :: 5 :: fn.word :: nameWords
  | .executionModeLocalSize fn x y z => [instructionHeader 6 16, fn.word, 17, x, y, z]
  | .typeVoid result => [instructionHeader 2 19, result.word]
  | .typeFunction result ret params =>
      instructionHeader (3 + params.length) 33 :: result.word :: ret.word :: params.map (fun p => p.word)
  | .functionBegin ret result fnType => [instructionHeader 5 54, ret.word, result.word, 0, fnType.word]
  | .functionEnd => [instructionHeader 1 56]
  | .label result => [instructionHeader 2 248, result.word]
  | .selectionMerge merge => [instructionHeader 3 247, merge.word, 0]
  | .branch target => [instructionHeader 2 249, target.word]
  | .branchConditional condition onTrue onFalse =>
      [instructionHeader 4 250, condition.word, onTrue.word, onFalse.word]
  | .returnVoid => [instructionHeader 1 253]

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Serializes a certified module to an in-memory SPIR-V word array. -/
def serializeWords (m : ValidatedModule s) : Array UInt32 :=
  #[0x07230203, 0x00010600, 0, m.module.bound, 0] ++
    (m.module.instructions.flatMap encodeInstruction).toArray

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- Minimal compute entry-point module used as a positive structural control. -/
def minimalCompute (scope : ModuleScope) : Module scope :=
  let voidTy : TypeId scope := ⟨1⟩
  let fnTy : TypeId scope := ⟨2⟩
  let mainFn : FunctionId scope := ⟨3⟩
  let entry : BlockId scope := ⟨4⟩
  { bound := 5
    instructions := [
      .capabilityShader,
      .memoryModelLogicalGlsl450,
      .entryPointCompute mainFn "main",
      .executionModeLocalSize mainFn 1 1 1,
      .typeVoid voidTy,
      .typeFunction fnTy voidTy [],
      .functionBegin voidTy mainFn fnTy,
      .label entry,
      .returnVoid,
      .functionEnd
    ] }

/- REF: docs/GRAPHICS_FOUNDATION.md#2-frontend-local-spir-v-subset -/
/-- The positive control is accepted by the selected structural validator. -/
theorem minimalCompute_valid (scope : ModuleScope) : validate (minimalCompute scope) = [] := by
  rfl

end Spikes.GraphicsFoundation.Spirv
