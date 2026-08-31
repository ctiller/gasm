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

import Gasm.Targets.X86_64.InstructionCensus

/-!
Compiled controls for the shared instance census.  The fixtures use a private class, so they do
not enlarge the production x86 registry, but they enter Lean's real `instanceExtension` and are
classified by the exact same reducing function as production forms.  This covers declaration
syntax that a filesystem/source parser cannot recognize reliably and proves that overlapping
concrete instances are visible to the duplicate detector.
-/

namespace Gasm.Targets.X86_64.InstructionCensusControls

open Lean Meta
open Gasm.Targets.X86_64.InstructionCensus

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private class FixtureInstruction (α : Type) where
  token : Nat

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure AnonymousForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance : FixtureInstruction AnonymousForm where token := 1

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure NamedForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance namedFormInstance : FixtureInstruction NamedForm where token := 2

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure AttributeDefForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
set_option warn.classDefReducibility false in
@[instance] private def attributeDefFormInstance : FixtureInstruction AttributeDefForm where token := 3

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure ReducibleAliasForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private abbrev FixtureInstructionAlias := FixtureInstruction

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
set_option warn.classDefReducibility false in
@[instance] private def reducibleAliasFormInstance : FixtureInstructionAlias ReducibleAliasForm where
  token := 4

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure ParameterizedForm (width : Nat)

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance (width : Nat) : FixtureInstruction (ParameterizedForm width) where token := width

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure OverlappingForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance overlappingFormInstanceA : FixtureInstruction OverlappingForm where token := 5

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance (priority := 2000) overlappingFormInstanceB : FixtureInstruction OverlappingForm where
  token := 6

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- A target alias must reduce to the same census identity as its underlying form. -/
private abbrev OverlappingFormAlias := OverlappingForm

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance overlappingFormAliasInstance : FixtureInstruction OverlappingFormAlias where
  token := 7

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private structure FixtureWrapper

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private abbrev FixtureWrapperAlias := FixtureWrapper

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
private instance fixtureWrapperAliasInstance : FixtureInstruction FixtureWrapperAlias where
  token := 8

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- The production existential wrapper itself also has an alias control: normalization must make
    the alias indistinguishable from `AnyX86_64Instruction` before wrapper exclusion. -/
private abbrev AnyInstructionWrapperAlias :=
  Gasm.Targets.X86_64.Instructions.AnyX86_64Instruction

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- A registered alias-target wrapper instance is the dangerous case: ordinary synthesis can
    select it, so the census must reject it before wrapper exclusion. -/
private instance (priority := 2000) aliasAnyInstructionWrapperInstance :
    Gasm.Targets.X86_64.Instructions.X86_64Instruction AnyInstructionWrapperAlias :=
  Gasm.Targets.X86_64.Instructions.instX86_64InstructionAnyX86_64Instruction

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Frame-shaped fixture whose proposition depends on the selected instruction instance. -/
private def FixtureFrame {α : Type} [FixtureInstruction α] (_ : α) : Prop :=
  FixtureInstruction.token (α := α) = 6

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Ordinary synthesis selects the higher-priority overlapping instance.  The compiled control
    below confirms that this theorem does not cover the other registered instance. -/
private theorem selectedOverlappingFrame : FixtureFrame OverlappingForm.mk := by rfl

run_cmd do
  let env ← Lean.getEnv
  Lean.Elab.Command.liftTermElabM do
    let candidates ← classCandidates env ``FixtureInstruction
    let hasConcrete (name : Name) := candidates.any fun candidate =>
      candidate.parameters.isEmpty && candidate.target.constName? == some name
    for name in [``AnonymousForm, ``NamedForm, ``AttributeDefForm, ``ReducibleAliasForm] do
      unless hasConcrete name do
        throwError "instruction census control: alternate compiled instance form was not classified: `{name}`"
    let parameterized := candidates.filter fun candidate =>
      candidate.target.getAppFn.constName? == some ``ParameterizedForm
    match parameterized with
    | [candidate] =>
        unless !candidate.parameters.isEmpty do
          throwError "instruction census control: parameterized instance lost its binders"
    | _ =>
        throwError "instruction census control: parameterized instance was not classified exactly once"
    let duplicates := duplicateConcreteTargetNames candidates
    unless duplicates == [``OverlappingForm] do
      throwError "instruction census control: overlapping concrete instances were not rejected exactly; \
        duplicate targets were {duplicates}"
    let overlapCandidates := duplicateConcreteTargetCandidates candidates
    unless overlapCandidates.length == 3 && overlapCandidates.all (fun candidate =>
        candidate.target.constName? == some ``OverlappingForm) do
      throwError "instruction census control: a target alias evaded normalized overlap detection"
    let wrapperCandidates := candidates.filter fun candidate =>
      candidate.target.constName? != some ``FixtureWrapper
    unless wrapperCandidates.length + 1 == candidates.length do
      throwError "instruction census control: a wrapper target alias evaded normalized exclusion"
    let normalizedProductionWrapper ← normalizeTarget (mkConst ``AnyInstructionWrapperAlias)
    unless isAnyInstructionWrapperTarget normalizedProductionWrapper do
      throwError "instruction census control: an alias of AnyX86_64Instruction evaded production \
        wrapper exclusion"
    let some frameInfo := env.find? ``selectedOverlappingFrame |
      throwError "instruction census control: selected overlapping frame theorem is missing"
    let expectedA := mkApp3 (mkConst ``FixtureFrame) (mkConst ``OverlappingForm)
      (mkConst ``overlappingFormInstanceA) (mkConst ``OverlappingForm.mk)
    let expectedB := mkApp3 (mkConst ``FixtureFrame) (mkConst ``OverlappingForm)
      (mkConst ``overlappingFormInstanceB) (mkConst ``OverlappingForm.mk)
    let coversA ← isDefEq frameInfo.type expectedA
    let coversB ← isDefEq frameInfo.type expectedB
    unless !coversA && coversB do
      throwError "instruction census control: an ordinary frame theorem did not remain tied to \
        only the globally selected overlapping instance"
    unless candidates.length == 9 do
      throwError "instruction census control: expected nine compiled fixture instances, found \
        {candidates.length}"

run_cmd do
  let env ← Lean.getEnv
  Lean.Elab.Command.liftTermElabM do
    let candidates ← classCandidates env
      ``Gasm.Targets.X86_64.Instructions.X86_64Instruction
    let wrappers := candidates.filter fun candidate =>
      isAnyInstructionWrapperTarget candidate.target
    unless wrappers.length == 2 do
      throwError "instruction census control: expected canonical and hostile alias wrapper \
        instances, found {wrappers.length}"
    try
      validateCanonicalWrapper env candidates
      throwError "instruction census control: hostile alias wrapper instance was accepted"
    catch error =>
      let message ← error.toMessageData.toString
      unless message.contains "exactly one canonical" &&
          message.contains "instX86_64InstructionAnyX86_64Instruction" &&
          message.contains "aliasAnyInstructionWrapperInstance" do
        throwError "instruction census control: wrapper rejection did not identify both compiled \
          declarations: {message}"

end Gasm.Targets.X86_64.InstructionCensusControls
