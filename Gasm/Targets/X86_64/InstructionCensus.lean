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
import Gasm.Targets.X86_64.Instructions

/-!
The one compiled census of x86-64 instruction forms.

Every population-sensitive gate consumes `concreteForms`: registry coverage, typed family
witnesses, global dispatch, and memory-frame theorems.  In particular, consumers must not repeat
their own less-reducing walk of `instanceExtension` or fall back to a hand-maintained type list.

The census reduces each registered instance type before recognizing the class head and reduces
the target itself, so reducible class aliases, target aliases, and alternate instance declaration
forms cannot disappear from one consumer or evade overlap/wrapper rejection.  It
then rejects parameterized or unnamed forms, forms outside a direct
`Instructions.<Family>` module, and more than one concrete instance for the same form type.  The
last condition is load-bearing: otherwise two overlapping instances could each contribute
different witnesses while ordinary typeclass synthesis gives frame or step semantics only to the
globally selected one.
-/

namespace Gasm.Targets.X86_64.InstructionCensus

open Lean Meta
open Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- One instance-extension entry after reducing its class head.  This generic intermediate is
    exposed so compiled negative controls can exercise the exact classifier with a private
    fixture class; production consumers use `ConcreteForm` through `concreteForms`. -/
structure ClassCandidate where
  target : Expr
  instanceExpr : Expr
  parameters : Array Expr

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- One admitted concrete production instruction form.  `instanceExpr` is the exact registered
    instance whose round-trip, operational, and memory-frame obligations are audited. -/
structure ConcreteForm where
  typeName : Name
  instanceExpr : Expr
  family : String

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Reduce a class target to the identity used by every later census decision. -/
def normalizeTarget (target : Expr) : MetaM Expr :=
  whnf target

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Classify every compiled instance whose reduced result has the requested class head.  This is
    the only `instanceExtension` walk used by the x86 population pipeline. -/
def classCandidates (env : Environment) (className : Name) : MetaM (List ClassCandidate) := do
  let insts := Lean.Meta.instanceExtension.getState env
  let mut found : List ClassCandidate := []
  for (_, entry) in insts.instanceNames.toList do
    let type ← inferType entry.val
    let (parameters, _, body) ← forallMetaTelescopeReducing type
    let body ← whnf body
    unless body.isAppOf className do continue
    let args := body.getAppArgs
    unless args.size == 1 do
      throwError "compiled class census expected `{className}` to have one target argument, got `{body}`"
    let target ← normalizeTarget args[0]!
    found := { target, instanceExpr := entry.val, parameters } :: found
  pure found

private def concreteTargetName? (candidate : ClassCandidate) : Option Name :=
  if candidate.parameters.isEmpty then candidate.target.constName? else none

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- All concrete candidates whose reduced target is represented more than once.  Keeping the
    candidates (rather than only their target names) lets the production diagnostic identify every
    colliding instance declaration and owner module. -/
def duplicateConcreteTargetCandidates (candidates : List ClassCandidate) : List ClassCandidate :=
  candidates.filter fun candidate =>
    match concreteTargetName? candidate with
    | some name => candidates.countP (fun other => concreteTargetName? other == some name) > 1
    | none => false

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Concrete target names represented more than once in a classified candidate list.  Kept
    separate from `concreteForms` so the overlapping-instance control tests the production
    duplicate detector directly. -/
def duplicateConcreteTargetNames (candidates : List ClassCandidate) : List Name :=
  let names := duplicateConcreteTargetCandidates candidates |>.filterMap concreteTargetName?
  (names.filter fun name => names.count name > 1).eraseDups

private def instructionsNamespace : Name := `Gasm.Targets.X86_64.Instructions

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- Wrapper exclusion is applied only after target normalization. -/
def isAnyInstructionWrapperTarget (target : Expr) : Bool :=
  target.constName? == some ``AnyX86_64Instruction

private def canonicalWrapperInstance : Name :=
  ``Gasm.Targets.X86_64.Instructions.instX86_64InstructionAnyX86_64Instruction

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- The open existential wrapper is infrastructure, but its instance still controls ordinary
    synthesis.  Require exactly the canonical declaration before excluding it from concrete-form
    obligations; otherwise a higher-priority alias-target instance could alter semantics while
    disappearing from every population audit. -/
def validateCanonicalWrapper (env : Environment) (candidates : List ClassCandidate) : MetaM Unit := do
  let wrappers := candidates.filter fun candidate =>
    isAnyInstructionWrapperTarget candidate.target
  match wrappers with
  | [candidate] =>
      unless candidate.parameters.isEmpty do
        throwError "x86 instruction census found a parameterized existential-wrapper instance: \
          `{candidate.instanceExpr}`"
      unless candidate.instanceExpr.constName? == some canonicalWrapperInstance do
        throwError "x86 instruction census expected canonical existential-wrapper instance \
          `{canonicalWrapperInstance}`, but found `{candidate.instanceExpr}`"
      let some instanceModuleIdx := env.getModuleIdxFor? canonicalWrapperInstance | throwError
        "x86 instruction census cannot determine the canonical wrapper instance module"
      let instanceModule := env.header.moduleNames[instanceModuleIdx.toNat]!
      unless instanceModule == `Gasm.Targets.X86_64.Instructions.Base do
        throwError "x86 instruction census canonical wrapper instance `{canonicalWrapperInstance}` \
          moved to unexpected module `{instanceModule}`"
  | _ =>
      let declarations := wrappers.filterMap fun candidate => candidate.instanceExpr.constName?
      throwError "x86 instruction census requires exactly one canonical \
        X86_64Instruction AnyX86_64Instruction instance, found {wrappers.length}: {declarations}"

private def declarationModule (env : Environment) (declaration : Name) : String :=
  match env.getModuleIdxFor? declaration with
  | some moduleIdx => env.header.moduleNames[moduleIdx.toNat]!.toString
  | none => "<unknown module>"

private def duplicateDiagnostic (env : Environment) (candidates : List ClassCandidate) : String :=
  String.intercalate "\n" <| candidates.filterMap fun candidate => do
    let targetName ← concreteTargetName? candidate
    let instanceName ← candidate.instanceExpr.constName?
    some s!"  target `{targetName}` in `{declarationModule env targetName}`: instance \
      `{instanceName}` in `{declarationModule env instanceName}`"

/- REF: docs/TARGETS/X86_64.md#encodable-instruction-registry-roundtrip-gate -/
/-- The unique, reduced, compiled production census.  All x86 form-population consumers must use
    this result rather than maintaining another environment walk or name manifest. -/
def concreteForms (env : Environment) : MetaM (List ConcreteForm) := do
  let candidates ← classCandidates env ``X86_64Instruction
  validateCanonicalWrapper env candidates
  let candidates := candidates.filter fun candidate =>
    !isAnyInstructionWrapperTarget candidate.target
  let duplicateCandidates := duplicateConcreteTargetCandidates candidates
  unless duplicateCandidates.isEmpty do
    throwError "x86 instruction census found overlapping concrete X86_64Instruction instances.\n\
      Each concrete form type must have exactly one registered instance because witness, step, and \
      frame semantics are indexed by that exact instance. Colliding declarations:\n\
      {duplicateDiagnostic env duplicateCandidates}"
  let mut forms : List ConcreteForm := []
  for candidate in candidates do
    unless candidate.parameters.isEmpty do
      throwError "x86 instruction census found a parameterized X86_64Instruction instance \
        `{candidate.instanceExpr}`. Finite registry membership requires a concrete form type."
    let some typeName := candidate.target.constName? | throwError
      "x86 instruction census found an X86_64Instruction instance whose concrete target is not \
      a named constant: `{candidate.instanceExpr}` targets `{candidate.target}`"
    let some moduleIdx := env.getModuleIdxFor? typeName | throwError
      "x86 instruction census cannot determine the defining module for `{typeName}`"
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    unless moduleName.getPrefix == instructionsNamespace do
      throwError "x86 instruction form `{typeName}` is defined in `{moduleName}`, outside a direct \
        `Gasm.Targets.X86_64.Instructions.<Family>` module; nested or external ownership is rejected"
    let some instanceName := candidate.instanceExpr.constName? | throwError
      "x86 instruction census found a concrete instance expression without a declaration name: \
      `{candidate.instanceExpr}`"
    let some instanceModuleIdx := env.getModuleIdxFor? instanceName | throwError
      "x86 instruction census cannot determine the defining module for instance `{instanceName}`"
    let instanceModuleName := env.header.moduleNames[instanceModuleIdx.toNat]!
    unless instanceModuleName == moduleName do
      throwError "x86 instruction form `{typeName}` is owned by `{moduleName}`, but its instance \
        `{instanceName}` is defined in `{instanceModuleName}`; form and semantics must have one \
        direct family owner"
    forms :=
      { typeName, instanceExpr := candidate.instanceExpr, family := moduleName.getString! } :: forms
  pure <| forms.toArray.qsort (fun left right => left.typeName.toString < right.typeName.toString)
    |>.toList

end Gasm.Targets.X86_64.InstructionCensus
