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
import Gasm.Targets.X86_64.Registry

/-!
Compiled audit for the x86 instruction-family proof pipeline.

The filesystem-side umbrella gate has exactly one job: every `Instructions/*.lean` module must
be reachable from `Instructions.lean`.  This module owns the semantic checks.  It reads Lean's
compiled typeclass environment, derives the family of every concrete `X86_64Instruction` form
from the form's defining module, unfolds the real typed witness lists, and checks exact
multiset equality.  It also compares each round-trip theorem's fully qualified declaration type
with the closed proposition the family data determines.  Source spelling, declaration syntax,
comments, and dead identifier occurrences are therefore irrelevant.
-/

namespace Gasm.Targets.X86_64.FamilyPipelineAudit

open Lean Meta
open Gasm.Targets.X86_64.Instructions

private structure LiveForm where
  typeName : Name
  instanceExpr : Expr
  family : String

private def instructionsNamespace : Name := `Gasm.Targets.X86_64.Instructions
private def roundtripNamespace : Name := `Gasm.Targets.X86_64.RoundtripGate

private partial def listElements (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then
    return []
  if e.isAppOf ``List.cons then
    let args := e.getAppArgs
    return args[1]! :: (← listElements args[2]!)
  throwError "x86 family audit expected a reducible List expression, got:\n{e}"

private partial def eraseExact (needle : Expr) : List Expr → Option (List Expr)
  | [] => none
  | candidate :: rest =>
      if needle == candidate then some rest else (candidate :: ·) <$> eraseExact needle rest

private partial def sameTypedMultiset (expected actual : List Expr) : MetaM Bool := do
  if expected.length != actual.length then return false
  let expected ← expected.mapM whnf
  let mut remaining ← actual.mapM whnf
  for witness in expected do
    let some next := eraseExact witness remaining | return false
    remaining := next
  return remaining.isEmpty

private def familyCasesName (family : String) : Name :=
  roundtripNamespace.str (family.toLower ++ "FamilyCases")

private def familyDecoderName (family : String) : Name :=
  instructionsNamespace.str (family.toLower ++ "TryDecode")

private def familyGateName (family : String) : Name :=
  roundtripNamespace.str (family.toLower ++ "Family_roundtripGate")

private def expectedRoundtripType (family : String) : MetaM Expr := do
  let casesName := familyCasesName family
  let decoderName := familyDecoderName family
  let pred ← mkAppM ``Gasm.Targets.X86_64.RoundtripGate.decodesOk #[mkConst decoderName]
  let allCases ← mkAppM ``List.all #[mkConst casesName, pred]
  mkAppM ``Eq #[allCases, mkConst ``Bool.true]

private def declarationHasExactType (env : Environment) (declName : Name)
    (expected : Expr) : MetaM Bool := do
  let some info := env.find? declName | return false
  isDefEq info.type expected

private def wrappedCases (form : LiveForm) : MetaM (List Expr) := do
  let casesExpr := mkApp2 (mkConst ``X86_64Instruction.roundtripCases [.zero])
    (mkConst form.typeName) form.instanceExpr
  let cases ← listElements casesExpr
  cases.mapM fun instr =>
    pure <| mkApp3 (mkConst ``AnyX86_64Instruction.mk)
      (mkConst form.typeName) form.instanceExpr instr

private def liveForms (env : Environment) : MetaM (List LiveForm) := do
  let insts := Lean.Meta.instanceExtension.getState env
  let mut found : List LiveForm := []
  for (_, entry) in insts.instanceNames.toList do
    let type ← inferType entry.val
    let (params, _, body) ← forallMetaTelescopeReducing type
    unless body.isAppOf ``X86_64Instruction do continue
    -- The open existential carrier is infrastructure, not an encodable instruction family.
    if body.getAppArgs[0]!.constName? == some ``AnyX86_64Instruction then continue
    unless params.isEmpty do
      throwError "x86 family audit found a parameterized X86_64Instruction instance `{entry.val}`. \
        Finite registry membership needs a concrete instruction-form type and typed witnesses."
    let some typeName := body.getAppArgs[0]!.constName? | throwError
      "x86 family audit found an X86_64Instruction instance whose form is not a named constant: \
      `{entry.val}` has type `{type}`"
    let some moduleIdx := env.getModuleIdxFor? typeName | throwError
      "x86 family audit cannot determine the defining module for `{typeName}`"
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    unless moduleName.getPrefix == instructionsNamespace do
      throwError "x86 instruction form `{typeName}` is defined in `{moduleName}`, outside a direct \
        `Gasm.Targets.X86_64.Instructions.<Family>` module; its proof-family ownership is ambiguous"
    found := { typeName, instanceExpr := entry.val, family := moduleName.getString! } :: found
  pure found

run_cmd do
  let env ← Lean.getEnv
  Lean.Elab.Command.liftTermElabM do
    let forms ← liveForms env
    unless forms.length > 0 do
      throwError "x86 family audit found no concrete X86_64Instruction instances"
    let families := (forms.map (·.family)).eraseDups
    let mut expectedAggregate : List Expr := []
    for family in families do
      let owned := forms.filter (·.family == family)
      let mut expectedFamily : List Expr := []
      for form in owned do
        let witnesses ← wrappedCases form
        if witnesses.isEmpty then
          throwError "x86 family audit: `{form.typeName}` has no roundtripCases witnesses"
        expectedFamily := expectedFamily ++ witnesses
      let casesName := familyCasesName family
      unless env.contains casesName do
        throwError "x86 family audit: missing typed family population `{casesName}`"
      let actualFamily ← listElements (mkConst casesName)
      unless ← sameTypedMultiset expectedFamily actualFamily do
        throwError "x86 family audit: `{casesName}` is not exactly the typed multiset of the live \
          instances' roundtripCases (missing, duplicate, cross-family, or dead witness)"
      expectedAggregate := expectedAggregate ++ actualFamily

      let gateName := familyGateName family
      let gateType ← expectedRoundtripType family
      unless ← declarationHasExactType env gateName gateType do
        throwError "x86 family audit: `{gateName}` is absent or does not have exactly the closed \
          proposition determined by `{casesName}` and `{familyDecoderName family}`"

      let wrongName := (`Gasm.Targets.X86_64.FamilyPipelineAudit.WrongNamespace).str
        gateName.getString!
      if ← declarationHasExactType env wrongName gateType then
        throwError "x86 family audit self-test failed: a wrong fully qualified theorem was accepted"

      -- Adversarial controls exercise the compiled checkers, not a parallel source parser.
      if let first :: rest := expectedFamily then
        if ← sameTypedMultiset expectedFamily rest then
          throwError "x86 family audit self-test failed: an omitted typed witness was accepted"
        if ← sameTypedMultiset expectedFamily (first :: actualFamily) then
          throwError "x86 family audit self-test failed: a duplicate typed witness was accepted"
        if let some foreignForm := forms.find? (·.family != family) then
          if let foreign :: _ ← wrappedCases foreignForm then
            if ← sameTypedMultiset expectedFamily (foreign :: rest) then
              throwError "x86 family audit self-test failed: a dead/cross-family typed witness was accepted"
      let hiddenPremise := mkForall `_ BinderInfo.default (mkConst ``True) gateType
      if ← isDefEq gateType hiddenPremise then
        throwError "x86 family audit self-test failed: a hidden theorem premise was accepted"

    let aggregate ← listElements
      (mkConst ``Gasm.Targets.X86_64.Registry.allEncodableInstructions)
    unless ← sameTypedMultiset expectedAggregate aggregate do
      throwError "x86 family audit: Registry.allEncodableInstructions is not exactly the typed \
        multiset union of every compiled family population"

end Gasm.Targets.X86_64.FamilyPipelineAudit
