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

import Gasm.Compiler.Word.StructuredCFG

namespace Gasm.Compiler.Word.StructuredPlanCompiler

open Gasm.Compiler.Word.Structured
open Gasm.Compiler.Word.StructuredCFG

namespace Plan

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- Injectively rename the stable symbolic roles of a plan. Source expressions, topology, and
    true/false orientation are unchanged. -/
def mapRole {OldScope NewScope : Type}
    (map : NodeId OldScope → NodeId NewScope) (injective : Function.Injective map) :
    {source : Structured.Expr InputContext .word} → {roles : List (NodeId OldScope)} →
      {root : NodeId OldScope} → Plan OldScope source roles root →
      Plan NewScope source (roles.map map) (map root)
  | _, _, _, .leaf role sourceNoIte => .leaf (map role) sourceNoIte
  | _, _, _, .branch role conditionNoIte truePlan falsePlan disjoint fresh => by
      let mapped := Plan.branch (map role) conditionNoIte
        (mapRole map injective truePlan) (mapRole map injective falsePlan) (by
          intro falseRole falseMember trueRole trueMember equal
          rcases List.mem_map.mp falseMember with ⟨oldFalse, oldFalseMember, rfl⟩
          rcases List.mem_map.mp trueMember with ⟨oldTrue, oldTrueMember, rfl⟩
          exact disjoint oldFalse oldFalseMember oldTrue oldTrueMember (injective equal)) (by
          intro member
          rw [List.mem_append] at member
          rcases member with falseMember | trueMember
          · rcases List.mem_map.mp falseMember with ⟨old, oldMember, equal⟩
            have same := injective equal
            subst old
            exact fresh (List.mem_append_left _ oldMember)
          · rcases List.mem_map.mp trueMember with ⟨old, oldMember, equal⟩
            have same := injective equal
            subst old
            exact fresh (List.mem_append_right _ oldMember))
      simpa only [List.map_append, List.map_singleton] using mapped

end Plan

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- The exact source subset accepted by automatic plan construction. Every selected `ite` is a
    plan node; its condition and every leaf are structurally branch-free. In particular, an `ite`
    hidden beneath `letE` is rejected rather than normalized or duplicated. -/
inductive DecisionTree : Structured.Expr InputContext .word → Type where
  | leaf {source : Structured.Expr InputContext .word} (sourceNoIte : NoIte source) :
      DecisionTree source
  | branch {condition : Structured.Expr InputContext .bool} (conditionNoIte : NoIte condition)
      {ifTrue ifFalse : Structured.Expr InputContext .word}
      (trueTree : DecisionTree ifTrue) (falseTree : DecisionTree ifFalse) :
      DecisionTree (.ite condition ifTrue ifFalse)

structure BranchFree {context : List ValueSort} {kind : ValueSort}
    (source : Structured.Expr context kind) : Type where
  proof : NoIte source

def branchFree? : {context : List ValueSort} → {kind : ValueSort} →
    (source : Structured.Expr context kind) → Option (BranchFree source)
  | _, _, .var _ => some ⟨.var⟩
  | _, _, .wordLit _ => some ⟨.wordLit⟩
  | _, _, .boolLit _ => some ⟨.boolLit⟩
  | _, _, .add lhs rhs =>
      match branchFree? lhs, branchFree? rhs with
      | some lhsProof, some rhsProof => some ⟨.add lhsProof.proof rhsProof.proof⟩
      | _, _ => none
  | _, _, .sub lhs rhs =>
      match branchFree? lhs, branchFree? rhs with
      | some lhsProof, some rhsProof => some ⟨.sub lhsProof.proof rhsProof.proof⟩
      | _, _ => none
  | _, _, .bitAnd lhs rhs =>
      match branchFree? lhs, branchFree? rhs with
      | some lhsProof, some rhsProof => some ⟨.bitAnd lhsProof.proof rhsProof.proof⟩
      | _, _ => none
  | _, _, .eq lhs rhs =>
      match branchFree? lhs, branchFree? rhs with
      | some lhsProof, some rhsProof => some ⟨.eq lhsProof.proof rhsProof.proof⟩
      | _, _ => none
  | _, _, .ult lhs rhs =>
      match branchFree? lhs, branchFree? rhs with
      | some lhsProof, some rhsProof => some ⟨.ult lhsProof.proof rhsProof.proof⟩
      | _, _ => none
  | _, _, .not value =>
      match branchFree? value with
      | some proof => some ⟨.not proof.proof⟩
      | none => none
  | _, _, .letE value body =>
      match branchFree? value, branchFree? body with
      | some valueProof, some bodyProof => some ⟨.letE valueProof.proof bodyProof.proof⟩
      | _, _ => none
  | _, _, .ite _ _ _ => none

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- Recognize exactly the first automatic decision-tree grammar. The result is indexed by the
    original source, so successful recognition cannot attach a tree to another expression. -/
def recognize : (source : Structured.Expr InputContext .word) → Option (DecisionTree source)
  | source@(.ite condition ifTrue ifFalse) =>
      match branchFree? condition, recognize ifTrue, recognize ifFalse with
      | some conditionProof, some trueTree, some falseTree =>
          some (.branch conditionProof.proof trueTree falseTree)
      | _, _, _ => none
  | source =>
      match branchFree? source with
      | some proof => some (.leaf proof.proof)
      | none => none

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- A generated stable symbolic plan. Its private role scope is part of the result, allowing plan
    composition to obtain nominal collision freedom structurally rather than through text names. -/
structure Compiled (source : Structured.Expr InputContext .word) : Type 1 where
  Scope : Type
  roles : List (NodeId Scope)
  root : NodeId Scope
  plan : Plan Scope source roles root

private def falseRole {FalseScope TrueScope : Type} (role : NodeId FalseScope) :
    NodeId (Option (Sum FalseScope TrueScope)) := ⟨some (.inl role.value)⟩

private def trueRole {FalseScope TrueScope : Type} (role : NodeId TrueScope) :
    NodeId (Option (Sum FalseScope TrueScope)) := ⟨some (.inr role.value)⟩

private theorem falseRole_injective {FalseScope TrueScope : Type} :
    Function.Injective (falseRole (FalseScope := FalseScope) (TrueScope := TrueScope)) := by
  intro lhs rhs equal
  cases lhs
  cases rhs
  simp only [falseRole, NodeId.mk.injEq, Option.some.injEq, Sum.inl.injEq] at equal
  cases equal
  rfl

private theorem trueRole_injective {FalseScope TrueScope : Type} :
    Function.Injective (trueRole (FalseScope := FalseScope) (TrueScope := TrueScope)) := by
  intro lhs rhs equal
  cases lhs
  cases rhs
  simp only [trueRole, NodeId.mk.injEq, Option.some.injEq, Sum.inr.injEq] at equal
  cases equal
  rfl

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- Compile a recognized tree to the existing stable-role plan. False and true subtrees are tagged
    into disjoint sides of `Sum`; `none` is the fresh parent role. No block or target evidence is
    selected here. -/
noncomputable def compile : {source : Structured.Expr InputContext .word} →
    DecisionTree source → Compiled source
  | _, .leaf sourceNoIte => {
      Scope := PUnit
      roles := [⟨PUnit.unit⟩]
      root := ⟨PUnit.unit⟩
      plan := .leaf ⟨PUnit.unit⟩ sourceNoIte
    }
  | _, .branch conditionNoIte trueTree falseTree => by
      let trueCompiled := compile trueTree
      let falseCompiled := compile falseTree
      let mappedFalse := Plan.mapRole
        (falseRole (FalseScope := falseCompiled.Scope) (TrueScope := trueCompiled.Scope))
        falseRole_injective falseCompiled.plan
      let mappedTrue := Plan.mapRole
        (trueRole (FalseScope := falseCompiled.Scope) (TrueScope := trueCompiled.Scope))
        trueRole_injective trueCompiled.plan
      let root : NodeId (Option (Sum falseCompiled.Scope trueCompiled.Scope)) := ⟨none⟩
      exact {
        Scope := Option (Sum falseCompiled.Scope trueCompiled.Scope)
        roles := falseCompiled.roles.map
            (falseRole (FalseScope := falseCompiled.Scope) (TrueScope := trueCompiled.Scope)) ++
          trueCompiled.roles.map
            (trueRole (FalseScope := falseCompiled.Scope) (TrueScope := trueCompiled.Scope)) ++
          [root]
        root
        plan := .branch root conditionNoIte mappedTrue mappedFalse (by
          intro falseNode falseMember trueNode trueMember equal
          rcases List.mem_map.mp falseMember with ⟨oldFalse, _, rfl⟩
          rcases List.mem_map.mp trueMember with ⟨oldTrue, _, rfl⟩
          simp [falseRole, trueRole] at equal) (by
          simp [root, falseRole, trueRole])
      }

/- REF: docs/MACRO_ASSEMBLER.md#automatic-structured-decision-plans -/
/-- Recognize and compile in one partial frontend step. Failure is a source-grammar rejection, not
    a link-time or runtime outcome. -/
noncomputable def compile? (source : Structured.Expr InputContext .word) : Option (Compiled source) :=
  (recognize source).map compile

end Gasm.Compiler.Word.StructuredPlanCompiler
