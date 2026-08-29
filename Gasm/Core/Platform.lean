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

import Gasm.Core.Types

/-!
Target-neutral whole-program verification substrate.

`Platform` describes an ISA/host execution profile.  Library and runtime
capabilities are supplied separately as a `CapabilityComposition`; the latter
is the argument to `VerifiedProgram`, so adding a library cannot silently
change the meaning of an existing platform proof.
-/

namespace Gasm.Core.Platform

universe u v

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The complete external input domain of a verified whole program.  A caller
    cannot replace it with a smaller test-vector type. -/
structure Environment where
  stdin            : ByteArray := ByteArray.empty
  args             : List String := []
  envVars          : List (String × String) := []
  incomingRequests : List String := []
  fileSystem       : List (String × ByteArray) := []
  clockTime        : UInt64 := 0
deriving Inhabited, BEq

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- An ISA/host profile with its actual loader, operational semantics, safety
    predicate, and serializer.  `Import` is target-owned rather than a string,
    so capability coverage cannot alias merely because two libraries chose the
    same spelling. -/
class Platform (P : Type u) where
  Artifact : Type v
  State : Type
  Observation : Type
  Import : Type
  Export : Type
  imports : Artifact → List Import
  artifactExports : Artifact → List Export
  artifactConnected : Artifact → Prop
  load : Artifact → Environment → State
  run : Artifact → State → Observation
  admissible : Artifact → State → Prop
  emit : Artifact → Except String ByteArray

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- One logical capability at a program entry boundary.  `Context` may contain
    concrete runtime values, erased ghost authority, or both.  Establishment is
    relational so equal physical states may carry different generations or
    ownership fragments. -/
structure Capability (P : Type) [Platform P] where
  Context : Type
  provides : Platform.Import (P := P) → Prop
  establishes : Platform.Artifact (P := P) → Environment →
    Platform.State (P := P) → Context → Prop

namespace Capability

/-- Empty capability row. -/
def empty (P : Type) [Platform P] : Capability P where
  Context := Unit
  provides := fun _ => False
  establishes := fun _ _ _ _ => True

/-- Product composition of two capability rows.  Shared physical placement is
    deliberately absent here; target-owned ABI realization proves that later. -/
def compose {P : Type} [Platform P] (left right : Capability P) : Capability P where
  Context := left.Context × right.Context
  provides := fun imported => left.provides imported ∨ right.provides imported
  establishes := fun artifact environment state context =>
    left.establishes artifact environment state context.1 ∧
      right.establishes artifact environment state context.2

/-- Capability provision is associative. -/
theorem compose_provides_assoc {P : Type} [Platform P]
    (a b c : Capability P) (imported : Platform.Import (P := P)) :
    (compose (compose a b) c).provides imported ↔
      (compose a (compose b c)).provides imported := by
  simp [compose, or_assoc]

/-- Capability provision is commutative. -/
theorem compose_provides_comm {P : Type} [Platform P]
    (a b : Capability P) (imported : Platform.Import (P := P)) :
    (compose a b).provides imported ↔ (compose b a).provides imported := by
  simp [compose, Or.comm]

/-- Establishment composition is associative up to the canonical reassociation
    of its dependent context product. -/
theorem compose_establishes_assoc {P : Type} [Platform P]
    (a b c : Capability P) (artifact : Platform.Artifact (P := P))
    (environment : Environment) (state : Platform.State (P := P))
    (ca : a.Context) (cb : b.Context) (cc : c.Context) :
    (compose (compose a b) c).establishes artifact environment state ((ca, cb), cc) ↔
      (compose a (compose b c)).establishes artifact environment state (ca, (cb, cc)) := by
  simp [compose, and_assoc]

/-- Establishment composition is commutative up to swapping the context pair. -/
theorem compose_establishes_comm {P : Type} [Platform P]
    (a b : Capability P) (artifact : Platform.Artifact (P := P))
    (environment : Environment) (state : Platform.State (P := P))
    (ca : a.Context) (cb : b.Context) :
    (compose a b).establishes artifact environment state (ca, cb) ↔
      (compose b a).establishes artifact environment state (cb, ca) := by
  simp [compose, And.comm]

end Capability

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- The selected composition of library/runtime capabilities for a verified
    program.  The root is a real dependent context row, not an allowlist. -/
structure CapabilityComposition (P : Type) [Platform P] where
  root : Capability P

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- The sole whole-program verification authority.  It is parameterized by an
    ISA/host platform and a composed capability row, never by a caller-chosen
    input domain.  Every environment, capability entry, platform safety fact,
    and observable behavior is mandatory evidence. -/
structure VerifiedProgram (P : Type) [Platform P] (capabilities : CapabilityComposition P) where
  name : String
  artifact : Platform.Artifact (P := P)
  exports : List (Platform.Export (P := P))
  exportsMatch : exports = Platform.artifactExports artifact
  artifactConnection : Platform.artifactConnected artifact
  spec : Environment → Platform.Observation (P := P)
  importsCovered : ∀ imported, imported ∈ Platform.imports artifact →
    capabilities.root.provides imported
  entryEstablished : ∀ environment,
    ∃ context, capabilities.root.establishes artifact environment
      (Platform.load artifact environment) context
  platformAdmissible : ∀ environment,
    Platform.admissible artifact (Platform.load artifact environment)
  traceEquivalence : ∀ environment,
    Platform.run artifact (Platform.load artifact environment) = spec environment

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Serialization is available only from the sole universal proof authority. -/
def emitVerifiedProgram {P : Type} [Platform P] {capabilities : CapabilityComposition P}
    (program : VerifiedProgram P capabilities) : Except String ByteArray :=
  Platform.emit program.artifact

/-- Marker for the only legitimate raw-emission use: a target's encoder fuzzer.
    Production target profiles deliberately do not receive this instance. -/
class FuzzingEmitter (P : Type) [Platform P] where
  emitUnchecked : Platform.Artifact (P := P) → Except String ByteArray

/-- Raw serialization requires an explicit fuzzing capability. -/
def rawEmitForFuzzing {P : Type} [Platform P] [FuzzingEmitter P]
    (artifact : Platform.Artifact (P := P)) : Except String ByteArray :=
  FuzzingEmitter.emitUnchecked artifact

end Gasm.Core.Platform
