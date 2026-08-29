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
import Gasm.Core.AbiContext

/-!
Target-neutral whole-program verification substrate.

`Platform` describes an ISA/host execution profile.  Library and runtime
capabilities are supplied separately as a `CapabilityComposition`; the latter
is the argument to `VerifiedProgram`, so adding a library cannot silently
change the meaning of an existing platform proof.
-/

namespace Gasm.Core.Platform

universe u v

/-- Versioned nominal identity for an external provider protocol.  Target
    profiles decide how a key is linked and which runtime families support it;
    the key itself carries no caller-authored semantic predicate. -/
structure ProviderProtocolKey where
  protocolNamespace : String
  operation : String
  version : Nat
deriving DecidableEq, BEq

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- The complete external input domain of a verified whole program.  A caller
    cannot replace it with a smaller test-vector type. -/
structure Environment where
  stdin            : ByteArray := ByteArray.empty
  args             : List String := []
  envVars          : List (String × String) := []
  incomingRequests : List ByteArray := []
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
  RuntimeContext : Type
  Import : Type
  /-- Target-owned identity for one concrete provider implementation.  Provider
      identities cannot be minted by a library capability. -/
  Provider : Type
  BoundaryWorld : Type
  BoundaryKey : Type
  BoundaryTarget : Type
  boundarySpec : BoundaryContextSpec BoundaryWorld BoundaryKey
  boundarySemantics : TargetBoundarySemantics BoundaryTarget
  imports : Artifact → List Import
  /-- Which typed imports are implemented by a target-owned provider. -/
  providerProvides : Provider → Import → Prop
  /-- The final emitted artifact is linked to this provider. -/
  providerLinked : Artifact → Provider → Prop
  /-- The concrete runtime context executes this provider as linked in the
      selected final artifact. Runtime support is artifact-indexed so targets
      can state it at realized call targets instead of imposing unrelated
      global-state obligations on every consumer. -/
  runtimeSupports : RuntimeContext → Artifact → Provider → Prop
  boundaryArtifact : Artifact → boundarySemantics.Artifact
  artifactConnected : Artifact → Prop
  load : Artifact → Environment → State
  run : RuntimeContext → Artifact → State → Observation
  admissible : RuntimeContext → Artifact → State → Prop
  emit : Artifact → Except String ByteArray

/- REF: docs/ABI_CONTEXT.md#4-dependent-obligation-transitions -/
/-- One logical capability at a program entry boundary.  `Context` may contain
    concrete runtime values, erased ghost authority, or both.  Establishment is
    relational so equal physical states may carry different generations or
    ownership fragments. -/
structure Capability (P : Type) [Platform P] where
  Context : Type
  /-- Selected target-owned implementations.  Logical capabilities can select
      provider identities, but cannot define what they provide, how they link,
      or which runtime implements them. -/
  providers : List (Platform.Provider (P := P))
  establishes : Platform.Artifact (P := P) → Environment →
    Platform.State (P := P) → Context → Prop

namespace Capability

/-- Empty capability row. -/
def empty (P : Type) [Platform P] : Capability P where
  Context := Unit
  providers := []
  establishes := fun _ _ _ _ => True

/-- Product composition of two capability rows.  Shared physical placement is
    deliberately absent here; target-owned ABI realization proves that later. -/
def compose {P : Type} [Platform P] (left right : Capability P) : Capability P where
  Context := left.Context × right.Context
  providers := left.providers ++ right.providers
  establishes := fun artifact environment state context =>
    left.establishes artifact environment state context.1 ∧
      right.establishes artifact environment state context.2

/-- Capability provider selection is associative. -/
theorem compose_providers_assoc {P : Type} [Platform P]
    (a b c : Capability P) :
    (compose (compose a b) c).providers =
      (compose a (compose b c)).providers := by
  simp [compose, List.append_assoc]

/-- Capability provider selection is commutative up to permutation. -/
theorem compose_providers_comm {P : Type} [Platform P]
    (a b : Capability P) :
    ((compose a b).providers.Perm (compose b a).providers) := by
  simp [compose, List.perm_append_comm]

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
  /-- Target lowering of the composed logical context. This is the only
      runtime value passed to platform execution; capabilities therefore
      cannot be decorative import claims. -/
  realize : Platform.Artifact (P := P) → root.Context →
    Platform.RuntimeContext (P := P)
  /-- Runtime support is proved once for every selected provider at any final
      artifact to which that provider is validly linked. Consumers reuse this
      certificate rather than replaying target/link reasoning per program. -/
  realizeSupports : ∀ context artifact provider, provider ∈ root.providers →
    Platform.providerLinked artifact provider →
    Platform.runtimeSupports (realize artifact context) artifact provider

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- The sole whole-program verification authority.  It is parameterized by an
    ISA/host platform and a composed capability row, never by a caller-chosen
    input domain.  Every environment, capability entry, platform safety fact,
    and observable behavior is mandatory evidence. -/
structure VerifiedProgram (P : Type) [Platform P] (capabilities : CapabilityComposition P) where
  name : String
  artifact : Platform.Artifact (P := P)
  exports : @VerifiedExportSet
    (Platform.BoundaryWorld (P := P))
    (Platform.BoundaryKey (P := P))
    (Platform.BoundaryTarget (P := P))
    (Platform.boundarySpec (P := P))
    (Platform.boundarySemantics (P := P))
  exportsArtifact : exports.artifact = Platform.boundaryArtifact artifact
  artifactConnection : Platform.artifactConnected artifact
  spec : Environment → Platform.Observation (P := P)
  importsCovered : ∀ imported, imported ∈ Platform.imports artifact →
    ∃ provider, provider ∈ capabilities.root.providers ∧
      Platform.providerProvides provider imported
  providersLinked : ∀ provider, provider ∈ capabilities.root.providers →
    Platform.providerLinked artifact provider
  entryContext : Environment → capabilities.root.Context
  entryEstablished : ∀ environment,
    capabilities.root.establishes artifact environment
      (Platform.load artifact environment) (entryContext environment)
  platformAdmissible : ∀ environment,
    Platform.admissible (capabilities.realize artifact (entryContext environment))
      artifact (Platform.load artifact environment)
  traceEquivalence : ∀ environment,
    Platform.run (capabilities.realize artifact (entryContext environment))
      artifact (Platform.load artifact environment) = spec environment

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Final-artifact and public-boundary evidence, reusable independently of a
    program's behavior theorem. -/
structure ProgramArtifactCertificate (P : Type) [Platform P] where
  artifact : Platform.Artifact (P := P)
  exports : @VerifiedExportSet
    (Platform.BoundaryWorld (P := P))
    (Platform.BoundaryKey (P := P))
    (Platform.BoundaryTarget (P := P))
    (Platform.boundarySpec (P := P))
    (Platform.boundarySemantics (P := P))
  exportsArtifact : exports.artifact = Platform.boundaryArtifact artifact
  artifactConnection : Platform.artifactConnected artifact

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Import coverage and final-provider linkage. This certificate contains no
    entry-state or behavioral obligation. -/
structure ProgramProviderCertificate (P : Type) [Platform P]
    (capabilities : CapabilityComposition P)
    (artifact : Platform.Artifact (P := P)) where
  importsCovered : ∀ imported, imported ∈ Platform.imports artifact →
    ∃ provider, provider ∈ capabilities.root.providers ∧
      Platform.providerProvides provider imported
  providersLinked : ∀ provider, provider ∈ capabilities.root.providers →
    Platform.providerLinked artifact provider

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Canonical-environment entry-context establishment, reusable by safety and
    behavior certificates for the same artifact. -/
structure ProgramEntryCertificate (P : Type) [Platform P]
    (capabilities : CapabilityComposition P)
    (artifact : Platform.Artifact (P := P)) where
  entryContext : Environment → capabilities.root.Context
  entryEstablished : ∀ environment,
    capabilities.root.establishes artifact environment
      (Platform.load artifact environment) (entryContext environment)

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Target safety/admissibility for the exact realized artifact and established
    entry context. -/
structure ProgramAdmissibilityCertificate (P : Type) [Platform P]
    (capabilities : CapabilityComposition P)
    (artifact : Platform.Artifact (P := P))
    (entry : ProgramEntryCertificate P capabilities artifact) where
  platformAdmissible : ∀ environment,
    Platform.admissible (capabilities.realize artifact (entry.entryContext environment))
      artifact (Platform.load artifact environment)

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- Universal observable refinement, deliberately independent of artifact
    serialization, provider lookup, and export-layout proofs. -/
structure ProgramBehaviorCertificate (P : Type) [Platform P]
    (capabilities : CapabilityComposition P)
    (artifact : Platform.Artifact (P := P))
    (entry : ProgramEntryCertificate P capabilities artifact) where
  spec : Environment → Platform.Observation (P := P)
  traceEquivalence : ∀ environment,
    Platform.run (capabilities.realize artifact (entry.entryContext environment))
      artifact (Platform.load artifact environment) = spec environment

namespace VerifiedProgram

/- REF: docs/ARCHITECTURE.md#21-platform-neutral-whole-program-boundary -/
/-- The general whole-program composition law. Each argument proves one
    ownership-scoped certificate; their dependent indices force agreement on
    the platform, capability composition, final artifact, and entry relation. -/
def compose {P : Type} [Platform P] {capabilities : CapabilityComposition P}
    (name : String)
    (artifact : ProgramArtifactCertificate P)
    (providers : ProgramProviderCertificate P capabilities artifact.artifact)
    (entry : ProgramEntryCertificate P capabilities artifact.artifact)
    (admissibility : ProgramAdmissibilityCertificate P capabilities artifact.artifact entry)
    (behavior : ProgramBehaviorCertificate P capabilities artifact.artifact entry) :
    VerifiedProgram P capabilities where
  name := name
  artifact := artifact.artifact
  exports := artifact.exports
  exportsArtifact := artifact.exportsArtifact
  artifactConnection := artifact.artifactConnection
  spec := behavior.spec
  importsCovered := providers.importsCovered
  providersLinked := providers.providersLinked
  entryContext := entry.entryContext
  entryEstablished := entry.entryEstablished
  platformAdmissible := admissibility.platformAdmissible
  traceEquivalence := behavior.traceEquivalence

end VerifiedProgram

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
