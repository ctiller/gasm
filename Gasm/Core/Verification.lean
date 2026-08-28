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
import Gasm.Effects.Trace
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Dispatcher
import Gasm.Targets.Linux.Linker

namespace Gasm.Core.Verification

open Gasm.Core
open Gasm.Effects
open Gasm.Targets.X86_64
open Gasm.Targets.Windows
open Gasm.Targets.Linux

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Universal model of the external operating system and runtime environment.
    Models all external data sources that operating system syscalls can query at runtime. -/
structure Environment where
  stdin            : ByteArray := ByteArray.empty
  args             : List String := []
  envVars          : List (String × String) := []
  incomingRequests : List String := []
  fileSystem       : List (String × ByteArray) := []
  clockTime        : UInt64 := 0
deriving Inhabited, BEq

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Typeclass defining how an abstract environment `Env` is loaded into a machine's initial execution state. -/
class EnvironmentLoader (Env : Type) where
  loadEnvironment : WindowsExecutable → Env → X86_64MachineState

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Default loader instance for standalone executables with closed/empty environment. -/
instance : EnvironmentLoader Unit where
  loadEnvironment exe _ := exe.load

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loader instance for CLI utilities and filter programs taking dynamic stdin streams. -/
instance : EnvironmentLoader ByteArray where
  loadEnvironment exe stdin := exe.loadWithStdin stdin

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loader instance for servers receiving network requests. -/
instance : EnvironmentLoader (List String) where
  loadEnvironment exe reqs := exe.loadWithRequests reqs

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Loader instance for full universal operating system environment. -/
instance : EnvironmentLoader Environment where
  loadEnvironment exe env :=
    let s0 := exe.loadWithStdin env.stdin
    { s0 with incomingRequests := env.incomingRequests }

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-Class Universally Parametric Verified Whole-Program Contract (x86_64 Windows).
    A binary executable CANNOT be emitted without supplying:
    1. A target executable image (`executable`) and its concrete instruction sequence (`instructions`).
    2. The high-level parametric specification function (`spec`).
    3. THE MATHEMATICAL UNIVERSAL EQUIVALENCE PROOF TERM (`traceEquivalence`)
       proving that for ALL possible external environments `env : Env`, the concrete machine execution
       matches the high-level specification trace. -/
structure VerifiedProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [ExternalCallInterceptor X86_64 Event] [BEq Event] [EnvironmentLoader Env] where
  name             : String
  executable       : WindowsExecutable
  instructions     : List X86_64Instr
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    let s0 := EnvironmentLoader.loadEnvironment executable env
    (runAsmTrace (Event := Event) instructions s0 == spec env) = true

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- First-Class Verified Program Contract specialized for dynamic stdin stream filters. -/
abbrev VerifiedStdinProgram (Event : Type := AnyEvent) [ExternalCallInterceptor X86_64 Event] [BEq Event] :=
  VerifiedProgram ByteArray Event

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-Class Verified Library Routine Contract.
    A routine CANNOT be exported without supplying:
    1. The symbolic assembly program (`program`).
    2. The high-level specification step function (`specStep`).
    3. The low-level machine state step function (`machStep`).
    4. The formal coupling invariant (`couplingInv`).
    5. THE MATHEMATICAL TRACE & STATE EQUIVALENCE PROOF TERM (`traceEquivalence`). -/
structure VerifiedRoutine (SpecState : Type) (MachineState : Type) (Event : Type) [BEq Event] where
  name             : String
  program          : List SymbolicInstr
  couplingInv      : SpecState → MachineState → Bool
  specStep         : SpecState → Option (SpecState × List Event)
  machStep         : MachineState → Option (MachineState × List Event)
  traceEquivalence :
    ∀ (s_spec : SpecState) (s_mach : MachineState),
      couplingInv s_spec s_mach = true →
      match specStep s_spec, machStep s_mach with
      | some (s_spec', specTrace), some (s_mach', machTrace) =>
          (specTrace == machTrace && couplingInv s_spec' s_mach' == true) = true
      | none, none => True
      | _, _ => False

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Type-Enforced Code Emission:
    It is IMPOSSIBLE to call this function without a valid, proved `VerifiedProgram`.
    All spike emitters, compilers, and production binary generators MUST use this function. -/
def emitVerifiedExecutable {Env : Type} {Event : Type}
    [ExternalCallInterceptor X86_64 Event] [BEq Event] [EnvironmentLoader Env]
    (p : VerifiedProgram Env Event) : ByteArray :=
  p.executable.emit

/- REF: docs/SYSTEM_EFFECTS.md#1-universal-environment-oracle-and-syscall-effects -/
/-- Typeclass defining how an abstract environment `Env` is loaded into a Linux machine's initial execution state. -/
class LinuxEnvironmentLoader (Env : Type) where
  loadEnvironment : LinuxExecutable → Env → X86_64MachineState

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Default loader instance for standalone Linux executables with closed/empty environment. -/
instance : LinuxEnvironmentLoader Unit where
  loadEnvironment exe _ := exe.load

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loader instance for Linux CLI utilities and filter programs taking dynamic stdin streams. -/
instance : LinuxEnvironmentLoader ByteArray where
  loadEnvironment exe stdin := exe.loadWithStdin stdin

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loader instance for Linux servers receiving network requests. -/
instance : LinuxEnvironmentLoader (List String) where
  loadEnvironment exe reqs := exe.loadWithRequests reqs

/- REF: docs/TARGETS/LINUX.md#32-standard-virtual-memory-layout -/
/-- Loader instance for full universal operating system environment on Linux. -/
instance : LinuxEnvironmentLoader Environment where
  loadEnvironment exe env :=
    let s0 := exe.loadWithStdin env.stdin
    { s0 with incomingRequests := env.incomingRequests }

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- First-Class Universally Parametric Verified Whole-Program Contract for Linux x86-64. -/
structure VerifiedLinuxProgram (Env : Type := Unit) (Event : Type := AnyEvent)
    [ExternalCallInterceptor X86_64 Event] [BEq Event] [LinuxEnvironmentLoader Env] where
  name             : String
  executable       : LinuxExecutable
  instructions     : List X86_64Instr
  spec             : Env → List Event
  traceEquivalence : ∀ (env : Env),
    let s0 := LinuxEnvironmentLoader.loadEnvironment executable env
    (runAsmTrace (Event := Event) instructions s0 == spec env) = true

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Type-Enforced Linux Code Emission:
    It is IMPOSSIBLE to call this function without a valid, proved `VerifiedLinuxProgram`. -/
def emitVerifiedLinuxExecutable {Env : Type} {Event : Type}
    [ExternalCallInterceptor X86_64 Event] [BEq Event] [LinuxEnvironmentLoader Env]
    (p : VerifiedLinuxProgram Env Event) : ByteArray :=
  p.executable.emit

/- REF: docs/REVIEW.md#law-8-semantic-spec-to-code-fidelity-anti-facade-law-no-dead-abstractions-or-mock-verification -/
/-- Unsafe raw binary emitter for differential encoding fuzzers and test oracles.
    Restricted solely to fuzzing test harnesses. -/
def rawEmitForFuzzing (exe : WindowsExecutable) : ByteArray :=
  exe.emit

end Gasm.Core.Verification
