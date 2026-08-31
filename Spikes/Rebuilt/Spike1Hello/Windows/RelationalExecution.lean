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

import Spikes.Rebuilt.Spike1Hello.RelationalExperiment
import Spikes.Rebuilt.Spike1Hello.Windows.Program
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.Windows.Win32API

/-!
# Private exact-artifact relational execution for rebuilt Spike 1

This file is intentionally spike-local. It fixes the exact linked instruction index, gives every
host transition an exact call-site occurrence, and models only the selected synchronous writable
stdout profile. It is the execution seam under test, not a shared API.
-/

namespace Spikes.Rebuilt.Spike1Hello.Windows.RelationalExecution

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Spikes.Rebuilt.Spike1Hello.RelationalExperiment
open Spikes.Rebuilt.Spike1Hello.Windows

def exactIndex : List (UInt64 × X86_64Instr) :=
  indexInstructions executable.load.rip instructions

theorem exact_index_length : exactIndex.length = 29 := by
  decide

def instructionRip (index : Nat) : Option UInt64 :=
  (exactIndex[index]?).map Prod.fst

inductive BoundarySite where
  | getStdHandle
  | writeFile
  | exitSuccess
  | exitFatal
deriving DecidableEq, Repr

def BoundarySite.instructionIndex : BoundarySite → Nat
  | .getStdHandle => 2
  | .writeFile => 15
  | .exitSuccess => 26
  | .exitFatal => 28

def BoundarySite.rip (site : BoundarySite) : Option UInt64 :=
  instructionRip site.instructionIndex

theorem boundary_sites_exist (site : BoundarySite) : site.rip.isSome := by
  cases site <;> decide

def bytesAt (state : X86_64MachineState) (address : UInt64) (count : Nat) : List UInt8 :=
  (List.range count).map fun offset =>
    X86_64Mem.readByte state.memory (address + offset.toUInt64)

def imageLayout :=
  computeSectionLayout executable.textBytes.size executable.rdataBytes.size 512

def messageAddress : UInt64 :=
  executable.imageBase + imageLayout.rdataRva.toUInt64

/-- Exact static-data range selected by this artifact. -/
def IsMessageSlice (address : UInt64) (count : Nat) : Prop :=
  ∃ offset : Nat,
    address = messageAddress + offset.toUInt64 ∧ offset + count ≤ messageBytes.size

/-- Eligibility owned by the selected provider profile. This is evidence, not a descriptive tag. -/
structure SynchronousStdout where
  handle : UInt64
  nonnull : handle ≠ 0
  notInvalid : handle ≠ 0xFFFFFFFFFFFFFFFF
  writable : Prop
  writableProof : writable

/-- Windows failures admitted as terminal synchronous failures. `ERROR_IO_PENDING` is excluded. -/
structure SynchronousWriteFailure where
  errorCode : UInt32
  notPending : errorCode ≠ 997

inductive TerminalCause where
  | success
  | noStdout
  | writeFailure (failure : SynchronousWriteFailure)
  | providerFault

/-- Exact identity of one boundary occurrence in the selected artifact. -/
structure BoundaryOccurrence where
  site : BoundarySite
  callRip : UInt64
  exactSite : site.rip = some callRip
  beforeCall : X86_64MachineState
  atCallRip : beforeCall.rip = callRip
  instruction : X86_64Instr
  exactLookup : instructionAtRipIndexed exactIndex callRip = some instruction
  enteredProvider : X86_64MachineState
  enteredExact : enteredProvider = X86_64Instruction.step instruction beforeCall

structure Config where
  machine : X86_64MachineState
  emitted : List UInt8
  logical : RelationalExperiment.State
  pendingFatal : Option TerminalCause := none
  terminalCause : Option TerminalCause := none

def acquiredLogical (state : RelationalExperiment.State) : RelationalExperiment.State :=
  { block := .writeRemaining, committed := state.committed, remaining := state.remaining }

def noStdoutLogical : RelationalExperiment.State :=
  { block := .terminal (.fatal .noStdout []), committed := [], remaining := [] }

def writeFailedLogical (state : RelationalExperiment.State) : RelationalExperiment.State :=
  { block := .terminal (.fatal .writeFailure state.committed)
    committed := state.committed
    remaining := [] }

/-- A target/profile-owned boundary transition. Count memory, return registers, emitted bytes and
fatal provenance are one indivisible occurrence. There is no oversized-success constructor. -/
inductive ProviderStep (profile : SynchronousStdout) :
    BoundaryOccurrence → Config → ProviderResponse → Config → Prop where
  | acquired {occurrence before} (site : occurrence.site = .getStdHandle)
      (same : before.machine = occurrence.beforeCall)
      (logicalStep : RelationalExperiment.Step before.logical .stdoutAcquired
        (acquiredLogical before.logical)) :
      ProviderStep profile occurrence before .stdoutAcquired
        { machine := (popReturnAddress occurrence.enteredProvider).setGpr64 .rax profile.handle
          emitted := before.emitted
          logical := acquiredLogical before.logical }
  | noStdout {occurrence before} (site : occurrence.site = .getStdHandle)
      (same : before.machine = occurrence.beforeCall)
      (logicalStep : RelationalExperiment.Step before.logical .noStdout
        noStdoutLogical) :
      ProviderStep profile occurrence before .noStdout
        { machine := (popReturnAddress occurrence.enteredProvider).setGpr64 .rax 0
          emitted := before.emitted
          logical := noStdoutLogical
          pendingFatal := some .noStdout }
  | accepted {occurrence before count afterLogical}
      (site : occurrence.site = .writeFile)
      (same : before.machine = occurrence.beforeCall)
      (handle : occurrence.enteredProvider.gprs .rcx = profile.handle)
      (overlapped : occurrence.enteredProvider.read64
        (occurrence.enteredProvider.rsp + 40) = 0)
      (writtenSlot : occurrence.enteredProvider.gprs .r9 =
        occurrence.enteredProvider.rsp + 48)
      (readable : IsMessageSlice (occurrence.enteredProvider.gprs .rdx)
        (occurrence.enteredProvider.gprs .r8).toNat)
      (bytesExact : bytesAt occurrence.enteredProvider
        (occurrence.enteredProvider.gprs .rdx) count =
          before.logical.remaining.take count)
      (logicalStep : RelationalExperiment.Step before.logical (.accepted count) afterLogical)
      (bounded : count ≤ (occurrence.enteredProvider.gprs .r8).toNat) :
      ProviderStep profile occurrence before (.accepted count)
        { machine := {
            (popReturnAddress occurrence.enteredProvider).setGpr64 .rax 1 with
            memory := X86_64Mem.write .w32 (occurrence.enteredProvider.gprs .r9) count.toUInt64
              (popReturnAddress occurrence.enteredProvider).memory }
          emitted := before.emitted ++ bytesAt occurrence.enteredProvider
            (occurrence.enteredProvider.gprs .rdx) count
          logical := afterLogical }
  | writeFailed {occurrence before} (failure : SynchronousWriteFailure)
      (site : occurrence.site = .writeFile)
      (same : before.machine = occurrence.beforeCall)
      (handle : occurrence.enteredProvider.gprs .rcx = profile.handle)
      (overlapped : occurrence.enteredProvider.read64
        (occurrence.enteredProvider.rsp + 40) = 0)
      (writtenSlot : occurrence.enteredProvider.gprs .r9 =
        occurrence.enteredProvider.rsp + 48)
      (readable : IsMessageSlice (occurrence.enteredProvider.gprs .rdx)
        (occurrence.enteredProvider.gprs .r8).toNat)
      (logicalStep : RelationalExperiment.Step before.logical .writeFailed
        (writeFailedLogical before.logical)) :
      ProviderStep profile occurrence before .writeFailed
        { machine := (popReturnAddress occurrence.enteredProvider).setGpr64 .rax 0
          emitted := before.emitted
          logical := writeFailedLogical before.logical
          pendingFatal := some (.writeFailure failure) }

inductive TargetEvent where
  | isa
  | provider (response : ProviderResponse)
  | exit (code : UInt32)
deriving Repr

def isBoundaryRip (rip : UInt64) : Prop :=
  ∃ site : BoundarySite, site.rip = some rip

/-- Only the selected exit block can turn a pending source cause into a terminal cause. The common
fatal machine block retains, rather than reconstructs, the provider occurrence's provenance. -/
inductive ExitDisposition : Config → BoundarySite → UInt32 → TerminalCause → Prop where
  | success {before} (pending : before.pendingFatal = none) :
      before.logical.block = .terminal (.success before.emitted) →
      ExitDisposition before .exitSuccess 0 .success
  | noStdout {before} (pending : before.pendingFatal = some .noStdout) :
      before.logical.block = .terminal (.fatal .noStdout []) →
      ExitDisposition before .exitFatal 1 .noStdout
  | writeFailure {before failure}
      (pending : before.pendingFatal = some (.writeFailure failure)) :
      before.logical.block = .terminal (.fatal .writeFailure before.emitted) →
      ExitDisposition before .exitFatal 1 (.writeFailure failure)

def Config.TerminalConsistent (config : Config) : Prop :=
  match config.terminalCause with
  | none => True
  | some _ => config.logical.IsTerminal

def Config.Agrees (config : Config) : Prop :=
  config.logical.Safe ∧ config.TerminalConsistent

theorem ExitDisposition.logicalTerminal {before site code cause}
    (disposition : ExitDisposition before site code cause) : before.logical.IsTerminal := by
  cases disposition with
  | success pending logical => exact ⟨_, logical⟩
  | noStdout pending logical => exact ⟨_, logical⟩
  | writeFailure pending logical => exact ⟨_, logical⟩

theorem ProviderStep.preservesAgreement {profile occurrence before response after}
    (step : ProviderStep profile occurrence before response after)
    (agrees : before.Agrees) : after.Agrees := by
  rcases agrees with ⟨safe, terminal⟩
  cases step with
  | acquired site same logicalStep =>
      exact ⟨logicalStep.preserves safe, trivial⟩
  | noStdout site same logicalStep =>
      exact ⟨logicalStep.preserves safe, trivial⟩
  | accepted site same handle overlapped writtenSlot readable bytesExact logicalStep bounded =>
      exact ⟨logicalStep.preserves safe, trivial⟩
  | writeFailed failure site same handle overlapped writtenSlot readable logicalStep =>
      exact ⟨logicalStep.preserves safe, trivial⟩

/-- One exact-artifact step. Ordinary ISA execution uses the production instruction semantics;
boundary execution starts with that same CALL step and then applies one admitted provider effect. -/
inductive ExactStep (profile : SynchronousStdout) : Config → TargetEvent → Config → Prop where
  | ordinary {before instruction}
      (running : before.terminalCause = none)
      (lookup : instructionAtRipIndexed exactIndex before.machine.rip = some instruction)
      (notBoundary : ¬ isBoundaryRip before.machine.rip) :
      ExactStep profile before .isa
        { before with machine := X86_64Instruction.step instruction before.machine }
  | boundary {before after response occurrence}
      (running : before.terminalCause = none)
      (atCall : occurrence.beforeCall = before.machine)
      (effect : ProviderStep profile occurrence before response after) :
      ExactStep profile before (.provider response) after
  | exit {before : Config} {occurrence : BoundaryOccurrence} {code : UInt32}
      {cause : TerminalCause}
      (running : before.terminalCause = none)
      (atCall : occurrence.beforeCall = before.machine)
      (argument : (occurrence.enteredProvider.gprs .rcx).toUInt32 = code) :
      ExitDisposition before occurrence.site code cause →
      ExactStep profile before (.exit code)
        { machine := { occurrence.enteredProvider with fault := some (.processExit code) }
          emitted := before.emitted
          logical := before.logical
          pendingFatal := before.pendingFatal
          terminalCause := some cause }

theorem ExactStep.preservesAgreement {profile before event after}
    (step : ExactStep profile before event after) (agrees : before.Agrees) : after.Agrees := by
  cases step with
  | ordinary => exact agrees
  | boundary running atCall effect => exact effect.preservesAgreement agrees
  | exit running atCall argument disposition =>
      exact ⟨agrees.1, disposition.logicalTerminal⟩

private theorem logicalPrefix_trans {a b c : RelationalExperiment.State}
    (left : RelationalExperiment.Prefix a b) (right : RelationalExperiment.Prefix b c) :
    RelationalExperiment.Prefix a c := by
  induction left with
  | refl => exact right
  | tail step rest ih => exact .tail step (ih right)

theorem ExactStep.logicalPrefix {profile before event after}
    (step : ExactStep profile before event after) :
    RelationalExperiment.Prefix before.logical after.logical := by
  cases step with
  | ordinary => exact .refl _
  | boundary running atCall effect =>
      cases effect with
      | acquired site same logicalStep => exact .tail logicalStep (.refl _)
      | noStdout site same logicalStep => exact .tail logicalStep (.refl _)
      | accepted site same handle overlapped writtenSlot readable bytesExact logicalStep bounded =>
          exact .tail logicalStep (.refl _)
      | writeFailed failure site same handle overlapped writtenSlot readable logicalStep =>
          exact .tail logicalStep (.refl _)
  | exit => exact .refl _

/-- Finite exact-artifact executions retain every ordinary/boundary occurrence. -/
inductive Execution (profile : SynchronousStdout) : Config → List TargetEvent → Config → Prop where
  | refl (config) : Execution profile config [] config
  | tail {before middle after event events} :
      ExactStep profile before event middle → Execution profile middle events after →
        Execution profile before (event :: events) after

theorem Execution.preservesAgreement {profile before events after}
    (execution : Execution profile before events after) (agrees : before.Agrees) : after.Agrees := by
  induction execution with
  | refl => exact agrees
  | tail step rest ih => exact ih (step.preservesAgreement agrees)

theorem Execution.logicalPrefix {profile before events after}
    (execution : Execution profile before events after) :
    RelationalExperiment.Prefix before.logical after.logical := by
  induction execution with
  | refl => exact .refl _
  | tail step rest ih => exact logicalPrefix_trans step.logicalPrefix ih

/-- The initial state is the exact PE loader state and exact data image. -/
def initial : Config :=
  { machine := executable.load, emitted := [], logical := RelationalExperiment.initial }

theorem initial_is_exact : initial.machine = executable.load := rfl

theorem initial_agrees : initial.Agrees := by
  exact ⟨RelationalExperiment.initial_safe, trivial⟩

theorem terminal_execution_refines {profile events after}
    (execution : Execution profile initial events after)
    (terminal : after.terminalCause.isSome) :
    ∃ observation, after.logical.block = .terminal observation ∧ Accepts observation := by
  have agrees := execution.preservesAgreement initial_agrees
  have logicalTerminal : after.logical.IsTerminal := by
    rcases hcause : after.terminalCause with _ | cause
    · simp [hcause] at terminal
    · simpa [Config.TerminalConsistent, hcause] using agrees.2
  have logicalPrefix : RelationalExperiment.Prefix RelationalExperiment.initial after.logical :=
    execution.logicalPrefix
  exact RelationalExperiment.terminal_sound logicalPrefix logicalTerminal

/-- An oversized success is absent at the actual provider seam, not converted by the common fatal
machine label into a source failure. -/
theorem oversized_provider_success_impossible (profile : SynchronousStdout)
    {occurrence before after count}
    (oversized : (occurrence.enteredProvider.gprs .r8).toNat < count) :
    ¬ ProviderStep profile occurrence before (.accepted count) after := by
  intro step
  cases step
  omega

end Spikes.Rebuilt.Spike1Hello.Windows.RelationalExecution
