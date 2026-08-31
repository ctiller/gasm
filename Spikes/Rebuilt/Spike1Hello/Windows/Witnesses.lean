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

import Spikes.Rebuilt.Spike1Hello.Windows.RelationalExecution

/-!
Closed required-behavior witnesses for the private Spike 1 execution experiment. The small runner
below executes only ordinary instructions from the exact artifact and refuses to cross a boundary;
its theorem produces the relational execution rather than becoming a second execution authority.
-/

namespace Spikes.Rebuilt.Spike1Hello.Windows.Witnesses

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Spikes.Rebuilt.Spike1Hello.RelationalExperiment
open Spikes.Rebuilt.Spike1Hello.Windows.RelationalExecution

def boundaryRip (rip : UInt64) : Bool :=
  [BoundarySite.getStdHandle, .writeFile, .exitSuccess, .exitFatal].any
    (fun site => site.rip == some rip)

theorem boundaryRip_false {rip : UInt64} (notBoundary : boundaryRip rip = false) :
    ¬ isBoundaryRip rip := by
  intro boundary
  rcases boundary with ⟨site, exact⟩
  cases site <;> simp [boundaryRip, exact] at notBoundary

def ordinaryOne? (config : Config) : Option Config :=
  if config.terminalCause.isSome then none
  else
    match instructionAtRipIndexed exactIndex config.machine.rip with
    | none => none
    | some instruction =>
        if boundaryRip config.machine.rip then none
        else some { config with machine := X86_64Instruction.step instruction config.machine }

theorem ordinaryOne_sound {profile config after}
    (ran : ordinaryOne? config = some after) : ExactStep profile config .isa after := by
  unfold ordinaryOne? at ran
  split at ran
  · contradiction
  rename_i running
  split at ran
  · contradiction
  rename_i instruction lookup
  split at ran
  · contradiction
  rename_i notBoundary
  cases ran
  have boundaryFalse : boundaryRip config.machine.rip = false := by
    cases value : boundaryRip config.machine.rip <;> simp_all
  exact .ordinary (by simpa using running) lookup
    (boundaryRip_false boundaryFalse)

theorem ordinaryOne_logical {config after} (ran : ordinaryOne? config = some after) :
    after.logical = config.logical := by
  unfold ordinaryOne? at ran
  split at ran <;> try contradiction
  split at ran <;> try contradiction
  split at ran <;> try contradiction
  cases ran
  rfl

def ordinaryRun : Nat → Config → Option Config
  | 0, config => some config
  | fuel + 1, config => ordinaryOne? config >>= ordinaryRun fuel

theorem ordinaryRun_sound {profile fuel before after}
    (ran : ordinaryRun fuel before = some after) :
    Execution profile before (List.replicate fuel .isa) after := by
  induction fuel generalizing before with
  | zero =>
      simp [ordinaryRun] at ran
      subst after
      exact .refl _
  | succ fuel ih =>
      simp only [ordinaryRun, Option.bind_eq_bind] at ran
      cases hone : ordinaryOne? before with
      | none => simp [hone] at ran
      | some middle =>
          rw [hone] at ran
          simp only [Option.bind_some] at ran
          exact .tail (ordinaryOne_sound hone) (ih ran)

theorem ordinaryRun_logical {fuel before after} (ran : ordinaryRun fuel before = some after) :
    after.logical = before.logical := by
  induction fuel generalizing before with
  | zero =>
      simp [ordinaryRun] at ran
      subst after
      rfl
  | succ fuel ih =>
      simp only [ordinaryRun, Option.bind_eq_bind] at ran
      cases hone : ordinaryOne? before with
      | none => simp [hone] at ran
      | some middle =>
          rw [hone] at ran
          simp only [Option.bind_some] at ran
          exact (ih ran).trans (ordinaryOne_logical hone)

theorem ordinaryRun_terminalCause {fuel before after}
    (ran : ordinaryRun fuel before = some after) :
    after.terminalCause = before.terminalCause := by
  induction fuel generalizing before with
  | zero =>
      simp [ordinaryRun] at ran
      subst after
      rfl
  | succ fuel ih =>
      simp only [ordinaryRun, Option.bind_eq_bind] at ran
      cases hone : ordinaryOne? before with
      | none => simp [hone] at ran
      | some middle =>
          rw [hone] at ran
          simp only [Option.bind_some] at ran
          have middleSame : middle.terminalCause = before.terminalCause := by
            unfold ordinaryOne? at hone
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            cases hone
            rfl
          exact (ih ran).trans middleSame

theorem ordinaryRun_emitted {fuel before after} (ran : ordinaryRun fuel before = some after) :
    after.emitted = before.emitted := by
  induction fuel generalizing before with
  | zero => simp [ordinaryRun] at ran; subst after; rfl
  | succ fuel ih =>
      simp only [ordinaryRun, Option.bind_eq_bind] at ran
      cases hone : ordinaryOne? before with
      | none => simp [hone] at ran
      | some middle =>
          rw [hone] at ran
          simp only [Option.bind_some] at ran
          have middleSame : middle.emitted = before.emitted := by
            unfold ordinaryOne? at hone
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            cases hone
            rfl
          exact (ih ran).trans middleSame

theorem ordinaryRun_pendingFatal {fuel before after}
    (ran : ordinaryRun fuel before = some after) :
    after.pendingFatal = before.pendingFatal := by
  induction fuel generalizing before with
  | zero => simp [ordinaryRun] at ran; subst after; rfl
  | succ fuel ih =>
      simp only [ordinaryRun, Option.bind_eq_bind] at ran
      cases hone : ordinaryOne? before with
      | none => simp [hone] at ran
      | some middle =>
          rw [hone] at ran
          simp only [Option.bind_some] at ran
          have middleSame : middle.pendingFatal = before.pendingFatal := by
            unfold ordinaryOne? at hone
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            split at hone <;> try contradiction
            cases hone
            rfl
          exact (ih ran).trans middleSame

def selectedProfile : SynchronousStdout where
  handle := 1
  nonnull := by decide
  notInvalid := by decide
  writable := True
  writableProof := trivial

structure BoundaryReady (site : BoundarySite) (before : Config) where
  callRip : UInt64
  instruction : X86_64Instr
  siteExact : site.rip = some callRip
  atRip : before.machine.rip = callRip
  lookup : instructionAtRipIndexed exactIndex callRip = some instruction

def BoundaryReady.occurrence {site before} (ready : BoundaryReady site before) :
    BoundaryOccurrence where
  site := site
  callRip := ready.callRip
  exactSite := ready.siteExact
  beforeCall := before.machine
  atCallRip := ready.atRip
  instruction := ready.instruction
  exactLookup := ready.lookup
  enteredProvider := X86_64Instruction.step ready.instruction before.machine
  enteredExact := rfl

/-- Exact ordinary prefix ending immediately before the selected GetStdHandle call. -/
theorem reaches_getStdHandle :
    ∃ before callRip, ordinaryRun 2 initial = some before ∧
      BoundarySite.getStdHandle.rip = some callRip ∧ before.machine.rip = callRip := by
  have ripResult : (ordinaryRun 2 initial).map (fun config => config.machine.rip) =
      BoundarySite.getStdHandle.rip := by
    native_decide
  cases ran : ordinaryRun 2 initial with
  | none =>
      rw [ran] at ripResult
      simp only [Option.map_none] at ripResult
      have present := boundary_sites_exist BoundarySite.getStdHandle
      rw [← ripResult] at present
      contradiction
  | some before =>
      refine ⟨before, before.machine.rip, rfl, ?_, rfl⟩
      simpa [ran] using ripResult.symm

theorem getStdHandle_ready :
    ∃ (before : Config) (_ready : BoundaryReady .getStdHandle before),
      Execution selectedProfile initial (List.replicate 2 .isa) before ∧
        before.logical = RelationalExperiment.initial ∧ before.terminalCause = none := by
  rcases reaches_getStdHandle with ⟨before, callRip, ran, site, atRip⟩
  have lookupResult :
      (ordinaryRun 2 initial).map (fun config =>
        (instructionAtRipIndexed exactIndex config.machine.rip).isSome) = some true := by
    native_decide
  rw [ran] at lookupResult
  simp only [Option.map_some] at lookupResult
  cases lookup : instructionAtRipIndexed exactIndex before.machine.rip with
  | none => simp [lookup] at lookupResult
  | some instruction =>
  refine ⟨before, {
    callRip
    instruction
    siteExact := site
    atRip
    lookup := by simpa [atRip] using lookup }, ordinaryRun_sound ran,
      ordinaryRun_logical ran, ordinaryRun_terminalCause ran⟩

theorem acquisition_witness :
    ∃ after, Execution selectedProfile initial
        (List.replicate 2 .isa ++ [.provider .stdoutAcquired]) after ∧
      after.logical = acquiredLogical RelationalExperiment.initial := by
  rcases getStdHandle_ready with ⟨before, ready, executionPrefix, logical, running⟩
  let occurrence := ready.occurrence
  let after : Config :=
    { machine := (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).setGpr64
        .rax selectedProfile.handle
      emitted := before.emitted
      logical := acquiredLogical before.logical }
  have logicalStep : RelationalExperiment.Step before.logical .stdoutAcquired
      (acquiredLogical before.logical) := by
    rw [logical]
    exact .stdoutAcquired
  have effect : ProviderStep selectedProfile occurrence before .stdoutAcquired after := by
    exact .acquired rfl rfl logicalStep
  have boundary : ExactStep selectedProfile before (.provider .stdoutAcquired) after :=
    .boundary running rfl effect
  exact ⟨after, executionPrefix.append (.tail boundary (.refl after)),
    by simp [after, logical]⟩

def getStdHandleBefore : Config :=
  (ordinaryRun 2 initial).getD initial

theorem getStdHandleBefore_run : ordinaryRun 2 initial = some getStdHandleBefore := by
  rfl

def getStdHandleReady : BoundaryReady .getStdHandle getStdHandleBefore where
  callRip := getStdHandleBefore.machine.rip
  instruction := instructions.get ⟨2, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by rfl

def afterAcquire : Config :=
  { machine := (Gasm.Targets.Windows.popReturnAddress getStdHandleReady.occurrence.enteredProvider).setGpr64
      .rax selectedProfile.handle
    emitted := getStdHandleBefore.emitted
    logical := acquiredLogical getStdHandleBefore.logical }

theorem acquire_exact_step :
    ExactStep selectedProfile getStdHandleBefore (.provider .stdoutAcquired) afterAcquire := by
  have effect : ProviderStep selectedProfile getStdHandleReady.occurrence getStdHandleBefore
      .stdoutAcquired afterAcquire := by
    apply ProviderStep.acquired rfl rfl
    exact .stdoutAcquired
  exact .boundary rfl rfl effect

def beforeFullWrite : Config :=
  (ordinaryRun 12 afterAcquire).getD afterAcquire

theorem beforeFullWrite_run : ordinaryRun 12 afterAcquire = some beforeFullWrite := by
  rfl

theorem beforeFullWrite_logical :
    beforeFullWrite.logical = acquiredLogical RelationalExperiment.initial := by
  exact (ordinaryRun_logical beforeFullWrite_run).trans rfl

def fullWriteReady : BoundaryReady .writeFile beforeFullWrite where
  callRip := beforeFullWrite.machine.rip
  instruction := instructions.get ⟨15, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by rfl

def afterFullWrite : Config :=
  let occurrence := fullWriteReady.occurrence
  let count := message.length
  let afterLogical : RelationalExperiment.State :=
    { block := .terminal (.success message), committed := message, remaining := [] }
  { machine := {
      (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).setGpr64 .rax 1 with
      memory := X86_64Mem.write .w32 (occurrence.enteredProvider.gprs .r9) count.toUInt64
        (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).memory }
    emitted := beforeFullWrite.emitted ++ bytesAt occurrence.enteredProvider
      (occurrence.enteredProvider.gprs .rdx) count
    logical := afterLogical }

theorem full_write_exact_step :
    ExactStep selectedProfile beforeFullWrite (.provider (.accepted message.length))
      afterFullWrite := by
  have effect : ProviderStep selectedProfile fullWriteReady.occurrence beforeFullWrite
      (.accepted message.length) afterFullWrite := by
    apply ProviderStep.accepted (afterLogical := {
      block := .terminal (.success message), committed := message, remaining := [] })
    · rfl
    · rfl
    · native_decide
    · native_decide
    · native_decide
    · exact ⟨0, by native_decide⟩
    · native_decide
    · rw [beforeFullWrite_logical]
      apply RelationalExperiment.Step.acceptedAll ⟨message.length, by native_decide⟩
      rfl
    · native_decide
  exact .boundary rfl rfl effect

def beforeSuccessExit : Config :=
  (ordinaryRun 10 afterFullWrite).getD afterFullWrite

theorem beforeSuccessExit_run : ordinaryRun 10 afterFullWrite = some beforeSuccessExit := by
  have present : (ordinaryRun 10 afterFullWrite).isSome = true := by native_decide
  cases ran : ordinaryRun 10 afterFullWrite with
  | none => simp [ran] at present
  | some result => simp [beforeSuccessExit, ran]

def successExitReady : BoundaryReady .exitSuccess beforeSuccessExit where
  callRip := beforeSuccessExit.machine.rip
  instruction := instructions.get ⟨26, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by
    rw [show beforeSuccessExit.machine.rip =
      (BoundarySite.exitSuccess.rip.get (boundary_sites_exist .exitSuccess)) by native_decide]
    rfl

theorem full_write_execution :
    ∃ after, Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider (.accepted message.length)] ++
        List.replicate 10 .isa ++ [.exit 0]) after ∧ after.terminalCause.isSome := by
  let after : Config :=
    { machine := { successExitReady.occurrence.enteredProvider with fault := some (.processExit 0) }
      emitted := beforeSuccessExit.emitted
      logical := beforeSuccessExit.logical
      pendingFatal := beforeSuccessExit.pendingFatal
      terminalCause := some .success }
  have pending : beforeSuccessExit.pendingFatal = none := by
    exact (ordinaryRun_pendingFatal beforeSuccessExit_run).trans rfl
  have logical : beforeSuccessExit.logical.block =
      .terminal (.success beforeSuccessExit.emitted) := by
    have logicalSame := ordinaryRun_logical beforeSuccessExit_run
    have emittedSame := ordinaryRun_emitted beforeSuccessExit_run
    rw [logicalSame, emittedSame]
    native_decide
  have exitStep : ExactStep selectedProfile beforeSuccessExit (.exit 0) after := by
    apply ExactStep.exit (ordinaryRun_terminalCause beforeSuccessExit_run |>.trans rfl) rfl
      (by native_decide)
    exact ExitDisposition.success pending logical
  refine ⟨after, ?_, by simp [after]⟩
  exact (ordinaryRun_sound getStdHandleBefore_run).append
    ((Execution.tail acquire_exact_step (Execution.refl _)).append
      ((ordinaryRun_sound beforeFullWrite_run).append
        ((Execution.tail full_write_exact_step (Execution.refl _)).append
          ((ordinaryRun_sound beforeSuccessExit_run).append
            (Execution.tail exitStep (Execution.refl _))))))

theorem full_write_refines :
    ∃ (after : Config) (observation : TerminalObservation),
      after.logical.block = Block.terminal observation ∧ Accepts observation := by
  rcases full_write_execution with ⟨after, execution, terminal⟩
  rcases terminal_execution_refines execution terminal with ⟨observation, block, accepts⟩
  exact ⟨after, observation, block, accepts⟩

def afterNoStdout : Config :=
  { machine := (Gasm.Targets.Windows.popReturnAddress getStdHandleReady.occurrence.enteredProvider).setGpr64
      .rax 0
    emitted := getStdHandleBefore.emitted
    logical := noStdoutLogical
    pendingFatal := some .noStdout }

theorem no_stdout_exact_step :
    ExactStep selectedProfile getStdHandleBefore (.provider .noStdout) afterNoStdout := by
  have effect : ProviderStep selectedProfile getStdHandleReady.occurrence getStdHandleBefore
      .noStdout afterNoStdout := by
    apply ProviderStep.noStdout rfl rfl
    exact .noStdout
  exact .boundary rfl rfl effect

def beforeNoStdoutExit : Config :=
  (ordinaryRun 3 afterNoStdout).getD afterNoStdout

theorem beforeNoStdoutExit_run : ordinaryRun 3 afterNoStdout = some beforeNoStdoutExit := by
  rfl

def noStdoutExitReady : BoundaryReady .exitFatal beforeNoStdoutExit where
  callRip := beforeNoStdoutExit.machine.rip
  instruction := instructions.get ⟨28, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by rfl

theorem no_stdout_execution :
    ∃ after, Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .noStdout] ++
        List.replicate 3 .isa ++ [.exit 1]) after ∧ after.terminalCause.isSome := by
  let after : Config :=
    { machine := { noStdoutExitReady.occurrence.enteredProvider with
          fault := some (.processExit 1) }
      emitted := beforeNoStdoutExit.emitted
      logical := beforeNoStdoutExit.logical
      pendingFatal := beforeNoStdoutExit.pendingFatal
      terminalCause := some .noStdout }
  have exitStep : ExactStep selectedProfile beforeNoStdoutExit (.exit 1) after := by
    apply ExactStep.exit (ordinaryRun_terminalCause beforeNoStdoutExit_run |>.trans rfl) rfl
      (by native_decide)
    apply ExitDisposition.noStdout
    · exact (ordinaryRun_pendingFatal beforeNoStdoutExit_run).trans rfl
    · have logicalSame := ordinaryRun_logical beforeNoStdoutExit_run
      rw [logicalSame]
      rfl
  refine ⟨after, ?_, by simp [after]⟩
  exact (ordinaryRun_sound getStdHandleBefore_run).append
    ((Execution.tail no_stdout_exact_step (Execution.refl _)).append
      ((ordinaryRun_sound beforeNoStdoutExit_run).append
        (Execution.tail exitStep (Execution.refl _))))

theorem no_stdout_refines :
    ∃ (after : Config) (observation : TerminalObservation),
      after.logical.block = Block.terminal observation ∧ Accepts observation := by
  rcases no_stdout_execution with ⟨after, execution, terminal⟩
  rcases terminal_execution_refines execution terminal with ⟨observation, block, accepts⟩
  exact ⟨after, observation, block, accepts⟩

def shortCount : Nat := 5

def afterShortWrite : Config :=
  let occurrence := fullWriteReady.occurrence
  let afterLogical : RelationalExperiment.State :=
    { block := .writeRemaining
      committed := message.take shortCount
      remaining := message.drop shortCount }
  { machine := {
      (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).setGpr64 .rax 1 with
      memory := X86_64Mem.write .w32 (occurrence.enteredProvider.gprs .r9) shortCount.toUInt64
        (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).memory }
    emitted := beforeFullWrite.emitted ++ bytesAt occurrence.enteredProvider
      (occurrence.enteredProvider.gprs .rdx) shortCount
    logical := afterLogical }

theorem short_write_exact_step :
    ExactStep selectedProfile beforeFullWrite (.provider (.accepted shortCount))
      afterShortWrite := by
  have effect : ProviderStep selectedProfile fullWriteReady.occurrence beforeFullWrite
      (.accepted shortCount) afterShortWrite := by
    apply ProviderStep.accepted (afterLogical := {
      block := .writeRemaining
      committed := message.take shortCount
      remaining := message.drop shortCount })
    · rfl
    · rfl
    · native_decide
    · native_decide
    · native_decide
    · exact ⟨0, by native_decide⟩
    · native_decide
    · rw [beforeFullWrite_logical]
      apply RelationalExperiment.Step.acceptedShort ⟨shortCount, by native_decide⟩
      native_decide
    · native_decide
  exact .boundary rfl rfl effect

def beforeRetriedWrite : Config :=
  (ordinaryRun 14 afterShortWrite).getD afterShortWrite

theorem beforeRetriedWrite_run : ordinaryRun 14 afterShortWrite = some beforeRetriedWrite := by
  rfl

def retriedWriteReady : BoundaryReady .writeFile beforeRetriedWrite where
  callRip := beforeRetriedWrite.machine.rip
  instruction := instructions.get ⟨15, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by rfl

/-- A positive short write returns to the exact WriteFile call site with the residual slice. -/
theorem short_write_retries :
    ∃ before, Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider (.accepted shortCount)] ++
        List.replicate 14 .isa) before ∧
      before.machine.rip = (BoundarySite.writeFile.rip.get (boundary_sites_exist .writeFile)) ∧
      before.logical.remaining = message.drop shortCount := by
  refine ⟨beforeRetriedWrite, ?_, by native_decide, ?_⟩
  · exact (ordinaryRun_sound getStdHandleBefore_run).append
      ((Execution.tail acquire_exact_step (Execution.refl _)).append
        ((ordinaryRun_sound beforeFullWrite_run).append
          ((Execution.tail short_write_exact_step (Execution.refl _)).append
            (ordinaryRun_sound beforeRetriedWrite_run))))
  · exact congrArg RelationalExperiment.State.remaining
      (ordinaryRun_logical beforeRetriedWrite_run) |>.trans rfl

def selectedFailure : SynchronousWriteFailure where
  errorCode := 5
  notPending := by decide

def afterWriteFailure : Config :=
  { machine := (Gasm.Targets.Windows.popReturnAddress fullWriteReady.occurrence.enteredProvider).setGpr64
      .rax 0
    emitted := beforeFullWrite.emitted
    logical := writeFailedLogical beforeFullWrite.logical
    pendingFatal := some (.writeFailure selectedFailure) }

theorem write_failure_exact_step :
    ExactStep selectedProfile beforeFullWrite (.provider .writeFailed) afterWriteFailure := by
  have effect : ProviderStep selectedProfile fullWriteReady.occurrence beforeFullWrite
      .writeFailed afterWriteFailure := by
    apply ProviderStep.writeFailed selectedFailure rfl rfl
    · native_decide
    · native_decide
    · native_decide
    · exact ⟨0, by native_decide⟩
    · rw [beforeFullWrite_logical]
      exact .writeFailed
  exact .boundary rfl rfl effect

def afterZeroWrite : Config :=
  let occurrence := fullWriteReady.occurrence
  { machine := {
      (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).setGpr64 .rax 1 with
      memory := X86_64Mem.write .w32 (occurrence.enteredProvider.gprs .r9) 0
        (Gasm.Targets.Windows.popReturnAddress occurrence.enteredProvider).memory }
    emitted := beforeFullWrite.emitted
    logical := beforeFullWrite.logical }

theorem zero_write_exact_step :
    ExactStep selectedProfile beforeFullWrite (.provider (.accepted 0)) afterZeroWrite := by
  have effect : ProviderStep selectedProfile fullWriteReady.occurrence beforeFullWrite
      (.accepted 0) afterZeroWrite := by
    apply ProviderStep.accepted (afterLogical := beforeFullWrite.logical)
    · rfl
    · rfl
    · native_decide
    · native_decide
    · native_decide
    · exact ⟨0, by native_decide⟩
    · simp [bytesAt]
    · rw [beforeFullWrite_logical]
      apply RelationalExperiment.Step.acceptedShort ⟨0, by simp⟩
      native_decide
    · native_decide
  simpa [afterZeroWrite, bytesAt] using
    (ExactStep.boundary (profile := selectedProfile) (by rfl) rfl effect)

def beforeZeroRetry : Config :=
  (ordinaryRun 14 afterZeroWrite).getD afterZeroWrite

theorem beforeZeroRetry_run : ordinaryRun 14 afterZeroWrite = some beforeZeroRetry := by
  rfl

/-- A zero write is safe and returns to the exact WriteFile site; progress is deliberately absent. -/
theorem zero_write_retries :
    ∃ before, Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider (.accepted 0)] ++
        List.replicate 14 .isa) before ∧
      before.machine.rip = (BoundarySite.writeFile.rip.get (boundary_sites_exist .writeFile)) ∧
      before.logical = acquiredLogical RelationalExperiment.initial := by
  refine ⟨beforeZeroRetry, ?_, by native_decide, ?_⟩
  · exact (ordinaryRun_sound getStdHandleBefore_run).append
      ((Execution.tail acquire_exact_step (Execution.refl _)).append
        ((ordinaryRun_sound beforeFullWrite_run).append
          ((Execution.tail zero_write_exact_step (Execution.refl _)).append
            (ordinaryRun_sound beforeZeroRetry_run))))
  · exact (ordinaryRun_logical beforeZeroRetry_run).trans
      (show afterZeroWrite.logical = acquiredLogical RelationalExperiment.initial by
        exact beforeFullWrite_logical)

def beforeWriteFailureExit : Config :=
  (ordinaryRun 3 afterWriteFailure).getD afterWriteFailure

theorem beforeWriteFailureExit_run :
    ordinaryRun 3 afterWriteFailure = some beforeWriteFailureExit := by
  rfl

def writeFailureExitReady : BoundaryReady .exitFatal beforeWriteFailureExit where
  callRip := beforeWriteFailureExit.machine.rip
  instruction := instructions.get ⟨28, by decide⟩
  siteExact := by native_decide
  atRip := rfl
  lookup := by rfl

theorem write_failure_execution :
    ∃ after, Execution selectedProfile initial
      (List.replicate 2 .isa ++ [.provider .stdoutAcquired] ++
        List.replicate 12 .isa ++ [.provider .writeFailed] ++
        List.replicate 3 .isa ++ [.exit 1]) after ∧ after.terminalCause.isSome := by
  let after : Config :=
    { machine := { writeFailureExitReady.occurrence.enteredProvider with
          fault := some (.processExit 1) }
      emitted := beforeWriteFailureExit.emitted
      logical := beforeWriteFailureExit.logical
      pendingFatal := beforeWriteFailureExit.pendingFatal
      terminalCause := some (.writeFailure selectedFailure) }
  have exitStep : ExactStep selectedProfile beforeWriteFailureExit (.exit 1) after := by
    apply ExactStep.exit (ordinaryRun_terminalCause beforeWriteFailureExit_run |>.trans rfl) rfl
      (by native_decide)
    apply ExitDisposition.writeFailure
    · exact (ordinaryRun_pendingFatal beforeWriteFailureExit_run).trans rfl
    · have logicalSame := ordinaryRun_logical beforeWriteFailureExit_run
      have emittedSame := ordinaryRun_emitted beforeWriteFailureExit_run
      rw [logicalSame, emittedSame]
      native_decide
  refine ⟨after, ?_, by simp [after]⟩
  exact (ordinaryRun_sound getStdHandleBefore_run).append
    ((Execution.tail acquire_exact_step (Execution.refl _)).append
      ((ordinaryRun_sound beforeFullWrite_run).append
        ((Execution.tail write_failure_exact_step (Execution.refl _)).append
          ((ordinaryRun_sound beforeWriteFailureExit_run).append
            (Execution.tail exitStep (Execution.refl _))))))

end Spikes.Rebuilt.Spike1Hello.Windows.Witnesses

