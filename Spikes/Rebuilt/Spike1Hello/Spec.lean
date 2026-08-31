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
# Rebuilt Spike 1 source contract

This file owns the target-independent `writeAll text onFatal` contract selected by Craig on
2026-08-31. It contains no handle, retry count, instruction, address, ABI, provider, numeric process
status, artifact, or `VerifiedProgram` definition.
-/

namespace Spikes.Rebuilt.Spike1Hello

/-- The logical text required before an ordinary successful termination. -/
def message : List UInt8 :=
  "Hello, World!\n".toUTF8.toList

/-- Fatal outcomes admitted by the Spike 1 root. A short write is deliberately absent. -/
inductive FatalOutputError where
  | noStdout
  | writeFailure
deriving DecidableEq, Repr

/-- Evidence delivered to the fatal continuation. Missing stdout occurs before output; a fatal
write retains exactly some committed prefix. -/
structure OutputFailure (text : List UInt8) where
  error : FatalOutputError
  committed : List UInt8
  valid : match error with
    | .noStdout => committed = []
    | .writeFailure => committed.IsPrefix text

/-- A source-level terminal observation. Target-specific numeric exit codes/actions are realization
facts and do not occur in the precious root. -/
inductive TerminalObservation where
  | success (emitted : List UInt8)
  | fatal (error : FatalOutputError) (committed : List UInt8)
deriving DecidableEq, Repr

/-- The fatal continuation is semantically terminal: it produces a terminal observation directly,
not an arbitrary program merely indexed by a non-returning result type. -/
structure FatalContinuation (text : List UInt8) where
  apply : OutputFailure text → TerminalObservation
  terminatesExactly : ∀ failure,
    apply failure = .fatal failure.error failure.committed

/-- Standard fatal policy for Spike 1. -/
def orFatal (text : List UInt8) : FatalContinuation text where
  apply := fun failure => .fatal failure.error failure.committed
  terminatesExactly := fun _ => rfl

/-- The actual precious source operation. `writeAll` absorbs short/zero writes below this boundary;
only complete success or the certified fatal continuation is source-visible. -/
structure WriteAllProgram where
  text : List UInt8
  onFatal : FatalContinuation text

/-- Ergonomic constructor corresponding to `writeAll text onFatal`. -/
def writeAll (text : List UInt8) (onFatal : FatalContinuation text) : WriteAllProgram :=
  { text, onFatal }

/-- Source semantics of `writeAll`: success emitted all text, or the actual fatal continuation ran.
There is no source-level partial-success or numeric-exit case. -/
def WriteAllProgram.Accepts (program : WriteAllProgram) : TerminalObservation → Prop
  | .success emitted => emitted = program.text
  | outcome@(.fatal _ _) => ∃ failure, program.onFatal.apply failure = outcome

/-- Rebuilt Spike 1 source program. -/
def hello : WriteAllProgram :=
  writeAll message (orFatal message)

/-- The sealed Spike 1 precious root used by lowering. -/
def Accepts : TerminalObservation → Prop :=
  hello.Accepts

theorem accepts_success : Accepts (.success message) := by
  rfl

theorem accepts_failure (failure : OutputFailure message) :
    Accepts (.fatal failure.error failure.committed) := by
  exact ⟨failure, (orFatal message).terminatesExactly failure⟩

theorem no_stdout_commits_nothing (failure : OutputFailure message)
    (missing : failure.error = .noStdout) : failure.committed = [] := by
  cases failure with
  | mk error committed valid =>
      simp only at missing
      subst error
      exact valid

theorem write_failure_commits_prefix (failure : OutputFailure message)
    (failed : failure.error = .writeFailure) : failure.committed.IsPrefix message := by
  cases failure with
  | mk error committed valid =>
      simp only at failed
      subst error
      exact valid

end Spikes.Rebuilt.Spike1Hello
