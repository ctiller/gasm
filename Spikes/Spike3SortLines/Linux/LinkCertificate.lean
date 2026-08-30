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

import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge
import Spikes.Spike3SortLines.Linux.Program

/-! # Spike 3 Linux resource-prefix linker certificate

This module pays the fixed linker-normalization cost once.  Consumers obtain exact production
fetches for the resource-exhaustion prefix without reducing the 347-instruction linker output or
running a second evaluator.  It is deliberately a placement certificate, not a native execution,
resource-outcome, or `VerifiedProgram` proof.
-/

namespace Spikes.Spike3SortLines.Linux

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The rejected reservation still asks the OS for the normal 64 KiB arena.  Zero is the caller's
    grant, not the emitted request length: using a zero-length `mmap` artifact here would prove a
    different (and invalid) failure path from the one selected by `noNativeArenaGrant`. -/
def spike3NoGrantReservationBytes : UInt32 := 65536

/-- The source prefix preceding the dedicated resource-failure label.  The fixed list boundary is
    checked by `spike3_no_grant_source_resource_decomposition`, so source edits cannot silently
    retarget this certificate. -/
def spike3NoGrantSourceBeforeResource : List SymbolicInstr :=
  (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes).take 326

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The source suffix following the labelled resource-failure fragment. -/
def spike3NoGrantSourceAfterResource : List SymbolicInstr :=
  (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes).drop 330

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The actual source program has the resource fragment at this exact structural splice.  Changes
    to source order fail this theorem rather than silently retargeting the failure proof. -/
theorem spike3_no_grant_source_resource_decomposition :
    spike3SymbolicProgramWithArena spike3NoGrantReservationBytes =
      spike3NoGrantSourceBeforeResource ++ spike3ResourceExhaustedSegment ++
        spike3NoGrantSourceAfterResource := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The three concrete instructions emitted by the dedicated failure source fragment. -/
def spike3ResourceFailureInstructions : List X86_64Instr := [
  mov_r32 .edi spike3ResourceFailureExitCode,
  mov_r32 .eax 60,
  syscall_op
]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The exact static link invocation used by the certificate.  The data-symbol list is included so
    this cannot be mistaken for a certificate for the same source under another link environment. -/
theorem spike3_no_grant_resource_link_invocation :
    spike3LinkedWithArena spike3NoGrantReservationBytes =
      linkLinuxProgramStatic (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes)
        [("crlfBytes", crlfBytes)] :=
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The selected final artifact's text is exactly the serialization of the instruction list used
    by the production evaluator.  This is by construction of this specific static-link operation. -/
theorem spike3_no_grant_resource_exact_text :
    (spike3ExecutableWithArena spike3NoGrantReservationBytes).textBytes =
      serializeInstructions (spike3InstructionsWithArena spike3NoGrantReservationBytes) := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The offset is calculated from the same estimated-text layout pass used by the static linker.
    Its fixed value is a checked consequence of the complete symbolic source decomposition, not a
    hand-maintained native address. -/
def spike3NoGrantResourceFailureBase : UInt64 :=
  let program := spike3SymbolicProgramWithArena spike3NoGrantReservationBytes
  let estTextSize := (program.map estimatedSize).foldl (· + ·) 0
  let (_, rodataBytesEst) := layoutDataSection 0 [("crlfBytes", crlfBytes)]
  let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
  let layoutEst := computeElf64Layout 0x400000 estTextSize rodataBytesEst.size shstrtabSize
  layoutEst.textVma +
    ((spike3NoGrantSourceBeforeResource.map estimatedSize).foldl (· + ·) 0).toUInt64

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
theorem spike3_no_grant_resource_failure_base :
    spike3NoGrantResourceFailureBase = 4199720 := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The actual internal label table built by the static linker resolves the selected source label
    to the computed prefix offset.  This makes the source-level splice and the concrete address
    meet at the same linker symbol, rather than merely sharing a hand-written number. -/
theorem spike3_no_grant_resource_label_resolves :
    let program := spike3SymbolicProgramWithArena spike3NoGrantReservationBytes
    let estTextSize := (program.map estimatedSize).foldl (· + ·) 0
    let (_, rodataBytesEst) := layoutDataSection 0 [("crlfBytes", crlfBytes)]
    let shstrtabSize := (buildShStrTab [".text", ".rodata", ".shstrtab"]).1.size
    let layoutEst := computeElf64Layout 0x400000 estTextSize rodataBytesEst.size shstrtabSize
    lookupSymbol (buildSymbolTable layoutEst.textVma program) "resource_exhausted" =
      some spike3NoGrantResourceFailureBase := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The exact production index of the artifact from the selected link invocation. -/
def spike3NoGrantResourceArtifactIndex : List (UInt64 × X86_64Instr) :=
  indexInstructions (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip
    (spike3InstructionsWithArena spike3NoGrantReservationBytes)

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The complete encoded instruction span remains within the UInt64 address space from the exact
    loader entry point.  The separate address-uniqueness theorem below is therefore not silently
    relying on modular wraparound. -/
theorem spike3_no_grant_resource_index_no_wrap :
    (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip.toNat +
      ((spike3InstructionsWithArena spike3NoGrantReservationBytes).map
        (fun instruction => (X86_64Instruction.encode instruction).size)).sum < 2 ^ 64 := by
  decide

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The linker emits the resource fragment at one exact indexed splice.  The `take`/`drop`
    boundaries are validated against the linker result here once; a consumer cannot replace this
    with a similarly shaped fragment at another address. -/
theorem spike3_no_grant_resource_index_decomposition :
    spike3NoGrantResourceArtifactIndex =
      spike3NoGrantResourceArtifactIndex.take 299 ++
        indexInstructions spike3NoGrantResourceFailureBase spike3ResourceFailureInstructions ++
          spike3NoGrantResourceArtifactIndex.drop 302 := by
  rfl

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- One bounded structural normalization establishes that the static linker's indexed addresses
    are non-wrapping and unique for this exact source/link invocation.  This is layout checking,
    not a native execution or trace decision. -/
theorem spike3_no_grant_resource_index_addresses_nodup :
    spike3NoGrantResourceArtifactIndex.map Prod.fst |>.Nodup := by
  decide

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The final-index resolution law is derived from the checked unique layout, never accepted as a
    Spike proof premise. -/
theorem spike3NoGrantResourceArtifactLayout :
    IndexedLayoutCertificate spike3NoGrantResourceArtifactIndex :=
  IndexedLayoutCertificate.ofNoDupAddresses _ spike3_no_grant_resource_index_addresses_nodup

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Minimal exact fetch handoff for any instruction in the selected resource-failure fragment.
    The caller provides only membership in the fixed three-instruction local index; final-artifact
    identity, source/link provenance, prefix placement, and address uniqueness are all derived
    above. -/
theorem spike3_no_grant_resource_failure_lookup
    (entry : UInt64 × X86_64Instr)
    (member : entry ∈ indexInstructions spike3NoGrantResourceFailureBase
      spike3ResourceFailureInstructions) :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex entry.1 = some entry.2 := by
  apply spike3NoGrantResourceArtifactLayout.resolves entry
  rw [spike3_no_grant_resource_index_decomposition]
  simp [member]

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- Fetch of the actual failure-exit setup instruction. -/
theorem spike3_no_grant_resource_failure_exit_code_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex
      spike3NoGrantResourceFailureBase =
      some (mov_r32 .edi spike3ResourceFailureExitCode) := by
  apply spike3_no_grant_resource_failure_lookup
    (spike3NoGrantResourceFailureBase, mov_r32 .edi spike3ResourceFailureExitCode)
  simp [indexInstructions, indexInstructions.loop, spike3ResourceFailureInstructions]

end Spikes.Spike3SortLines.Linux
