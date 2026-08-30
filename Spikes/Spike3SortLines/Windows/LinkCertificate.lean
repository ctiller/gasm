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
import Spikes.Spike3SortLines.Windows.Program

/-! # Spike 3 Win32 no-grant linker certificate

The failed-arena execution is a proof about one exact PE image, not a similarly
shaped instruction list.  This module pays the finite linker normalization cost
once and exposes only the fetch facts needed by the preparation-failure trace.
It does not execute the program or create a `VerifiedProgram`.
-/

namespace Spikes.Spike3SortLines.Windows

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#4-current-memory-and-ingestion-boundary -/
/-- The no-grant artifact still asks VirtualAlloc for the ordinary 64 KiB arena.  The zero is
    the capability's admitted capacity, never a different zero-byte allocation request. -/
def spike3NoGrantReservationBytes : UInt32 := 65536

/-- The exact source prefix preceding the dedicated resource-failure fragment. -/
def spike3NoGrantSourceBeforeResource : List SymbolicInstr :=
  (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes).take 331

/-- The exact source suffix following the dedicated resource-failure fragment. -/
def spike3NoGrantSourceAfterResource : List SymbolicInstr :=
  (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes).drop 334

/-- A source edit that moves the resource label invalidates this splice rather than silently
    retargeting the no-grant proof. -/
theorem spike3_no_grant_source_resource_decomposition :
    spike3SymbolicProgramWithArena spike3NoGrantReservationBytes =
      spike3NoGrantSourceBeforeResource ++ spike3ResourceExhaustedSegment ++
        spike3NoGrantSourceAfterResource := by
  rfl

/-- Concrete instructions emitted by the exact source fragment.  The second instruction is the
    PE linker-resolved indirect call to the ExitProcess IAT slot, not an abstract host exit. -/
def spike3ResourceFailureInstructions : List X86_64Instr := [
  mov_r32 .ecx spike3ResourceFailureExitCode,
  call_rip 6838
]

/-- The complete static invocation whose output this certificate indexes. -/
theorem spike3_no_grant_resource_link_invocation :
    spike3LinkedWithArena spike3NoGrantReservationBytes =
      linkWindowsProgram (spike3SymbolicProgramWithArena spike3NoGrantReservationBytes)
        [("crlfBytes", crlfBytes)] :=
  rfl

/-- The selected final PE text is exactly the serialization of the production instruction list. -/
theorem spike3_no_grant_resource_exact_text :
    (spike3ExecutableWithArena spike3NoGrantReservationBytes).textBytes =
      serializeInstructions (spike3InstructionsWithArena spike3NoGrantReservationBytes) := by
  rfl

/-- Exact loaded address of `resource_exhausted`, derived from the same source/layout pass that
    emits the selected PE artifact. -/
def spike3NoGrantResourceFailureBase : UInt64 :=
  let program := spike3SymbolicProgramWithArena spike3NoGrantReservationBytes
  let estTextSize := (program.map estimatedSize).foldl (· + ·) 0
  let (_, rdataBytesEst) := layoutDataSection 0 [("crlfBytes", crlfBytes)]
  let layout := computeSectionLayout estTextSize rdataBytesEst.size 512
  0x140000000 + layout.textRva.toUInt64 +
    ((spike3NoGrantSourceBeforeResource.map estimatedSize).foldl (· + ·) 0).toUInt64

theorem spike3_no_grant_resource_failure_base :
    spike3NoGrantResourceFailureBase = 5368714583 := by
  rfl

/-- The assembler's source label is the corresponding RVA; the loader image base is accounted
    for separately by `spike3NoGrantResourceFailureBase`. -/
theorem spike3_no_grant_resource_label_resolves :
    let program := spike3SymbolicProgramWithArena spike3NoGrantReservationBytes
    let estTextSize := (program.map estimatedSize).foldl (· + ·) 0
    let (_, rdataBytesEst) := layoutDataSection 0 [("crlfBytes", crlfBytes)]
    let layout := computeSectionLayout estTextSize rdataBytesEst.size 512
    lookupSymbol (buildSymbolTable layout.textRva.toUInt64 program) "resource_exhausted" =
      some 5463 := by
  rfl

/-- The production index of the selected loaded PE artifact. -/
def spike3NoGrantResourceArtifactIndex : List (UInt64 × X86_64Instr) :=
  indexInstructions (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip
    (spike3InstructionsWithArena spike3NoGrantReservationBytes)

/-- The initial allocation request is a fixed source-derived PE prefix.  Its two indirect-call
    displacements land on the GetStdHandle and VirtualAlloc IAT slots respectively; the slot
    identities themselves are proved separately by the IAT lemmas, because they depend on the
    loaded PE memory rather than only on text layout. -/
def spike3NoGrantInitialInstructions : List X86_64Instr := [
  sub_rsp 120,
  mov_r32 .ecx 0xFFFFFFF6,
  call_rip 8177,
  mov_r64 .r12 .rax,
  xor_r32 .ecx .ecx,
  mov_r32 .edx 65536,
  mov_r32 .r8d 0x3000,
  mov_r32 .r9d 0x04,
  call_rip 8181,
  cmp_r64_imm8 .rax 0,
  je_rel32 1314
]

/-- Exact prefix splice for the no-grant transition.  This is intentionally a property of the
    final indexed artifact, not a second hand-written execution list. -/
theorem spike3_no_grant_initial_index_decomposition :
    spike3NoGrantResourceArtifactIndex =
      indexInstructions (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip
        spike3NoGrantInitialInstructions ++ spike3NoGrantResourceArtifactIndex.drop 11 := by
  rfl

theorem spike3_no_grant_resource_index_no_wrap :
    (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip.toNat +
      ((spike3InstructionsWithArena spike3NoGrantReservationBytes).map
        (fun instruction => (X86_64Instruction.encode instruction).size)).sum < 2 ^ 64 := by
  decide

/-- The linker emits the source fragment at this exact concrete instruction splice. -/
theorem spike3_no_grant_resource_index_decomposition :
    spike3NoGrantResourceArtifactIndex =
      spike3NoGrantResourceArtifactIndex.take 304 ++
        indexInstructions spike3NoGrantResourceFailureBase spike3ResourceFailureInstructions ++
          spike3NoGrantResourceArtifactIndex.drop 306 := by
  rfl

theorem spike3_no_grant_resource_index_addresses_nodup :
    spike3NoGrantResourceArtifactIndex.map Prod.fst |>.Nodup := by
  decide

theorem spike3NoGrantResourceArtifactLayout :
    IndexedLayoutCertificate spike3NoGrantResourceArtifactIndex :=
  IndexedLayoutCertificate.ofNoDupAddresses _ spike3_no_grant_resource_index_addresses_nodup

theorem spike3_no_grant_initial_lookup
    (entry : UInt64 × X86_64Instr)
    (member : entry ∈ indexInstructions
      (spike3ExecutableWithArena spike3NoGrantReservationBytes).load.rip
      spike3NoGrantInitialInstructions) :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex entry.1 = some entry.2 := by
  apply spike3NoGrantResourceArtifactLayout.resolves entry
  rw [spike3_no_grant_initial_index_decomposition]
  simp [member]

/-- Exact fetch handoff for each instruction in the selected source-derived failure fragment. -/
theorem spike3_no_grant_resource_failure_lookup
    (entry : UInt64 × X86_64Instr)
    (member : entry ∈ indexInstructions spike3NoGrantResourceFailureBase
      spike3ResourceFailureInstructions) :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex entry.1 = some entry.2 := by
  apply spike3NoGrantResourceArtifactLayout.resolves entry
  rw [spike3_no_grant_resource_index_decomposition]
  simp [member]

theorem spike3_no_grant_resource_failure_exit_code_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex
      spike3NoGrantResourceFailureBase =
      some (mov_r32 .ecx spike3ResourceFailureExitCode) := by
  apply spike3_no_grant_resource_failure_lookup
    (spike3NoGrantResourceFailureBase, mov_r32 .ecx spike3ResourceFailureExitCode)
  simp [indexInstructions, indexInstructions.loop, spike3ResourceFailureInstructions]

theorem spike3_no_grant_resource_failure_exit_code_size :
    (X86_64Instruction.encode (mov_r32 .ecx spike3ResourceFailureExitCode)).size = 5 := by
  rfl

theorem spike3_no_grant_resource_failure_exit_call_lookup :
    instructionAtRipIndexed spike3NoGrantResourceArtifactIndex
      (spike3NoGrantResourceFailureBase + 5) = some (call_rip 6838) := by
  apply spike3_no_grant_resource_failure_lookup
    (spike3NoGrantResourceFailureBase + 5, call_rip 6838)
  simp [indexInstructions, indexInstructions.loop, spike3ResourceFailureInstructions,
    spike3_no_grant_resource_failure_exit_code_size]

end Spikes.Spike3SortLines.Windows
