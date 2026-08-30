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

import Spikes.Spike3SortLines.Windows.Program

/-!
# Stable Win32 IAT layout certificate for Spike 3

This module derives the published 64 KiB artifact's text size from the exact symbolic source and
the production assembler. Seven 64-item source chunks keep kernel reduction bounded; a structural
assembler theorem reconnects their size to the emitted bytes without serializing the aggregate
byte array. Consumers receive only the opaque layout projections and therefore do not replay the
source/linker calculation after an unrelated IAT proof edit.

This certificate adds no execution, outcome, or `VerifiedProgram` authority.
-/

namespace Spikes.Spike3SortLines.Windows

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def encodedSize (instructions : List X86_64Instr) : Nat :=
  (instructions.map fun instruction => (X86_64Instruction.encode instruction).size).sum

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
def emittedSize : SymbolicInstr → Nat
  | .movData32 dst _ => if (reg32Code dst).2 then 6 else 5
  | item => estimatedSize item

@[simp] private theorem jmp_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jmp_rel8 disp)).size = 2 := by
  rfl

@[simp] private theorem jmp_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jmp_rel32 disp)).size = 5 := by rfl
@[simp] private theorem je_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (je_rel8 disp)).size = 2 := by rfl
@[simp] private theorem je_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (je_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jne_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jne_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jne_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jne_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jl_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jl_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jle_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jle_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jle_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jle_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jg_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jg_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jge_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jge_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jge_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jge_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jb_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jb_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jb_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jb_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jae_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jae_rel8 disp)).size = 2 := by rfl
@[simp] private theorem jae_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (jae_rel32 disp)).size = 6 := by rfl
@[simp] private theorem ja_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (ja_rel8 disp)).size = 2 := by rfl
@[simp] private theorem ja_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (ja_rel32 disp)).size = 6 := by rfl
@[simp] private theorem jbe_rel8_size (disp : UInt8) :
    (X86_64Instruction.encode (jbe_rel8 disp)).size = 2 := by rfl
@[simp] private theorem lea_rip_size (dst : Reg64) (disp : Int32) :
    (X86_64Instruction.encode (lea_rip dst disp)).size = 7 := by rfl
@[simp] private theorem mov_r32_size (dst : Reg32) (imm : UInt32) :
    (X86_64Instruction.encode (mov_r32 dst imm)).size =
      (if (reg32Code dst).2 then 6 else 5) := by
  cases dst <;> rfl
@[simp] private theorem call_rip_size (disp : Int32) :
    (X86_64Instruction.encode (call_rip disp)).size = 6 := by rfl
@[simp] private theorem call_rel32_size (disp : Int32) :
    (X86_64Instruction.encode (call_rel32 disp)).size = 5 := by rfl

theorem emit_encodedSize (allSymbols : SymbolTable) (curRip : UInt64)
    (items : List SymbolicInstr) (acc : List X86_64Instr) :
    encodedSize (assembleProgram.emit allSymbols curRip items acc) =
      encodedSize acc + (items.map emittedSize).sum := by
  induction items generalizing curRip acc with
  | nil => simp [assembleProgram.emit]
  | cons item items ih =>
      cases item <;>
        simp only [assembleProgram.emit, List.map_cons, List.sum_cons, emittedSize] <;>
        rw [ih] <;>
        simp [encodedSize, estimatedSize, Nat.add_assoc]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
theorem assembleProgram_encodedSize (baseRip : UInt64) (program : List SymbolicInstr)
    (externalSymbols : SymbolTable := []) :
    encodedSize (assembleProgram baseRip program externalSymbols) =
      (program.map emittedSize).sum := by
  unfold assembleProgram
  simpa [encodedSize] using emit_encodedSize (buildSymbolTable baseRip program ++ externalSymbols)
    baseRip program []

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
theorem foldl_append_size.{u} {α : Type u} (f : α → ByteArray)
    (items : List α) (acc : ByteArray) :
    (items.foldl (fun bytes item => bytes ++ f item) acc).size =
      items.foldl (fun size item => size + (f item).size) acc.size := by
  induction items generalizing acc with
  | nil => rfl
  | cons item items ih =>
      simp only [List.foldl_cons]
      rw [ih (acc ++ f item), ByteArray.size_append]

private theorem foldl_encodedSize (instructions : List X86_64Instr) (acc : Nat) :
    instructions.foldl
        (fun size instruction => size + (X86_64Instruction.encode instruction).size) acc =
      acc + encodedSize instructions := by
  induction instructions generalizing acc with
  | nil => simp [encodedSize]
  | cons instruction instructions ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [encodedSize, Nat.add_assoc]

/- REF: docs/TARGETS/X86_64.md#2-binary-instruction-encoding -/
theorem serializeInstructions_size (instructions : List X86_64Instr) :
    (serializeInstructions instructions).size = encodedSize instructions := by
  unfold serializeInstructions
  rw [foldl_append_size, foldl_encodedSize]
  simp

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
def spike3HistoricalSource : List SymbolicInstr :=
  spike3SymbolicProgramWithArena 65536

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
def spike3HistoricalSourceChunk (chunk : Nat) : List SymbolicInstr :=
  (spike3HistoricalSource.drop (chunk * 64)).take 64

private def sourceSize (items : List SymbolicInstr) : Nat :=
  (items.map emittedSize).sum

private theorem sourceSize_split (items : List SymbolicInstr) :
    sourceSize items = sourceSize (items.take 64) + sourceSize (items.drop 64) := by
  unfold sourceSize
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

private theorem chunk0_size : sourceSize (spike3HistoricalSourceChunk 0) = 316 := by decide
private theorem chunk1_size : sourceSize (spike3HistoricalSourceChunk 1) = 239 := by decide
private theorem chunk2_size : sourceSize (spike3HistoricalSourceChunk 2) = 273 := by decide
private theorem chunk3_size : sourceSize (spike3HistoricalSourceChunk 3) = 238 := by decide
private theorem chunk4_size : sourceSize (spike3HistoricalSourceChunk 4) = 259 := by decide
private theorem chunk5_size : sourceSize (spike3HistoricalSourceChunk 5) = 223 := by decide
private theorem chunk6_size : sourceSize (spike3HistoricalSourceChunk 6) = 1 := by decide

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
theorem spike3_historical_source_size : sourceSize spike3HistoricalSource = 1549 := by
  rw [sourceSize_split spike3HistoricalSource]
  change sourceSize (spike3HistoricalSourceChunk 0) + _ = _
  rw [chunk0_size, sourceSize_split]
  change 316 + (sourceSize (spike3HistoricalSourceChunk 1) + _) = _
  rw [chunk1_size, sourceSize_split]
  change 316 + (239 + (sourceSize (spike3HistoricalSourceChunk 2) + _)) = _
  rw [chunk2_size, sourceSize_split]
  change 316 + (239 + (273 + (sourceSize (spike3HistoricalSourceChunk 3) + _))) = _
  rw [chunk3_size, sourceSize_split]
  change 316 + (239 + (273 + (238 + (sourceSize (spike3HistoricalSourceChunk 4) + _)))) = _
  rw [chunk4_size, sourceSize_split]
  change 316 + (239 + (273 + (238 + (259 +
    (sourceSize (spike3HistoricalSourceChunk 5) + _))))) = _
  rw [chunk5_size, sourceSize_split]
  change 316 + (239 + (273 + (238 + (259 + (223 +
    (sourceSize (spike3HistoricalSourceChunk 6) + _)))))) = _
  rw [chunk6_size]
  decide

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
theorem spike3_historical_instruction_size :
    encodedSize (spike3InstructionsWithArena 65536) = 1549 := by
  unfold spike3InstructionsWithArena spike3LinkedWithArena linkWindowsProgram
  change encodedSize (assembleProgram _ (spike3SymbolicProgramWithArena 65536) _) = 1549
  rw [assembleProgram_encodedSize (externalSymbols := _)]
  exact spike3_historical_source_size

/- REF: docs/SPIKES/SPIKE3_SORT_LINES.md#1-overview-high-level-architecture -/
theorem spike3_historical_text_size :
    (spike3ExecutableWithArena 65536).textBytes.size = 1549 := by
  unfold spike3ExecutableWithArena spike3LinkedWithArena linkWindowsProgram
  rw [serializeInstructions_size]
  change encodedSize (assembleProgram _ (spike3SymbolicProgramWithArena 65536) _) = 1549
  rw [assembleProgram_encodedSize (externalSymbols := _)]
  exact spike3_historical_source_size

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
structure IATLayoutCertificate : Prop where
  canonicalExecutable : spike3Executable =
    spike3ExecutableWithArena 65536
  textSize : spike3Executable.textBytes.size = 1549
  rdataSize : spike3Executable.rdataBytes.size = 2
  layout :
    computeSectionLayout spike3Executable.textBytes.size spike3Executable.rdataBytes.size 512 =
      { textRva := 0x1000, textRawSize := 2048, rdataRva := 0x2000, rdataRawSize := 512,
        idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 }

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
theorem spike3IATLayout : IATLayoutCertificate where
  canonicalExecutable := rfl
  textSize := by
    rw [show spike3Executable =
      spike3ExecutableWithArena 65536 from rfl]
    exact spike3_historical_text_size
  rdataSize := by decide
  layout := by
    rw [show spike3Executable.textBytes.size = 1549 from (by
      rw [show spike3Executable =
        spike3ExecutableWithArena 65536 from rfl]
      exact spike3_historical_text_size)]
    decide

end Spikes.Spike3SortLines.Windows
