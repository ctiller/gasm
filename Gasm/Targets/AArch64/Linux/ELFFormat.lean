/-
Copyright 2026 Google LLC

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
import Gasm.Targets.ELF.Format

namespace Gasm.Targets.AArch64.Linux

open Gasm.Core
open Gasm.Targets.ELF

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Aligns a value up to the nearest multiple of alignment. -/
def alignUp (val : Nat) (alignment : Nat) : Nat :=
  Gasm.Targets.ELF.alignUp val alignment

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Computed memory and file offsets for a 64-bit static AArch64 Linux ELF binary. -/
structure Elf64Layout where
  textOffset     : Nat
  textVma        : Address
  textSize       : Nat
  rodataOffset   : Nat
  rodataVma      : Address
  rodataSize     : Nat
  shstrtabOffset : Nat
  shstrtabSize   : Nat
  shdrsOffset    : Nat
  fileSize       : Nat
  deriving Repr, DecidableEq

/- REF: docs/TARGETS/ARM64.md#14-linux-target-static-elf64--svc-0-abi -/
/-- Computes canonical static ELF64 layout with 4KB page alignment for AArch64. -/
def computeElf64Layout (baseVma : Address) (textSize : Nat) (rodataSize : Nat) (shstrtabSize : Nat) : Elf64Layout :=
  let textOffset := 0x1000
  let textVma := baseVma + textOffset.toUInt64
  let rodataOffset := alignUp (textOffset + textSize) 0x1000
  let rodataVma := baseVma + rodataOffset.toUInt64
  let shstrtabOffset := alignUp (rodataOffset + rodataSize) 16
  let shdrsOffset := alignUp (shstrtabOffset + shstrtabSize) 8
  let shdrsSize := 4 * 64 -- NULL, .text, .rodata, .shstrtab
  let fileSize := shdrsOffset + shdrsSize
  { textOffset     := textOffset,
    textVma        := textVma,
    textSize       := textSize,
    rodataOffset   := rodataOffset,
    rodataVma      := rodataVma,
    rodataSize     := rodataSize,
    shstrtabOffset := shstrtabOffset,
    shstrtabSize   := shstrtabSize,
    shdrsOffset    := shdrsOffset,
    fileSize       := fileSize }

end Gasm.Targets.AArch64.Linux
