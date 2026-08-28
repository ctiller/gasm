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
import Gasm.Targets.ELF.Format

/-
Gasm/Targets/ELF/Parser.lean - Total, panic-free ELF64 reader (TCB.md T5 class)

WHY THIS FILE EXISTS: `Gasm.Targets.ELF.Format`/`Gasm.Targets.Linux.Emitter` write ELF64
bytes; nothing in this tree reads them back. TCB.md's T5 entry names this precisely --
"nothing the proof observes reads [the emitted bytes]" -- and every one of gasm's Linux
Spikes (1-5, plus the Spike 5 gunzip variant) now emits an ELF64 executable with zero
in-tree check that the bytes are well-formed by this project's own understanding of the
format, only external evidence (the real Linux loader accepting them). This module closes
half that gap: a structured `bytes -> Elf64_Ehdr / Elf64_Phdr list / Elf64_Shdr list /
section-payload list` reader, `Except`-returning with a typed error for every malformed
case it distinguishes, and total (structural recursion on an explicit fuel/list argument
throughout -- no `partial def` anywhere in this file, matching this task's explicit
prohibition; `partial def` compiles to a kernel-opaque constant with zero equation lemmas).

TOTALITY DISCIPLINE: every recursive helper below (`parsePhdrsAux`, `parseShdrsAux`,
`validateSegmentsAux`, `extractSectionsAux`, `readCStringBytesAux`, `sortByOffsetInsert`/
`sortByOffset`) recurses structurally on a `Nat` fuel argument or on a `List` -- the same
shape `Stdlib/Png/Spec.lean`'s `parseChunk` and `Stdlib/Png/StabilityFuzzer.lean`'s
`scanChunksAux` already use in this codebase. `e_phnum`/`e_shnum` are `UInt16` (bounded by
construction, never unbounded input), so fuel = their `.toNat` value is a real, finite,
syntactically-checkable termination measure -- not a magic constant standing in for
"trust me, this terminates."

PANIC SAFETY: every multi-byte read is bounds-checked (`pos + width > bytes.size`) BEFORE
any `.get!` call reaches it, mirroring `Stdlib/Png/Spec.lean`'s established convention in
this codebase (see that file's own note on the `String.fromUTF8!` panic the PNG parser-
stability fuzzer found: a `.get!`/`String.fromUTF8!` reached without a preceding bounds/
validity check is exactly the defect class this module is written to avoid). Section names
are decoded with `String.fromUTF8?` (`Option`-returning), never the panicking `!` variant,
for the identical reason that fix exists in `Stdlib/Png/Spec.lean`.

SCOPE: this reader recognizes exactly what this project's own ELF64 writer
(`Gasm.Targets.Linux.emitELF64Executable`) and `Gasm.Targets.ELF.Format`'s shared structures
describe -- 64-bit (`ELFCLASS64`), little-endian (`ELFDATA2LSB`), `ET_EXEC`/`ET_DYN`,
`EM_X86_64`. A file failing any of those checks is a clean, typed rejection, not a "best
effort" partial read -- see `ElfParseError`.
-/

namespace Gasm.Targets.ELF

open Gasm.Core

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Typed taxonomy of every malformed-ELF64-input case this parser distinguishes. Modeled on
    `Stdlib.Png.PngError`'s inductive taxonomy (`Stdlib/Png/Spec.lean`): every rejection is a
    named constructor carrying the offending field's raw value where useful for diagnostics,
    never a bare string or a panic. -/
inductive ElfParseError where
  | truncated                                        -- not enough bytes for a fixed-size
                                                       -- header/entry, or a declared table/
                                                       -- range runs past end-of-file
  | badMagic                                          -- e_ident[0..3] != \x7fELF
  | unsupportedClass (code : UInt8)                   -- only ELFCLASS64 (2) is supported
  | unsupportedEndianness (code : UInt8)               -- only ELFDATA2LSB (1) is supported
  | unsupportedIdentVersion (code : UInt8)            -- e_ident[EI_VERSION] must be 1
  | unsupportedVersion (v : UInt32)                   -- e_version must be 1
  | invalidEhsize (size : UInt16)                     -- e_ehsize must be 64
  | unsupportedType (t : UInt16)                      -- only ET_EXEC / ET_DYN are supported
  | unsupportedMachine (m : UInt16)                   -- only EM_X86_64 is supported
  | invalidPhentsize (size : UInt16)                  -- e_phentsize must be 56 when e_phnum > 0
  | invalidShentsize (size : UInt16)                  -- e_shentsize must be 64 when e_shnum > 0
  | invalidShstrndx (idx : UInt16) (shnum : UInt16)   -- e_shstrndx >= e_shnum (e_shnum > 0)
  | segmentOutOfRange (index : Nat)                   -- p_offset + p_filesz exceeds file size
  | sectionOutOfRange (index : Nat)                   -- sh_offset + sh_size exceeds file size
  deriving DecidableEq, Repr, Inhabited

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads a single bounds-checked byte. -/
def readU8 (bytes : ByteArray) (pos : Nat) : Except ElfParseError UInt8 :=
  if pos < bytes.size then pure (bytes.get! pos) else throw .truncated

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads a little-endian `UInt16` at `pos`, bounds-checked before any byte access. -/
def readU16LE (bytes : ByteArray) (pos : Nat) : Except ElfParseError UInt16 := do
  if pos + 2 > bytes.size then throw .truncated
  let b0 := (bytes.get! pos).toUInt16
  let b1 := (bytes.get! (pos + 1)).toUInt16
  pure (b0 ||| (b1 <<< 8))

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads a little-endian `UInt32` at `pos`, bounds-checked before any byte access. -/
def readU32LE (bytes : ByteArray) (pos : Nat) : Except ElfParseError UInt32 := do
  if pos + 4 > bytes.size then throw .truncated
  let b0 := (bytes.get! pos).toUInt32
  let b1 := (bytes.get! (pos + 1)).toUInt32
  let b2 := (bytes.get! (pos + 2)).toUInt32
  let b3 := (bytes.get! (pos + 3)).toUInt32
  pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads a little-endian `UInt64` at `pos`, bounds-checked before any byte access. -/
def readU64LE (bytes : ByteArray) (pos : Nat) : Except ElfParseError UInt64 := do
  if pos + 8 > bytes.size then throw .truncated
  let b0 := (bytes.get! pos).toUInt64
  let b1 := (bytes.get! (pos + 1)).toUInt64
  let b2 := (bytes.get! (pos + 2)).toUInt64
  let b3 := (bytes.get! (pos + 3)).toUInt64
  let b4 := (bytes.get! (pos + 4)).toUInt64
  let b5 := (bytes.get! (pos + 5)).toUInt64
  let b6 := (bytes.get! (pos + 6)).toUInt64
  let b7 := (bytes.get! (pos + 7)).toUInt64
  pure (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
        (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))

/- REF: elf-sysv-psabi#object-files -/
/-- Parses the 64-byte `Elf64_Ehdr` at the start of `bytes`, rejecting every malformed
    field this parser distinguishes (see `ElfParseError`). Accepts only what this project's
    own writer (`Gasm.Targets.Linux.emitELF64Executable`) and the shared `Elf64_Ehdr`
    structure describe: `ELFCLASS64`, `ELFDATA2LSB`, `EV_CURRENT`, `ET_EXEC`/`ET_DYN`,
    `EM_X86_64`. -/
def parseElf64Header (bytes : ByteArray) : Except ElfParseError Elf64_Ehdr := do
  if bytes.size < 64 then throw .truncated
  let m0 := bytes.get! 0
  let m1 := bytes.get! 1
  let m2 := bytes.get! 2
  let m3 := bytes.get! 3
  if m0 != 0x7F || m1 != 0x45 || m2 != 0x4C || m3 != 0x46 then throw .badMagic
  let identClass := bytes.get! 4
  if identClass != 2 then throw (.unsupportedClass identClass)
  let identData := bytes.get! 5
  if identData != 1 then throw (.unsupportedEndianness identData)
  let identVersion := bytes.get! 6
  if identVersion != 1 then throw (.unsupportedIdentVersion identVersion)
  let identOsAbi := bytes.get! 7
  let identAbiVersion := bytes.get! 8
  -- e_ident[9..15] is reserved padding; not validated (real producers vary here).
  let e_type ← readU16LE bytes 16
  let e_machine ← readU16LE bytes 18
  let e_version ← readU32LE bytes 20
  let e_entry ← readU64LE bytes 24
  let e_phoff ← readU64LE bytes 32
  let e_shoff ← readU64LE bytes 40
  let e_flags ← readU32LE bytes 48
  let e_ehsize ← readU16LE bytes 52
  let e_phentsize ← readU16LE bytes 54
  let e_phnum ← readU16LE bytes 56
  let e_shentsize ← readU16LE bytes 58
  let e_shnum ← readU16LE bytes 60
  let e_shstrndx ← readU16LE bytes 62
  if e_version != 1 then throw (.unsupportedVersion e_version)
  if e_ehsize != 64 then throw (.invalidEhsize e_ehsize)
  if e_type != ET_EXEC && e_type != ET_DYN then throw (.unsupportedType e_type)
  if e_machine != EM_X86_64 then throw (.unsupportedMachine e_machine)
  if e_phnum > 0 && e_phentsize != 56 then throw (.invalidPhentsize e_phentsize)
  if e_shnum > 0 && e_shentsize != 64 then throw (.invalidShentsize e_shentsize)
  if e_shnum > 0 && e_shstrndx >= e_shnum then throw (.invalidShstrndx e_shstrndx e_shnum)
  pure {
    identMag0 := m0, identMag1 := m1, identMag2 := m2, identMag3 := m3,
    identClass := identClass, identData := identData, identVersion := identVersion,
    identOsAbi := identOsAbi, identAbiVersion := identAbiVersion,
    e_type := e_type, e_machine := e_machine, e_version := e_version, e_entry := e_entry,
    e_phoff := e_phoff, e_shoff := e_shoff, e_flags := e_flags, e_ehsize := e_ehsize,
    e_phentsize := e_phentsize, e_phnum := e_phnum, e_shentsize := e_shentsize,
    e_shnum := e_shnum, e_shstrndx := e_shstrndx
  }

/- REF: elf-sysv-psabi#object-files -/
/-- Parses a single 56-byte `Elf64_Phdr` at `pos`. -/
def parseElf64Phdr (bytes : ByteArray) (pos : Nat) : Except ElfParseError Elf64_Phdr := do
  if pos + 56 > bytes.size then throw .truncated
  let p_type ← readU32LE bytes pos
  let p_flags ← readU32LE bytes (pos + 4)
  let p_offset ← readU64LE bytes (pos + 8)
  let p_vaddr ← readU64LE bytes (pos + 16)
  let p_paddr ← readU64LE bytes (pos + 24)
  let p_filesz ← readU64LE bytes (pos + 32)
  let p_memsz ← readU64LE bytes (pos + 40)
  let p_align ← readU64LE bytes (pos + 48)
  pure { p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align }

/- REF: elf-sysv-psabi#object-files -/
/-- Parses a single 64-byte `Elf64_Shdr` at `pos`. -/
def parseElf64Shdr (bytes : ByteArray) (pos : Nat) : Except ElfParseError Elf64_Shdr := do
  if pos + 64 > bytes.size then throw .truncated
  let sh_name ← readU32LE bytes pos
  let sh_type ← readU32LE bytes (pos + 4)
  let sh_flags ← readU64LE bytes (pos + 8)
  let sh_addr ← readU64LE bytes (pos + 16)
  let sh_offset ← readU64LE bytes (pos + 24)
  let sh_size ← readU64LE bytes (pos + 32)
  let sh_link ← readU32LE bytes (pos + 40)
  let sh_info ← readU32LE bytes (pos + 44)
  let sh_addralign ← readU64LE bytes (pos + 48)
  let sh_entsize ← readU64LE bytes (pos + 56)
  pure { sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info,
         sh_addralign, sh_entsize }

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Parses `fuel` consecutive `Elf64_Phdr` entries starting at file offset `base`, 56 bytes
    apart, `idx` counting up from 0 purely for error-message context. Structural recursion on
    `fuel` (bounded by `e_phnum : UInt16` at every call site -- see `parsePhdrs`): total, no
    `partial def`. -/
def parsePhdrsAux (bytes : ByteArray) (base : Nat) : Nat → Nat → Except ElfParseError (List Elf64_Phdr)
  | 0, _ => pure []
  | fuel + 1, idx => do
    let ph ← parseElf64Phdr bytes (base + idx * 56)
    let rest ← parsePhdrsAux bytes base fuel (idx + 1)
    pure (ph :: rest)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Parses `ehdr.e_phnum` program header entries starting at `ehdr.e_phoff`. -/
def parsePhdrs (bytes : ByteArray) (ehdr : Elf64_Ehdr) : Except ElfParseError (List Elf64_Phdr) :=
  parsePhdrsAux bytes ehdr.e_phoff.toNat ehdr.e_phnum.toNat 0

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Parses `fuel` consecutive `Elf64_Shdr` entries starting at file offset `base`, 64 bytes
    apart. Structural recursion on `fuel` (bounded by `e_shnum : UInt16`): total. -/
def parseShdrsAux (bytes : ByteArray) (base : Nat) : Nat → Nat → Except ElfParseError (List Elf64_Shdr)
  | 0, _ => pure []
  | fuel + 1, idx => do
    let sh ← parseElf64Shdr bytes (base + idx * 64)
    let rest ← parseShdrsAux bytes base fuel (idx + 1)
    pure (sh :: rest)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Parses `ehdr.e_shnum` section header entries starting at `ehdr.e_shoff`. -/
def parseShdrs (bytes : ByteArray) (ehdr : Elf64_Ehdr) : Except ElfParseError (List Elf64_Shdr) :=
  parseShdrsAux bytes ehdr.e_shoff.toNat ehdr.e_shnum.toNat 0

/- REF: elf-sysv-psabi#object-files -/
/-- Validates that every `PT_LOAD`-or-otherwise segment's declared file range
    `[p_offset, p_offset + p_filesz)` actually fits inside the file -- a malformed segment
    claiming bytes past end-of-file is rejected here rather than silently read as zeros or
    panicking. Structural recursion on the segment list: total. Validation only (no data is
    captured): segment file ranges typically overlap the header/section regions this parser
    already captures via `Elf64_Shdr`-driven extraction (see this module's header comment on
    `serializeElf64Parsed`'s scope), so capturing segment bytes a second time would duplicate
    exactly the content sections already own, without adding parse-validity coverage this
    bounds check does not already provide. -/
def validateSegmentsAux (bytes : ByteArray) : List Elf64_Phdr → Nat → Except ElfParseError Unit
  | [], _ => pure ()
  | ph :: rest, idx =>
    if ph.p_offset.toNat + ph.p_filesz.toNat > bytes.size then throw (.segmentOutOfRange idx)
    else validateSegmentsAux bytes rest (idx + 1)

/- REF: elf-sysv-psabi#object-files -/
/-- Extracts each section's raw file bytes (`[sh_offset, sh_offset + sh_size)`), parallel to
    the input `Elf64_Shdr` list. `SHT_NULL` and `SHT_NOBITS` sections contribute
    `ByteArray.empty` without a file-range check: `SHT_NULL`'s size is always 0 by convention,
    and `SHT_NOBITS` (e.g. `.bss`) by definition occupies no file space at all -- its
    `sh_size` describes memory footprint once loaded, not a byte range present in this file,
    so checking it against `bytes.size` would reject well-formed files. Structural recursion
    on the section list: total. -/
def extractSectionsAux (bytes : ByteArray) : List Elf64_Shdr → Nat → Except ElfParseError (List ByteArray)
  | [], _ => pure []
  | sh :: rest, idx => do
    let data ←
      if sh.sh_type == SHT_NULL || sh.sh_type == SHT_NOBITS then
        pure ByteArray.empty
      else
        let off := sh.sh_offset.toNat
        let sz := sh.sh_size.toNat
        if off + sz > bytes.size then throw (.sectionOutOfRange idx)
        else pure (bytes.extract off (off + sz))
    let restData ← extractSectionsAux bytes rest (idx + 1)
    pure (data :: restData)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- The structured result of parsing a well-formed ELF64 file: the file header, every program
    header, every section header, and every section's raw file bytes (parallel to `shdrs`;
    `SHT_NULL`/`SHT_NOBITS` sections carry `ByteArray.empty`). -/
structure Elf64Parsed where
  ehdr        : Elf64_Ehdr
  phdrs       : List Elf64_Phdr
  shdrs       : List Elf64_Shdr
  sectionData : List ByteArray
  deriving DecidableEq

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Top-level ELF64 reader: `bytes -> Except ElfParseError Elf64Parsed`. Total (every helper
    it calls is total; no `partial def`), panic-free on malformed input (every multi-byte
    read and every declared file range is bounds-checked before use), and a typed error for
    every malformed case this parser distinguishes -- see `ElfParseError`. -/
def parseElf64 (bytes : ByteArray) : Except ElfParseError Elf64Parsed := do
  let ehdr ← parseElf64Header bytes
  let phdrs ← parsePhdrs bytes ehdr
  let _ ← validateSegmentsAux bytes phdrs 0
  let shdrs ← parseShdrs bytes ehdr
  let sectionData ← extractSectionsAux bytes shdrs 0
  pure { ehdr, phdrs, shdrs, sectionData }

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads a NUL-terminated byte run starting at `pos`, stopping at the first `0x00` byte or
    end-of-buffer (whichever comes first), NOT including the terminator. Structural recursion
    on `fuel`: total. -/
def readCStringBytesAux (bytes : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | fuel + 1, pos, acc =>
    if pos >= bytes.size then acc
    else
      let b := bytes.get! pos
      if b == 0 then acc
      else readCStringBytesAux bytes fuel (pos + 1) (acc.push b)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Reads the NUL-terminated byte run starting at `offset` in `bytes`. Fuel is
    `bytes.size + 1 - offset`, an always-sufficient (Nat-truncated-subtraction-safe even when
    `offset > bytes.size`) upper bound on how many bytes remain to scan. -/
def readCStringBytes (bytes : ByteArray) (offset : Nat) : ByteArray :=
  readCStringBytesAux bytes (bytes.size + 1 - offset) offset ByteArray.empty

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- The section-header string table's raw bytes, i.e. `sectionData[e_shstrndx]` --
    `ByteArray.empty` if `e_shnum = 0` or the index is out of range (both already rejected by
    `parseElf64Header`'s `invalidShstrndx` check whenever `e_shnum > 0`, so this `getD` default
    is unreachable dead-code safety, not a silent-acceptance path). -/
def Elf64Parsed.shstrtabBytes (p : Elf64Parsed) : ByteArray :=
  p.sectionData.getD p.ehdr.e_shstrndx.toNat ByteArray.empty

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Resolves a section header's name via the section-header string table, `none` if the
    resulting bytes are not valid UTF-8 (using `String.fromUTF8?`, never the panicking `!`
    variant -- see this module's header comment). -/
def Elf64Parsed.sectionName (p : Elf64Parsed) (sh : Elf64_Shdr) : Option String :=
  String.fromUTF8? (readCStringBytes p.shstrtabBytes sh.sh_name.toNat)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Looks up a section's raw file bytes by name (e.g. `.text`, `.rodata`), `none` if no
    section resolves to that name. This is the lookup an emitter-defect check uses to compare
    a parsed section's payload directly against the bytes originally handed to
    `Gasm.Targets.Linux.emitELF64Executable`. -/
def Elf64Parsed.sectionNamed (p : Elf64Parsed) (name : String) : Option ByteArray :=
  ((p.shdrs.zip p.sectionData).find? (fun (sh, _) => p.sectionName sh == some name)).map (·.2)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Zero-pads `bytes` up to `targetSize` (a no-op if already at least that long) -- the same
    shape as `Gasm.Targets.Linux.padTo`, reproduced locally so this file stays independent of
    the `Linux` target layer (`Gasm.Targets.ELF` is the shared base both `Linux` and
    `BareMetal` build on; it must not depend downward on either). -/
def padZerosTo (bytes : ByteArray) (targetSize : Nat) : ByteArray :=
  if bytes.size >= targetSize then bytes
  else bytes ++ ByteArray.mk (Array.replicate (targetSize - bytes.size) (0 : UInt8))

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Insertion-sort a `(fileOffset, bytes)` chunk list into ascending offset order. A small,
    self-contained, total sort (no dependency on any `Array.qsort`-shaped API this codebase
    does not already use elsewhere) -- the chunk count `serializeElf64Parsed` builds is always
    small (header + phdr table + one entry per section + shdr table), so insertion sort's
    quadratic worst case is irrelevant here. Structural recursion on the list: total. -/
def sortByOffsetInsert (item : Nat × ByteArray) : List (Nat × ByteArray) → List (Nat × ByteArray)
  | [] => [item]
  | x :: rest => if item.1 <= x.1 then item :: x :: rest else x :: sortByOffsetInsert item rest

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Sorts a `(fileOffset, bytes)` chunk list into ascending offset order. -/
def sortByOffset : List (Nat × ByteArray) → List (Nat × ByteArray)
  | [] => []
  | x :: rest => sortByOffsetInsert x (sortByOffset rest)

/- REF: docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer -/
/-- Re-serializes a parsed `Elf64Parsed` back into a `ByteArray`: places the file header at
    offset 0, the program header table at `ehdr.e_phoff`, every non-empty section's bytes at
    its own `sh_offset`, and the section header table at `ehdr.e_shoff`, zero-filling any gap
    between consecutive pieces (the same convention `Gasm.Targets.Linux.emitELF64Executable`
    itself uses via `padTo`). SCOPE (see this module's header comment and this task's
    deliverable-4 writeup): this placement strategy is only correct when the recorded offsets
    are pairwise non-overlapping and in a consistent order with their declared sizes --
    exactly the invariant every ELF64 file this project's own writer produces satisfies, and
    exactly what the parser-stability fuzzer (`Spikes/Common/ElfStabilityFuzzer.lean`) checks
    holds empirically against real emitted binaries. It is NOT a general-purpose ELF writer
    for arbitrary (e.g. adversarially overlapping) `Elf64Parsed` values -- a well-formedness
    hypothesis (offsets pairwise non-overlapping and consistent with declared sizes; `e_phnum`/
    `e_shnum` matching list lengths; `e_shstrndx` in range) would be needed for a general
    `parse (write x) = .ok x` theorem, and no such predicate is defined in this tree today --
    see `docs/TARGETS/LINUX.md#33-elf64-parser-stability-fuzzer` for the full writeup of why
    that theorem is not attempted in this pass. -/
def serializeElf64Parsed (p : Elf64Parsed) : ByteArray := Id.run do
  let mut chunks : List (Nat × ByteArray) := [(0, serializeElf64Header p.ehdr)]
  if !p.phdrs.isEmpty then
    let phdrBytes := (p.phdrs.map serializeElf64Phdr).foldl (· ++ ·) ByteArray.empty
    chunks := chunks ++ [(p.ehdr.e_phoff.toNat, phdrBytes)]
  for (sh, data) in p.shdrs.zip p.sectionData do
    if data.size > 0 then
      chunks := chunks ++ [(sh.sh_offset.toNat, data)]
  if !p.shdrs.isEmpty then
    let shdrBytes := (p.shdrs.map serializeElf64Shdr).foldl (· ++ ·) ByteArray.empty
    chunks := chunks ++ [(p.ehdr.e_shoff.toNat, shdrBytes)]
  let sorted := sortByOffset chunks
  let mut out := ByteArray.empty
  for (off, data) in sorted do
    out := padZerosTo out off
    out := out ++ data
  return out

end Gasm.Targets.ELF
