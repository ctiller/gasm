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
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Assembler
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Linker
import Stdlib.Zlib.Windows
import Spikes.Spike5Gzip.Spec

namespace Spikes.Spike5Gzip.Windows

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Windows
open Gasm.Targets.Windows.Linker
open Stdlib.Zlib.Windows
open Spikes.Spike5Gzip

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Symbolic program definition for Spike 5 on Windows x86_64 directly calling Stdlib.Zlib.Windows routines. -/
def spike5SymbolicProgram : List SymbolicInstr :=
  gzipStreamSymbolicProgram

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Linked binary program artifact for Spike 5 Windows. -/
def spike5Linked : LinkedWindowsProgram :=
  linkWindowsProgram spike5SymbolicProgram [("gzipHeaderBytes", gzipHeaderBytes)]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Lowered concrete machine instruction sequence for Spike 5 Windows. -/
def spike5Instructions : List X86_64Instr :=
  spike5Linked.instructions

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Complete Windows executable specification for Spike 5 GZIP compressor. -/
def spike5Executable : WindowsExecutable :=
  spike5Linked.executable

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Symbolic program definition for Spike 5 GUNZIP decompressor on Windows x86_64. -/
def spike5GunzipSymbolicProgram : List SymbolicInstr :=
  gunzipStreamSymbolicProgram

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Linked binary program artifact for Spike 5 GUNZIP Windows. -/
def spike5GunzipLinked : LinkedWindowsProgram :=
  linkWindowsProgram spike5GunzipSymbolicProgram []

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Lowered concrete machine instruction sequence for Spike 5 GUNZIP Windows. -/
def spike5GunzipInstructions : List X86_64Instr :=
  spike5GunzipLinked.instructions

/- REF: docs/SPIKES/SPIKE5_GZIP.md#41-x8664-windows-kernel32dll -/
/-- Complete Windows executable specification for Spike 5 GUNZIP decompressor. -/
def spike5GunzipExecutable : WindowsExecutable :=
  spike5GunzipLinked.executable

end Spikes.Spike5Gzip.Windows
