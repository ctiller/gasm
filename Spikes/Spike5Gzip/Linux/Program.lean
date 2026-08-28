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
import Gasm.Targets.Linux.ELFFormat
import Gasm.Targets.Linux.Linker
import Stdlib.Zlib.Linux
import Spikes.Spike5Gzip.Spec

namespace Spikes.Spike5Gzip.Linux

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.Assembler
open Gasm.Targets.Linux
open Stdlib.Zlib.Linux
open Spikes.Spike5Gzip

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Symbolic program definition for Spike 5 on Linux x86_64 directly calling Stdlib.Zlib.Linux routines. -/
def spike5SymbolicProgram : List SymbolicInstr :=
  gzipStreamSymbolicProgram

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Linked binary program artifact for Spike 5 Linux. -/
def spike5Linked : LinkedLinuxProgram :=
  linkLinuxProgramStatic spike5SymbolicProgram [("gzipHeaderBytes", gzipHeaderBytes)]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Lowered concrete machine instruction sequence for Spike 5 Linux. -/
def spike5Instructions : List X86_64Instr :=
  spike5Linked.instructions

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Complete Linux executable specification for Spike 5 GZIP compressor. -/
def spike5Executable : LinuxExecutable :=
  spike5Linked.executable

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Symbolic program definition for Spike 5 GUNZIP decompressor on Linux x86_64. -/
def spike5GunzipSymbolicProgram : List SymbolicInstr :=
  gunzipStreamSymbolicProgram

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Linked binary program artifact for Spike 5 GUNZIP Linux. -/
def spike5GunzipLinked : LinkedLinuxProgram :=
  linkLinuxProgramStatic spike5GunzipSymbolicProgram [("gzipHeaderBytes", gzipHeaderBytes)]

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Lowered concrete machine instruction sequence for Spike 5 GUNZIP Linux. -/
def spike5GunzipInstructions : List X86_64Instr :=
  spike5GunzipLinked.instructions

/- REF: docs/SPIKES/SPIKE5_GZIP.md#2-monadic-specification-cli-state-machine -/
/-- Complete Linux executable specification for Spike 5 GUNZIP decompressor. -/
def spike5GunzipExecutable : LinuxExecutable :=
  spike5GunzipLinked.executable

end Spikes.Spike5Gzip.Linux
