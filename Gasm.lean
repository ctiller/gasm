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
import Gasm.Core.Rng
import Gasm.Core.Arch
import Gasm.Core.Permissions
import Gasm.Core.Obligations
import Gasm.Core.State
import Gasm.Core.BlockM
import Gasm.Core.CFG
import Gasm.Core.Callable
import Gasm.Core.ABI
import Gasm.Core.AbiContext
import Gasm.Core.Platform
import Gasm.Core.Verification

import Gasm.MemoryModel.CpuGraph
import Gasm.MemoryModel.ProgramOrder
import Gasm.MemoryModel.FiniteSearch
import Gasm.MemoryModel.CpuGraphNegativeControls
import Gasm.MemoryModel.FiniteSearchNegativeControls
import Gasm.MemoryModel.StructuralBaselineFixture

import Gasm.Effects.Inject
import Gasm.Effects.Console
import Gasm.Effects.FileSystem
import Gasm.Effects.Process
import Gasm.Effects.Clock
import Gasm.Effects.Network
import Gasm.Effects.Trace
import Gasm.Effects.ReadBinder
import Gasm.Effects.ReadBinderWiring
import Gasm.Effects.CanonicalizeTrace

import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.X86_64.Instructions.Sub
import Gasm.Targets.X86_64.Instructions.Add
import Gasm.Targets.X86_64.Instructions.Mov
import Gasm.Targets.X86_64.Instructions.Lea
import Gasm.Targets.X86_64.Instructions.Xor
import Gasm.Targets.X86_64.Instructions.Call
import Gasm.Targets.X86_64.Instructions.Ret
import Gasm.Targets.X86_64.Instructions
import Gasm.Targets.X86_64.Encoding
import Gasm.Targets.X86_64.Decoder
import Gasm.Targets.X86_64.Disassembler
import Gasm.Targets.X86_64.Roundtrip
import Gasm.Targets.X86_64.Semantics
import Gasm.Targets.X86_64.MacroAssembler
import Gasm.Targets.X86_64.MacroAssembler.PlatformBridge
import Gasm.Targets.X86_64.CFGBridge
import Gasm.Targets.X86_64.HardwareHarness
import Gasm.Targets.X86_64.SemanticsFuzzer
-- Imported for its two elaboration-time `run_cmd` audits (memory-hook seal lint; frame-theorem
-- coverage against `Registry.expectedInstructionTypes`). Both fail the build, so this import is
-- what makes them run on an ordinary `lake build` rather than only when something happens to
-- pull in the module.
import Gasm.Targets.X86_64.MemoryFrameAudit

import Gasm.Execution.QEMUAArch64

import Gasm.Targets.AArch64
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Emitter
import Gasm.Targets.AArch64.BareMetal.Executable
import Gasm.Targets.AArch64.BareMetal.Linker
import Gasm.Targets.AArch64.QEMU

import Gasm.Compiler.Word
import Gasm.Compiler.Word.MicrosoftX64
import Gasm.Compiler.Word.MicrosoftX64Platform
import Gasm.Compiler.Word.Examples

import Gasm.Targets.Windows.ABI
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.Windows.Emitter

import Gasm.Targets.ELF.Format
import Gasm.Targets.ELF.Notes
import Gasm.Targets.ELF.Parser

import Gasm.Targets.Linux.ABI
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Linux.ELFFormat
import Gasm.Targets.Linux.Emitter
import Gasm.Targets.Linux.Linker
import Gasm.Targets.Dispatcher

import Gasm.Targets.Wasm.Types
import Gasm.Targets.Wasm.AST
import Gasm.Targets.Wasm.LEB128
import Gasm.Targets.Wasm.Binary
import Gasm.Targets.Wasm.Text
import Gasm.Targets.Wasm.Semantics
import Gasm.Targets.Wasm.Linker
import Gasm.Targets.Wasm.Fuzzable
import Gasm.Targets.Wasm.HostOracle
import Gasm.Targets.Wasm.SemanticsFuzzer

import Gasm.Targets.X86_64.EncodingFuzzer
import Gasm.Targets.X86_64.Fuzzer
import Gasm.Targets.X86_64.HardwareTimingHarness
import Gasm.Targets.X86_64.NASM
import Gasm.Targets.X86_64.PerfHardwareFuzzer
import Gasm.Targets.X86_64.Performance

import Gasm.Targets.BareMetal.ELFFormat
import Gasm.Targets.BareMetal.UART
import Gasm.Targets.BareMetal.Device
import Gasm.Targets.BareMetal.Emitter
import Gasm.Targets.BareMetal.Executable
import Gasm.Targets.BareMetal.Linker
import Gasm.Targets.BareMetal.QEMU

import Gasm.Targets.WASI.ABI
