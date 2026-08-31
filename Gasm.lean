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
import Gasm.Core.CFGBuilder
import Gasm.Core.RecursiveCFGBuilder
import Gasm.Core.Callable
import Gasm.Core.ABI
import Gasm.Core.AbiContext
import Gasm.Core.Platform
import Gasm.Core.Verification

import Gasm.Proof.LocalExecution

import Gasm.MemoryModel.CpuGraph
import Gasm.MemoryModel.CpuGraphPremiseControls
import Gasm.MemoryModel.ProgramOrder
import Gasm.MemoryModel.ProgramOrderPremiseControls
import Gasm.MemoryModel.FiniteSearch
import Gasm.MemoryModel.CpuGraphNegativeControls
import Gasm.MemoryModel.FiniteSearchNegativeControls
import Gasm.MemoryModel.StructuralBaselineFixture
import Gasm.MemoryModel.RelationPath
import Gasm.MemoryModel.RelationPathControls
import Gasm.MemoryModel.CpuGraphOrderPath
import Gasm.MemoryModel.CpuGraphOrderPathControls
import Gasm.MemoryModel.CpuGraphCoherencePath
import Gasm.MemoryModel.CpuGraphCoherencePathControls
import Gasm.MemoryModel.Envelope
import Gasm.MemoryModel.EnvelopeControls
import Gasm.MemoryModel.AddressRange
import Gasm.MemoryModel.AddressRangeControls
import Gasm.MemoryModel.EnvelopeOccurrencePath
import Gasm.MemoryModel.EnvelopeOccurrencePathControls
import Gasm.MemoryModel.BindingHistory
import Gasm.MemoryModel.ObligationWorld
import Gasm.MemoryModel.ObligationWorldControls
import Gasm.MemoryModel.BindingHistoryControls
import Gasm.MemoryModel.ProgramOrderPath
import Gasm.MemoryModel.ProgramOrderPathControls

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
import Gasm.Targets.X86_64.MemoryRange
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
import Gasm.Targets.X86_64.MacroAssembler.Condition
import Gasm.Targets.X86_64.MacroAssembler.SelectedPrefixBridge
import Gasm.Targets.X86_64.MacroAssembler.ControlPoints
import Gasm.Targets.X86_64.CFGBridge
import Gasm.Targets.X86_64.CFGLinker
import Gasm.Targets.X86_64.EventfulSegment
import Gasm.Targets.X86_64.ExecutionCutpoint
import Gasm.Targets.X86_64.LocalBlockDischarge
import Gasm.Targets.X86_64.SelectedLoopTermination
import Gasm.Targets.X86_64.DecimalSegments
import Gasm.Targets.X86_64.DecimalStepFacts
import Gasm.Targets.X86_64.DecimalPass
import Gasm.Targets.X86_64.DecimalSchedule
import Gasm.Targets.X86_64.DecimalMacro
import Gasm.Targets.X86_64.DecimalMacroSelectedPrefix
import Gasm.Targets.X86_64.VerifiedProgramCFG
import Gasm.Targets.X86_64.HardwareHarness
import Gasm.Targets.X86_64.HardwareMemoryPlan
import Gasm.Targets.X86_64.HardwareMemoryProtocol
import Gasm.Targets.X86_64.HardwareMemoryHarness
import Gasm.Targets.X86_64.HardwareMemoryDifferential
import Gasm.Targets.X86_64.SemanticsFuzzer
-- Imported for elaboration-time compiled-environment audits: memory-hook sealing, exact frame
-- theorem types, live instruction-family witness population, and exact local round-trip gates.
-- These fail an ordinary build on drift; source-text spelling is not treated as proof evidence.
import Gasm.Targets.X86_64.InstructionCensus
import Gasm.Targets.X86_64.MemoryFrameAudit
import Gasm.Targets.X86_64.FamilyPipelineAudit
import Gasm.Targets.X86_64.StackStorePrefix
import Gasm.Targets.X86_64.StackStorePrefixLink
import Gasm.Targets.X86_64.StackStorePrefixExecution

import Gasm.Execution.QEMUAArch64

import Gasm.Targets.AArch64
import Gasm.Targets.AArch64.MacroAssembler
import Gasm.Targets.AArch64.MacroAssembler.PlatformBridge
import Gasm.Targets.AArch64.BareMetal.Device
import Gasm.Targets.AArch64.BareMetal.Emitter
import Gasm.Targets.AArch64.BareMetal.Executable
import Gasm.Targets.AArch64.BareMetal.Linker
import Gasm.Targets.AArch64.QEMU

import Gasm.Compiler.Word
import Gasm.Compiler.Word.MicrosoftX64
import Gasm.Compiler.Word.MicrosoftX64Platform
import Gasm.Compiler.Word.AArch64AAPCS64
import Gasm.Compiler.Word.LeanReify
import Gasm.Compiler.Word.Structured
import Gasm.Compiler.Word.StructuredCFG
import Gasm.Compiler.Word.StructuredLeanReify
import Gasm.Compiler.Word.StructuredPlanCompiler
import Gasm.Compiler.Word.StructuredStraightLine
import Gasm.Compiler.Word.StructuredStraightLineAArch64
import Gasm.Compiler.Word.StructuredStraightLineAArch64.Differential
import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry
import Gasm.Compiler.Word.StructuredStraightLineMicrosoftX64Entry.Differential
import Gasm.Compiler.Word.Examples
import Gasm.Compiler.TypedCFG

import Gasm.Targets.Windows.ABI
import Gasm.Targets.Windows.PEFormat
import Gasm.Targets.Windows.Win32API
import Gasm.Targets.Windows.ProcessEntryMemory
import Gasm.Targets.Windows.Emitter

import Gasm.Targets.ELF.Format
import Gasm.Targets.ELF.Notes
import Gasm.Targets.ELF.Parser

import Gasm.Targets.Linux.ABI
import Gasm.Targets.Linux.Syscall
import Gasm.Targets.Linux.OutcomeBridge
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
import Gasm.Targets.WASI.ObservableNormalization
