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
import Gasm.Core.Rng
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.Windows.Emitter
import Gasm.Targets.Windows.Win32API

namespace Gasm.Targets.X86_64.HardwareHarness

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Result captured from hardware execution for a single test case. -/
structure HardwareExecutionResult where
  gprs    : Reg64 → UInt64
  flags   : UInt64
  faulted : Bool := false

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
instance : Inhabited HardwareExecutionResult where
  default := { gprs := fun _ => 0, flags := 0, faulted := false }

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Decodes 136 binary bytes from hardware output into HardwareExecutionResult. -/
def decodeHardwareResult (bytes : ByteArray) (offset : Nat) : HardwareExecutionResult := Id.run do
  let getU8 (off : Nat) : UInt64 :=
    if off < bytes.size then (bytes.get! off).toUInt64 else 0

  let getU64 (off : Nat) : UInt64 :=
    let b0 := getU8 (off + 0)
    let b1 := getU8 (off + 1)
    let b2 := getU8 (off + 2)
    let b3 := getU8 (off + 3)
    let b4 := getU8 (off + 4)
    let b5 := getU8 (off + 5)
    let b6 := getU8 (off + 6)
    let b7 := getU8 (off + 7)
    b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

  let rax := getU64 (offset + 0)
  let rcx := getU64 (offset + 8)
  let rdx := getU64 (offset + 16)
  let rbx := getU64 (offset + 24)
  let rsp := getU64 (offset + 32)
  let rbp := getU64 (offset + 40)
  let rsi := getU64 (offset + 48)
  let rdi := getU64 (offset + 56)
  let r8  := getU64 (offset + 64)
  let r9  := getU64 (offset + 72)
  let r10 := getU64 (offset + 80)
  let r11 := getU64 (offset + 88)
  let r12 := getU64 (offset + 96)
  let r13 := getU64 (offset + 104)
  let r14 := getU64 (offset + 112)
  let r15 := getU64 (offset + 120)
  let flg := getU64 (offset + 128)
  let faulted := getU8 (offset + 135) != 0

  let gprsMap (r : Reg64) : UInt64 :=
    match r with
    | Reg64.rax => rax | Reg64.rcx => rcx | Reg64.rdx => rdx | Reg64.rbx => rbx
    | Reg64.rsp => rsp | Reg64.rbp => rbp | Reg64.rsi => rsi | Reg64.rdi => rdi
    | Reg64.r8  => r8  | Reg64.r9  => r9  | Reg64.r10 => r10 | Reg64.r11 => r11
    | Reg64.r12 => r12 | Reg64.r13 => r13 | Reg64.r14 => r14 | Reg64.r15 => r15

  { gprs := gprsMap, flags := flg, faulted := faulted }

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Builds the .text bytecode for test execution using the exact computed section layout. -/
def buildTestText (layout : SectionLayout) (testCases : List (X86_64MachineState × ByteArray)) : ByteArray := Id.run do
  let totalTests := testCases.length
  let outBufferSize := totalTests * 136
  let imageBase : UInt64 := 0x140000000
  let textRva   : UInt64 := layout.textRva.toUInt64
  let rdataRva  : UInt64 := layout.rdataRva.toUInt64
  let idataRva  : UInt64 := layout.idataRva.toUInt64

  let recoveryRipVarAddr : UInt64 := imageBase + rdataRva + 0
  let currentOutVarAddr  : UInt64 := imageBase + rdataRva + 8
  let savedRspVarAddr    : UInt64 := imageBase + rdataRva + 16
  let outBufferAddr      : UInt64 := imageBase + rdataRva + 24

  -- 1. VEH Handler Code at beginning of .text (offset 0)
  let mut vehHandler := ByteArray.empty
  -- mov rdx, [rcx+8] (pContextRecord)
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x51, 0x08]
  -- mov rax, recoveryRipVarAddr; mov rax, [rax]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian recoveryRipVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  -- mov [rdx+0xF8], rax (pContextRecord.Rip)
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x89, 0x82, 0xF8, 0x00, 0x00, 0x00]
  -- mov rax, savedRspVarAddr; mov rax, [rax]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  -- mov [rdx+0x98], rax (pContextRecord.Rsp)
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x89, 0x82, 0x98, 0x00, 0x00, 0x00]
  -- mov rax, currentOutVarAddr; mov rax, [rax]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian currentOutVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  -- mov byte ptr [rax+135], 1 (set faulted = true)
  vehHandler := vehHandler ++ ByteArray.mk #[0xC6, 0x80, 0x87, 0x00, 0x00, 0x00, 0x01]
  -- mov eax, 0xFFFFFFFF (EXCEPTION_CONTINUE_EXECUTION)
  vehHandler := vehHandler ++ ByteArray.mk #[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]
  -- ret
  vehHandler := vehHandler ++ ByteArray.mk #[0xC3]

  let jmpToMain := ByteArray.mk #[0xEB, (vehHandler.size).toUInt8] -- jmp short past vehHandler
  let vehHandlerAddr : UInt64 := imageBase + textRva + jmpToMain.size.toUInt64

  -- 2. Entry point prologue (starts immediately after VEH handler)
  let mut mainBody := ByteArray.empty
  -- sub rsp, 72
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x83, 0xEC, 0x48]
  -- save rbx, rbp, rsi, rdi
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x5C, 0x24, 0x20]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x6C, 0x24, 0x28]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x74, 0x24, 0x30]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x7C, 0x24, 0x38]

  -- Save pristine RSP into savedRspVarAddr: mov rax, savedRspVarAddr; mov [rax], rsp
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x20]

  -- Register VEH: AddVectoredExceptionHandler(1, vehHandlerAddr)
  -- mov rcx, 1
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0x01, 0x00, 0x00, 0x00]
  -- mov rdx, vehHandlerAddr
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian vehHandlerAddr
  -- mov rax, [idataRva + 0x18] (AddVectoredExceptionHandler)
  let addVehIatAddr := imageBase + idataRva + 0x18
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian addVehIatAddr
  mainBody := mainBody ++ ByteArray.mk #[0xFF, 0x10] -- call [rax]

  -- Build test vector loop
  let mut testLoop := ByteArray.empty
  for testIdx in [0:totalTests] do
    let (state, instrBytes) := testCases[testIdx]!
    let testOutAddr := outBufferAddr + (testIdx * 136).toUInt64

    -- Construct test block payload first
    let mut block := ByteArray.empty

    -- Load initial RFLAGS: mov rax, state.flags; push rax; popfq
    let validFlags := (state.flags &&& arithmeticStatusMask) ||| 2
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian validFlags
    block := block ++ ByteArray.mk #[0x50, 0x9D]

    -- Load all GPRs (except rsp which remains stack-backed)
    block := block ++ ByteArray.mk #[0x48, 0xB9] ++ uint64ToLittleEndian (state.gprs .rcx)
    block := block ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian (state.gprs .rdx)
    block := block ++ ByteArray.mk #[0x48, 0xBB] ++ uint64ToLittleEndian (state.gprs .rbx)
    block := block ++ ByteArray.mk #[0x48, 0xBD] ++ uint64ToLittleEndian (state.gprs .rbp)
    block := block ++ ByteArray.mk #[0x48, 0xBE] ++ uint64ToLittleEndian (state.gprs .rsi)
    block := block ++ ByteArray.mk #[0x48, 0xBF] ++ uint64ToLittleEndian (state.gprs .rdi)
    block := block ++ ByteArray.mk #[0x49, 0xB8] ++ uint64ToLittleEndian (state.gprs .r8)
    block := block ++ ByteArray.mk #[0x49, 0xB9] ++ uint64ToLittleEndian (state.gprs .r9)
    block := block ++ ByteArray.mk #[0x49, 0xBA] ++ uint64ToLittleEndian (state.gprs .r10)
    block := block ++ ByteArray.mk #[0x49, 0xBB] ++ uint64ToLittleEndian (state.gprs .r11)
    block := block ++ ByteArray.mk #[0x49, 0xBC] ++ uint64ToLittleEndian (state.gprs .r12)
    block := block ++ ByteArray.mk #[0x49, 0xBD] ++ uint64ToLittleEndian (state.gprs .r13)
    block := block ++ ByteArray.mk #[0x49, 0xBE] ++ uint64ToLittleEndian (state.gprs .r14)
    block := block ++ ByteArray.mk #[0x49, 0xBF] ++ uint64ToLittleEndian (state.gprs .r15)
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian (state.gprs .rax)

    -- Execute instruction under test
    block := block ++ instrBytes

    -- Capture RFLAGS and all 16 GPRs without clobbering any register
    block := block ++ ByteArray.mk #[0x9C]                          -- pushfq
    block := block ++ ByteArray.mk #[0x8F, 0x44, 0x24, 0xF8]       -- pop qword ptr [rsp-8] (flags)
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x44, 0x24, 0xF0] -- mov [rsp-16], rax
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian testOutAddr -- mov rax, testOutAddr
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x48, 0x08]       -- mov [rax+8], rcx
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x50, 0x10]       -- mov [rax+16], rdx
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x58, 0x18]       -- mov [rax+24], rbx
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x60, 0x20]       -- mov [rax+32], rsp
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x68, 0x28]       -- mov [rax+40], rbp
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x70, 0x30]       -- mov [rax+48], rsi
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x78, 0x38]       -- mov [rax+56], rdi
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x40, 0x40]       -- mov [rax+64], r8
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x48, 0x48]       -- mov [rax+72], r9
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x50, 0x50]       -- mov [rax+80], r10
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x58, 0x58]       -- mov [rax+88], r11
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x60, 0x60]       -- mov [rax+96], r12
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x68, 0x68]       -- mov [rax+104], r13
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x70, 0x70]       -- mov [rax+112], r14
    block := block ++ ByteArray.mk #[0x4C, 0x89, 0x78, 0x78]       -- mov [rax+120], r15
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x4C, 0x24, 0xF8] -- mov rcx, [rsp-8] (flags)
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x88, 0x80, 0x00, 0x00, 0x00] -- mov [rax+128], rcx
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x48, 0x08]       -- mov rcx, [rax+8] (restore rcx)
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x54, 0x24, 0xF0] -- mov rdx, [rsp-16] (original rax)
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x10]             -- mov [rax], rdx (store original rax)

    -- Reset pristine RSP: mov rax, savedRspVarAddr; mov rsp, [rax]
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x20]

    -- Setup code: 23 bytes for currentRecoveryRip + 23 bytes for currentTestOutAddr = 46 bytes
    let setupSize := 46
    let recoveryOffset := jmpToMain.size + vehHandler.size + mainBody.size + testLoop.size + setupSize + block.size
    let recoveryRip := imageBase + textRva + recoveryOffset.toUInt64

    let mut setup := ByteArray.empty
    setup := setup ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian recoveryRipVarAddr
    setup := setup ++ ByteArray.mk #[0x48, 0xB9] ++ uint64ToLittleEndian recoveryRip
    setup := setup ++ ByteArray.mk #[0x48, 0x89, 0x08]

    setup := setup ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian currentOutVarAddr
    setup := setup ++ ByteArray.mk #[0x48, 0xB9] ++ uint64ToLittleEndian testOutAddr
    setup := setup ++ ByteArray.mk #[0x48, 0x89, 0x08]

    testLoop := testLoop ++ setup ++ block

  -- Epilogue
  let mut epilogue := ByteArray.empty
  -- Restore pristine RSP: mov rax, savedRspVarAddr; mov rsp, [rax]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x20]

  -- Restore non-volatile registers
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x5C, 0x24, 0x20]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x6C, 0x24, 0x28]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x74, 0x24, 0x30]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x7C, 0x24, 0x38]

  -- Call GetStdHandle(STD_OUTPUT_HANDLE = -11)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0xF5, 0xFF, 0xFF, 0xFF]
  let getStdHandleIatAddr := imageBase + idataRva + 0x00
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian getStdHandleIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  -- Call WriteFile(hStdout, outBufferAddr, outBufferSize, &written, NULL)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x89, 0xC1]                                       -- mov rcx, rax (hStdout)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian outBufferAddr      -- mov rdx, outBufferAddr
  epilogue := epilogue ++ ByteArray.mk #[0x49, 0xC7, 0xC0] ++ uint32ToLittleEndian outBufferSize.toUInt32 -- mov r8, outBufferSize
  epilogue := epilogue ++ ByteArray.mk #[0x4C, 0x8D, 0x4C, 0x24, 0x28]                         -- mov r9, rsp+0x28 (&written)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] -- mov qword ptr [rsp+0x20], 0 (lpOverlapped)
  let writeFileIatAddr := imageBase + idataRva + 0x08
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian writeFileIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  -- Call ExitProcess(0)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x31, 0xC9]
  let exitProcessIatAddr := imageBase + idataRva + 0x10
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian exitProcessIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  jmpToMain ++ vehHandler ++ mainBody ++ testLoop ++ epilogue

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Emits a native PE executable that registers a Vectored Exception Handler (VEH), executes test cases on host CPU, and writes binary results. -/
def emitNativeBatchTestExe (testCases : List (X86_64MachineState × ByteArray)) (outFileName : String := ".tmp_gasm_hw_out.bin") : ByteArray := Id.run do
  let totalTests := testCases.length
  let outBufferSize := totalTests * 136
  let outNameBytes := String.toUTF8 (outFileName ++ "\x00")
  let rdataTotal := 32 + alignUp outBufferSize 16 + outNameBytes.size
  let rdata := ByteArray.mk (Array.replicate (max 512 rdataTotal) (0 : UInt8))
  let importNames := ["GetStdHandle", "WriteFile", "ExitProcess", "AddVectoredExceptionHandler"]

  let dummyLayout : SectionLayout := { textRawSize := 512, rdataRva := 0x2000, rdataRawSize := 512, idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 }
  let dummyText := buildTestText dummyLayout testCases
  let idataEst := buildKernel32IDataSection 0x3000 importNames
  let layout := computeSectionLayout dummyText.size rdata.size idataEst.size
  let text := buildTestText layout testCases

  emitPE32Executable text rdata importNames

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Executes a batch of test vectors natively on the CPU using a Gasm-emitted Windows PE runner.
    Structural guarantee against a fail-open hardware oracle: the only way to produce a
    `HardwareExecutionResult` is by decoding the harness's actual captured output bytes via
    `decodeHardwareResult`. Every failure mode — the harness process failing to spawn, exiting
    abnormally, or writing a short/garbled output buffer — is routed through `Except.error`
    instead of ever constructing a `HardwareExecutionResult`, so a harness that isn't really
    executing cannot masquerade as one that produced real (e.g. all-faulted) results: there is
    no code path left that fabricates a value of the success type. -/
def runHardwareBatch (testCases : List (X86_64MachineState × ByteArray)) (tmpExePath : String := "./.tmp_gasm_hw_fuzz.exe") (tmpOutPath : String := ".tmp_gasm_hw_out.bin") : IO (Except String (List HardwareExecutionResult)) := do
  if testCases.isEmpty then return .ok []
  let exeBytes := emitNativeBatchTestExe testCases tmpOutPath
  IO.FS.writeBinFile tmpExePath exeBytes

  try
    let child ← IO.Process.spawn {
      cmd := tmpExePath
      stdout := .piped
      stderr := .piped
    }
    let expectedBytes := testCases.length * 136
    let outBytes ← child.stdout.read expectedBytes.toUSize
    let exitCode ← child.wait

    if outBytes.size < expectedBytes then
      let stderrMsg ← child.stderr.readToEnd
      return .error s!"Hardware fuzz harness '{tmpExePath}' produced {outBytes.size}/{expectedBytes} expected bytes (exit code {exitCode}): {stderrMsg}"

    let mut results : List HardwareExecutionResult := []
    for i in [0:testCases.length] do
      let res := decodeHardwareResult outBytes (i * 136)
      results := results ++ [res]
    return .ok results
  catch e =>
    return .error s!"Hardware fuzz harness '{tmpExePath}' failed to spawn or execute: {e}"

/- REF: docs/TARGETS/WINDOWS.md#1-microsoft-x64-calling-convention -/
/-- Mandatory hardware-oracle world-sanity gate: runs a known-answer positive control (a
    deterministic `mov r64, imm64` that must execute without faulting and produce an exact
    register match) and a known-fault negative control (`div` by zero, which must be reported
    as faulted) through the exact same `runHardwareBatch` path used by real fuzz vectors, before
    any real vectors are tested. These no longer serve as the defense against a fail-open
    oracle (the `Except` return type of `runHardwareBatch` makes fabricated results
    unrepresentable, so that defense is structural), but they still confirm the world the
    harness runs in is actually behaving as expected end-to-end — CPU executing injected code,
    VEH installed and firing, output buffer decoded correctly. Throws and aborts the entire run
    on any control failure, including `runHardwareBatch` itself reporting `Except.error`. -/
def verifyHardwareOracleControls : IO Unit := do
  let positiveState : X86_64MachineState := (default : X86_64MachineState).setGpr64 .rax 0
  let positiveBytes : ByteArray := ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian 0xC0FFEE1234 -- mov rax, 0xC0FFEE1234
  let negativeState : X86_64MachineState := ((default : X86_64MachineState).setGpr64 .rbx 0).setGpr64 .rax 42
  let negativeBytes : ByteArray := ByteArray.mk #[0x48, 0xF7, 0xF3] -- div rbx (RDX:RAX / RBX, RBX = 0 => #DE)

  let testCases : List (X86_64MachineState × ByteArray) := [(positiveState, positiveBytes), (negativeState, negativeBytes)]
  let resultsE ← runHardwareBatch testCases "./.tmp_gasm_hw_control.exe" ".tmp_gasm_hw_control_out.bin"
  match resultsE with
  | .error msg =>
    throw (IO.userError s!"HARDWARE ORACLE SANITY CHECK FAILED: the harness could not execute the control vectors at all ({msg}). Aborting: the hardware fuzzer cannot be trusted.")
  | .ok [posRes, negRes] =>
    if posRes.faulted then
      throw (IO.userError "HARDWARE ORACLE SANITY CHECK FAILED: positive control (mov rax, 0xC0FFEE1234) reported faulted=true. The hardware harness is not actually executing test vectors.")
    else if posRes.gprs .rax != 0xC0FFEE1234 then
      throw (IO.userError s!"HARDWARE ORACLE SANITY CHECK FAILED: positive control expected RAX=0xC0FFEE1234, got {formatHex64 (posRes.gprs .rax)}. The hardware harness is not executing test vectors correctly.")
    else if !negRes.faulted then
      throw (IO.userError "HARDWARE ORACLE SANITY CHECK FAILED: negative control (div rbx with RBX=0) did not report faulted=true. The hardware harness is not detecting real CPU faults.")
    else
      pure ()
  | .ok _ =>
    throw (IO.userError "HARDWARE ORACLE SANITY CHECK FAILED: runHardwareBatch returned an unexpected number of control results.")

end Gasm.Targets.X86_64.HardwareHarness
