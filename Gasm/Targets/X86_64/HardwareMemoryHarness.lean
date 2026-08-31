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

import Gasm.Targets.X86_64.HardwareMemoryProtocol

namespace Gasm.Targets.X86_64.HardwareMemoryHarness

open Gasm.Core
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.HardwareMemoryPlan
open Gasm.Targets.X86_64.HardwareMemoryProtocol
open Gasm.Targets.Windows

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- An unprepared request.  The harness, not its caller, chooses the final mapped scratch address
    and calls `HardwareMemoryPlan.prepare` after computing the exact PE layout. -/
structure Request where
  caseId : UInt64
  form : ScratchMov
  seed : X86_64MachineState
  deriving Inhabited

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- A checked plan paired with the native observation bearing the same framed case identity.
    The constructor is harness-owned: callers may inspect an observation, but cannot relabel its
    plan or fabricate a result/plan pairing after native execution. -/
structure Observation where
  private mk ::
  plan : Plan
  result : Result

private def imageBase : UInt64 := 0x140000000
private def controlBytes : Nat := 32
private def outputStart : Nat := controlBytes

private def outputBytes (count : Nat) : Nat := count * recordBytes
private def scratchStart (count : Nat) : Nat := outputStart + alignUp (outputBytes count) 16
private def scratchOffset (count index : Nat) : Nat := scratchStart count + index * regionBytes

-- Windows x64 entry has RSP ≡ 8 (mod 16). Subtracting 0x58 both owns every slot below and
-- restores 16-byte call alignment. The first 32 bytes remain API shadow space.
private def stackFrameBytes : Nat := 0x58
private def savedRbxOffset : Nat := 0x20
private def savedRbpOffset : Nat := 0x28
private def savedRsiOffset : Nat := 0x30
private def savedRdiOffset : Nat := 0x38
private def capturedFlagsOffset : Nat := 0x40
private def capturedRaxOffset : Nat := 0x48

private structure StackSlot where
  offset : Nat
  width : Nat

private def stackSlots : List StackSlot := [
  ⟨savedRbxOffset, 8⟩, ⟨savedRbpOffset, 8⟩, ⟨savedRsiOffset, 8⟩,
  ⟨savedRdiOffset, 8⟩, ⟨capturedFlagsOffset, 8⟩, ⟨capturedRaxOffset, 8⟩
]

private def stackLayoutValid : Bool :=
  stackFrameBytes < 0x80 &&
  stackFrameBytes % 16 == 8 &&
  stackSlots.all (fun slot =>
    0x20 ≤ slot.offset && slot.width == 8 && slot.offset + slot.width ≤ stackFrameBytes) &&
  (stackSlots.map StackSlot.offset).eraseDups.length == stackSlots.length

/- REF: docs/TARGETS/WINDOWS.md#13-strict-prohibition-of-red-zone -/
-- Every harness temporary is in an owned, distinct stack slot. No capture lives below RSP.
#guard stackLayoutValid

private def putU8 (bytes : ByteArray) (offset : Nat) (value : UInt8) : ByteArray :=
  bytes.set! offset value

private def putU32 (bytes : ByteArray) (offset : Nat) (value : UInt32) : ByteArray :=
  let bytes := putU8 bytes offset value.toUInt8
  let bytes := putU8 bytes (offset + 1) (value >>> 8).toUInt8
  let bytes := putU8 bytes (offset + 2) (value >>> 16).toUInt8
  putU8 bytes (offset + 3) (value >>> 24).toUInt8

private def putU64 (bytes : ByteArray) (offset : Nat) (value : UInt64) : ByteArray :=
  let bytes := putU32 bytes offset value.toUInt32
  putU32 bytes (offset + 4) (value >>> 32).toUInt32

private def putBytes (target : ByteArray) (offset : Nat) (source : ByteArray) : ByteArray := Id.run do
  let mut result := target
  for i in [0:source.size] do
    result := putU8 result (offset + i) (source.get! i)
  result

private def makeRdata (plans : List Plan) : ByteArray := Id.run do
  let total := max 512 (scratchStart plans.length + plans.length * regionBytes)
  let mut bytes := ByteArray.mk (Array.replicate total (0 : UInt8))
  for i in [0:plans.length] do
    let plan := plans[i]!
    let out := outputStart + i * recordBytes
    bytes := putU64 bytes out wireMagic
    bytes := putU32 bytes (out + 8) wireVersion
    bytes := putU32 bytes (out + 12) recordBytes.toUInt32
    bytes := putU64 bytes (out + 16) plan.caseId
    bytes := putU32 bytes (out + 24) regionBytes.toUInt32
    bytes := putBytes bytes (out + planIdentityOffset) plan.planIdentity
    bytes := putBytes bytes (scratchOffset plans.length i) plan.regionBefore
  bytes

private def storeRegDisp32 (rex modrm : UInt8) (disp : Nat) : ByteArray :=
  ByteArray.mk #[rex, 0x89, modrm] ++ uint32ToLittleEndian disp.toUInt32

private def loadRegDisp32 (rex modrm : UInt8) (disp : Nat) : ByteArray :=
  ByteArray.mk #[rex, 0x8B, modrm] ++ uint32ToLittleEndian disp.toUInt32

private def buildText (layout : SectionLayout) (plans : List Plan) : ByteArray := Id.run do
  let totalTests := plans.length
  let outBufferSize := outputBytes totalTests
  let textRva := layout.textRva.toUInt64
  let rdataRva := layout.rdataRva.toUInt64
  let idataRva := layout.idataRva.toUInt64
  let recoveryRipVarAddr := imageBase + rdataRva
  let currentOutVarAddr := imageBase + rdataRva + 8
  let savedRspVarAddr := imageBase + rdataRva + 16
  let outBufferAddr := imageBase + rdataRva + outputStart.toUInt64

  let mut vehHandler := ByteArray.empty
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x51, 0x08]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian recoveryRipVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x89, 0x82, 0xF8, 0x00, 0x00, 0x00]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x89, 0x82, 0x98, 0x00, 0x00, 0x00]
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian currentOutVarAddr
  vehHandler := vehHandler ++ ByteArray.mk #[0x48, 0x8B, 0x00]
  -- Framed fault marker at record byte 28.
  vehHandler := vehHandler ++ ByteArray.mk #[0xC6, 0x40, 0x1C, 0x01]
  vehHandler := vehHandler ++ ByteArray.mk #[0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xC3]

  let jmpToMain := ByteArray.mk #[0xEB, vehHandler.size.toUInt8]
  let vehHandlerAddr := imageBase + textRva + jmpToMain.size.toUInt64

  let mut mainBody := ByteArray.empty
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x83, 0xEC, stackFrameBytes.toUInt8]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x5C, 0x24, savedRbxOffset.toUInt8]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x6C, 0x24, savedRbpOffset.toUInt8]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x74, 0x24, savedRsiOffset.toUInt8]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x7C, 0x24, savedRdiOffset.toUInt8]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0x89, 0x20]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0x01, 0x00, 0x00, 0x00]
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian vehHandlerAddr
  let addVehIatAddr := imageBase + idataRva + 0x18
  mainBody := mainBody ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian addVehIatAddr
  mainBody := mainBody ++ ByteArray.mk #[0xFF, 0x10]

  let mut testLoop := ByteArray.empty
  for testIdx in [0:totalTests] do
    let plan := plans[testIdx]!
    let state := plan.initialState
    let testOutAddr := outBufferAddr + (testIdx * recordBytes).toUInt64
    let scratchAddr := plan.regionBase
    let mut block := ByteArray.empty

    let validFlags := (state.flags &&& arithmeticStatusMask) ||| 2
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian validFlags
    block := block ++ ByteArray.mk #[0x50, 0x9D]
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

    -- The exact production bytes stored by `prepare`; there is no native-side reconstruction.
    block := block ++ plan.instructionBytes

    block := block ++ ByteArray.mk #[0x9C, 0x8F, 0x44, 0x24, capturedFlagsOffset.toUInt8]
    block := block ++ ByteArray.mk #[0x48, 0x89, 0x44, 0x24, capturedRaxOffset.toUInt8]
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian testOutAddr
    block := block ++ storeRegDisp32 0x48 0x88 (registerResultOffset .rcx)
    block := block ++ storeRegDisp32 0x48 0x90 (registerResultOffset .rdx)
    block := block ++ storeRegDisp32 0x48 0x98 (registerResultOffset .rbx)
    block := block ++ storeRegDisp32 0x48 0xA0 (registerResultOffset .rsp)
    block := block ++ storeRegDisp32 0x48 0xA8 (registerResultOffset .rbp)
    block := block ++ storeRegDisp32 0x48 0xB0 (registerResultOffset .rsi)
    block := block ++ storeRegDisp32 0x48 0xB8 (registerResultOffset .rdi)
    block := block ++ storeRegDisp32 0x4C 0x80 (registerResultOffset .r8)
    block := block ++ storeRegDisp32 0x4C 0x88 (registerResultOffset .r9)
    block := block ++ storeRegDisp32 0x4C 0x90 (registerResultOffset .r10)
    block := block ++ storeRegDisp32 0x4C 0x98 (registerResultOffset .r11)
    block := block ++ storeRegDisp32 0x4C 0xA0 (registerResultOffset .r12)
    block := block ++ storeRegDisp32 0x4C 0xA8 (registerResultOffset .r13)
    block := block ++ storeRegDisp32 0x4C 0xB0 (registerResultOffset .r14)
    block := block ++ storeRegDisp32 0x4C 0xB8 (registerResultOffset .r15)
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x4C, 0x24, capturedFlagsOffset.toUInt8]
    block := block ++ storeRegDisp32 0x48 0x88 flagsResultOffset -- flags through rcx
    block := block ++ loadRegDisp32 0x48 0x88 (registerResultOffset .rcx)
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x54, 0x24, capturedRaxOffset.toUInt8]
    block := block ++ storeRegDisp32 0x48 0x90 (registerResultOffset .rax)

    -- Registers are already captured, so rax/rcx/rdx are now scratch temporaries.
    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian testOutAddr
    block := block ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian scratchAddr
    for chunkIndex in List.range (regionBytes / 8) do
      let offset := chunkIndex * 8
      block := block ++ ByteArray.mk #[0x48, 0x8B, 0x4A, offset.toUInt8]
      block := block ++ storeRegDisp32 0x48 0x88 (regionResultOffset + offset)

    block := block ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
    block := block ++ ByteArray.mk #[0x48, 0x8B, 0x20]

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

  let mut epilogue := ByteArray.empty
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian savedRspVarAddr
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x20]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x5C, 0x24, savedRbxOffset.toUInt8]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x6C, 0x24, savedRbpOffset.toUInt8]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x74, 0x24, savedRsiOffset.toUInt8]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x8B, 0x7C, 0x24, savedRdiOffset.toUInt8]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0xF5, 0xFF, 0xFF, 0xFF]
  let getStdHandleIatAddr := imageBase + idataRva
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian getStdHandleIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10, 0x48, 0x89, 0xC1]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian outBufferAddr
  epilogue := epilogue ++ ByteArray.mk #[0x49, 0xC7, 0xC0] ++ uint32ToLittleEndian outBufferSize.toUInt32
  epilogue := epilogue ++ ByteArray.mk #[0x4C, 0x8D, 0x4C, 0x24, 0x28]
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0x44, 0x24, 0x20, 0, 0, 0, 0]
  let writeFileIatAddr := imageBase + idataRva + 8
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian writeFileIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10, 0x48, 0x31, 0xC9]
  let exitProcessIatAddr := imageBase + idataRva + 16
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian exitProcessIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  jmpToMain ++ vehHandler ++ mainBody ++ testLoop ++ epilogue

private def planForLayout (layout : SectionLayout) (requests : List Request) : Except String (List Plan) := do
  let mut plans : List Plan := []
  for i in [0:requests.length] do
    let request := requests[i]!
    let regionBase := imageBase + layout.rdataRva.toUInt64 + (scratchOffset requests.length i).toUInt64
    let plan ← prepare request.caseId request.form request.seed regionBase
    plans := plans ++ [plan]
  pure plans

private def idsDistinct (requests : List Request) : Bool :=
  let ids := requests.map (·.caseId)
  ids.eraseDups.length == ids.length

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Prepares exact layout-dependent plans and emits their native PE runner.  A dummy layout is used
    only to discover text size; all accepted plans are rebuilt against the final layout, and text
    size must remain invariant before emission. -/
def emit (requests : List Request) : Except String (List Plan × ByteArray) := do
  if requests.isEmpty then throw "scratch-memory hardware batch must be nonempty"
  if !idsDistinct requests then throw "scratch-memory hardware case identities must be unique"
  let importNames := ["GetStdHandle", "WriteFile", "ExitProcess", "AddVectoredExceptionHandler"]
  let dummyLayout : SectionLayout := {
    textRawSize := 512, rdataRva := 0x2000, rdataRawSize := 512,
    idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000
  }
  let dummyPlans ← planForLayout dummyLayout requests
  let dummyText := buildText dummyLayout dummyPlans
  let dummyRdata := makeRdata dummyPlans
  let idataEst := buildKernel32IDataSection 0x3000 importNames
  let layout := computeSectionLayout dummyText.size dummyRdata.size idataEst.size
  let plans ← planForLayout layout requests
  let text := buildText layout plans
  if text.size != dummyText.size then throw "scratch-memory PE text size changed after final address planning"
  let rdata := makeRdata plans
  pure (plans, emitPE32Executable text rdata importNames)

/- REF: docs/TRUST_REBUILD_PLAN.md#25-applicability-and-checked-access-authority -/
/-- Executes an exact scratch-memory batch.  Output is read to EOF and decoded with exact framing;
    native faults are rejected because this first slice admits only wholly mapped, nonfaulting
    scratch accesses and therefore makes no partial-postimage claim. -/
def run (requests : List Request)
    (tmpExePath : String := "./.tmp_gasm_hw_memory.exe") : IO (Except String (List Observation)) := do
  let (plans, exeBytes) ← match emit requests with
    | .ok prepared => pure prepared
    | .error msg => return .error msg
  IO.FS.writeBinFile tmpExePath exeBytes
  try
    let child ← IO.Process.spawn { cmd := tmpExePath, stdout := .piped, stderr := .piped }
    let mut outBytes := ByteArray.empty
    let mut reading := true
    while reading do
      let chunk ← child.stdout.read 4096
      if chunk.isEmpty then reading := false else outBytes := outBytes ++ chunk
    let stderrMsg ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode != 0 then
      return .error s!"scratch-memory harness exited with code {exitCode}: {stderrMsg}"
    let results ← match decodeBatch outBytes (plans.map (·.caseId)) with
      | .ok results => pure results
      | .error msg => return .error msg
    if results.any (·.machine.faulted) then
      return .error "scratch-memory harness observed an instruction fault in a nonfaulting mapped plan"
    pure <| .ok (plans.zip results |>.map fun pair => Observation.mk pair.1 pair.2)
  catch e =>
    pure <| .error s!"scratch-memory harness failed to spawn or execute: {e}"

end Gasm.Targets.X86_64.HardwareMemoryHarness
