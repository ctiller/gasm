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

/-
Gasm/Targets/X86_64/HardwareTimingHarness.lean - RDTSC/RDTSCP hardware measurement harness.
See docs/RDTSC_HARNESS.md for the full design (containment/escape-hatch/fail-closed rationale);
this file's own comments cover only mechanics.

WHY A NEW FILE, NOT AN EXTENSION OF HardwareHarness.lean's 136-byte capture. `CPUID` clobbers
RAX/RBX/RCX/RDX unconditionally; `HardwareHarness.buildTestText`'s existing correctness capture
both loads test-vector operands into those exact registers AND uses RAX/RCX as scratch to write
the capture buffer. Bracketing the existing single-shot block with CPUID would corrupt the very
registers that block exists to observe untouched. This file is therefore a second, independent
batch-run entry point (`runTimingBatch`, `Except`-typed exactly like `runHardwareBatch`) with its
own PE emission, never sharing a test block with the correctness harness. `HardwareHarness.lean`
itself is untouched by this file.

CPUID/RDTSCP ARE AN ESCAPE HATCH, not modeled `X86_64Instruction` instances -- see
docs/RDTSC_HARNESS.md #3 for the full reasoning (no meaningful `step` semantics, no consumer of a
correctness contract, matches the harness's own existing practice of hand-assembling
infrastructure bytes that never appear in an emittable `X86_64Instr` list).

MEASUREMENT METHODOLOGY (docs/RDTSC_HARNESS.md #6): straight-line unrolling for both warm-up
(`warmupIterations` copies, no CPU loop, no reserved loop-counter register) and the measured
section (`measuredRepetitions` brackets, each with a host-computed hardcoded output address, no
reserved address-scratch register). Each bracket is
`CPUID;setup;LFENCE;RDTSC;start;PUSH;body;RDTSCP;end;PUSH;CPUID;POP;POP;SUB` -- see
`bracketBytes`'s own comment for why setup is outside the timestamp and why the trailing CPUID
and second PUSH exist (Intel's own recommended
open/close-bracketing idiom, applied so the closing CPUID's own register clobber cannot corrupt
the already-captured end timestamp). -/
import Lean
import Gasm.Core.Types
import Gasm.Targets.X86_64.Registers
import Gasm.Targets.X86_64.Instructions.Base
import Gasm.Targets.Windows.Emitter
import Gasm.Targets.Windows.Win32API

namespace Gasm.Targets.X86_64.HardwareTimingHarness

open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.Windows

/- REF: docs/RDTSC_HARNESS.md#6-measurement-methodology -/
/-- One named kernel this harness can time: `perInstanceBytes` is executed
    `kernelUnrollPerRep` times per measured bracket (and `warmupIterations` times, unrolled,
    during warm-up); `perBracketSetupBytes` runs once per bracket after the opening CPUID but
    before the timestamp, and once at the top of warm-up, before any `perInstanceBytes` copies.
    See `docs/RDTSC_HARNESS.md`'s `shl_by_cl` discussion for why a kernel needs this: CPUID
    clobbers RCX every bracket, so a kernel whose timing depends on a specific register value,
    e.g. the CL shift count, must re-establish it per bracket without charging that harness
    setup to the modeled instruction. -/
structure TimingKernel where
  name                 : String
  perInstanceBytes     : ByteArray
  perBracketSetupBytes : ByteArray := ByteArray.empty
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#61-no-cpu-loop-straight-line-unrolling-instead -/
/-- Warm-up iteration count: straight-line unrolled copies of a kernel's `perInstanceBytes`,
    letting turbo/cache state stabilize before any timed bracket runs. Top of the wsc-cited
    5k-20k range -- see the design doc for why (raised from an initial, smaller value during
    this task's own hardware validation, since that value did not reliably stabilize turbo/
    frequency state before the measured section began; the actual before/after evidence is
    Law-14-governed data, not repeated here -- docs/REVIEW.md #4.4). -/
def warmupIterations : Nat := 20000

/- REF: docs/RDTSC_HARNESS.md#63-per-repetition-bracket -/
/-- Measured repetitions per kernel: odd, so the median is a real element of the sample, not an
    average of two middle values. -/
def measuredRepetitions : Nat := 63

/- REF: docs/RDTSC_HARNESS.md#63-per-repetition-bracket -/
/-- Kernel-instance copies executed inside a single timed bracket, amortizing CPUID/RDTSC(P)
    bracket overhead against single-cycle-class kernels. Empirically raised from an initial 16 to
    512 (docs/RDTSC_HARNESS.md #6.3's evidence note, per-run measured figures never repeated here
    -- docs/REVIEW.md #4.4 -- see calibration/x86_64/*.json for the actual numbers): at the
    original, smaller unroll count, the bracket's OWN measurement noise on a shared, contended
    development machine (CPUID's own latency varies run to run, plus concurrent load from other
    agent worktrees, docs/RDTSC_HARNESS.md #7) was comparable in magnitude to a small kernel
    body's own real cost, making the two statistically indistinguishable. A larger unroll count
    makes even a single-cycle-class instruction's aggregate cost an order of magnitude larger
    than that noise floor. -/
def kernelUnrollPerRep : Nat := 512

/- REF: docs/RDTSC_HARNESS.md#62-register-safety-the-one-hazard-straight-line-unrolling-does-not-remove -/
/-- Repeats `unit` `count` times via binary-exponentiation doubling (O(log count) `ByteArray`
    allocations rather than O(count) small appends) -- naive `for _ in [0:count] do acc := acc ++
    unit` is quadratic for the 5,000-iteration counts this harness needs and was measured
    unacceptably slow at that scale before this function replaced it. -/
def repeatBytes (unit : ByteArray) (count : Nat) : ByteArray := Id.run do
  if count == 0 || unit.isEmpty then
    return ByteArray.empty
  let mut result := ByteArray.empty
  let mut base := unit
  let mut n := count
  while n > 0 do
    if n % 2 == 1 then
      result := result ++ base
    base := base ++ base
    n := n / 2
  return result

/- REF: docs/RDTSC_HARNESS.md#63-per-repetition-bracket -/
/-- One fully-unrolled measured bracket: opening CPUID, harness-only `setupBytes`, LFENCE+RDTSC,
    `bodyBytes` (exactly `kernelUnrollPerRep` instruction copies), serialized RDTSCP+CPUID close,
    and a raw cycle delta stored at the host-computed `outAddr`. LFENCE keeps the setup before
    RDTSC, so setup is necessary execution context but is not charged to the modeled stream. The
    end timestamp is combined into RAX and pushed BEFORE the closing CPUID runs (Intel's
    documented RDTSCP+CPUID idiom: the trailing CPUID prevents later instructions from executing
    before the timed read retires) so that CPUID's own EAX/EBX/ECX/EDX clobber cannot destroy the
    very value it is meant to protect -- both PUSH/POP pairs are written here, matched, never
    fuzzer-generated, so they introduce no RSP drift. -/
def bracketBytes (setupBytes bodyBytes : ByteArray) (outAddr : UInt64) : ByteArray :=
  ByteArray.mk #[0x31, 0xC0]                                    -- xor eax, eax (CPUID leaf 0)
  ++ ByteArray.mk #[0x0F, 0xA2]                                 -- cpuid (open serialize)
  ++ setupBytes                                                  -- harness context, outside timing
  ++ ByteArray.mk #[0x0F, 0xAE, 0xE8]                           -- lfence (setup before timestamp)
  ++ ByteArray.mk #[0x0F, 0x31]                                 -- rdtsc
  ++ ByteArray.mk #[0x48, 0xC1, 0xE2, 0x20]                     -- shl rdx, 32
  ++ ByteArray.mk #[0x48, 0x09, 0xD0]                           -- or rax, rdx  (rax = start_ts)
  ++ ByteArray.mk #[0x50]                                       -- push rax
  ++ bodyBytes
  ++ ByteArray.mk #[0x0F, 0x01, 0xF9]                           -- rdtscp
  ++ ByteArray.mk #[0x48, 0xC1, 0xE2, 0x20]                     -- shl rdx, 32
  ++ ByteArray.mk #[0x48, 0x09, 0xD0]                           -- or rax, rdx  (rax = end_ts)
  ++ ByteArray.mk #[0x50]                                       -- push rax  (protect end_ts)
  ++ ByteArray.mk #[0x31, 0xC0]                                 -- xor eax, eax (CPUID leaf 0)
  ++ ByteArray.mk #[0x0F, 0xA2]                                 -- cpuid (close serialize)
  ++ ByteArray.mk #[0x58]                                       -- pop rax  (end_ts)
  ++ ByteArray.mk #[0x5A]                                       -- pop rdx  (start_ts)
  ++ ByteArray.mk #[0x48, 0x29, 0xD0]                           -- sub rax, rdx  (raw delta)
  ++ ByteArray.mk #[0x48, 0x89, 0xC3]                           -- mov rbx, rax  (delta, rbx free)
  ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian outAddr -- mov rax, outAddr
  ++ ByteArray.mk #[0x48, 0x89, 0x18]                           -- mov [rax], rbx

/- REF: docs/RDTSC_HARNESS.md#7-where-this-harness-is-and-is-not-valid-to-run -/
/-- Bytes-per-kernel of the output record: one raw `UInt64` cycle delta per measured repetition. -/
def timingRecordSize : Nat := measuredRepetitions * 8

/- REF: docs/RDTSC_HARNESS.md#63-per-repetition-bracket -/
/-- Builds one kernel's full test-case block: straight-line warm-up (no timing), then
    `measuredRepetitions` fully-unrolled timed brackets, each writing to its own hardcoded
    output slot -- see this file's header for why no CPU loop and no address-scratch register
    are used anywhere in this function. -/
def buildKernelBlock (outBufferAddr : UInt64) (testIdx : Nat) (k : TimingKernel) : ByteArray := Id.run do
  let testOutAddr := outBufferAddr + (testIdx * timingRecordSize).toUInt64
  let mut block := ByteArray.empty
  -- Warm-up: setup once, then straight-line unrolled instance copies, no timing.
  block := block ++ k.perBracketSetupBytes ++ repeatBytes k.perInstanceBytes warmupIterations
  -- Measured section: fully unrolled brackets, each re-running perBracketSetupBytes after the
  -- opening CPUID but before LFENCE+RDTSC, then timing exactly kernelUnrollPerRep copies.
  let bracketBody := repeatBytes k.perInstanceBytes kernelUnrollPerRep
  let measuredPass : ByteArray := Id.run do
    let mut pass := ByteArray.empty
    for r in [0:measuredRepetitions] do
      let repAddr := testOutAddr + (r * 8).toUInt64
      pass := pass ++ bracketBytes k.perBracketSetupBytes bracketBody repAddr
    return pass
  -- PRE-FAULT PASS (docs/RDTSC_HARNESS.md #6.3's page-fault evidence note): the measured
  -- section's own code -- unlike `warmupIterations`' copies, which live in a separate,
  -- already-warm code region -- is executed for the first time right here. Empirically, during
  -- this task's own hardware validation, the FIRST execution of each freshly-unrolled measured
  -- bracket showed a substantial, run-pattern-correlated cycle inflation relative to later,
  -- identical executions of the same bytes, consistent with Windows lazily demand-paging this
  -- executable's `.text` pages on first touch -- a page fault mid-bracket is indistinguishable,
  -- to RDTSC, from genuine kernel cost, and (unlike a sparse SMI/interrupt tail) affected too
  -- large a fraction of samples for the median alone to filter reliably. The specific magnitude
  -- observed is Law-14-governed measured data, not repeated here (docs/REVIEW.md #4.4). Execute
  -- the exact measuredPass instructions at the exact same addresses twice: a stack-resident
  -- two-pass counter avoids reserving a GPR, and the first pass's output is overwritten by the
  -- second. The backward JNE displacement is measured from the end of its own 6-byte encoding:
  -- measuredPass + 4-byte DEC + 6-byte JNE. `bracketBytes`'s PUSH/POP pairs are balanced, so the
  -- counter remains at [RSP] between passes and is removed afterward without stack drift.
  let backToMeasuredPass := -Int32.ofNat (measuredPass.size + 10)
  block := block ++ ByteArray.mk #[0x6A, 0x02]                   -- push 2 (two passes)
  block := block ++ measuredPass                                -- loop target
  block := block ++ ByteArray.mk #[0x48, 0xFF, 0x0C, 0x24]     -- dec qword ptr [rsp]
  block := block ++ ByteArray.mk #[0x0F, 0x85]                  -- jne rel32
  block := block ++ int32ToLittleEndian backToMeasuredPass
  block := block ++ ByteArray.mk #[0x48, 0x83, 0xC4, 0x08]     -- add rsp, 8
  return block

/- REF: docs/RDTSC_HARNESS.md#63-per-repetition-bracket -/
/-- Builds the full `.text` section: a fixed prologue (stack space for the WriteFile call's
    shadow space -- no register save/restore, since this program never returns and no kernel
    body's own register use needs preserving across kernels), every kernel's block back to
    back, then the GetStdHandle/WriteFile/ExitProcess epilogue -- the same three-import
    convention `HardwareHarness.buildTestText` already uses, copied deliberately rather than
    reinvented. -/
def buildTimingText (layout : SectionLayout) (kernels : List TimingKernel) : ByteArray := Id.run do
  let totalTests := kernels.length
  let outBufferSize := totalTests * timingRecordSize
  let imageBase : UInt64 := 0x140000000
  let rdataRva := layout.rdataRva.toUInt64
  let idataRva := layout.idataRva.toUInt64
  let outBufferAddr : UInt64 := imageBase + rdataRva + 0

  -- Prologue: reserve 72 bytes (shadow space + &written scratch), matching
  -- HardwareHarness.buildTestText's own reservation so the epilogue's [rsp+0x20]/[rsp+0x28]
  -- arithmetic below is valid.
  let mut body := ByteArray.mk #[0x48, 0x83, 0xEC, 0x48] -- sub rsp, 72

  -- Request a process-wide affinity mask selecting logical processor 0 for the entire run:
  -- SetProcessAffinityMask((HANDLE)-1 /* current process pseudo-handle, needs no
  -- GetCurrentProcess() call -- it is always -1 */, 1). Closes docs/RDTSC_HARNESS.md #7's named
  -- open item, motivated by an unpinned-baseline finding during hardware
  -- validation: a dependency-chain kernel's measured cycle distribution was substantially less
  -- consistent than a near-zero-cost kernel's on the same run, on this shared development
  -- machine -- consistent with (though not conclusively proven to be) the OS scheduler migrating
  -- this single thread between cores of different effective frequency/microarchitecture (e.g. a
  -- hybrid P/E-core layout) partway through the measured section. Pinning to one fixed logical
  -- processor removes that migration as a variable when the call succeeds. The emitted program
  -- does not currently capture the BOOL return, so generated provenance must record this as a
  -- requested-but-unverified process affinity mask rather than claim confirmed pinning;
  -- the specific before/after figures are Law-14-governed measured data, not repeated in comments
  -- (docs/REVIEW.md #4.4) -- see calibration/x86_64/*.json for any run's actual numbers.
  body := body ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0xFF, 0xFF, 0xFF, 0xFF] -- mov rcx, -1
  body := body ++ ByteArray.mk #[0x48, 0xC7, 0xC2, 0x01, 0x00, 0x00, 0x00] -- mov rdx, 1
  let setAffinityIatAddr := imageBase + idataRva + 0x18
  body := body ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian setAffinityIatAddr
  body := body ++ ByteArray.mk #[0xFF, 0x10] -- call [rax]

  for testIdx in [0:totalTests] do
    let k := kernels[testIdx]!
    body := body ++ buildKernelBlock outBufferAddr testIdx k

  -- Epilogue: GetStdHandle(STD_OUTPUT_HANDLE=-11); WriteFile(hStdout, outBufferAddr,
  -- outBufferSize, &written, NULL); ExitProcess(0). Byte-for-byte the same convention as
  -- HardwareHarness.buildTestText's own epilogue (import order [GetStdHandle, WriteFile,
  -- ExitProcess] at idataRva+0x00/0x08/0x10).
  let mut epilogue := ByteArray.empty
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0xC1, 0xF5, 0xFF, 0xFF, 0xFF] -- mov rcx, -11
  let getStdHandleIatAddr := imageBase + idataRva + 0x00
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian getStdHandleIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10] -- call [rax]

  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x89, 0xC1]                                       -- mov rcx, rax (hStdout)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xBA] ++ uint64ToLittleEndian outBufferAddr        -- mov rdx, outBufferAddr
  epilogue := epilogue ++ ByteArray.mk #[0x49, 0xC7, 0xC0] ++ uint32ToLittleEndian outBufferSize.toUInt32 -- mov r8, outBufferSize
  epilogue := epilogue ++ ByteArray.mk #[0x4C, 0x8D, 0x4C, 0x24, 0x28]                            -- lea r9, [rsp+0x28] (&written)
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00]    -- mov qword [rsp+0x20], 0 (lpOverlapped)
  let writeFileIatAddr := imageBase + idataRva + 0x08
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian writeFileIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  epilogue := epilogue ++ ByteArray.mk #[0x48, 0x31, 0xC9] -- xor rcx, rcx
  let exitProcessIatAddr := imageBase + idataRva + 0x10
  epilogue := epilogue ++ ByteArray.mk #[0x48, 0xB8] ++ uint64ToLittleEndian exitProcessIatAddr
  epilogue := epilogue ++ ByteArray.mk #[0xFF, 0x10]

  return body ++ epilogue

/- REF: docs/RDTSC_HARNESS.md#5-result-record-extension -/
/-- Emits a native PE executable that runs every kernel's warm-up + measured brackets and writes
    the raw cycle-delta buffer via WriteFile -- the timing-harness analogue of
    `HardwareHarness.emitNativeBatchTestExe`. -/
def emitTimingBatchExe (kernels : List TimingKernel) (_outFileName : String := ".tmp_gasm_timing_out.bin") : ByteArray := Id.run do
  let totalTests := kernels.length
  let outBufferSize := totalTests * timingRecordSize
  let importNames := ["GetStdHandle", "WriteFile", "ExitProcess", "SetProcessAffinityMask"]

  let dummyLayout : SectionLayout := { textRawSize := 512, rdataRva := 0x2000, rdataRawSize := 512, idataRva := 0x3000, idataRawSize := 512, sizeOfImage := 0x4000 }
  let dummyText := buildTimingText dummyLayout kernels
  let idataEst := buildKernel32IDataSection 0x3000 importNames
  let rdataTotal := alignUp outBufferSize 16
  let rdata := ByteArray.mk (Array.replicate (max 512 rdataTotal) (0 : UInt8))
  let layout := computeSectionLayout dummyText.size rdata.size idataEst.size
  let text := buildTimingText layout kernels

  emitPE32Executable text rdata importNames

/- REF: docs/RDTSC_HARNESS.md#5-result-record-extension -/
/-- One kernel's measured result: `rawDeltaCycles` preserves run order (`measuredRepetitions`
    entries), never pre-sorted or pre-reduced here -- reduction (median/min/max, timer-overhead
    subtraction, per-instance amortization) is `PerfHardwareFuzzer.lean`'s job, kept separate
    from decoding per `docs/CALIBRATION_GOVERNANCE.md` #5's "samples stored pre-subtraction"
    requirement. -/
structure HardwareKernelTiming where
  name           : String
  rawDeltaCycles : List UInt64
  deriving Inhabited

/- REF: docs/RDTSC_HARNESS.md#5-result-record-extension -/
/-- Decodes one kernel's `timingRecordSize`-byte slice into its ordered raw cycle deltas. -/
def decodeTimingResult (bytes : ByteArray) (offset : Nat) : List UInt64 := Id.run do
  let getU8 (off : Nat) : UInt64 :=
    if off < bytes.size then (bytes.get! off).toUInt64 else 0
  let getU64 (off : Nat) : UInt64 := Id.run do
    let mut v : UInt64 := 0
    for i in [0:8] do
      v := v ||| (getU8 (off + i) <<< (8 * i).toUInt64)
    return v
  let mut deltas : List UInt64 := []
  for r in [0:measuredRepetitions] do
    deltas := deltas ++ [getU64 (offset + r * 8)]
  return deltas

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Runs a batch of timing kernels natively on the host CPU. Structural guarantee against a
    fail-open timing oracle, mirroring `HardwareHarness.runHardwareBatch`: the only way to
    produce a `HardwareKernelTiming` is by decoding the harness's actual captured output bytes;
    every failure mode (spawn failure, abnormal exit, short/garbled output) routes through
    `Except.error`, never a fabricated success-shaped value. -/
def runTimingBatch (kernels : List TimingKernel) (tmpExePath : String := "./.tmp_gasm_timing_fuzz.exe") (tmpOutPath : String := ".tmp_gasm_timing_out.bin") : IO (Except String (List HardwareKernelTiming)) := do
  if kernels.isEmpty then return .ok []
  let exeBytes := emitTimingBatchExe kernels tmpOutPath
  IO.FS.writeBinFile tmpExePath exeBytes

  try
    let child ← IO.Process.spawn {
      cmd := tmpExePath
      stdout := .piped
      stderr := .piped
    }
    let expectedBytes := kernels.length * timingRecordSize
    let outBytes ← child.stdout.read expectedBytes.toUSize
    let exitCode ← child.wait

    if exitCode != 0 then
      let stderrMsg ← child.stderr.readToEnd
      return .error s!"Timing harness '{tmpExePath}' exited with code {exitCode}: {stderrMsg}"

    if outBytes.size < expectedBytes then
      let stderrMsg ← child.stderr.readToEnd
      return .error s!"Timing harness '{tmpExePath}' produced {outBytes.size}/{expectedBytes} expected bytes (exit code {exitCode}): {stderrMsg}"

    let mut results : List HardwareKernelTiming := []
    for i in [0:kernels.length] do
      let k := kernels[i]!
      let deltas := decodeTimingResult outBytes (i * timingRecordSize)
      results := results ++ [{ name := k.name, rawDeltaCycles := deltas }]
    return .ok results
  catch e =>
    return .error s!"Timing harness '{tmpExePath}' failed to spawn or execute: {e}"

-- ---------------------------------------------------------------------------------------------
-- Named kernels: hand-curated, register-disjoint by construction (docs/RDTSC_HARNESS.md #9).
-- ---------------------------------------------------------------------------------------------

/- REF: docs/RDTSC_HARNESS.md#64-timer-overhead-calibration-pass -/
/-- The calibration pass: an empty body, timing the CPUID/RDTSC(P) bracket alone. -/
def timerOverheadKernel : TimingKernel := { name := "timer_overhead", perInstanceBytes := ByteArray.empty }

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Positive control: a single-byte NOP, harness-internal (not a modeled `X86_64Instruction`),
    expected to measure at (or just above) the timer-overhead floor. -/
def nopLoopKernel : TimingKernel := { name := "nop_loop", perInstanceBytes := ByteArray.mk #[0x90] }

/- REF: docs/RDTSC_HARNESS.md#4-containment-fail-closed-world-sampling-vs-correctness-unrepresentable-by-construction -/
/-- Discrimination-pair partner: `ADD RAX, 1`, a serially-dependent chain (each instance depends
    on the previous instance's result through RAX) -- must measure reliably slower than
    `nop_loop`; this is the mechanized version of the "two kernels that must differ" control
    that would have caught wsc's actual symptom (two kernels measured identically). -/
def longDependentChainKernel : TimingKernel := { name := "long_dependent_chain", perInstanceBytes := ByteArray.mk #[0x48, 0x83, 0xC0, 0x01] }

/- REF: docs/RDTSC_HARNESS.md#9-kernel-suite-and-evidence -/
/-- `docs/RDTSC_HARNESS.md`'s named spot-check: `SHL RAX, CL`, modeled as 1 uop
    (`Gasm/Targets/X86_64/Instructions/Shift.lean`'s `ShlR64Cl.toUops`) despite Intel P-cores
    documented elsewhere as needing an extra flag-merge uop when the count is runtime-variable.
    `perBracketSetupBytes` re-establishes `CL := 5` every bracket (CPUID clobbers RCX every
    time) so the shift count is a fixed, known, non-degenerate value rather than whatever
    CPUID's own leaf-0 ECX output happens to leave behind. -/
def shlByClKernel : TimingKernel :=
  { name := "shl_by_cl"
    perBracketSetupBytes := ByteArray.mk #[0xB1, 0x05]        -- mov cl, 5
    perInstanceBytes     := ByteArray.mk #[0x48, 0xD3, 0xE0] } -- shl rax, cl

end Gasm.Targets.X86_64.HardwareTimingHarness
