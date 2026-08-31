#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
tests/e2e/cases/tier4_real_world.py - Tier 4: Real-World Application Scenarios Test Suite.

Covers 12 realistic end-to-end user workflows, algorithms, hash functions, and system validation scenarios
composed exclusively from x86-64 GPR instructions and immediates without memory operands.
Follows the fail-honest exit code contract:
  - Exit 0: Passed
  - Exit 1: Failed
  - Exit 2: Skipped due to missing prerequisite
"""

import time
from typing import Callable, List, Tuple
from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus


class BaseTier4Test(TestCase):
    def __init__(self, test_id: str, name: str, milestone: str, feature_id: int, description: str):
        super().__init__(
            test_id=test_id,
            name=name,
            tier=4,
            milestone=milestone,
            feature_id=feature_id,
            description=description,
        )


def make_tier4_test(
    test_id: str,
    name: str,
    mstone: str,
    feat_id: int,
    desc: str,
    fn: Callable[[ExecutionContext], Tuple[TestStatus, str]],
) -> TestCase:
    class DynamicTier4Test(BaseTier4Test):
        def __init__(self):
            super().__init__(test_id, name, mstone, feat_id, desc)

        def run(self, ctx: ExecutionContext) -> TestResult:
            start = time.monotonic()
            try:
                status, msg = fn(ctx)
                return TestResult(
                    self.test_id,
                    self.name,
                    self.tier,
                    self.milestone,
                    self.feature_id,
                    status,
                    msg,
                    time.monotonic() - start,
                )
            except Exception as e:
                return TestResult(
                    self.test_id,
                    self.name,
                    self.tier,
                    self.milestone,
                    self.feature_id,
                    TestStatus.ERROR,
                    str(e),
                    time.monotonic() - start,
                )

    return DynamicTier4Test()


def get_tier4_tests() -> List[TestCase]:
    tests: List[TestCase] = []

    # T4.01: 128-bit Multi-Precision Integer Addition (ADD + ADC)
    def t4_01(ctx: ExecutionContext):
        asm_code = """
        ; 128-bit addition: [rdx:rax] += [rcx:rbx]
        add rax, rbx
        adc rdx, rcx
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"128-bit ADD+ADC assembly failed: {err}"
        return TestStatus.PASS, f"128-bit addition workload assembled cleanly ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.01", "workload_128bit_addition", "M4", 17,
        "128-bit multi-precision integer addition using ADD low word + ADC high word",
        t4_01,
    ))

    # T4.02: 128-bit Multi-Precision Integer Subtraction (SUB + SBB)
    def t4_02(ctx: ExecutionContext):
        asm_code = """
        ; 128-bit subtraction: [rdx:rax] -= [rcx:rbx]
        sub rax, rbx
        sbb rdx, rcx
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"128-bit SUB+SBB assembly failed: {err}"
        return TestStatus.PASS, f"128-bit subtraction workload assembled cleanly ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.02", "workload_128bit_subtraction", "M4", 18,
        "128-bit multi-precision integer subtraction using SUB low word + SBB high word",
        t4_02,
    ))

    # T4.03: Branchless Integer Absolute Value (abs(x))
    def t4_03(ctx: ExecutionContext):
        asm_code = """
        ; Branchless 64-bit absolute value in RAX
        cqo             ; sign-extend RAX into RDX (all 0s or all 1s)
        xor rax, rdx    ; 1s complement if negative, identity if positive
        sub rax, rdx    ; 2s complement (+1) if negative
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Branchless abs assembly failed: {err}"
        return TestStatus.PASS, f"Branchless integer absolute value assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.03", "workload_branchless_abs", "M4", 20,
        "Branchless 64-bit integer absolute value using CQO sign-fill + XOR + SUB",
        t4_03,
    ))

    # T4.04: Big-Endian Network Packet Header Parser
    def t4_04(ctx: ExecutionContext):
        asm_code = """
        ; Big-endian 32-bit network word unpack in EAX
        bswap eax       ; reverse network byte order to host byte order
        mov edx, eax
        shr edx, 16     ; extract upper 16-bit header field
        and eax, 0xFFFF ; extract lower 16-bit payload length
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Network header parser assembly failed: {err}"
        return TestStatus.PASS, f"Network header parser workload assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.04", "workload_network_header_parser", "M5", 23,
        "Big-endian network packet header parser using BSWAP + SHR + AND bitmasking",
        t4_04,
    ))

    # T4.05: Fast Population Count & Bit Manipulation Primitive
    def t4_05(ctx: ExecutionContext):
        asm_code = """
        ; Bit manipulation index calculation
        popcnt rax, rbx ; count total set bits (Hamming weight)
        lzcnt rcx, rbx  ; count leading zero bits
        tzcnt rdx, rbx  ; count trailing zero bits
        add rax, rcx
        add rax, rdx
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Bit manipulation assembly failed: {err}"
        return TestStatus.PASS, f"Bit count primitives workload assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.05", "workload_bit_manipulation_pipeline", "M5", 22,
        "Bit manipulation primitives pipeline composing POPCNT, LZCNT, and TZCNT",
        t4_05,
    ))

    # T4.06: Branchless Min/Max & Value Clamping
    def t4_06(ctx: ExecutionContext):
        asm_code = """
        ; Clamp RAX between R8 (min) and R9 (max)
        cmp rax, r8
        cmovl rax, r8   ; rax = max(rax, r8)
        cmp rax, r9
        cmovg rax, r9   ; rax = min(rax, r9)
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Clamping workload assembly failed: {err}"
        return TestStatus.PASS, f"Branchless value clamping workload assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.06", "workload_branchless_clamping", "M6", 25,
        "Branchless value clamping between lower and upper bounds using CMP + CMOVcc",
        t4_06,
    ))

    # T4.07: FNV-1a 64-bit Hash Step
    def t4_07(ctx: ExecutionContext):
        asm_code = """
        ; FNV-1a 64-bit hash update: hash = (hash ^ byte) * FNV_PRIME
        movzx rdx, bl                   ; zero-extend next byte from BL
        xor rax, rdx                    ; hash ^= byte
        mov r10, 0x100000001B3          ; FNV_64_PRIME
        imul rax, r10                   ; hash *= FNV_PRIME
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"FNV-1a hash step assembly failed: {err}"
        return TestStatus.PASS, f"FNV-1a 64-bit hash step assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.07", "workload_fnv1a_hash_step", "M4", 20,
        "FNV-1a 64-bit hash step using MOVZX byte zero-extension + XOR + IMUL prime multiplication",
        t4_07,
    ))

    # T4.08: Fast Integer Division by Constant
    def t4_08(ctx: ExecutionContext):
        asm_code = """
        ; Fast signed division of EAX by 3 using reciprocal multiplication
        mov edx, 0x55555556             ; magic reciprocal for / 3
        imul edx                        ; EDX:EAX = input * reciprocal
        mov eax, edx
        shr eax, 31                     ; extract sign bit of quotient
        add eax, edx                    ; adjust for negative numerator
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Fast division assembly failed: {err}"
        return TestStatus.PASS, f"Fast constant division workload assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.08", "workload_fast_division_by_constant", "M3", 16,
        "Fast integer division by constant using 1-operand IMUL + SHR + ADD adjustment",
        t4_08,
    ))

    # T4.09: Multi-Condition Decision Tree Evaluator
    def t4_09(ctx: ExecutionContext):
        asm_code = """
        ; Evaluate multiple condition codes into bitmask in RAX
        xor eax, eax
        cmp r8, r9
        setl al         ; bit 0: r8 < r9
        cmp r10, r11
        setz bl         ; bit 1: r10 == r11
        shl ebx, 1
        or eax, ebx     ; composite bitmask
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Decision tree assembly failed: {err}"
        return TestStatus.PASS, f"Multi-condition decision tree assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.09", "workload_decision_tree_evaluator", "M6", 24,
        "Multi-condition decision tree evaluator building bitmask from SETcc comparisons",
        t4_09,
    ))

    # T4.10: String Byte Search / Memchr Loop Step
    def t4_10(ctx: ExecutionContext):
        asm_code = """
        ; String search step: compare AL with target BL, update index ECX
        cmp al, bl
        setz dl         ; dl = 1 if match found, else 0
        movzx edx, dl
        add ecx, 1      ; increment scan pointer
        sub esi, edx    ; decrement remaining match target
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Memchr step assembly failed: {err}"
        return TestStatus.PASS, f"Memchr byte scan loop step assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.10", "workload_memchr_scan_step", "M6", 24,
        "Memchr string byte search step using 8-bit CMP + SETZ + MOVZX + ADD/SUB",
        t4_10,
    ))

    # T4.11: Atomic Compare-and-Swap (CAS) Spinlock Step
    def t4_11(ctx: ExecutionContext):
        asm_code = """
        ; Atomic CAS spinlock step: compare RAX with RBX, swap RCX if matched
        cmpxchg rbx, rcx ; if (RBX == RAX) { RBX = RCX; ZF = 1; } else { RAX = RBX; ZF = 0; }
        setz al          ; AL = 1 if lock acquired, else 0
        movzx eax, al
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"CAS spinlock assembly failed: {err}"
        return TestStatus.PASS, f"Atomic CAS spinlock step assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.11", "workload_atomic_cas_step", "M5", 23,
        "Atomic Compare-and-Swap (CAS) step using CMPXCHG + SETZ + MOVZX",
        t4_11,
    ))

    # T4.12: Sub-Register Packing / Unpacking
    def t4_12(ctx: ExecutionContext):
        asm_code = """
        ; Pack two 16-bit words (AX, BX) into 32-bit register EDX, then unpack
        movzx edx, ax   ; EDX = word 0
        movzx ecx, bx   ; ECX = word 1
        shl ecx, 16     ; ECX = word 1 << 16
        or edx, ecx     ; EDX = packed [word 1 | word 0]
        mov ax, dx      ; unpack low word
        shr edx, 16     ; unpack high word
        mov bx, dx
        """
        ok, raw, err = ctx.assemble_nasm(asm_code)
        if not ok:
            return TestStatus.FAIL, f"Packing/unpacking assembly failed: {err}"
        return TestStatus.PASS, f"Sub-register packing/unpacking assembled ({len(raw)} bytes): {raw.hex()}"

    tests.append(make_tier4_test(
        "T4.12", "workload_subreg_pack_unpack", "M4", 20,
        "Sub-register packing and unpacking using MOVZX + SHL + OR + SHR",
        t4_12,
    ))

    return tests
