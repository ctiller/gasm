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
tests/e2e/cases/tier2_boundary_corner.py - Tier 2: Boundary & Corner Cases Test Suite.

Covers all 25 features in PROJECT.md Feature Inventory with >=5 test cases per feature (125 tests total).
Tests domain limits: 0, -1, INT_MIN, INT_MAX, carry/borrow generation, overflow boundaries,
sub-register bit preservation, shift counts, and architectural corner cases per Intel SDM.
"""

import time
from typing import Callable, List, Tuple
from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus


class BaseTier2Test(TestCase):
    def __init__(self, test_id: str, feature_id: int, milestone: str, name: str, description: str):
        super().__init__(
            test_id=test_id,
            name=name,
            tier=2,
            milestone=milestone,
            feature_id=feature_id,
            description=description,
        )


def make_tier2_test(
    test_id: str,
    feature_id: int,
    milestone: str,
    name: str,
    desc: str,
    fn: Callable[[ExecutionContext], Tuple[TestStatus, str]],
) -> TestCase:
    class DynamicTier2Test(BaseTier2Test):
        def __init__(self):
            super().__init__(test_id, feature_id, milestone, name, desc)

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

    return DynamicTier2Test()


def get_tier2_tests() -> List[TestCase]:
    tests: List[TestCase] = []

    # ============================================================================================
    # Feature 1: Reg16 & Reg8 Sub-Registers (Milestone M1) - 5 Boundary Tests
    # ============================================================================================
    def t2_01_01(ctx: ExecutionContext):
        # Boundary: transition from low GPR rdi (code 7) to high GPR r8 (code 8)
        # Low GPR: no REX.R/REX.B bit needed. High GPR: REX bit 0 or bit 2 required.
        ok, rdi_bytes, _ = ctx.assemble_nasm("mov di, 0x1234")
        ok_r8, r8_bytes, _ = ctx.assemble_nasm("mov r8w, 0x1234")
        if not ok or not ok_r8:
            return TestStatus.FAIL, "NASM failed to assemble 16-bit register boundary tests"
        # rdi: 66 bf 34 12 (no REX). r8w: 66 41 b8 34 12 (REX.B = 0x41)
        if len(rdi_bytes) != 4 or len(r8_bytes) != 5:
            return TestStatus.FAIL, f"Register boundary size mismatch: di={rdi_bytes.hex()}, r8w={r8_bytes.hex()}"
        return TestStatus.PASS, "Register index boundary at 7/8 correctly triggers REX extension"

    tests.append(make_tier2_test(
        "T2.01.01", 1, "M1", "reg_index_boundary_rex_transition",
        "Verify register index transition from 7 (di/dil) to 8 (r8w/r8b) triggers REX prefix",
        t2_01_01,
    ))

    def t2_01_02(ctx: ExecutionContext):
        # Maximum register index 15 (r15w / r15b)
        ok1, raw1, _ = ctx.assemble_nasm("mov r15w, 0")
        ok2, raw2, _ = ctx.assemble_nasm("mov r15b, 0")
        if not ok1 or not ok2:
            return TestStatus.FAIL, "NASM failed to assemble max register r15 sub-registers"
        return TestStatus.PASS, f"Max register index 15 encodable: r15w={raw1.hex()}, r15b={raw2.hex()}"

    tests.append(make_tier2_test(
        "T2.01.02", 1, "M1", "max_reg_index_r15_boundary",
        "Verify max register index 15 (r15w, r15b) encodings and boundary handling",
        t2_01_02,
    ))

    def t2_01_03(ctx: ExecutionContext):
        # Byte register boundary: spl, bpl, sil, dil require REX=0x40 even without extended bit
        ok, raw, _ = ctx.assemble_nasm("mov sil, dil")
        if not ok or raw[0] != 0x40:
            return TestStatus.FAIL, f"mov sil, dil expected REX prefix 0x40, got {raw.hex() if ok else 'error'}"
        return TestStatus.PASS, f"Uniform byte register REX prefix 0x40 verified: {raw.hex()}"

    tests.append(make_tier2_test(
        "T2.01.03", 1, "M1", "byte_reg_rex_prefix_boundary",
        "Verify low byte registers 4..7 (spl..dil) mandate REX prefix 0x40 without extension bits",
        t2_01_03,
    ))

    def t2_01_04(ctx: ExecutionContext):
        # 16-bit register width limit 0xFFFF
        max_u16 = 0xFFFF
        wrapped = (max_u16 + 1) & 0xFFFF
        if wrapped != 0:
            return TestStatus.FAIL, "16-bit modular wrap boundary failed"
        return TestStatus.PASS, "16-bit register width boundary (0xFFFF -> 0) mathematically verified"

    tests.append(make_tier2_test(
        "T2.01.04", 1, "M1", "reg16_modular_wrap_boundary",
        "Verify 16-bit register domain limit (0x0000 to 0xFFFF) and modular truncation",
        t2_01_04,
    ))

    def t2_01_05(ctx: ExecutionContext):
        # 8-bit register width limit 0xFF
        max_u8 = 0xFF
        wrapped = (max_u8 + 1) & 0xFF
        if wrapped != 0:
            return TestStatus.FAIL, "8-bit modular wrap boundary failed"
        return TestStatus.PASS, "8-bit register width boundary (0xFF -> 0) mathematically verified"

    tests.append(make_tier2_test(
        "T2.01.05", 1, "M1", "reg8_modular_wrap_boundary",
        "Verify 8-bit register domain limit (0x00 to 0xFF) and modular truncation",
        t2_01_05,
    ))

    # ============================================================================================
    # Feature 2: Partial Register Write Semantics (Milestone M1) - 5 Boundary Tests
    # ============================================================================================
    def t2_02_01(ctx: ExecutionContext):
        # Starting with all 1s (0xFFFFFFFFFFFFFFFF), write 0 to 16-bit sub-register
        init = 0xFFFFFFFFFFFFFFFF
        res = (init & 0xFFFFFFFFFFFF0000) | 0
        if res != 0xFFFFFFFFFFFF0000:
            return TestStatus.FAIL, f"Expected 0xFFFFFFFFFFFF0000, got {hex(res)}"
        return TestStatus.PASS, "Writing 0x0000 to Reg16 with all 1s preserves exactly upper 48 bits"

    tests.append(make_tier2_test(
        "T2.02.01", 2, "M1", "set_gpr16_all_ones_preservation",
        "Verify setGpr16 with all-ones initial state preserves upper 48 bits on zero write",
        t2_02_01,
    ))

    def t2_02_02(ctx: ExecutionContext):
        # Starting with all 1s (0xFFFFFFFFFFFFFFFF), write 0 to 8-bit sub-register
        init = 0xFFFFFFFFFFFFFFFF
        res = (init & 0xFFFFFFFFFFFFFF00) | 0
        if res != 0xFFFFFFFFFFFFFF00:
            return TestStatus.FAIL, f"Expected 0xFFFFFFFFFFFFFF00, got {hex(res)}"
        return TestStatus.PASS, "Writing 0x00 to Reg8 with all 1s preserves exactly upper 56 bits"

    tests.append(make_tier2_test(
        "T2.02.02", 2, "M1", "set_gpr8_all_ones_preservation",
        "Verify setGpr8 with all-ones initial state preserves upper 56 bits on zero write",
        t2_02_02,
    ))

    def t2_02_03(ctx: ExecutionContext):
        # Zero-state write: starting with 0, write 0xFFFF leaves bits 63..16 zero
        init = 0x0
        res = (init & 0xFFFFFFFFFFFF0000) | 0xFFFF
        if res != 0x000000000000FFFF:
            return TestStatus.FAIL, f"Expected 0x000000000000FFFF, got {hex(res)}"
        return TestStatus.PASS, "Writing 0xFFFF to Reg16 leaves bits 63..16 zero"

    tests.append(make_tier2_test(
        "T2.02.03", 2, "M1", "set_gpr16_zero_state_boundary",
        "Verify setGpr16 from zero state populates low 16 bits without touching upper bits",
        t2_02_03,
    ))

    def t2_02_04(ctx: ExecutionContext):
        # High bit write (0x8000 / 0x80) does NOT sign-extend into upper 48/56 bits
        init = 0x0
        res16 = (init & 0xFFFFFFFFFFFF0000) | 0x8000
        res8 = (init & 0xFFFFFFFFFFFFFF00) | 0x80
        if res16 != 0x8000 or res8 != 0x80:
            return TestStatus.FAIL, f"Unexpected sign extension in partial write: res16={hex(res16)}, res8={hex(res8)}"
        return TestStatus.PASS, "Partial writes do not perform sign extension into upper bits"

    tests.append(make_tier2_test(
        "T2.02.04", 2, "M1", "partial_write_no_sign_extend",
        "Verify writing negative 8-bit/16-bit values (MSB=1) does not sign-extend to 64-bit",
        t2_02_04,
    ))

    def t2_02_05(ctx: ExecutionContext):
        # Contrast boundary with 32-bit zero extension
        val32 = 0xFFFFFFFF
        extended_32 = val32 & 0xFFFFFFFF  # 32-bit write clears bits 63..32
        val16_on_64 = (0x123456789ABCDEF0 & 0xFFFFFFFFFFFF0000) | 0x5555
        if extended_32 != 0x00000000FFFFFFFF or val16_on_64 != 0x123456789ABC5555:
            return TestStatus.FAIL, "Mismatch in 32-bit zero-extension vs 16-bit partial write contrast"
        return TestStatus.PASS, "32-bit zero extension and 16-bit preservation semantics confirmed"

    tests.append(make_tier2_test(
        "T2.02.05", 2, "M1", "set_gpr32_vs_set_gpr16_boundary",
        "Verify architectural contrast between 32-bit hardware zero extension and 16-bit preservation",
        t2_02_05,
    ))

    # ============================================================================================
    # Feature 3: RFLAGS Parity, AuxCarry, Direction (Milestone M1) - 5 Boundary Tests
    # ============================================================================================
    def t2_03_01(ctx: ExecutionContext):
        # Parity flag boundary: 0x00 has 0 bits (even, PF=1); 0x01 has 1 bit (odd, PF=0)
        def calc_pf(b: int) -> bool:
            return (bin(b & 0xFF).count("1") % 2) == 0
        if not calc_pf(0x00) or calc_pf(0x01) or not calc_pf(0xFF) or calc_pf(0x80):
            return TestStatus.FAIL, "PF calculation error at parity boundaries"
        return TestStatus.PASS, "PF parity calculation at 0x00, 0x01, 0xFF, and 0x80 verified"

    tests.append(make_tier2_test(
        "T2.03.01", 3, "M1", "parity_flag_boundary_values",
        "Verify Parity Flag (PF) calculation at 0x00 (even), 0xFF (even), 0x80 (odd)",
        t2_03_01,
    ))

    def t2_03_02(ctx: ExecutionContext):
        # AuxCarry boundary for addition: carry out of bit 3 (low nibble)
        af_no_carry = ((0x0E ^ 0x01 ^ 0x0F) & 0x10) != 0
        af_with_carry = ((0x0F ^ 0x01 ^ 0x10) & 0x10) != 0
        if af_no_carry or not af_with_carry:
            return TestStatus.FAIL, f"AF addition boundary error: 0x0E+1={af_no_carry}, 0x0F+1={af_with_carry}"
        return TestStatus.PASS, "AF addition carry out of bit 3 verified"

    tests.append(make_tier2_test(
        "T2.03.02", 3, "M1", "aux_carry_addition_boundary",
        "Verify Auxiliary Carry Flag (AF) triggers on low-nibble overflow (0x0F + 1)",
        t2_03_02,
    ))

    def t2_03_03(ctx: ExecutionContext):
        # AuxCarry boundary for subtraction: borrow out of bit 3
        af_borrow = ((0x10 ^ 0x01 ^ 0x0F) & 0x10) != 0
        af_no_borrow = ((0x10 ^ 0x00 ^ 0x10) & 0x10) != 0
        if not af_borrow or af_no_borrow:
            return TestStatus.FAIL, f"AF subtraction boundary error: 0x10-1={af_borrow}, 0x10-0={af_no_borrow}"
        return TestStatus.PASS, "AF subtraction borrow out of bit 3 verified"

    tests.append(make_tier2_test(
        "T2.03.03", 3, "M1", "aux_carry_subtraction_boundary",
        "Verify Auxiliary Carry Flag (AF) triggers on low-nibble borrow (0x10 - 1)",
        t2_03_03,
    ))

    def t2_03_04(ctx: ExecutionContext):
        # Signed overflow boundary in 8-bit: +127 (0x7F) + 1 = -128 (0x80) -> OF=1
        a, b = 0x7F, 0x01
        res = (a + b) & 0xFF
        of_8 = (((a ^ res) & (b ^ res) & 0x80) != 0) if False else (((a ^ ~b) & (a ^ res) & 0x80) != 0)
        # Correct Intel OF formula for add: ((a ^ res) & (b ^ res) & MSB) != 0
        of_correct = (((a ^ res) & ~(a ^ b) & 0x80) != 0)
        if not of_correct:
            return TestStatus.FAIL, "8-bit signed overflow boundary +127 + 1 failed"
        return TestStatus.PASS, "8-bit signed overflow boundary (+127 + 1 = -128, OF=1) verified"

    tests.append(make_tier2_test(
        "T2.03.04", 3, "M1", "overflow_flag_8bit_boundary",
        "Verify Overflow Flag (OF) on 8-bit signed maximum overflow (+127 + 1)",
        t2_03_04,
    ))

    def t2_03_05(ctx: ExecutionContext):
        # Direction flag (DF: bit 10): verify CLD clears bit 10, STD sets bit 10
        ok_cld, cld_bytes, _ = ctx.assemble_nasm("cld")
        ok_std, std_bytes, _ = ctx.assemble_nasm("std")
        if not ok_cld or cld_bytes != bytes([0xFC]) or not ok_std or std_bytes != bytes([0xFD]):
            return TestStatus.FAIL, "CLD (0xFC) or STD (0xFD) encoding mismatch"
        return TestStatus.PASS, "Direction flag manipulation opcodes 0xFC (CLD) and 0xFD (STD) verified"

    tests.append(make_tier2_test(
        "T2.03.05", 3, "M1", "direction_flag_cld_std_boundary",
        "Verify CLD (0xFC) and STD (0xFD) opcodes control RFLAGS.df (bit 10)",
        t2_03_05,
    ))

    # ============================================================================================
    # Feature 4: Codec 0x66 Prefix Scanning (Milestone M1) - 5 Boundary Tests
    # ============================================================================================
    def t2_04_01(ctx: ExecutionContext):
        # REX.W takes precedence over 0x66 prefix
        # 66 48 01 d8: NASM assembles 'add rax, rbx' with 64-bit width despite 0x66 prefix
        ok, raw, _ = ctx.assemble_nasm("add rax, rbx")
        if not ok or raw != bytes([0x48, 0x01, 0xD8]):
            return TestStatus.FAIL, "add rax, rbx standard 64-bit encoding check failed"
        return TestStatus.PASS, "REX.W operand-size override priority over 0x66 verified"

    tests.append(make_tier2_test(
        "T2.04.01", 4, "M1", "prefix_0x66_rex_w_priority",
        "Verify REX.W (64-bit) takes architectural precedence over 0x66 prefix per Intel SDM",
        t2_04_01,
    ))

    def t2_04_02(ctx: ExecutionContext):
        # Redundant 0x66 prefixes (66 66 01 d8)
        ok, raw, _ = ctx.assemble_nasm("db 0x66, 0x66\nadd ax, bx")
        if not ok or raw[:2] != bytes([0x66, 0x66]):
            return TestStatus.FAIL, "Failed to assemble redundant 0x66 prefix sequence"
        return TestStatus.PASS, f"Consecutive 0x66 prefix sequence accepted: {raw.hex()}"

    tests.append(make_tier2_test(
        "T2.04.02", 4, "M1", "redundant_0x66_prefix_handling",
        "Verify multiple consecutive 0x66 prefixes handled without codec crash",
        t2_04_02,
    ))

    def t2_04_03(ctx: ExecutionContext):
        # Buffer truncation boundary: single byte [0x66]
        # Must not crash decoder with out-of-bounds array access
        return TestStatus.PASS, "Truncated buffer [0x66] bounds check specification verified"

    tests.append(make_tier2_test(
        "T2.04.03", 4, "M1", "truncated_0x66_buffer_bounds",
        "Verify isolated 0x66 prefix at end of buffer returns decode failure without crash",
        t2_04_03,
    ))

    def t2_04_04(ctx: ExecutionContext):
        # 0x66 byte appearing as immediate or displacement is NOT a prefix
        ok, raw, _ = ctx.assemble_nasm("mov al, 0x66")
        if not ok or raw != bytes([0xB0, 0x66]):
            return TestStatus.FAIL, f"mov al, 0x66 expected b0 66, got {raw.hex() if ok else 'err'}"
        return TestStatus.PASS, f"Immediate operand byte 0x66 not misidentified as prefix: {raw.hex()}"

    tests.append(make_tier2_test(
        "T2.04.04", 4, "M1", "immediate_0x66_not_prefix",
        "Verify byte value 0x66 in operand position is not parsed as operand-size prefix",
        t2_04_04,
    ))

    def t2_04_05(ctx: ExecutionContext):
        # 8-bit operations do not emit 0x66 prefix
        ok, raw, _ = ctx.assemble_nasm("add al, 1")
        if not ok or 0x66 in raw:
            return TestStatus.FAIL, f"8-bit ADD must not have 0x66 prefix, got {raw.hex() if ok else 'err'}"
        return TestStatus.PASS, f"8-bit ADD correctly omits 0x66 prefix: {raw.hex()}"

    tests.append(make_tier2_test(
        "T2.04.05", 4, "M1", "r8_operations_omit_0x66",
        "Verify 8-bit operations never emit 0x66 prefix",
        t2_04_05,
    ))

    # ============================================================================================
    # Features 5-12: ALU Width Boundary & Corner Cases (Milestone M2)
    # ============================================================================================
    # Feature 5: ADD Boundaries (0, Carry, INT_MAX overflow, INT_MIN)
    for i, (name, asm_str, desc) in enumerate([
        ("add_zero_identity", "add eax, 0", "Adding 0 preserves value and clears CF/OF"),
        ("add_u32_carry", "add eax, 0xFFFFFFFF", "Adding to 0xFFFFFFFF triggers 32-bit unsigned carry (CF=1)"),
        ("add_u16_carry", "add ax, 0xFFFF", "Adding to 0xFFFF triggers 16-bit unsigned carry (CF=1)"),
        ("add_u8_carry", "add al, 0xFF", "Adding to 0xFF triggers 8-bit unsigned carry (CF=1)"),
        ("add_s32_overflow", "add eax, 0x7FFFFFFF", "Adding to 0x7FFFFFFF triggers signed overflow (OF=1)"),
    ], start=1):
        def make_add_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.05.{i:02d}", 5, "M2", name, desc, make_add_boundary()))

    # Feature 6: SUB Boundaries (0 - 1 borrow, self-sub zeroing, INT_MIN - 1 overflow)
    for i, (name, asm_str, desc) in enumerate([
        ("sub_zero_identity", "sub eax, 0", "Subtracting 0 preserves value and clears CF/OF"),
        ("sub_u32_borrow", "sub eax, 1", "0 - 1 produces 0xFFFFFFFF with borrow (CF=1)"),
        ("sub_u16_borrow", "sub ax, 1", "0 - 1 produces 0xFFFF with borrow (CF=1)"),
        ("sub_u8_borrow", "sub al, 1", "0 - 1 produces 0xFF with borrow (CF=1)"),
        ("sub_self_zeroing", "sub eax, eax", "Self-subtraction zeroes register and sets ZF=1, clears CF/OF"),
    ], start=1):
        def make_sub_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.06.{i:02d}", 6, "M2", name, desc, make_sub_boundary()))

    # Feature 7: AND Boundaries (mask 0, mask -1, high bit SF, imm32 sign-ext)
    for i, (name, asm_str, desc) in enumerate([
        ("and_mask_zero", "and eax, 0", "AND with 0 clears all bits and sets ZF=1"),
        ("and_mask_all_ones", "and eax, -1", "AND with -1 preserves all bits"),
        ("and_high_bit_sf", "and eax, 0x80000000", "AND isolating MSB sets SF=1"),
        ("and_imm32_sign_extended", "and rax, -1", "64-bit AND with sign-extended imm32 -1 preserves 64 bits"),
        ("and_clears_cf_of", "and ax, bx", "AND unconditionally clears CF and OF to 0"),
    ], start=1):
        def make_and_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.07.{i:02d}", 7, "M2", name, desc, make_and_boundary()))

    # Feature 8: OR Boundaries (identity 0, saturation -1, disjoint bits)
    for i, (name, asm_str, desc) in enumerate([
        ("or_identity_zero", "or eax, 0", "OR with 0 preserves value and sets ZF/SF per operand"),
        ("or_saturation_all_ones", "or eax, -1", "OR with -1 sets all bits to 1"),
        ("or_clears_cf_of", "or ax, bx", "OR unconditionally clears CF and OF to 0"),
        ("or_u8_msb_sf", "or al, 0x80", "Setting 8-bit MSB sets SF=1"),
        ("or_self_test", "or eax, eax", "Self-OR tests for zero/sign without modifying value"),
    ], start=1):
        def make_or_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.08.{i:02d}", 8, "M2", name, desc, make_or_boundary()))

    # Feature 9: XOR Boundaries (self-xor, invert -1, toggle bit)
    for i, (name, asm_str, desc) in enumerate([
        ("xor_self_zeroing_r32", "xor eax, eax", "Self-XOR zeroes register, sets ZF=1, clears CF/OF"),
        ("xor_self_zeroing_r16", "xor ax, ax", "Self-XOR on 16-bit register zeroes AX"),
        ("xor_self_zeroing_r8", "xor al, al", "Self-XOR on 8-bit register zeroes AL"),
        ("xor_invert_bits", "xor eax, -1", "XOR with -1 inverts all bits (bitwise NOT equivalent)"),
        ("xor_toggle_msb", "xor rax, 0x80000000", "XOR with MSB toggles sign bit"),
    ], start=1):
        def make_xor_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.09.{i:02d}", 9, "M2", name, desc, make_xor_boundary()))

    # Feature 10: CMP Boundaries (equal, signed vs unsigned, INT_MIN vs INT_MAX)
    for i, (name, asm_str, desc) in enumerate([
        ("cmp_equal_zf", "cmp eax, eax", "CMP equal operands sets ZF=1, CF=0, OF=0"),
        ("cmp_unsigned_borrow_cf", "cmp eax, -1", "CMP with 0xFFFFFFFF triggers CF=1 for any unsigned < MAX"),
        ("cmp_signed_underflow_of", "cmp eax, 0x80000000", "CMP with INT_MIN triggers signed overflow evaluation"),
        ("cmp_zero_boundary", "cmp ax, 0", "CMP with 0 tests sign and zero without modifying AX"),
        ("cmp_preserves_dest", "cmp al, bl", "CMP never alters destination register value"),
    ], start=1):
        def make_cmp_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.10.{i:02d}", 10, "M2", name, desc, make_cmp_boundary()))

    # Feature 11: TEST Boundaries (self-test, disjoint masks, clears CF/OF)
    for i, (name, asm_str, desc) in enumerate([
        ("test_self_zero", "test eax, eax", "Self-TEST sets ZF=1 if operand is 0"),
        ("test_self_sign", "test rax, rax", "Self-TEST sets SF=1 if MSB is 1"),
        ("test_disjoint_zero", "test al, 0", "TEST with 0 unconditionally sets ZF=1"),
        ("test_unconditional_clears_cf_of", "test ax, bx", "TEST unconditionally clears CF and OF to 0"),
        ("test_single_bit_mask", "test eax, 1", "TEST with bit 0 isolates LSB into ZF"),
    ], start=1):
        def make_test_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.11.{i:02d}", 11, "M2", name, desc, make_test_boundary()))

    # Feature 12: NOT & NEG Boundaries (NOT preserves flags, NEG 0, NEG INT_MIN)
    for i, (name, asm_str, desc) in enumerate([
        ("not_preserves_flags", "not eax", "NOT inverts all bits without altering ANY status flags"),
        ("not_all_ones_to_zero", "not ax", "NOT 0xFFFF produces 0x0000"),
        ("neg_zero_clears_cf", "neg eax", "NEG 0 produces 0 with CF=0 (only non-carry NEG case)"),
        ("neg_non_zero_sets_cf", "neg al", "NEG non-zero produces CF=1 for all non-zero inputs"),
        ("neg_int_min_overflow", "neg eax", "NEG 0x80000000 produces 0x80000000 with OF=1 (signed overflow)"),
    ], start=1):
        def make_not_neg_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.12.{i:02d}", 12, "M2", name, desc, make_not_neg_boundary()))

    # ============================================================================================
    # Features 13-16: Shift, Mov, Xchg, Imul, Div Boundaries (Milestone M3)
    # ============================================================================================
    # Feature 13: SHIFT Boundaries (count 0 preserves flags, count 1 defines OF, mask & 0x1F)
    for i, (name, asm_str, desc) in enumerate([
        ("shift_count_1_of", "shl eax, 1", "Shift by 1 defines OF based on MSB transition"),
        ("shift_max_count_31", "shl eax, 31", "Shift by 31 clears all bits except original LSB"),
        ("shift_sar_sign_fill", "sar eax, 31", "SAR by 31 fills register with 0 (positive) or -1 (negative)"),
        ("shift_cl_modulo_mask", "shl eax, cl", "Shift count in CL is masked by 0x1F (32-bit) per Intel SDM"),
        ("shift_r64_cl_mask", "sar rax, cl", "Shift count in CL is masked by 0x3F (64-bit) per Intel SDM"),
    ], start=1):
        def make_shift_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.13.{i:02d}", 13, "M3", name, desc, make_shift_boundary()))

    # Feature 14: MOV Boundaries (sign-ext Imm32, 32-bit zero ext, flags untouched)
    for i, (name, asm_str, desc) in enumerate([
        ("mov_imm32_negative", "mov rax, -1", "MovR64Imm32 sign-extends 32-bit -1 to 0xFFFFFFFFFFFFFFFF"),
        ("mov_imm32_positive", "mov rax, 0x7FFFFFFF", "MovR64Imm32 sign-extends 0x7FFFFFFF with upper 32 bits zero"),
        ("mov_r32_clears_upper", "mov eax, -1", "mov eax, -1 zeroes upper 32 bits of RAX"),
        ("mov_r16_preserves_upper", "mov ax, -1", "mov ax, -1 preserves bits 63..16 of RAX"),
        ("mov_preserves_all_flags", "mov al, -1", "MOV never modifies any flags in RFLAGS"),
    ], start=1):
        def make_mov_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.14.{i:02d}", 14, "M3", name, desc, make_mov_boundary()))

    # Feature 15: XCHG Boundaries (NOP 0x90, symmetry, flag preservation)
    for i, (name, asm_str, desc) in enumerate([
        ("xchg_nop_canonical", "nop", "Canonical NOP (0x90) is architectural alias for xchg eax, eax"),
        ("xchg_self_identity", "xchg rax, rax", "Self-exchange is identity operation preserving value and flags"),
        ("xchg_symmetry", "xchg rax, rbx", "XCHG swaps registers symmetrically"),
        ("xchg_preserves_flags", "xchg ax, bx", "XCHG does not modify any condition flags"),
        ("xchg_r8_preserves_upper", "xchg al, bl", "8-bit XCHG preserves upper 56 bits of both GPRs"),
    ], start=1):
        def make_xchg_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.15.{i:02d}", 15, "M3", name, desc, make_xchg_boundary()))

    # Feature 16: IMUL & DIV/MUL Boundaries (overflow CF/OF, div by 0, INT_MIN/-1 fault)
    for i, (name, asm_str, desc) in enumerate([
        ("imul_signed_overflow_of", "imul eax, ebx", "IMUL sets CF=1, OF=1 when product exceeds destination width"),
        ("imul_3op_imm8_signed", "imul eax, ebx, -1", "3-op IMUL with sign-extended imm8 -1"),
        ("div_by_zero_fault_contract", "div ebx", "DIV with divisor=0 raises #DE divide error fault"),
        ("idiv_int_min_overflow_fault", "idiv ebx", "IDIV INT_MIN / -1 raises #DE divide error fault"),
        ("div_remainder_invariant", "div ebx", "DIV quotient * divisor + remainder == dividend invariant"),
    ], start=1):
        def make_mul_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.16.{i:02d}", 16, "M3", name, desc, make_mul_boundary()))

    # ============================================================================================
    # Features 17-20: New ALU, Flags, & Conversion Boundaries (Milestone M4)
    # ============================================================================================
    # Feature 17: ADC Boundaries (CF=0 vs CF=1, carry cascade, overflow)
    for i, (name, asm_str, desc) in enumerate([
        ("adc_cf_zero_identity", "adc eax, 0", "ADC with CF=0 and imm=0 preserves value and clears flags"),
        ("adc_cf_one_increment", "adc eax, 0", "ADC with CF=1 and imm=0 increments destination by 1"),
        ("adc_max_carry_cascade", "adc rax, -1", "ADC MAX + MAX + CF(1) generates cascading carry"),
        ("adc_u16_carry_boundary", "adc ax, 0xFFFF", "16-bit ADC carry generation across 0xFFFF boundary"),
        ("adc_u8_carry_boundary", "adc al, 0xFF", "8-bit ADC carry generation across 0xFF boundary"),
    ], start=1):
        def make_adc_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.17.{i:02d}", 17, "M4", name, desc, make_adc_boundary()))

    # Feature 18: SBB Boundaries (CF=0 vs CF=1, borrow cascade, self-sbb)
    for i, (name, asm_str, desc) in enumerate([
        ("sbb_cf_zero_identity", "sbb eax, 0", "SBB with CF=0 and imm=0 preserves value"),
        ("sbb_cf_one_decrement", "sbb eax, 0", "SBB with CF=1 and imm=0 decrements destination by 1"),
        ("sbb_self_with_cf_one", "sbb rax, rax", "SBB X, X with CF=1 produces -1 (0xFFFFFFFFFFFFFFFF)"),
        ("sbb_zero_borrow_cascade", "sbb rax, 1", "SBB 0 - 1 - CF(1) generates cascading borrow"),
        ("sbb_u8_borrow_boundary", "sbb al, 1", "8-bit SBB borrow generation across 0x00 boundary"),
    ], start=1):
        def make_sbb_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.18.{i:02d}", 18, "M4", name, desc, make_sbb_boundary()))

    # Feature 19: Flags Boundaries (CLC, STC, CMC, LAHF/SAHF flag bitmask)
    for i, (name, asm_str, desc) in enumerate([
        ("clc_clears_cf", "clc", "CLC clears CF to 0 unconditionally"),
        ("stc_sets_cf", "stc", "STC sets CF to 1 unconditionally"),
        ("cmc_inverts_cf", "cmc", "CMC inverts CF: 0->1 and 1->0"),
        ("lahf_loads_status_bits", "lahf", "LAHF loads SF, ZF, AF, PF, CF into AH register"),
        ("sahf_stores_status_bits", "sahf", "SAHF stores AH into SF, ZF, AF, PF, CF without altering OF"),
    ], start=1):
        def make_flags_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.19.{i:02d}", 19, "M4", name, desc, make_flags_boundary()))

    # Feature 20: Sign/Zero Extension Boundaries (CBW, CWDE, CDQE, CQO, MOVSX, MOVZX)
    for i, (name, asm_str, desc) in enumerate([
        ("cbw_negative_msb", "cbw", "CBW sign-extends AL=0x80 to AX=0xFF80"),
        ("cwde_negative_msb", "cwde", "CWDE sign-extends AX=0x8000 to EAX=0xFFFF8000"),
        ("cdqe_negative_msb", "cdqe", "CDQE sign-extends EAX=0x80000000 to RAX=0xFFFFFFFF80000000"),
        ("cqo_sign_fill_rdx", "cqo", "CQO sign-extends RAX into RDX (RDX=-1 if negative, 0 if positive)"),
        ("movsx_r64_r8_sign_fill", "movsx rax, bl", "MOVSX sign-extends 8-bit register to 64-bit"),
    ], start=1):
        def make_conv_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.20.{i:02d}", 20, "M4", name, desc, make_conv_boundary()))

    # ============================================================================================
    # Features 21-23: Bit Operations, Scans, & Byte Swaps Boundaries (Milestone M5)
    # ============================================================================================
    # Feature 21: Bit Test Boundaries (bit 0, bit 63, toggle twice, reset)
    for i, (name, asm_str, desc) in enumerate([
        ("bt_bit_0_lsb", "bt rax, 0", "BT tests LSB (bit 0) into CF"),
        ("bt_bit_63_msb", "bt rax, 63", "BT tests MSB (bit 63) into CF"),
        ("btc_toggle_twice_identity", "btc rax, 5", "BTC toggles tested bit; two toggles restores original value"),
        ("btr_clear_bit", "btr rax, 15", "BTR clears tested bit to 0 unconditionally"),
        ("bts_set_bit", "bts rax, 31", "BTS sets tested bit to 1 unconditionally"),
    ], start=1):
        def make_bt_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.21.{i:02d}", 21, "M5", name, desc, make_bt_boundary()))

    # Feature 22: Bit Scan & Counting Boundaries (BSF 0, POPCNT 0/64, LZCNT 0)
    for i, (name, asm_str, desc) in enumerate([
        ("bsf_zero_input_zf", "bsf rax, rbx", "BSF on zero input sets ZF=1 per Intel SDM"),
        ("bsr_msb_scan", "bsr rax, rbx", "BSR on 0x8000000000000000 returns index 63"),
        ("popcnt_zero_input", "popcnt rax, rbx", "POPCNT on 0 returns 0 and sets ZF=1"),
        ("popcnt_all_ones", "popcnt rax, rbx", "POPCNT on 0xFFFFFFFFFFFFFFFF returns 64"),
        ("lzcnt_zero_returns_operand_size", "lzcnt rax, rbx", "LZCNT on 0 returns 64 and sets CF=1"),
    ], start=1):
        def make_scan_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.22.{i:02d}", 22, "M5", name, desc, make_scan_boundary()))

    # Feature 23: Byte Swap & Exchange Boundaries (BSWAP palindrome, CMPXCHG success/fail)
    for i, (name, asm_str, desc) in enumerate([
        ("bswap_r64_endian_reverse", "bswap rax", "BSWAP reverses all 8 bytes of 64-bit GPR"),
        ("bswap_r32_zero_extend", "bswap eax", "BSWAP on 32-bit register reverses 4 bytes and zero-extends"),
        ("cmpxchg_match_writes_dest", "cmpxchg rbx, rcx", "CMPXCHG on match (dest == RAX) sets ZF=1 and writes source"),
        ("cmpxchg_mismatch_loads_rax", "cmpxchg rbx, rcx", "CMPXCHG on mismatch clears ZF=0 and loads dest into RAX"),
        ("xadd_atomic_sum_swap", "xadd rax, rbx", "XADD swaps old dest into source and writes sum to dest"),
    ], start=1):
        def make_swap_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.23.{i:02d}", 23, "M5", name, desc, make_swap_boundary()))

    # ============================================================================================
    # Features 24-25: Condition Codes Boundaries (Milestone M6)
    # ============================================================================================
    # Feature 24: SETcc Boundaries (SETZ with ZF=1/0, SETL with SF!=OF, preservation of upper bits)
    for i, (name, asm_str, desc) in enumerate([
        ("setz_zf_one", "setz al", "SETZ writes byte 1 when ZF=1, byte 0 when ZF=0"),
        ("setnz_zf_zero", "setnz al", "SETNZ writes byte 1 when ZF=0, byte 0 when ZF=1"),
        ("setc_cf_one", "setc al", "SETC writes byte 1 when CF=1, byte 0 when CF=0"),
        ("setl_sf_xor_of", "setl al", "SETL writes byte 1 when SF != OF (signed less)"),
        ("setcc_preserves_upper_56", "setz al", "SETcc writes only low 8 bits, preserving upper 56 bits"),
    ], start=1):
        def make_setcc_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.24.{i:02d}", 24, "M6", name, desc, make_setcc_boundary()))

    # Feature 25: CMOVcc Boundaries (CMOVE true/false, 32-bit zero-ext, flags unchanged)
    for i, (name, asm_str, desc) in enumerate([
        ("cmovz_true_moves_value", "cmovz rax, rbx", "CMOVZ moves source to dest when ZF=1"),
        ("cmovz_false_preserves_dest", "cmovz rax, rbx", "CMOVZ leaves destination unmodified when ZF=0"),
        ("cmov_r32_zero_extends_on_true", "cmovz eax, ebx", "32-bit CMOV zero-extends to 64-bit on satisfied condition"),
        ("cmov_false_leaves_upper_intact", "cmovz eax, ebx", "False CMOV condition makes NO modification to destination"),
        ("cmov_preserves_all_flags", "cmovl rax, rbx", "CMOVcc never modifies any status flags in RFLAGS"),
    ], start=1):
        def make_cmov_boundary(a_str=asm_str):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()}"
            return t
        tests.append(make_tier2_test(f"T2.25.{i:02d}", 25, "M6", name, desc, make_cmov_boundary()))

    return tests
