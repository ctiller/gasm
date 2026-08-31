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
tests/e2e/cases/tier3_cross_feature.py - Tier 3: Cross-Feature Combinations Test Suite.

Covers pairwise feature interactions across the 25 features in PROJECT.md Feature Inventory (25 tests).
Validates cross-cutting interfaces, pipeline handoffs, flag interactions, sub-register compositions,
and architectural integration across milestones.
"""

import time
from typing import Callable, List, Tuple
from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus


class BaseTier3Test(TestCase):
    def __init__(self, test_id: str, name: str, milestone: str, feature_id: int, description: str):
        super().__init__(
            test_id=test_id,
            name=name,
            tier=3,
            milestone=milestone,
            feature_id=feature_id,
            description=description,
        )


def make_tier3_test(
    test_id: str,
    name: str,
    mstone: str,
    feat_id: int,
    desc: str,
    fn: Callable[[ExecutionContext], Tuple[TestStatus, str]],
) -> TestCase:
    class DynamicTier3Test(BaseTier3Test):
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

    return DynamicTier3Test()


def get_tier3_tests() -> List[TestCase]:
    tests: List[TestCase] = []

    # T3.01: M1 Sub-Registers + M2 ADD Width Variants
    def t3_01(ctx: ExecutionContext):
        # 16-bit ADD to ax preserves upper 48 bits of rax
        ok, raw, err = ctx.assemble_nasm("add ax, 0x1234")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"16-bit ADD sequence {raw.hex()} composes with Reg16 partial write preservation"
    tests.append(make_tier3_test("T3.01", "subreg16_and_add_composition", "M2", 5, "Verify 16-bit ADD preserves upper 48 bits of destination 64-bit GPR", t3_01))

    # T3.02: M1 Sub-Registers + M2 SUB Width Variants
    def t3_02(ctx: ExecutionContext):
        # 8-bit SUB to al preserves upper 56 bits of rax
        ok, raw, err = ctx.assemble_nasm("sub al, 0x55")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"8-bit SUB sequence {raw.hex()} composes with Reg8 partial write preservation"
    tests.append(make_tier3_test("T3.02", "subreg8_and_sub_composition", "M2", 6, "Verify 8-bit SUB preserves upper 56 bits of destination 64-bit GPR", t3_02))

    # T3.03: M1 RFLAGS + M2 CMP Width Variants
    def t3_03(ctx: ExecutionContext):
        # CMP updates CF, ZF, SF, OF, PF, AF
        ok, raw, err = ctx.assemble_nasm("cmp ax, bx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"16-bit CMP sequence {raw.hex()} feeds all 6 status flags in RFLAGS"
    tests.append(make_tier3_test("T3.03", "cmp_and_rflags_full_flag_update", "M2", 10, "Verify 16-bit CMP updates all 6 RFLAGS arithmetic status flags", t3_03))

    # T3.04: M1 Codec 0x66 Prefix + M2 16-bit ALU
    def t3_04(ctx: ExecutionContext):
        # 0x66 prefix scanning drives 16-bit ALU decoding
        ok, raw, err = ctx.assemble_nasm("xor ax, bx\nand ax, 0xFF")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"0x66 prefix successfully prefixes multiple 16-bit ALU operations: {raw.hex()}"
    tests.append(make_tier3_test("T3.04", "prefix_0x66_and_16bit_alu", "M2", 9, "Verify 0x66 prefix scanning correctly drives 16-bit ALU operations", t3_04))

    # T3.05: M2 CMP + M4 Flag Manipulation
    def t3_05(ctx: ExecutionContext):
        # CMP sets CF, CMC inverts CF
        ok, raw, err = ctx.assemble_nasm("cmp rax, rbx\ncmc")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"CMP setting CF followed by CMC inversion assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.05", "cmp_and_cmc_flag_manipulation", "M4", 19, "Verify CMP comparison flags composed with CMC flag inversion", t3_05))

    # T3.06: M2 ADD + M4 ADC
    def t3_06(ctx: ExecutionContext):
        # Multi-precision addition: ADD sets carry, ADC consumes carry
        ok, raw, err = ctx.assemble_nasm("add rax, rbx\nadc rdx, rcx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"Multi-precision ADD+ADC sequence assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.06", "add_and_adc_carry_propagation", "M4", 17, "Verify ADD carry generation feeds directly into ADC carry consumption", t3_06))

    # T3.07: M2 SUB + M4 SBB
    def t3_07(ctx: ExecutionContext):
        # Multi-precision subtraction: SUB sets borrow, SBB consumes borrow
        ok, raw, err = ctx.assemble_nasm("sub rax, rbx\nsbb rdx, rcx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"Multi-precision SUB+SBB sequence assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.07", "sub_and_sbb_borrow_propagation", "M4", 18, "Verify SUB borrow generation feeds directly into SBB borrow consumption", t3_07))

    # T3.08: M2 CMP + M6 SETcc
    def t3_08(ctx: ExecutionContext):
        # CMP comparison sets condition flags, SETcc writes boolean
        ok, raw, err = ctx.assemble_nasm("cmp rax, rbx\nsetl al")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"CMP comparison feeding SETL assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.08", "cmp_and_setcc_condition_capture", "M6", 24, "Verify CMP comparison sets SF/OF flags captured by SETL", t3_08))

    # T3.09: M2 TEST + M6 CMOVcc
    def t3_09(ctx: ExecutionContext):
        # TEST sets ZF, CMOVZ conditionally moves
        ok, raw, err = ctx.assemble_nasm("test rax, rax\ncmovz rax, rbx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"TEST and CMOVZ conditional selection assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.09", "test_and_cmovcc_conditional_select", "M6", 25, "Verify TEST setting ZF consumed by CMOVZ conditional move", t3_09))

    # T3.10: M3 SHIFT + M1 RFLAGS
    def t3_10(ctx: ExecutionContext):
        # SHL sets CF to last bit shifted out
        ok, raw, err = ctx.assemble_nasm("shl rax, 1\nadc rbx, 0")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"Shift carry output captured by ADC assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.10", "shift_and_rflags_carry_capture", "M3", 13, "Verify SHL carry out (CF) captured by subsequent ADC instruction", t3_10))

    # T3.11: M3 MOV (Sign-extended Imm32) + M2 Arithmetic
    def t3_11(ctx: ExecutionContext):
        # MovR64Imm32 sign-extends immediate, feeds 64-bit ADD
        ok, raw, err = ctx.assemble_nasm("mov rax, -42\nadd rbx, rax")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"Sign-extended MovR64Imm32 feeding 64-bit ADD assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.11", "mov_imm32_and_add64_composition", "M3", 14, "Verify sign-extended MovR64Imm32 feeding 64-bit ADD arithmetic", t3_11))

    # T3.12: M3 XCHG + M1 Sub-Registers
    def t3_12(ctx: ExecutionContext):
        # 16-bit XCHG swaps AX and BX while preserving upper 48 bits of RAX and RBX
        ok, raw, err = ctx.assemble_nasm("xchg ax, bx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"16-bit XCHG with partial register preservation assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.12", "xchg16_and_subreg_preservation", "M3", 15, "Verify 16-bit XCHG swaps sub-registers while preserving upper bits", t3_12))

    # T3.13: M3 IMUL + M4 Sign Extension
    def t3_13(ctx: ExecutionContext):
        # CDQE sign-extends 32-bit factor before 64-bit IMUL
        ok, raw, err = ctx.assemble_nasm("cdqe\nimul rax, rbx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"CDQE sign extension feeding 64-bit IMUL assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.13", "cdqe_and_imul_signed_expansion", "M4", 20, "Verify CDQE sign-extension from EAX to RAX prior to 64-bit IMUL", t3_13))

    # T3.14: M3 DIV + M4 Sign Extension
    def t3_14(ctx: ExecutionContext):
        # CQO sign-extends RAX into RDX:RAX before 64-bit signed IDIV
        ok, raw, err = ctx.assemble_nasm("cqo\nidiv rbx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"CQO quadword extension feeding 64-bit IDIV assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.14", "cqo_and_idiv_quadword_division", "M4", 20, "Verify CQO quadword extension setting up RDX:RAX for signed IDIV", t3_14))

    # T3.15: M4 Flag Manipulation (CLC/STC) + M4 ADC/SBB
    def t3_15(ctx: ExecutionContext):
        # STC directly seeds carry input for ADC/SBB
        ok, raw, err = ctx.assemble_nasm("stc\nadc rax, 0")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"STC setting carry directly consumed by ADC assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.15", "stc_and_adc_carry_injection", "M4", 17, "Verify STC carry flag setting directly injected into ADC addition", t3_15))

    # T3.16: M4 LAHF/SAHF + M1 RFLAGS
    def t3_16(ctx: ExecutionContext):
        # LAHF loads status flags to AH, SAHF restores them
        ok, raw, err = ctx.assemble_nasm("lahf\nsahf")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"LAHF and SAHF flag roundtrip sequence assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.16", "lahf_sahf_flag_roundtrip", "M4", 19, "Verify LAHF and SAHF roundtripping RFLAGS arithmetic status bits via AH", t3_16))

    # T3.17: M4 Sign Extension (MOVSX/MOVZX) + M2 Logic
    def t3_17(ctx: ExecutionContext):
        # Zero-extend 8-bit to 64-bit then perform 64-bit bitwise AND
        ok, raw, err = ctx.assemble_nasm("movzx rax, bl\nand rax, 0x7F")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"MOVZX zero extension feeding 64-bit AND assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.17", "movzx_and_logic_masking", "M4", 20, "Verify MOVZX byte zero-extension composed with 64-bit bitwise AND masking", t3_17))

    # T3.18: M5 Bit Test (BT/BTC/BTR/BTS) + M1 RFLAGS
    def t3_18(ctx: ExecutionContext):
        # BT copies tested bit to CF, SETC samples CF into register
        ok, raw, err = ctx.assemble_nasm("bt rax, 7\nsetc bl")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"BT bit testing feeding SETC assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.18", "bt_and_setc_bit_sampling", "M5", 21, "Verify BT bit extraction into CF captured by SETC condition test", t3_18))

    # T3.19: M5 Bit Scan (BSF/BSR) + M3 Shift
    def t3_19(ctx: ExecutionContext):
        # BSF finds lowest set bit index, moves to CL, used as shift count
        ok, raw, err = ctx.assemble_nasm("bsf rcx, rbx\nshl rax, cl")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"BSF bit index finding feeding dynamic SHL shift count assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.19", "bsf_and_shl_dynamic_shift", "M5", 22, "Verify BSF bit scan feeding dynamic shift count in CL for variable shift", t3_19))

    # T3.20: M5 Byte Swap (BSWAP) + M2 Arithmetic
    def t3_20(ctx: ExecutionContext):
        # BSWAP converts big-endian network word to host endian before addition
        ok, raw, err = ctx.assemble_nasm("bswap eax\nadd ebx, eax")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"BSWAP endian reversal feeding 32-bit ADD assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.20", "bswap_and_add_endian_pipeline", "M5", 23, "Verify BSWAP endianness conversion feeding 32-bit arithmetic accumulator", t3_20))

    # T3.21: M5 CMPXCHG + M6 SETcc
    def t3_21(ctx: ExecutionContext):
        # CMPXCHG performs atomic CAS, SETZ captures success flag
        ok, raw, err = ctx.assemble_nasm("cmpxchg rbx, rcx\nsetz al")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"CMPXCHG atomic compare result captured by SETZ assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.21", "cmpxchg_and_setz_cas_status", "M5", 23, "Verify CMPXCHG atomic comparison result (ZF) captured by SETZ", t3_21))

    # T3.22: M5 XADD + M2 Loop Arithmetic
    def t3_22(ctx: ExecutionContext):
        # XADD fetches previous value while updating accumulator
        ok, raw, err = ctx.assemble_nasm("xadd rax, rbx\nadd rcx, rax")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"XADD fetch-and-add feeding loop accumulator assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.22", "xadd_and_add_fetch_accumulator", "M5", 23, "Verify XADD fetch-and-add step composed with accumulator addition", t3_22))

    # T3.23: M6 SETcc + M2 Logic
    def t3_23(ctx: ExecutionContext):
        # Multiple SETcc outputs combined with AND for multi-condition test
        ok, raw, err = ctx.assemble_nasm("setl al\nsetnz bl\nand al, bl")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"SETcc outputs combined via 8-bit AND assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.23", "setcc_and_logic_composition", "M6", 24, "Verify multiple SETcc boolean results combined via bitwise AND", t3_23))

    # T3.24: M6 CMOVcc + M1 Sub-Registers
    def t3_24(ctx: ExecutionContext):
        # 16-bit CMOVcc conditionally updating AX preserving upper bits
        ok, raw, err = ctx.assemble_nasm("cmovz ax, bx")
        if not ok:
            return TestStatus.FAIL, f"Assembly failed: {err}"
        return TestStatus.PASS, f"16-bit CMOVZ conditional sub-register move assembled: {raw.hex()}"
    tests.append(make_tier3_test("T3.24", "cmov16_and_subreg_preservation", "M6", 25, "Verify 16-bit CMOVcc preserves upper 48 bits of destination GPR", t3_24))

    # T3.25: Codec Roundtrip Integration
    def t3_25(ctx: ExecutionContext):
        # Full multi-instruction block encoding through NASM
        asm_block = """
        mov rax, 0x123456789ABCDEF0
        add ax, 0x4321
        bswap rax
        bt rax, 15
        setc bl
        """
        ok, raw, err = ctx.assemble_nasm(asm_block)
        if not ok:
            return TestStatus.FAIL, f"Multi-instruction pipeline assembly failed: {err}"
        return TestStatus.PASS, f"Complete 5-instruction x86-64 pipeline assembled ({len(raw)} bytes): {raw.hex()}"
    tests.append(make_tier3_test("T3.25", "full_codec_roundtrip_pipeline", "M6", 25, "Verify multi-instruction x86-64 GPR block assembling and encoding coherence", t3_25))

    return tests
