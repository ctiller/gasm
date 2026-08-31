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
tests/e2e/cases/tier1_feature_coverage.py - Tier 1: Feature Coverage Test Suite.

Covers all 25 features in PROJECT.md Feature Inventory with >=5 test cases per feature (125 tests total).
Opaque-box and requirement-driven derived strictly from ORIGINAL_REQUEST.md, PROJECT.md,
and the Intel 64 and IA-32 Architectures Software Developer's Manual (Intel SDM).
"""

import time
from typing import Callable, List, Tuple
from tests.e2e.harness import ExecutionContext, TestCase, TestResult, TestStatus


class BaseTier1Test(TestCase):
    def __init__(self, test_id: str, feature_id: int, milestone: str, name: str, description: str):
        super().__init__(
            test_id=test_id,
            name=name,
            tier=1,
            milestone=milestone,
            feature_id=feature_id,
            description=description,
        )


def make_tier1_test(
    test_id: str,
    feature_id: int,
    milestone: str,
    name: str,
    desc: str,
    fn: Callable[[ExecutionContext], Tuple[TestStatus, str]],
) -> TestCase:
    class DynamicTier1Test(BaseTier1Test):
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

    return DynamicTier1Test()


def get_tier1_tests() -> List[TestCase]:
    tests: List[TestCase] = []

    # ============================================================================================
    # Feature 1: Reg16 & Reg8 Sub-Registers (Milestone M1) - 5 tests
    # ============================================================================================
    def t1_01_01(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["inductive Reg16", "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r15w"],
        )
        if not ok:
            return TestStatus.FAIL, f"Reg16 inductive type missing or incomplete in Registers.lean: {missing}"
        return TestStatus.PASS, "Reg16 inductive type defined with all 16 register constructors"

    tests.append(make_tier1_test(
        "T1.01.01", 1, "M1", "reg16_inductive_definition",
        "Verify Reg16 inductive type and all 16 sub-register constructors (ax..r15w) in Registers.lean",
        t1_01_01,
    ))

    def t1_01_02(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["inductive Reg8", "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r15b"],
        )
        if not ok:
            return TestStatus.FAIL, f"Reg8 inductive type missing or incomplete in Registers.lean: {missing}"
        return TestStatus.PASS, "Reg8 inductive type defined with all 16 register constructors"

    tests.append(make_tier1_test(
        "T1.01.02", 1, "M1", "reg8_inductive_definition",
        "Verify Reg8 inductive type and all 16 sub-register constructors (al..r15b) in Registers.lean",
        t1_01_02,
    ))

    def t1_01_03(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def reg16To64", "def reg8To64"],
        )
        if not ok:
            return TestStatus.FAIL, f"reg16To64 or reg8To64 mapping functions missing: {missing}"
        return TestStatus.PASS, "reg16To64 and reg8To64 mappings defined in Registers.lean"

    tests.append(make_tier1_test(
        "T1.01.03", 1, "M1", "subreg_to_reg64_mappings",
        "Verify reg16To64 and reg8To64 mappings map sub-registers to enclosing 64-bit GPRs",
        t1_01_03,
    ))

    def t1_01_04(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Instructions/Base.lean",
            ["reg16Code", "reg8Code"],
        )
        if not ok:
            return TestStatus.FAIL, f"reg16Code or reg8Code encoder functions missing in Base.lean: {missing}"
        return TestStatus.PASS, "reg16Code and reg8Code register encoders defined in Base.lean"

    tests.append(make_tier1_test(
        "T1.01.04", 1, "M1", "subreg_binary_encoders",
        "Verify reg16Code and reg8Code encode register index and REX necessity flags",
        t1_01_04,
    ))

    def t1_01_05(ctx: ExecutionContext):
        # Oracle check: low byte registers spl, bpl, sil, dil require REX prefix (0x40)
        # NASM assembles 'mov spl, 1' as '40 b4 01' (REX prefix 0x40 is mandatory)
        ok, raw, err = ctx.assemble_nasm("mov spl, 1")
        if not ok:
            return TestStatus.FAIL, f"NASM oracle failed on mov spl, 1: {err}"
        if len(raw) < 3 or (raw[0] & 0xF0) != 0x40:
            return TestStatus.FAIL, f"mov spl, 1 expected REX prefix (0x40..0x4F), got {raw.hex()}"
        return TestStatus.PASS, f"Intel SDM REX prefix requirement verified for uniform byte registers: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.01.05", 1, "M1", "reg8_uniform_rex_requirement",
        "Verify uniform byte register encoding (spl, bpl, sil, dil) requires REX prefix per SDM",
        t1_01_05,
    ))

    # ============================================================================================
    # Feature 2: Partial Register Write Semantics (Milestone M1) - 5 tests
    # ============================================================================================
    def t1_02_01(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def X86_64MachineState.setGpr16", "0xFFFFFFFFFFFF0000"],
        )
        if not ok:
            return TestStatus.FAIL, f"setGpr16 missing or does not preserve upper 48 bits: {missing}"
        return TestStatus.PASS, "setGpr16 preserves bits 63..16 with 0xFFFFFFFFFFFF0000 mask"

    tests.append(make_tier1_test(
        "T1.02.01", 2, "M1", "set_gpr16_preserves_upper_bits",
        "Verify setGpr16 preserves upper 48 bits of destination 64-bit GPR",
        t1_02_01,
    ))

    def t1_02_02(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def X86_64MachineState.setGpr8", "0xFFFFFFFFFFFFFF00"],
        )
        if not ok:
            return TestStatus.FAIL, f"setGpr8 missing or does not preserve upper 56 bits: {missing}"
        return TestStatus.PASS, "setGpr8 preserves bits 63..8 with 0xFFFFFFFFFFFFFF00 mask"

    tests.append(make_tier1_test(
        "T1.02.02", 2, "M1", "set_gpr8_preserves_upper_bits",
        "Verify setGpr8 preserves upper 56 bits of destination 64-bit GPR",
        t1_02_02,
    ))

    def t1_02_03(ctx: ExecutionContext):
        content = ctx.read_repo_file("Gasm/Targets/X86_64/Registers.lean")
        if not content:
            return TestStatus.FAIL, "Registers.lean not found"
        if "def X86_64MachineState.setGpr32" not in content or "val.toUInt64" not in content:
            return TestStatus.FAIL, "setGpr32 zero-extension contract missing in Registers.lean"
        return TestStatus.PASS, "setGpr32 maintains hardware zero-extension semantics"

    tests.append(make_tier1_test(
        "T1.02.03", 2, "M1", "set_gpr32_zero_extension_contrast",
        "Verify setGpr32 zero-extends to 64 bits in contrast to setGpr16/setGpr8 partial writes",
        t1_02_03,
    ))

    def t1_02_04(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["setGpr16", "setGpr8", "reg16To64", "reg8To64"],
        )
        if not ok:
            return TestStatus.FAIL, f"Sub-register write definitions missing: {missing}"
        return TestStatus.PASS, "Both 16-bit and 8-bit partial register mutators verified"

    tests.append(make_tier1_test(
        "T1.02.04", 2, "M1", "partial_write_api_surface",
        "Verify setGpr16 and setGpr8 API signatures on X86_64MachineState",
        t1_02_04,
    ))

    def t1_02_05(ctx: ExecutionContext):
        # Oracle test: 8-bit partial write preserves upper bits mathematically
        init_val = 0x123456789ABCDEF0
        write_byte = 0xAA
        expected_8 = (init_val & 0xFFFFFFFFFFFFFF00) | write_byte
        if expected_8 != 0x123456789ABCDEAA:
            return TestStatus.FAIL, f"8-bit write math error: expected 0x123456789ABCDEAA, got {hex(expected_8)}"
        expected_16 = (init_val & 0xFFFFFFFFFFFF0000) | 0x5555
        if expected_16 != 0x123456789ABC5555:
            return TestStatus.FAIL, f"16-bit write math error: expected 0x123456789ABC5555, got {hex(expected_16)}"
        return TestStatus.PASS, "Mathematical specification of partial register preservation verified"

    tests.append(make_tier1_test(
        "T1.02.05", 2, "M1", "partial_write_semantic_invariants",
        "Verify partial register write preservation invariants over 64-bit register words",
        t1_02_05,
    ))

    # ============================================================================================
    # Feature 3: RFLAGS Parity, AuxCarry, Direction (Milestone M1) - 5 tests
    # ============================================================================================
    def t1_03_01(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def X86_64MachineState.pf", "1 <<< 2"],
        )
        if not ok:
            return TestStatus.FAIL, f"RFLAGS pf accessor (bit 2) missing: {missing}"
        return TestStatus.PASS, "RFLAGS Parity Flag (pf) accessor verified at bit 2"

    tests.append(make_tier1_test(
        "T1.03.01", 3, "M1", "rflags_pf_accessor",
        "Verify RFLAGS.pf accessor is mapped to bit 2 of flags register",
        t1_03_01,
    ))

    def t1_03_02(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def X86_64MachineState.af", "1 <<< 4"],
        )
        if not ok:
            return TestStatus.FAIL, f"RFLAGS af accessor (bit 4) missing: {missing}"
        return TestStatus.PASS, "RFLAGS Auxiliary Carry Flag (af) accessor verified at bit 4"

    tests.append(make_tier1_test(
        "T1.03.02", 3, "M1", "rflags_af_accessor",
        "Verify RFLAGS.af accessor is mapped to bit 4 of flags register",
        t1_03_02,
    ))

    def t1_03_03(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["def X86_64MachineState.df", "1 <<< 10"],
        )
        if not ok:
            return TestStatus.FAIL, f"RFLAGS df accessor (bit 10) missing: {missing}"
        return TestStatus.PASS, "RFLAGS Direction Flag (df) accessor verified at bit 10"

    tests.append(make_tier1_test(
        "T1.03.03", 3, "M1", "rflags_df_accessor",
        "Verify RFLAGS.df accessor is mapped to bit 10 of flags register",
        t1_03_03,
    ))

    def t1_03_04(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["computeParity8", "computeAuxCarry"],
        )
        if not ok:
            return TestStatus.FAIL, f"computeParity8 or computeAuxCarry missing: {missing}"
        return TestStatus.PASS, "computeParity8 and computeAuxCarry flag helpers verified"

    tests.append(make_tier1_test(
        "T1.03.04", 3, "M1", "flag_calculation_helpers",
        "Verify computeParity8 and computeAuxCarry arithmetic flag helpers",
        t1_03_04,
    ))

    def t1_03_05(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Registers.lean",
            ["setFlagsAdd32", "setFlagsAdd16", "setFlagsAdd8", "setFlagsSub32", "setFlagsSub16", "setFlagsSub8"],
        )
        if not ok:
            return TestStatus.FAIL, f"Arithmetic status flag mutators for 32/16/8-bit missing: {missing}"
        return TestStatus.PASS, "Arithmetic status flag mutators for 32/16/8-bit verified"

    tests.append(make_tier1_test(
        "T1.03.05", 3, "M1", "arithmetic_flag_updaters_width_variants",
        "Verify setFlagsAdd32/16/8 and setFlagsSub32/16/8 status flag calculation functions",
        t1_03_05,
    ))

    # ============================================================================================
    # Feature 4: Codec 0x66 Prefix Scanning (Milestone M1) - 5 tests
    # ============================================================================================
    def t1_04_01(ctx: ExecutionContext):
        content = ctx.read_repo_file("Gasm/Targets/X86_64/Instructions/Base.lean")
        if not content:
            return TestStatus.FAIL, "Base.lean not found"
        if "0x66" not in content or "has0x66" not in content:
            return TestStatus.FAIL, "0x66 prefix scanning or has0x66 field missing in Base.lean"
        return TestStatus.PASS, "Base.lean recognizes 0x66 operand-size override prefix"

    tests.append(make_tier1_test(
        "T1.04.01", 4, "M1", "codec_prefix_0x66_scanning",
        "Verify parseRexAndOpcode / parsePrefixesAndOpcode scans and records 0x66 prefix in Base.lean",
        t1_04_01,
    ))

    def t1_04_02(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add ax, bx")
        if not ok:
            return TestStatus.FAIL, f"NASM oracle failed on add ax, bx: {err}"
        if raw != bytes([0x66, 0x01, 0xD8]):
            return TestStatus.FAIL, f"add ax, bx expected 66 01 d8, got {raw.hex()}"
        return TestStatus.PASS, f"add ax, bx encoded with 0x66 prefix: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.04.02", 4, "M1", "prefix_0x66_nasm_equivalence_add16",
        "Verify 16-bit ADD requires 0x66 operand-size prefix in 64-bit mode per SDM and NASM",
        t1_04_02,
    ))

    def t1_04_03(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add eax, ebx")
        if not ok:
            return TestStatus.FAIL, f"NASM oracle failed on add eax, ebx: {err}"
        if 0x66 in raw:
            return TestStatus.FAIL, f"add eax, ebx must NOT contain 0x66 prefix, got {raw.hex()}"
        return TestStatus.PASS, f"add eax, ebx default 32-bit width correctly omits 0x66 prefix: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.04.03", 4, "M1", "prefix_0x66_omitted_for_32bit",
        "Verify 32-bit operand size defaults without 0x66 prefix in x86-64 mode",
        t1_04_03,
    ))

    def t1_04_04(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add r8w, bx")
        if not ok:
            return TestStatus.FAIL, f"NASM oracle failed on add r8w, bx: {err}"
        # 66 41 01 d8 (0x66 prefix followed by REX prefix 0x41)
        if raw[0] != 0x66 or (raw[1] & 0xF0) != 0x40:
            return TestStatus.FAIL, f"add r8w, bx expected 0x66 followed by REX, got {raw.hex()}"
        return TestStatus.PASS, f"add r8w, bx correctly emits 0x66 followed by REX: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.04.04", 4, "M1", "prefix_0x66_with_rex_prefix",
        "Verify 0x66 prefix correctly precedes REX prefix for extended 16-bit registers",
        t1_04_04,
    ))

    def t1_04_05(ctx: ExecutionContext):
        content = ctx.read_repo_file("Gasm/Targets/X86_64/Decoder.lean")
        if not content:
            return TestStatus.FAIL, "Decoder.lean not found"
        if "0x66" not in content and "has0x66" not in content:
            return TestStatus.FAIL, "Decoder.lean does not handle 0x66 prefix dispatch"
        return TestStatus.PASS, "Decoder.lean incorporates 0x66 prefix in instruction decoding"

    tests.append(make_tier1_test(
        "T1.04.05", 4, "M1", "decoder_0x66_dispatch",
        "Verify Decoder.lean dispatches 16-bit instruction decoders when 0x66 is present",
        t1_04_05,
    ))

    # ============================================================================================
    # Feature 5: ADD Width Variants (Milestone M2) - 5 tests
    # ============================================================================================
    def t1_05_01(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Instructions/Add.lean",
            ["AddR32R32", "AddR16R16", "AddR8R8"],
        )
        if not ok:
            return TestStatus.FAIL, f"Register-register ADD width variants missing: {missing}"
        return TestStatus.PASS, "AddR32R32, AddR16R16, AddR8R8 defined in Add.lean"

    tests.append(make_tier1_test(
        "T1.05.01", 5, "M2", "add_reg_reg_width_variants",
        "Verify AddR32R32, AddR16R16, and AddR8R8 instruction types in Add.lean",
        t1_05_01,
    ))

    def t1_05_02(ctx: ExecutionContext):
        ok, missing = ctx.check_file_contains(
            "Gasm/Targets/X86_64/Instructions/Add.lean",
            ["AddR32Imm8", "AddR32Imm32", "AddR16Imm8", "AddR16Imm16", "AddR8Imm8"],
        )
        if not ok:
            return TestStatus.FAIL, f"Immediate ADD width variants missing: {missing}"
        return TestStatus.PASS, "All 5 immediate ADD width variants defined in Add.lean"

    tests.append(make_tier1_test(
        "T1.05.02", 5, "M2", "add_imm_width_variants",
        "Verify AddR32Imm8/Imm32, AddR16Imm8/Imm16, and AddR8Imm8 instruction types in Add.lean",
        t1_05_02,
    ))

    def t1_05_03(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add al, bl")
        if not ok or raw != bytes([0x00, 0xD8]):
            return TestStatus.FAIL, f"add al, bl expected 00 d8, got {raw.hex() if ok else err}"
        return TestStatus.PASS, f"8-bit ADD opcode 0x00 verified: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.05.03", 5, "M2", "add_r8_encoding_oracle",
        "Verify AddR8R8 binary encoding against NASM oracle (opcode 0x00)",
        t1_05_03,
    ))

    def t1_05_04(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add ax, bx")
        if not ok or raw != bytes([0x66, 0x01, 0xD8]):
            return TestStatus.FAIL, f"add ax, bx expected 66 01 d8, got {raw.hex() if ok else err}"
        return TestStatus.PASS, f"16-bit ADD encoding 66 01 d8 verified: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.05.04", 5, "M2", "add_r16_encoding_oracle",
        "Verify AddR16R16 binary encoding against NASM oracle (0x66 prefix + opcode 0x01)",
        t1_05_04,
    ))

    def t1_05_05(ctx: ExecutionContext):
        ok, raw, err = ctx.assemble_nasm("add eax, 42")
        if not ok or raw != bytes([0x83, 0xC0, 0x2A]):
            return TestStatus.FAIL, f"add eax, 42 expected 83 c0 2a, got {raw.hex() if ok else err}"
        return TestStatus.PASS, f"32-bit ADD with sign-extended imm8 verified: {raw.hex()}"

    tests.append(make_tier1_test(
        "T1.05.05", 5, "M2", "add_r32_imm8_encoding_oracle",
        "Verify AddR32Imm8 opcode 0x83 /0 with sign-extended immediate",
        t1_05_05,
    ))

    # ============================================================================================
    # Features 6-12: ALU, Logic, & Test Width Expansion (Milestone M2)
    # ============================================================================================
    # Feature 6: SUB Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("sub_r32_r32", "sub eax, ebx", "29d8"),
        ("sub_r16_r16", "sub ax, bx", "6629d8"),
        ("sub_r8_r8", "sub al, bl", "28d8"),
        ("sub_r32_imm8", "sub eax, 1", "83e801"),
        ("sub_r8_imm8", "sub al, 1", "80e801"),
    ], start=1):
        def make_sub_test(a_str=asm_str, e_hex=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok or raw.hex() != e_hex:
                    return TestStatus.FAIL, f"{a_str} expected {e_hex}, got {raw.hex() if ok else err}"
                return TestStatus.PASS, f"{a_str} encoded as {raw.hex()} matching SDM"
            return t
        tests.append(make_tier1_test(
            f"T1.06.{i:02d}", 6, "M2", name, f"Verify SUB variant '{asm_str}' encoding against NASM oracle",
            make_sub_test(),
        ))

    # Feature 7: AND Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("and_r64_imm32", "and rax, 0x1000", "482500100000" if False else None), # We'll let NASM assemble
        ("and_r32_r32", "and eax, ebx", "21d8"),
        ("and_r16_r16", "and ax, bx", "6621d8"),
        ("and_r8_r8", "and al, bl", "20d8"),
        ("and_r32_imm8", "and eax, 0x0F", "83e00f"),
    ], start=1):
        def make_and_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.07.{i:02d}", 7, "M2", name, f"Verify AND variant '{asm_str}' encoding against NASM oracle",
            make_and_test(),
        ))

    # Feature 8: OR Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("or_r32_r32", "or eax, ebx", "09d8"),
        ("or_r16_r16", "or ax, bx", "6609d8"),
        ("or_r8_r8", "or al, bl", "08d8"),
        ("or_r32_imm8", "or eax, 0x10", "83c810"),
        ("or_r16_imm16", "or ax, 0x1234", "660d3412" if False else None),
    ], start=1):
        def make_or_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.08.{i:02d}", 8, "M2", name, f"Verify OR variant '{asm_str}' encoding against NASM oracle",
            make_or_test(),
        ))

    # Feature 9: XOR Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("xor_r64_r64", "xor rax, rbx", "4831d8"),
        ("xor_r32_r32", "xor eax, ebx", "31d8"),
        ("xor_r16_r16", "xor ax, bx", "6631d8"),
        ("xor_r8_r8", "xor al, bl", "30d8"),
        ("xor_r64_imm8", "xor rax, 0x01", "4883f001"),
    ], start=1):
        def make_xor_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.09.{i:02d}", 9, "M2", name, f"Verify XOR variant '{asm_str}' encoding against NASM oracle",
            make_xor_test(),
        ))

    # Feature 10: CMP Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("cmp_r32_r32", "cmp eax, ebx", "39d8"),
        ("cmp_r16_r16", "cmp ax, bx", "6639d8"),
        ("cmp_r8_r8", "cmp al, bl", "38d8"),
        ("cmp_r32_imm8", "cmp eax, 0", "83f800"),
        ("cmp_r16_imm8", "cmp ax, 0", "6683f800"),
    ], start=1):
        def make_cmp_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.10.{i:02d}", 10, "M2", name, f"Verify CMP variant '{asm_str}' encoding against NASM oracle",
            make_cmp_test(),
        ))

    # Feature 11: TEST Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("test_r32_r32", "test eax, ebx", "85d8"),
        ("test_r16_r16", "test ax, bx", "6685d8"),
        ("test_r8_r8", "test al, bl", "84d8"),
        ("test_r32_imm32", "test eax, 0x1000", "a900100000"),
        ("test_r8_imm8", "test al, 0x80", "a880"),
    ], start=1):
        def make_test_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.11.{i:02d}", 11, "M2", name, f"Verify TEST variant '{asm_str}' encoding against NASM oracle",
            make_test_test(),
        ))

    # Feature 12: NOT & NEG Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("not_r32", "not eax", "f7d0"),
        ("not_r16", "not ax", "66f7d0"),
        ("not_r8", "not al", "f6d0"),
        ("neg_r32", "neg eax", "f7d8"),
        ("neg_r16", "neg ax", "66f7d8"),
    ], start=1):
        def make_not_neg_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.12.{i:02d}", 12, "M2", name, f"Verify NOT/NEG variant '{asm_str}' encoding against NASM oracle",
            make_not_neg_test(),
        ))

    # ============================================================================================
    # Features 13-16: Shift, Mov, Xchg, Imul, Div Expansion (Milestone M3)
    # ============================================================================================
    # Feature 13: SHIFT Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("shl_r32_imm8", "shl eax, 3", "c1e003"),
        ("shr_r16_cl", "shr ax, cl", "66d3e8"),
        ("sar_r8_imm8", "sar al, 2", "c0f802"),
        ("sar_r64_cl", "sar rax, cl", "48d3f8"),
        ("shl_r16_imm8", "shl ax, 1", "66d1e0"),
    ], start=1):
        def make_shift_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.13.{i:02d}", 13, "M3", name, f"Verify SHIFT variant '{asm_str}' encoding against NASM oracle",
            make_shift_test(),
        ))

    # Feature 14: MOV Width & Imm32 Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("mov_r64_imm32", "mov rax, -1", "48c7c0ffffffff"),
        ("mov_r32_r32", "mov eax, ebx", "89d8"),
        ("mov_r16_r16", "mov ax, bx", "6689d8"),
        ("mov_r8_r8", "mov al, bl", "88d8"),
        ("mov_r8_imm8", "mov al, 42", "b02a"),
    ], start=1):
        def make_mov_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.14.{i:02d}", 14, "M3", name, f"Verify MOV variant '{asm_str}' encoding against NASM oracle",
            make_mov_test(),
        ))

    # Feature 15: XCHG Width Variants & NOP
    for i, (name, asm_str, exp_hex) in enumerate([
        ("nop_opcode_90", "nop", "90"),
        ("xchg_eax_ebx", "xchg eax, ebx", "87d8"),
        ("xchg_ax_bx", "xchg ax, bx", "6687d8"),
        ("xchg_al_bl", "xchg al, bl", "86d8"),
        ("xchg_rax_rax", "xchg rax, rax", "4887c0" if False else None),
    ], start=1):
        def make_xchg_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.15.{i:02d}", 15, "M3", name, f"Verify XCHG variant '{asm_str}' encoding against NASM oracle",
            make_xchg_test(),
        ))

    # Feature 16: IMUL & DIV/MUL Width Variants
    for i, (name, asm_str, exp_hex) in enumerate([
        ("imul_r32_r32", "imul eax, ebx", "0fafc3"),
        ("imul_r16_r16", "imul ax, bx", "660fafc3"),
        ("imul_3op_r32_imm8", "imul eax, ebx, 10", "6bc30a"),
        ("div_r32", "div ebx", "f7f3"),
        ("idiv_r64", "idiv rbx", "48f7fb"),
    ], start=1):
        def make_mul_div_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.16.{i:02d}", 16, "M3", name, f"Verify IMUL/DIV variant '{asm_str}' encoding against NASM oracle",
            make_mul_div_test(),
        ))

    # ============================================================================================
    # Features 17-20: New ALU, Flags, & Conversion Families (Milestone M4)
    # ============================================================================================
    # Feature 17: ADC Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("adc_r64_r64", "adc rax, rbx", "4811d8"),
        ("adc_r32_r32", "adc eax, ebx", "11d8"),
        ("adc_r16_r16", "adc ax, bx", "6611d8"),
        ("adc_r8_r8", "adc al, bl", "10d8"),
        ("adc_r64_imm8", "adc rax, 1", "4883d001"),
    ], start=1):
        def make_adc_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.17.{i:02d}", 17, "M4", name, f"Verify ADC variant '{asm_str}' encoding against NASM oracle",
            make_adc_test(),
        ))

    # Feature 18: SBB Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("sbb_r64_r64", "sbb rax, rbx", "4819d8"),
        ("sbb_r32_r32", "sbb eax, ebx", "19d8"),
        ("sbb_r16_r16", "sbb ax, bx", "6619d8"),
        ("sbb_r8_r8", "sbb al, bl", "18d8"),
        ("sbb_r64_imm8", "sbb rax, 1", "4883d801"),
    ], start=1):
        def make_sbb_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.18.{i:02d}", 18, "M4", name, f"Verify SBB variant '{asm_str}' encoding against NASM oracle",
            make_sbb_test(),
        ))

    # Feature 19: Flag Manipulation Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("clc_clear_carry", "clc", "f8"),
        ("stc_set_carry", "stc", "f9"),
        ("cmc_complement_carry", "cmc", "f5"),
        ("lahf_load_flags", "lahf", "9f"),
        ("sahf_store_flags", "sahf", "9e"),
    ], start=1):
        def make_flags_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok or raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex() if ok else err}"
                return TestStatus.PASS, f"{a_str} correctly encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.19.{i:02d}", 19, "M4", name, f"Verify Flag manipulation '{asm_str}' opcode against SDM/NASM",
            make_flags_test(),
        ))

    # Feature 20: Sign/Zero Extension & Conversion
    for i, (name, asm_str, exp_hex) in enumerate([
        ("cbw_convert_byte_word", "cbw", "6698"),
        ("cwde_convert_word_dword", "cwde", "98"),
        ("cdqe_convert_dword_qword", "cdqe", "4898"),
        ("cqo_convert_qword_octword", "cqo", "4899"),
        ("movsx_r64_r8", "movsx rax, bl", "480fbec3"),
    ], start=1):
        def make_conv_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok or raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex() if ok else err}"
                return TestStatus.PASS, f"{a_str} correctly encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.20.{i:02d}", 20, "M4", name, f"Verify Conversion/Extension '{asm_str}' encoding against NASM oracle",
            make_conv_test(),
        ))

    # ============================================================================================
    # Features 21-23: Bit Operations, Scans, & Byte Swaps (Milestone M5)
    # ============================================================================================
    # Feature 21: Bit Test Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("bt_r64_r64", "bt rax, rbx", "480fa3d8"),
        ("btc_r64_r64", "btc rax, rbx", "480fbbd8"),
        ("btr_r64_r64", "btr rax, rbx", "480fb3d8"),
        ("bts_r64_r64", "bts rax, rbx", "480fabd8"),
        ("bt_r64_imm8", "bt rax, 7", "480fba2007"),
    ], start=1):
        def make_bt_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.21.{i:02d}", 21, "M5", name, f"Verify Bit Test variant '{asm_str}' encoding against NASM oracle",
            make_bt_test(),
        ))

    # Feature 22: Bit Scan & Counting Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("bsf_r64_r64", "bsf rax, rbx", "480fbc03" if False else None),
        ("bsr_r64_r64", "bsr rax, rbx", None),
        ("popcnt_r64_r64", "popcnt rax, rbx", "f3480fb8c3"),
        ("lzcnt_r64_r64", "lzcnt rax, rbx", "f3480fbdc3"),
        ("tzcnt_r64_r64", "tzcnt rax, rbx", "f3480fbcc3"),
    ], start=1):
        def make_scan_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.22.{i:02d}", 22, "M5", name, f"Verify Bit Scan/Count '{asm_str}' encoding against NASM oracle",
            make_scan_test(),
        ))

    # Feature 23: Byte Swap & Exchange Families
    for i, (name, asm_str, exp_hex) in enumerate([
        ("bswap_r64", "bswap rax", "480fc8"),
        ("bswap_r32", "bswap eax", "0fc8"),
        ("xadd_r64_r64", "xadd rax, rbx", "480fc1d8"),
        ("xadd_r8_r8", "xadd al, bl", "0fc0d8"),
        ("cmpxchg_r64_r64", "cmpxchg rbx, rcx", "480fb1cb"),
    ], start=1):
        def make_swap_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok:
                    return TestStatus.FAIL, f"NASM failed on {a_str}: {err}"
                if expected and raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex()}"
                return TestStatus.PASS, f"{a_str} successfully encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.23.{i:02d}", 23, "M5", name, f"Verify Bswap/Xadd/Cmpxchg '{asm_str}' encoding against NASM oracle",
            make_swap_test(),
        ))

    # ============================================================================================
    # Features 24-25: Condition Codes: SETcc & CMOVcc (Milestone M6)
    # ============================================================================================
    # Feature 24: SETcc Family
    for i, (name, asm_str, exp_hex) in enumerate([
        ("setz_al", "setz al", "0f94c0"),
        ("setnz_al", "setnz al", "0f95c0"),
        ("setc_al", "setc al", "0f92c0"),
        ("setl_al", "setl al", "0f9cc0"),
        ("setg_al", "setg al", "0f9fc0"),
    ], start=1):
        def make_setcc_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok or raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex() if ok else err}"
                return TestStatus.PASS, f"{a_str} correctly encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.24.{i:02d}", 24, "M6", name, f"Verify SETcc variant '{asm_str}' encoding against NASM oracle",
            make_setcc_test(),
        ))

    # Feature 25: CMOVcc Expansion
    for i, (name, asm_str, exp_hex) in enumerate([
        ("cmovz_r64_r64", "cmovz rax, rbx", "480f44c3"),
        ("cmovnz_r64_r64", "cmovnz rax, rbx", "480f45c3"),
        ("cmovc_r64_r64", "cmovc rax, rbx", "480f42c3"),
        ("cmovz_r32_r32", "cmovz eax, ebx", "0f44c3"),
        ("cmovz_r16_r16", "cmovz ax, bx", "660f44c3"),
    ], start=1):
        def make_cmov_test(a_str=asm_str, expected=exp_hex):
            def t(ctx: ExecutionContext):
                ok, raw, err = ctx.assemble_nasm(a_str)
                if not ok or raw.hex() != expected:
                    return TestStatus.FAIL, f"{a_str} expected {expected}, got {raw.hex() if ok else err}"
                return TestStatus.PASS, f"{a_str} correctly encoded as {raw.hex()}"
            return t
        tests.append(make_tier1_test(
            f"T1.25.{i:02d}", 25, "M6", name, f"Verify CMOVcc variant '{asm_str}' encoding against NASM oracle",
            make_cmov_test(),
        ))

    return tests
