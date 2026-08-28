# Test Infrastructure Specification: AArch64 QEMU Support in gasm

## 1. Overview & Architectural Principles

This document specifies the end-to-end (E2E), opaque-box, requirement-driven test infrastructure for the AArch64 QEMU Support implementation in `gasm`. The test infrastructure is designed to validate all 28 features across Milestones M1 through M7 as specified in `PROJECT.md` and derived authoritatively from `ORIGINAL_REQUEST.md`.

### Core Architectural Principles

1. **Opaque-Box, Requirement-Driven Verification**:
   Tests observe the system strictly through its external, specified surfaces: file formats, exit codes, stdout/stderr streams, ELF binary structures, JSON schemas, and command-line interfaces. Internal Lean definitions are validated through mechanical gates (`lake build`, `lake exe ...`, `python scripts/...`) rather than white-box mock substitutions.

2. **Distinct Exit Code Semantics (Fail-Honest Contract)**:
   In alignment with `docs/SPIKES.md` §4 item 5, `docs/TARGETS/ARM64.md`, and `scripts/run_gates.py`, the test runner and all harnesses enforce strict, non-conflated exit codes:
   - **Exit 0 (`PASS`)**: All executed tests passed completely.
   - **Exit 1 (`FAIL`)**: One or more tests failed verification, or encountered an unhandled error.
   - **Exit 2 (`SKIP`)**: Tests were skipped due to an absent external host runner or oracle (e.g. `qemu-system-aarch64` or `qemu-aarch64`), and all other executed tests passed. A missing oracle never silently passes as exit 0.

3. **Systematic 4-Tier Test Methodology**:
   - **Tier 1: Feature Coverage**: At least 5 explicit test cases for every feature in the `PROJECT.md` Feature Inventory (28 features × 5 = 140 tests).
   - **Tier 2: Boundary & Corner Cases**: At least 5 test cases per feature targeting empty, max, zero, overflow, domain extremes, malformed inputs, and state boundaries (28 features × 5 = 140 tests).
   - **Tier 3: Cross-Feature Combinations**: Pairwise and multi-module interaction tests exercising architectural boundaries between milestones (25 tests).
   - **Tier 4: Real-World Application Scenarios**: Full lifecycle user workloads and application scenarios simulating real-world execution environments (12 tests).
   - **Total Test Suite Inventory**: 317 test cases.

4. **Progressive Testability**:
   Tests are tagged by Milestone (`M1` through `M7`) and Feature ID (`1` through `28`). Milestone track leads can execute only the relevant subset of tests during development (e.g. `python tests/e2e/runner.py --milestone M1`), ensuring immediate and independent verifiability.

---

## 2. Test Runner & Harness Architecture (`tests/e2e/`)

The test harness and test runner are implemented in Python 3 under `tests/e2e/`, providing portable, direct subprocess invocation without shell pipelines (avoiding exit code masking).

### Directory Layout

```
tests/e2e/
├── harness.py                        # Core execution context, tool detector, ELF validator
├── runner.py                         # CLI test runner entry point (exit codes 0, 1, 2)
└── cases/
    ├── __init__.py                   # Cases package
    ├── tier1_feature_coverage.py     # Tier 1: 140 tests (Features 1–28)
    ├── tier2_boundary_corner.py      # Tier 2: 140 boundary tests (Features 1–28)
    ├── tier3_cross_feature.py        # Tier 3: 25 cross-feature tests
    └── tier4_real_world.py           # Tier 4: 12 real-world application scenarios
```

### Execution Context & Tool Detection (`tests/e2e/harness.py`)

The `ExecutionContext` manages external tooling resolution, respecting environment variable overrides before PATH and standard system directories:
- **Bare Metal QEMU**: `GASM_QEMU_AARCH64` override -> `PATH` (`qemu-system-aarch64`) -> `C:\Program Files\qemu\qemu-system-aarch64.exe` -> `/usr/bin/qemu-system-aarch64`.
- **Linux User QEMU**: `GASM_QEMU_USER_AARCH64` override -> `PATH` (`qemu-aarch64`, `qemu-aarch64-static`) -> `/usr/bin/qemu-aarch64`.
- **Differential Assembler**: `GASM_LLVM_MC` override -> `PATH` (`llvm-mc-19`, `llvm-mc`).
- **Lean Toolchain**: `lake` and `lean` resolved via PATH.

### AArch64 ELF64 Binary Validation

The test harness includes an embedded, pure Python ELF64 validator verifying:
- Magic: `\x7fELF`
- Class: `ELFCLASS64` (`2`)
- Data: `ELFDATA2LSB` (`1`, 2's complement little-endian)
- Version: `EV_CURRENT` (`1`)
- Machine: `EM_AARCH64` (`183` / `0x00B7`)
- Type: `ET_EXEC` (`2`)
- Entry point address: Non-zero physical/virtual load target (`0x40000000` for Bare Metal, `0x400078` for Linux).

---

## 3. Test Runner CLI Specification (`tests/e2e/runner.py`)

### Invocation Commands

```bash
# Run the complete test suite across all 4 tiers (317 tests)
python3 tests/e2e/runner.py

# Filter by tier (1, 2, 3, or 4)
python3 tests/e2e/runner.py --tier 1
python3 tests/e2e/runner.py --tier 2
python3 tests/e2e/runner.py --tier 3
python3 tests/e2e/runner.py --tier 4

# Filter by milestone (progressive testability)
python3 tests/e2e/runner.py --milestone M1
python3 tests/e2e/runner.py --milestone M2
python3 tests/e2e/runner.py --milestone M3
python3 tests/e2e/runner.py --milestone M4
python3 tests/e2e/runner.py --milestone M5
python3 tests/e2e/runner.py --milestone M6
python3 tests/e2e/runner.py --milestone M7

# Filter by feature ID (1 through 28)
python3 tests/e2e/runner.py --feature 1
python3 tests/e2e/runner.py --feature 14

# Run a specific test case by ID
python3 tests/e2e/runner.py --test T1.01.01
python3 tests/e2e/runner.py --test T4.01

# List all test cases without running
python3 tests/e2e/runner.py --list

# Machine-parseable JSON summary
python3 tests/e2e/runner.py --json

# Fail immediately on first failure
python3 tests/e2e/runner.py --fail-fast
```

---

## 4. Feature Coverage Matrix (Tiers 1 & 2)

| # | Feature Name | Milestone | Tier 1 Test IDs (Happy Path & Contracts) | Tier 2 Test IDs (Boundary & Extremes) |
|---|--------------|-----------|------------------------------------------|---------------------------------------|
| 1 | Reference Registration | M1 | `T1.01.01` – `T1.01.05` | `T2.01.01` – `T2.01.05` |
| 2 | License Token | M1 | `T1.02.01` – `T1.02.05` | `T2.02.01` – `T2.02.05` |
| 3 | Target Spec Docs | M1 | `T1.03.01` – `T1.03.05` | `T2.03.01` – `T2.03.05` |
| 4 | Citation Discipline | M1 | `T1.04.01` – `T1.04.05` | `T2.04.01` – `T2.04.05` |
| 5 | Registers & State | M2 | `T1.05.01` – `T1.05.05` | `T2.05.01` – `T2.05.05` |
| 6 | Addressing Modes | M2 | `T1.06.01` – `T1.06.05` | `T2.06.01` – `T2.06.05` |
| 7 | Machine Semantics | M2 | `T1.07.01` – `T1.07.05` | `T2.07.01` – `T2.07.05` |
| 8 | Instruction Surface | M3 | `T1.08.01` – `T1.08.05` | `T2.08.01` – `T2.08.05` |
| 9 | 32-bit Codec | M3 | `T1.09.01` – `T1.09.05` | `T2.09.01` – `T2.09.05` |
| 10 | Round-Trip Proofs | M3 | `T1.10.01` – `T1.10.05` | `T2.10.01` – `T2.10.05` |
| 11 | Registry Exhaustiveness | M3 | `T1.11.01` – `T1.11.05` | `T2.11.01` – `T2.11.05` |
| 12 | Performance Model | M3 | `T1.12.01` – `T1.12.05` | `T2.12.01` – `T2.12.05` |
| 13 | Obligation Enforcement | M3 | `T1.13.01` – `T1.13.05` | `T2.13.01` – `T2.13.05` |
| 14 | Bare Metal Target | M4 | `T1.14.01` – `T1.14.05` | `T2.14.01` – `T2.14.05` |
| 15 | Linux Target | M4 | `T1.15.01` – `T1.15.05` | `T2.15.01` – `T2.15.05` |
| 16 | QEMU Runners | M4 | `T1.16.01` – `T1.16.05` | `T2.16.01` – `T2.16.05` |
| 17 | Spike 1 Hello World | M5 | `T1.17.01` – `T1.17.05` | `T2.17.01` – `T2.17.05` |
| 18 | Spike 2 Fibonacci | M5 | `T1.18.01` – `T1.18.05` | `T2.18.01` – `T2.18.05` |
| 19 | Spike 3 Sort Lines | M5 | `T1.19.01` – `T1.19.05` | `T2.19.01` – `T2.19.05` |
| 20 | Spike 4 HTTP Server | M5 | `T1.20.01` – `T1.20.05` | `T2.20.01` – `T2.20.05` |
| 21 | Spike 5 GZIP | M5 | `T1.21.01` – `T1.21.05` | `T2.21.01` – `T2.21.05` |
| 22 | Encoding Fuzzing | M6 | `T1.22.01` – `T1.22.05` | `T2.22.01` – `T2.22.05` |
| 23 | Semantics Fuzzing | M6 | `T1.23.01` – `T1.23.05` | `T2.23.01` – `T2.23.05` |
| 24 | Stability Fuzzing | M6 | `T1.24.01` – `T1.24.05` | `T2.24.01` – `T2.24.05` |
| 25 | Lakefile Integration | M6 | `T1.25.01` – `T1.25.05` | `T2.25.01` – `T2.25.05` |
| 26 | CI Gate Integration | M6 | `T1.26.01` – `T1.26.05` | `T2.26.01` – `T2.26.05` |
| 27 | E2E Test Suite Pass | M7 | `T1.27.01` – `T1.27.05` | `T2.27.01` – `T2.27.05` |
| 28 | Adversarial Hardening | M7 | `T1.28.01` – `T1.28.05` | `T2.28.01` – `T2.28.05` |

---

## 5. Cross-Feature Combinations Matrix (Tier 3)

| Test ID | Interaction | Scope | Verified Interaction Invariant |
|---------|-------------|-------|--------------------------------|
| `T3.01` | F1 × F2 | M1 | ARM reference registered in `references.json` with `arm-unmodified-only` license. |
| `T3.02` | F3 × F4 | M1 | `docs/TARGETS/ARM64.md` headings provide valid targets for all Lean `REF:` citations. |
| `T3.03` | F3 × F5 | M2 | Register architecture anchors in `ARM64.md` align with `Registers.lean` declarations. |
| `T3.04` | F5 × F6 | M2 | `AArch64AddrMode` evaluation function resolves addressing modes against register state. |
| `T3.05` | F6 × F8 | M3 | Load/store instruction families compose correctly with addressing mode offsets. |
| `T3.06` | F7 × F9 | M3 | Machine step semantics execute decoded instruction AST preserving architectural state. |
| `T3.07` | F8 × F9 | M3 | All 15 instruction families encode to 32-bit words and decode cleanly. |
| `T3.08` | F9 × F10 | M3 | Codec round-trip theorem `decode (encode i) = i` holds across all instruction families. |
| `T3.09` | F10 × F11 | M3 | Instruction registry exhaustive audit verifies all round-trip shards participate in gate. |
| `T3.10` | F8 × F12 | M3 | Every instruction family maps to micro-op sequence in Cortex-A53 performance model. |
| `T3.11` | F12 × F13 | M3 | `CheckAArch64Obligations` verifies honest validation oracle and cost provenance. |
| `T3.12` | F9 × F14 | M4 | Bare Metal ELF emitter encodes instructions directly into flat ELF text segment. |
| `T3.13` | F9 × F15 | M4 | Linux ELF emitter encodes `SVC #0` and argument setup instructions into static ELF. |
| `T3.14` | F14 × F16 | M4 | `QEMUAArch64` system runner boots Bare Metal ELF on QEMU `virt` platform. |
| `T3.15` | F15 × F16 | M4 | `QEMUAArch64` user runner executes Linux ELF binary under QEMU user-mode. |
| `T3.16` | F14 × F17 | M5 | Spike 1 Bare Metal writes Hello World to PL011 UART and exits via semihosting. |
| `T3.17` | F15 × F17 | M5 | Spike 1 Linux executable executes cleanly, invoking `sys_write` and `sys_exit`. |
| `T3.18` | F5 × F18 | M5 | Fibonacci calculation registers and `UDIV`/`MSUB` match specification trace. |
| `T3.19` | F15 × F19 | M5 | SmolAlloc dynamic heap and quicksort sort multi-line input on Linux. |
| `T3.20` | F15 × F20 | M5 | Linux socket syscalls and linear handle model parse and respond to HTTP requests. |
| `T3.21` | F15 × F21 | M5 | DEFLATE compression, CRC-32 checksum, and RFC 1952 packaging round-trip on Linux. |
| `T3.22` | F9 × F22 | M6 | Differential encoding fuzzer verifies Lean binary encoder against `llvm-mc-19`. |
| `T3.23` | F7 × F23 | M6 | Semantics fuzzer executes differential tests against QEMU execution traces. |
| `T3.24` | F9 × F24 | M6 | Stability fuzzer mutates instruction words and verifies decoder crash-freedom. |
| `T3.25` | F26 × F27 | M7 | CI gate runner `scripts/run_gates.py` integrates automated E2E test runner. |

---

## 6. Real-World Application Scenarios (Tier 4)

| Test ID | Scenario Name | Milestone | Description & Acceptance Invariant |
|---------|---------------|-----------|-------------------------------------|
| `T4.01` | Bare Metal Boot to UART Console | M5 | Compile Bare Metal ELF, boot under QEMU `virt`, capture PL011 UART bytes, verify clean semihosting exit 0. |
| `T4.02` | Linux Syscall Execution Workflow | M5 | Compile static ELF64 executable, execute under `qemu-aarch64`, verify stdout output and process exit code 0. |
| `T4.03` | Fibonacci Pipeline to fib(93) | M5 | Compute Fibonacci numbers up to 64-bit non-overflow ceiling (fib(93)), format decimals via `UDIV`/`MSUB`, emit to stdout. |
| `T4.04` | In-Memory Line Sorter with SmolAlloc | M5 | Stream text lines from stdin into dynamically allocated heap buffers, sort with quicksort, emit ordered output. |
| `T4.05` | HTTP 1.1 Web Server Transactions | M5 | Launch HTTP server on localhost port, send concurrent `GET /`, `GET /status`, and invalid routes, verify response bodies. |
| `T4.06` | GZIP Compression/Decompression Cycle | M5 | Compress payload with DEFLATE/RFC 1951, decompress with GUNZIP, assert 100% bit-for-bit payload recovery. |
| `T4.07` | Clean Workspace CI Gate Execution | M6 | Run `python scripts/run_gates.py --quick`, verify all fast mechanical gates pass and exit code 2 (PASSED_PARTIAL). |
| `T4.08` | Differential Assembly with LLVM-MC | M6 | Assemble batches of AArch64 instructions using Lean encoder and `llvm-mc-19`, assert exact byte equivalence. |
| `T4.09` | Missing Oracle Fail-Honest Degradation | M4 | Simulate absent QEMU runner, assert runner reports exit code 2 (skip) rather than false pass or crash. |
| `T4.10` | Reference Registry Integrity Enforcement | M1 | Run `scripts/check_references.py` and `scripts/check_refs.py`, ensuring all references and anchors resolve. |
| `T4.11` | Zero-Uncited Declaration Audit | M1 | Run `lake exe check_refs_coverage`, ensuring 100% citation coverage across compiled environment declarations. |
| `T4.12` | Law 10 Soundness Axiom Audit | M6 | Run `lake exe check_gates_axioms`, ensuring zero `sorry` and zero unapproved axioms across all target modules. |

---

## 7. Authoritative Output Derivation Sources

Every test case derives its expected outputs from authoritative sources:
1. **Hardware & ISA Specifications**:
   - Arm Architecture Reference Manual (Armv8-A / Armv9-A, ARM DDI 0487)
   - PrimeCell UART (PL011) Technical Reference Manual (ARM DDI 0183)
   - Semihosting for AArch32 and AArch64 (ARM DUI 0058 / DUI 0471)
   - Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64, ARM IHI 0055)
2. **Operating System ABI Specifications**:
   - Linux System Call ABI for AArch64 (`man 2 syscall`, asm-generic syscall mapping table)
   - System V ABI for AArch64 (ELF64 object file format specification)
3. **Repository Design Documents**:
   - `docs/REVIEW.md` (Laws 1–14)
   - `docs/TARGETS/ARM64.md` (AArch64 architectural specification)
   - `references.json` (authoritative external reference pins)
4. **Hardware & Emulation Oracles**:
   - `llvm-mc-19` (authoritative binary encoding oracle)
   - `qemu-system-aarch64` (Cortex-A53 system execution oracle)
   - `qemu-aarch64` (Linux user-space execution oracle)

---

## 8. Integration with CI Gates (`scripts/run_gates.py`)

The E2E test runner is integrated into the mechanical gate table in `scripts/run_gates.py`:
- In `--quick` mode, fast Tier 1 and Tier 2 tests run to verify citation integrity, license compliance, and schema validity.
- In full gate mode, the complete suite across all 4 tiers executes, requiring `qemu_system_aarch64`, `qemu_aarch64`, and `llvm_mc` prerequisites.
- If an oracle is missing in a full run, `run_gates.py` halts before running gates (`ABORTED`, exit 3), preventing silent fail-open skips.
