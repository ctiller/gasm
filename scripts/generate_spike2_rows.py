#!/usr/bin/env python3
"""Deterministically emit concrete Spike2 Linux row certificates.

The source templates remain proof terms; this tool only substitutes the row-local names,
predecessor checkpoint, and closed Fibonacci literals.  It deliberately refuses an unsupported
digit-length template instead of silently producing a mismatched certificate.
"""
from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ROWS = ROOT / "Spikes" / "Spike2Fibonacci" / "Linux"


def fibs() -> list[int]:
    values = [0, 1]
    for _ in range(2, 92):
        values.append(values[-1] + values[-2])
    return values


def render_two_digit(row: int, template: str) -> str:
    values = fibs()
    if len(str(values[row])) != 2:
        raise ValueError(f"row {row} has {len(str(values[row]))} digits; no matching template")
    template_path = ROWS / template
    if not template_path.is_file():
        raise ValueError(f"missing concrete row template: {template_path}")
    source = template_path.read_text(encoding="utf-8")
    source = source.replace("Row7", f"Row{row}")
    source = source.replace("row7", f"row{row}")
    source = source.replace("Row 7", f"Row {row}")
    source = source.replace("row seven", f"row {row}")
    source = source.replace("spike2Row6AfterRecurrence", f"spike2Row{row - 1}AfterRecurrence")
    source = source.replace("Linux.Row6", f"Linux.Row{row - 1}")
    source = source.replace("spike2_main_header_selected_prefix 6", f"spike2_main_header_selected_prefix {row - 1}")
    source = source.replace("gprs .r13 = 8", f"gprs .r13 = {row + 1}")
    source = source.replace("gprs .r14 = 21", f"gprs .r14 = {values[row + 1]}")
    source = source.replace("gprs .r15 = 34", f"gprs .r15 = {values[row + 2]}")
    return source


def self_test() -> None:
    rendered = render_two_digit(8, "Row7.lean")
    required = ("spike2Row7AfterRecurrence", "gprs .r14 = 34", "gprs .r15 = 55")
    if any(item not in rendered for item in required):
        raise SystemExit("Row7→Row8 recurrence substitution self-test failed")
    boundary = boundary_source(8)
    typed_header = (
        "import Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts",
        "private theorem spike2Row8BodyRip",
        "Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts.spike2Row7HeaderFacts",
        "theorem spike2Row8IndexHeaderLookupF : instructionAtRipIndexed spike2Indexed "
        "(spike2AfterMainHeader spike2Row7AfterRecurrence).rip = some "
        "(mov_rsp_byte 0x40 0x46) := by\n  rw [spike2Row8BodyRip]\n  rfl",
    )
    if any(item not in boundary for item in typed_header):
        raise SystemExit("Row8 typed header lookup self-test failed")
    if "spike2Row8IndexHeaderLookupF : instructionAtRipIndexed spike2Indexed " \
            "(spike2AfterMainHeader spike2Row7AfterRecurrence).rip = some " \
            "(mov_rsp_byte 0x40 0x46) := by rfl" in boundary:
        raise SystemExit("Row8 header lookup regressed to closed rfl reduction")
    try:
        render_two_digit(8, "MissingTemplate.lean")
    except ValueError:
        return
    raise SystemExit("missing-template self-test did not fail closed")


def boundary_source(row: int) -> str:
    """Keep closed checkpoint definitions in a private row-boundary namespace.

    A consumer can therefore import this lightweight data module without bringing the
    predecessor's certificate declarations into its namespace or forcing their proof terms.
    The separate connector is the only place that imports both a production row and its
    independently closed boundary spelling.
    """
    if row >= 8:
        # The data package must own every closed formatter state that a stage may start from;
        # retain definitions through recurrence, but cut before the first proof declaration.
        source = render_two_digit(row, "Row7.lean")
        marker = f"theorem spike2_row{row}_"
        source = source[:source.index(marker)]
        trailing_comment = source.rfind("\n/-")
        if trailing_comment != -1:
            source = source[:trailing_comment]
        source += "\nend Spikes.Spike2Fibonacci.Linux\n"
        # Every generated row consumes its predecessor's data-only namespace, including Row8.
        predecessor = f"Linux.Row{row - 1}BoundaryData"
        source = source.replace(f"Linux.Row{row - 1}", predecessor)
        if row == 8:
            source = source.replace(
                "import Spikes.Spike2Fibonacci.Linux.Row7BoundaryData",
                "import Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts",
            )
        source = source.replace("private theorem sequentialCmp", f"theorem spike2Row{row}SequentialCmp")
        source = source.replace("sequentialCmp", f"spike2Row{row}SequentialCmp")
    else:
        template = ROWS / f"Row{row}.lean"
        if not template.is_file():
            raise ValueError(f"missing boundary template: {template}")
        source = template.read_text(encoding="utf-8")
        marker = f"theorem spike2_row{row}_"
        if marker in source:
            source = source[:source.index(marker)]
            # The certificate's REF/doc block immediately precedes its theorem; retaining it would
            # leave an unterminated comment after the proof section is removed.
            trailing_comment = source.rfind("\n/-")
            if trailing_comment != -1:
                source = source[:trailing_comment]
            source += "\nend Spikes.Spike2Fibonacci.Linux\n"
        if row > 1:
            source = source.replace(f"Linux.Row{row - 1}", f"Linux.Row{row - 1}BoundaryData")
        source = source.replace("private theorem sequentialCmp", f"theorem spike2Row{row}SequentialCmp")
        source = source.replace("sequentialCmp", f"spike2Row{row}SequentialCmp")
    parent_namespace = "Spikes.Spike2Fibonacci.Linux"
    boundary_namespace = f"{parent_namespace}.Row{row}BoundaryData"
    source = source.replace(f"namespace {parent_namespace}", f"namespace {boundary_namespace}", 1)
    source = source.replace(f"end {parent_namespace}\n", f"end {boundary_namespace}\n")
    source = source.replace("private theorem sequentialDivR10", f"theorem spike2Row{row}SequentialDivR10")
    source = source.replace("sequentialDivR10", f"spike2Row{row}SequentialDivR10")
    if row > 1:
        imports_end = source.index("\n\n/-!")
        source = source[:imports_end] + (
            f"\n\nopen {parent_namespace}.Row{row - 1}BoundaryData"
        ) + source[imports_end:]
    if row >= 8:
        if row == 8:
            source = add_typed_header_lookup_sequence(source, row)
        else:
            source = add_lookup_sequence(source, row, "IndexHeader",
                "(spike2AfterMainHeader spike2Row7AfterRecurrence)", [
                    ("F", "mov_rsp_byte 0x40 0x46"), ("I", "mov_rsp_byte 0x41 0x69"),
                    ("B", "mov_rsp_byte 0x42 0x62"), ("Open", "mov_rsp_byte 0x43 0x28"),
                    ("Cmp", "cmp_r64_imm8 .r13 10"), ("Branch", "jge_rel8 41"),
                ])
        source = add_lookup_sequence(source, row, "Index", f"spike2Row{row}AfterIndexHeader", [
            ("Move", "mov_r64 .rax .r13"), ("Ascii", "add_r64_imm8 .rax 0x30"),
            ("Cursor", "lea_rsp .rdi 0x44"), ("Store", "mov_mem8 .rdi .rax"),
            ("Close", "mov_rsp_byte 0x45 0x29"), ("Space", "mov_rsp_byte 0x46 0x20"),
            ("Equals", "mov_rsp_byte 0x47 0x3d"), ("ValueSpace", "mov_rsp_byte 0x48 0x20"),
            ("ValueCursor", "lea_rsp .rdi 0x49"), ("Join", "jmp_rel8 65"),
        ])
        source = add_lookup_sequence(source, row, "ValueSetup", f"spike2Row{row}AfterIndex", [
            ("Move", "mov_r64 .rax .r14"), ("Base", "mov_r64_imm64 .r10 10"),
            ("Count", "xor_r32 .ecx .ecx"),
        ])
        source = add_extraction_observations(
            source, row, "ExtractionFirst", f"spike2Row{row}AfterValueSetup"
        )
        source = add_extraction_observations(
            source, row, "ExtractionSecond", f"spike2Row{row}AfterExtractionFirst"
        )
        source = add_write_observations(
            source, row, "WriteFirst", f"spike2Row{row}AfterExtraction"
        )
        source = add_write_observations(
            source, row, "WriteSecond", f"spike2Row{row}AfterWriteFirst"
        )
    return source


def add_lookup_sequence(source: str, row: int, prefix: str, state: str,
                        steps: list[tuple[str, str]]) -> str:
    """Export exact instruction-index observations for a producer-local straight-line slice."""
    end = f"end Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData\n"
    if not source.endswith(end):
        raise ValueError("boundary source lacks namespace terminator")
    at = state
    body: list[str] = []
    for name, instr in steps:
        body.append(
            f"theorem spike2Row{row}{prefix}Lookup{name} : instructionAtRipIndexed spike2Indexed "
            f"{at}.rip = some ({instr}) := by rfl\n"
        )
        at = f"(X86_64Instruction.step ({instr}) {at})"
    return source[:-len(end)] + "\n" + "".join(body) + end


def add_typed_header_lookup_sequence(source: str, row: int) -> str:
    """Emit Row 8's predecessor-interface lookup proofs without reducing Row 7."""
    if row != 8:
        raise ValueError("typed header lookup sequence is currently validated for Row8 only")
    end = f"end Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData\n"
    if not source.endswith(end):
        raise ValueError("boundary source lacks namespace terminator")
    body = '''private theorem spike2Row8BodyRip :
    (spike2AfterMainHeader spike2Row7AfterRecurrence).rip = 4198447 := by
  obtain ⟨rip, counter, _⟩ :=
    Spikes.Spike2Fibonacci.Linux.Row7BoundaryFacts.spike2Row7HeaderFacts
  exact spike2_after_main_header_body_rip 7 spike2Row7AfterRecurrence (by omega) rip counter

private theorem movRspByte40Rip (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) state).rip = state.rip + 5 := rfl

private theorem movRspByte41Rip (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) state).rip = state.rip + 5 := rfl

private theorem movRspByte42Rip (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) state).rip = state.rip + 5 := rfl

private theorem movRspByte43Rip (state : X86_64MachineState) :
    (X86_64Instruction.step (mov_rsp_byte 0x43 0x28) state).rip = state.rip + 5 := rfl

/- The lookup proofs intentionally rewrite through a typed RIP boundary before reducing the
   fixed final instruction index.  This prevents every lookup from replaying the closed Row 7
   execution merely to recover its entry address. -/
theorem spike2Row8IndexHeaderLookupF : instructionAtRipIndexed spike2Indexed (spike2AfterMainHeader spike2Row7AfterRecurrence).rip = some (mov_rsp_byte 0x40 0x46) := by
  rw [spike2Row8BodyRip]
  rfl
theorem spike2Row8IndexHeaderLookupI : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)).rip = some (mov_rsp_byte 0x41 0x69) := by
  rw [movRspByte40Rip, spike2Row8BodyRip]
  rfl
theorem spike2Row8IndexHeaderLookupB : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence))).rip = some (mov_rsp_byte 0x42 0x62) := by
  rw [movRspByte41Rip, movRspByte40Rip, spike2Row8BodyRip]
  rfl
theorem spike2Row8IndexHeaderLookupOpen : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)))).rip = some (mov_rsp_byte 0x43 0x28) := by
  rw [movRspByte42Rip, movRspByte41Rip, movRspByte40Rip, spike2Row8BodyRip]
  rfl
theorem spike2Row8IndexHeaderLookupCmp : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (mov_rsp_byte 0x43 0x28) (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence))))).rip = some (cmp_r64_imm8 .r13 10) := by
  rw [movRspByte43Rip, movRspByte42Rip, movRspByte41Rip, movRspByte40Rip, spike2Row8BodyRip]
  rfl
theorem spike2Row8IndexHeaderLookupBranch : instructionAtRipIndexed spike2Indexed (X86_64Instruction.step (cmp_r64_imm8 .r13 10) (X86_64Instruction.step (mov_rsp_byte 0x43 0x28) (X86_64Instruction.step (mov_rsp_byte 0x42 0x62) (X86_64Instruction.step (mov_rsp_byte 0x41 0x69) (X86_64Instruction.step (mov_rsp_byte 0x40 0x46) (spike2AfterMainHeader spike2Row7AfterRecurrence)))))).rip = some (jge_rel8 41) := by
  rw [show (X86_64Instruction.step (cmp_r64_imm8 .r13 10)
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row7AfterRecurrence)))))).rip =
      (X86_64Instruction.step (mov_rsp_byte 0x43 0x28)
        (X86_64Instruction.step (mov_rsp_byte 0x42 0x62)
          (X86_64Instruction.step (mov_rsp_byte 0x41 0x69)
            (X86_64Instruction.step (mov_rsp_byte 0x40 0x46)
              (spike2AfterMainHeader spike2Row7AfterRecurrence))))).rip + 4 by rfl,
    movRspByte43Rip, movRspByte42Rip, movRspByte41Rip, movRspByte40Rip, spike2Row8BodyRip]
  rfl
'''
    return source[:-len(end)] + "\n" + body + end


def add_extraction_observations(source: str, row: int, pass_name: str, state: str) -> str:
    end = f"end Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData\n"
    if not source.endswith(end):
        raise ValueError("boundary source lacks namespace terminator")
    prefix = f"spike2Row{row}{pass_name}"
    xor = f"(X86_64Instruction.step (xor_r32 .edx .edx) {state})"
    div = f"(X86_64Instruction.step (div_r64 .r10) {xor})"
    ascii = f"(X86_64Instruction.step (add_r64_imm8 .rdx 0x30) {div})"
    push = f"(X86_64Instruction.step (push_r64 .rdx) {ascii})"
    count = f"(X86_64Instruction.step (add_r64_imm8 .rcx 1) {push})"
    cmp = f"(X86_64Instruction.step (cmp_r64_imm8 .rax 0) {count})"
    steps = [
        ("Xor", state, "xor_r32 .edx .edx"),
        ("Div", xor, "div_r64 .r10"), ("Ascii", div, "add_r64_imm8 .rdx 0x30"),
        ("Push", ascii, "push_r64 .rdx"), ("Count", push, "add_r64_imm8 .rcx 1"),
        ("Cmp", count, "cmp_r64_imm8 .rax 0"), ("Branch", cmp, "jne_rel8 236"),
    ]
    body = "\n".join(
        f"/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/\n"
        f"theorem {prefix}Lookup{name} : instructionAtRipIndexed spike2Indexed {at}.rip = some ({instr}) := by rfl\n"
        for name, at, instr in steps
    )
    return source[:-len(end)] + "\n" + body + end


def add_write_observations(source: str, row: int, pass_name: str, state: str) -> str:
    """Export the five exact lookup facts for one concrete decimal-write pass."""
    end = f"end Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData\n"
    if not source.endswith(end):
        raise ValueError("boundary source lacks namespace terminator")
    prefix = f"spike2Row{row}{pass_name}"
    pop = f"(X86_64Instruction.step (pop_r64 .rdx) {state})"
    store = f"(X86_64Instruction.step (mov_mem8 .rdi .rdx) {pop})"
    cursor = f"(X86_64Instruction.step (add_r64_imm8 .rdi 1) {store})"
    decrement = f"(X86_64Instruction.step (sub_r64_imm8 .rcx 1) {cursor})"
    steps = [
        ("Pop", state, "pop_r64 .rdx"), ("Store", pop, "mov_mem8 .rdi .rdx"),
        ("Cursor", store, "add_r64_imm8 .rdi 1"),
        ("Decrement", cursor, "sub_r64_imm8 .rcx 1"), ("Branch", decrement, "jne_rel8 243"),
    ]
    body = "\n".join(
        f"/- REF: docs/MACRO_ASSEMBLER.md#decimal-extraction-and-write-passes -/\n"
        f"theorem {prefix}Lookup{name} : instructionAtRipIndexed spike2Indexed {at}.rip = some ({instr}) := by rfl\n"
        for name, at, instr in steps
    )
    return source[:-len(end)] + "\n" + body + end


def replace_lookup_rfl(stage: str, row: int) -> str:
    names = iter(("Xor", "Div", "Ascii", "Push", "Count", "Cmp", "Branch"))
    lines = stage.splitlines()
    for index, line in enumerate(lines[:-1]):
        if line.strip() == "· rfl" and lines[index + 1].strip() == "· decide":
            lines[index] = line.replace("rfl", f"exact spike2Row{row}ExtractionFirstLookup{next(names)}")
    return "\n".join(lines) + "\n"


def extraction_second_source(row: int, first_source: str) -> str:
    """Reuse the seven concrete instructions with the next closed loop state and JNE edge."""
    return (first_source
        .replace("ExtractionFirstLookup", "ExtractionSecondLookup")
        .replace("extraction_first_selected_prefix", "extraction_second_selected_prefix")
        .replace("AfterValueSetup", "AfterExtractionStart")
        .replace("AfterExtractionFirst", "AfterExtraction")
        .replace("AfterExtractionStart", "AfterExtractionFirst")
        .replace("conditionalTaken", "conditionalFallthrough"))


def leaf_header(row: int, local_cmp: bool = False) -> str:
    local_cmp_source = "" if not local_cmp else f'''private theorem spike2Row{row}SequentialCmp (dst : Reg64) (value : UInt8) :
    SequentialInstruction (cmp_r64_imm8 dst value) where
  encoding := .compareImm8 dst value
  safeFallthrough := by intro _ _; rfl

'''
    return f'''import Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData

namespace Spikes.Spike2Fibonacci.Linux

open Gasm.Core
open Gasm.Effects
open Gasm.Targets
open Gasm.Targets.Linux
open Gasm.Targets.X86_64
open Gasm.Targets.X86_64.Instructions
open Gasm.Targets.X86_64.MacroAssembler
open Spikes.Spike2Fibonacci
open Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

{local_cmp_source}'''


def row7_section(start: str, end: str) -> str:
    source = (ROWS / "Row7.lean").read_text(encoding="utf-8")
    return source[source.index(start):source.index(end)]


def write_first_source(row: int) -> str:
    body = row7_section(
        "theorem spike2_row7_write_first_selected_prefix", "theorem spike2_row7_write_second_selected_prefix"
    )
    body = body.replace("Row7", f"Row{row}").replace("row7", f"row{row}")
    return replace_write_lookup_rfl(
        leaf_header(row) + body + "end Spikes.Spike2Fibonacci.Linux\n", row, "WriteFirst"
    )


def extraction_first_source(row: int) -> str:
    """Render the first decimal extraction pass from the canonical Row 7 source."""
    body = row7_section(
        "theorem spike2_row7_extraction_first_selected_prefix",
        "theorem spike2_row7_extraction_second_selected_prefix",
    )
    body = (body.replace("Row7", f"Row{row}").replace("row7", f"row{row}")
        .replace("sequentialDivR10", f"spike2Row{row}SequentialDivR10")
        .replace("sequentialCmp", f"spike2Row{row}SequentialCmp"))
    return replace_lookup_rfl(
        leaf_header(row, local_cmp=True) + body + "\nend Spikes.Spike2Fibonacci.Linux\n", row
    )


def write_second_source(row: int, first_source: str) -> str:
    return (first_source
        .replace("WriteFirstLookup", "WriteSecondLookup")
        .replace("write_first_selected_prefix", "write_second_selected_prefix")
        .replace("AfterExtraction", "AfterWriteStart")
        .replace("AfterWriteFirst", "AfterWrite")
        .replace("AfterWriteStart", "AfterWriteFirst")
        .replace("conditionalTaken", "conditionalFallthrough"))


def replace_write_lookup_rfl(stage: str, row: int, pass_name: str) -> str:
    names = iter(("Pop", "Store", "Cursor", "Decrement", "Branch"))
    lines = stage.splitlines()
    for index, line in enumerate(lines[:-1]):
        if line.strip() == "· rfl" and lines[index + 1].strip() == "· decide":
            lines[index] = line.replace("rfl", f"exact spike2Row{row}{pass_name}Lookup{next(names)}")
    return "\n".join(lines) + "\n"


def write_boundary_chain(last_row: int, check: bool) -> None:
    for row in range(1, last_row + 1):
        target = ROWS / f"Row{row}BoundaryData.lean"
        rendered = boundary_source(row)
        if check:
            if not target.exists() or target.read_bytes() != rendered.encode("utf-8"):
                raise SystemExit(f"stale generated boundary data: {target}")
        else:
            target.write_text(rendered, encoding="utf-8", newline="\n")


def boundary_facts_source(row: int) -> str:
    """Emit the small, data-only loop-header interface for one closed row boundary."""
    values = fibs()
    predecessor_rsp = (
        "spike2AfterPrologue.rsp" if row == 1 else
        f"Spikes.Spike2Fibonacci.Linux.Row{row - 1}BoundaryData."
        f"spike2Row{row - 1}AfterRecurrence.rsp"
    )
    return f'''import Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData

/-!
# Row {row} data-only header boundary

This module imports checkpoint data only, never a `SelectedPrefix` certificate.  Its exact
physical header fields are the complete predecessor interface consumed by a later row stage.
-/

namespace Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryFacts

open Gasm.Targets.X86_64
open Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryData

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

/- REF: docs/EQUIVALENCE_PROOFS.md#1-mathematical-formulation-of-equivalence -/
/-- Exact post-recurrence facts for closed Row {row}. -/
theorem spike2Row{row}HeaderFacts :
    spike2Row{row}AfterRecurrence.rip = spike2MainLoopRip ∧
    spike2Row{row}AfterRecurrence.gprs .r13 = {row + 1} ∧
    spike2Row{row}AfterRecurrence.gprs .r14 = {values[row + 1]} ∧
    spike2Row{row}AfterRecurrence.gprs .r15 = {values[row + 2]} ∧
    spike2Row{row}AfterRecurrence.rsp = {predecessor_rsp} ∧
    spike2Row{row}AfterRecurrence.fault = none := by
  decide

end Spikes.Spike2Fibonacci.Linux.Row{row}BoundaryFacts
'''


def write_boundary_facts(last_row: int, check: bool) -> None:
    for row in range(1, last_row + 1):
        target = ROWS / f"Row{row}BoundaryFacts.lean"
        rendered = boundary_facts_source(row)
        if check:
            if not target.exists() or target.read_bytes() != rendered.encode("utf-8"):
                raise SystemExit(f"stale generated boundary facts: {target}")
        else:
            target.write_text(rendered, encoding="utf-8", newline="\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("row", type=int, nargs="*", help="Rows to emit (currently 8 only)")
    parser.add_argument("--check", action="store_true", help="Fail if output differs from regeneration")
    parser.add_argument("--self-test", action="store_true", help="Check recurrence substitution and fail-closed lookup")
    parser.add_argument("--boundary-through", type=int, help="Emit lightweight boundary data through this row")
    parser.add_argument("--facts-through", type=int, help="Emit data-only header facts through this row")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    if args.boundary_through:
        write_boundary_chain(args.boundary_through, args.check)
    if args.facts_through:
        write_boundary_facts(args.facts_through, args.check)
    for row in args.row:
        if row != 8:
            raise SystemExit("only Row8 is enabled until its focused Lean check validates the template")
        extraction_first = extraction_first_source(row)
        write_first = write_first_source(row)
        outputs = {
            ROWS / f"Row{row}ExtractionFirst.lean": extraction_first,
            ROWS / f"Row{row}ExtractionSecond.lean": extraction_second_source(row, extraction_first),
            ROWS / f"Row{row}WriteFirst.lean": write_first,
            ROWS / f"Row{row}WriteSecond.lean": write_second_source(row, write_first),
        }
        for target, rendered in outputs.items():
            if args.check:
                if not target.exists() or target.read_bytes() != rendered.encode("utf-8"):
                    raise SystemExit(f"stale generated certificate: {target}")
            else:
                target.write_text(rendered, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
