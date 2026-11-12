"""Structural certificate checks for the original II-10 finite-control writers.

This module checks emitted program structure and observed finite executions.
It is NOT a proof of MTM.Outputs for every input and polynomial, nor a
proof that the Lean assembler matches the Python assembler on all programs.
"""
from dataclasses import dataclass
from typing import Sequence

from pvnp.two_phase_tape_writer import Writer, execute


ARITY = {
    "finish": 0,
    "copy": 1,
    "take": 2,
    "next_input": 4,
    "head": 3,
    "inc": 1,
    "emit": 1,
}


@dataclass(frozen=True)
class ControlCertificate:
    instruction_count: int
    entry: int
    branch_edges: int
    unreachable_instructions: tuple[int, ...]
    coefficients: tuple[int, ...]
    input_width: int


def certify_control(writer: Writer) -> ControlCertificate:
    """Reject out-of-bounds branches, malformed arities and dangling entry."""
    program = writer.instructions
    count = len(program)
    if not count or not 0 <= writer.entry < count:
        raise ValueError("Invalid program entry")
    if writer.width < 0 or any(c < 0 for c in writer.coefficients):
        raise ValueError("Invalid fixed machine parameters")
    edges = 0
    for address, instruction in enumerate(program):
        required = ARITY.get(instruction.op)
        if required is None or len(instruction.targets) != required:
            raise ValueError(f"Invalid instruction form at {address}: {instruction}")
        for next_address in instruction.targets:
            if not isinstance(next_address, int) or not 0 <= next_address < count:
                raise ValueError(f"Dangling branch at {address}: {next_address}")
        edges += len(instruction.targets)
    seen, pending = set(), [writer.entry]
    while pending:
        pc = pending.pop()
        if pc not in seen:
            seen.add(pc)
            pending.extend(program[pc].targets)
    return ControlCertificate(
        instruction_count=count,
        entry=writer.entry,
        branch_edges=edges,
        unreachable_instructions=tuple(sorted(set(range(count)) - seen)),
        coefficients=tuple(writer.coefficients),
        input_width=writer.width,
    )


@dataclass(frozen=True)
class ExecutionCertificate:
    input_length: int
    output_length: int
    actual_steps: int
    stated_step_bound: int
    control: ControlCertificate


def certify_execution(writer: Writer, input_bits: Sequence[bool],
                      expected_output: Sequence[bool]) -> ExecutionCertificate:
    """Check first halt, exact word, trailing blank and declared step budget
    through the original interpreter. These remain bounded tests."""
    control = certify_control(writer)
    if any(type(b) is not bool for b in input_bits):
        raise ValueError("Input must be Boolean")
    word, steps = execute(writer, input_bits)
    if list(word) != list(expected_output):
        raise AssertionError("Original finite-control writer output disagrees with specification")
    bound = writer.step_bound(len(input_bits))
    if not 0 < steps <= bound:
        raise AssertionError("Original writer exceeded its declared polynomial step budget")
    return ExecutionCertificate(
        input_length=len(input_bits),
        output_length=len(word),
        actual_steps=steps,
        stated_step_bound=bound,
        control=control,
    )
