"""Trace-level invariant audit for the original two-phase single-tape writers.

Uses the *actual* `Writer.transition` function, not a second simulator
implementation. Tests are necessarily finite; a successful trace is NOT
a proof of the universally quantified Lean `MTM.Outputs` theorem.
"""
from dataclasses import dataclass
from typing import Sequence

from pvnp.two_phase_tape_writer import (
    BLANK, HALT, LEFT, START, Cell, Writer,
)
from pvnp.phase_xvi.writer_certificate import certify_control


@dataclass(frozen=True)
class TraceCertificate:
    steps: int
    step_bound: int
    min_head: int
    max_head: int
    instruction_counts: tuple[tuple[str, int], ...]
    return_to_left_end_count: int
    output_length: int


def audit_trace(writer: Writer, input_bits: Sequence[bool],
                expected_output: Sequence[bool]) -> TraceCertificate:
    """Verify concrete trace invariants and the exact canonical output word.

    The input `Writer` has fixed instructions and finite-control branches.
    The trace is charged one transition at a time.  A single failure raises
    AssertionError with the corresponding proof-obligation name.
    """
    cert = certify_control(writer)
    x = tuple(input_bits)
    if any(type(b) is not bool for b in x):
        raise ValueError("Non-Boolean input")
    if any(type(b) is not bool for b in expected_output):
        raise ValueError("Non-Boolean output specification")
    tape = dict(enumerate(x))
    state, head = START, 0
    visited_min = visited_max = 0
    counts: dict[str, int] = {}
    sentinels = 0
    steps = 0
    bound = writer.step_bound(len(x))
    while state != HALT:
        if steps >= bound:
            raise AssertionError("II-10 runtime bound exceeded")
        tag = state[0]
        counts[tag] = counts.get(tag, 0) + 1
        if tag in ("scan", "return", "neighbor"):
            pc = state[1]
            if not (isinstance(pc, int) and 0 <= pc < cert.instruction_count):
                raise AssertionError(f"Invalid finite-control address: {state!r}")
        if tag == "scan" and head < 0:
            raise AssertionError("Forward scan entered negative tape cell")
        if tag == "neighbor" and head <= 0:
            raise AssertionError("Neighbor probe not to the right of the origin")
        if tag == "return" and head < -1:
            raise AssertionError("Return scan crossed the left-end sentinel")
        if steps >= 2 and tape.get(-1) != LEFT:
            raise AssertionError("Left-end sentinel was overwritten or erased")
        if tag == "return" and tape.get(head) == LEFT:
            sentinels += 1
        old = tape.get(head, BLANK)
        nxt, written, direction = writer.transition(state, old)
        if direction not in (-1, 1):
            raise AssertionError("Machine transition is not a legal L/R move")
        if state == HALT:
            raise AssertionError("Unreachable halted state evaluated")
        tape[head] = written
        head += direction
        visited_min = min(visited_min, head)
        visited_max = max(visited_max, head)
        state = nxt
        steps += 1
    output = []
    i = 0
    while type(tape.get(i)) is bool:
        output.append(tape[i])
        i += 1
        if i > len(expected_output):
            raise AssertionError("Output longer than specification")
    if output != list(expected_output):
        raise AssertionError(f"Output mismatch after first halt: {output!r}")
    if tape.get(len(expected_output)) is not BLANK:
        raise AssertionError("No blank immediately after output")
    if tape.get(-1) != LEFT:
        raise AssertionError("Missing final left-end marker")
    if not 0 < steps <= bound:
        raise AssertionError("Invalid first-halt transition count")
    if visited_min < -1:
        raise AssertionError("Visited outside expected left boundary")
    if counts.get("mark", 0) != 1:
        raise AssertionError("Left-end marker initialization not exactly once")
    if counts.get("normalize", 0) != len(x) + 1:
        raise AssertionError("Input-normalization scan did not cover all input bits")
    if sentinels == 0:
        raise AssertionError("Finite-control writer never returned to left-end")
    return TraceCertificate(steps, bound, visited_min, visited_max,
                            tuple(sorted(counts.items())), sentinels, len(output))
