"""Single-head, single-tape transducers for the two canonical W_M words.

Only transition(state, symbol) is called by the executor. The program (including
all literal code blocks) is fixed before the input is supplied. Input and output
use the same raw Boolean alphabet, with None as the blank, as in Part II.
"""
from dataclasses import dataclass, replace
from typing import Hashable, NamedTuple, Sequence

from .two_phase_state_serializer import TwoPhaseState, initial_state, state_bits


@dataclass(frozen=True)
class Cell:
    inp: bool | None = None
    acc: bool = False
    dest: bool = False
    outer: bool = False
    inner: bool = False
    out: bool | None = None


LEFT = "left-end"
BLANK = None
HALT = ("halt",)
START = ("start",)


class Instruction(NamedTuple):
    op: str
    args: tuple
    targets: tuple[int, ...]


@dataclass(frozen=True)
class Writer:
    instructions: tuple[Instruction, ...]
    entry: int
    coefficients: tuple[int, ...]
    width: int

    def transition(self, state: tuple, symbol) -> tuple[tuple, object, int]:
        """A single total finite-control transition on the known alphabet."""
        tag = state[0]
        if tag == "start":
            return ("mark",), symbol, -1
        if tag == "mark":
            return ("normalize",), LEFT, 1
        if tag == "normalize":
            if isinstance(symbol, bool):
                return state, Cell(inp=symbol), 1
            return ("return", self.entry), symbol, -1
        if tag == "return":
            if symbol == LEFT:
                return ("scan", state[1]), symbol, 1
            return state, symbol, -1
        if tag == "halt":
            return state, symbol, 1

        label = state[1]
        op, args, targets = self.instructions[label]
        if tag == "neighbor" or op == "head":
            data = symbol.inp if isinstance(symbol, Cell) else None
            branch = 0 if data is None else 1 + int(data)
            return ("return", targets[branch]), symbol, -1

        # All entries to a scan are at the origin. During normalized scans
        # only work cells followed by blank are reachable.
        cell = symbol if isinstance(symbol, Cell) else Cell()
        end = not isinstance(symbol, Cell)
        if op == "finish":
            if cell.out is None:
                return HALT, BLANK, 1
            return state, cell.out, 1
        if op == "copy":
            if end:
                return ("return", targets[0]), symbol, -1
            src, dst = args
            bit = cell.inp is not None if src == "input" else False if src == "zero" else getattr(cell, src)
            return state, replace(cell, **{dst: bit}), 1
        if op in ("take", "next_input"):
            if end:
                return ("return", targets[-1]), symbol, -1
            track = args[0]
            if getattr(cell, track):
                updated = replace(cell, **{track: False})
                if op == "next_input":
                    return ("neighbor", label), updated, 1
                return ("return", targets[0]), updated, -1
            return state, cell, 1
        if op == "inc":
            if not cell.dest:
                return ("return", targets[0]), replace(cell, dest=True), -1
            return state, cell, 1
        if op == "emit":
            if cell.out is None:
                return ("return", targets[0]), replace(cell, out=args[0]), -1
            return state, cell, 1
        raise ValueError(f"Invalid program instruction {op!r}")

    def step_bound(self, n: int) -> int:
        """Uniform (loose) bound, with constants fixed at machine construction."""
        d = len(self.coefficients)
        a = 1 + sum(self.coefficients)
        radius_bound = a * (n + 1) ** d
        span = n + radius_bound + (self.width + 3) * (2 * radius_bound + 3) + 8
        sweeps = (d + 4) * (12 + 8 * self.width) * (radius_bound + 1) + a + 10
        return (sweeps + 4) * (2 * span + 6)


class _Code:
    def __init__(self):
        self.ins = []

    def add(self, op, args, *targets):
        self.ins.append(Instruction(op, tuple(args), tuple(targets)))
        return len(self.ins) - 1

    def word(self, bits, end):
        for bit in reversed(bits):
            end = self.add("emit", [bit], end)
        return end

    def repeated(self, bits, end):
        take = self.add("take", ["outer"])
        yes = self.word(bits, take)
        self.ins[take] = Instruction("take", ("outer",), (yes, end))
        return self.add("copy", ["acc", "outer"], take)

    def horner(self, coefficient, end):
        # a <- a*n + c. Each loop consumes one previously copied mark.
        end = self.add("copy", ["dest", "acc"], end)
        for _ in range(coefficient):
            end = self.add("inc", [], end)
        outer = self.add("take", ["outer"])
        inner = self.add("take", ["inner"])
        inc = self.add("inc", [], inner)
        self.ins[inner] = Instruction("take", ("inner",), (inc, outer))
        enter = self.add("copy", ["input", "inner"], inner)
        self.ins[outer] = Instruction("take", ("outer",), (enter, end))
        return self.add("copy", ["acc", "outer"], self.add("copy", ["zero", "dest"], outer))


def _assemble(code, start, coefficients, width):
    coefficients = tuple(coefficients)
    if any(type(c) is not int or c < 0 for c in coefficients):
        raise ValueError("Expected coefficients of a natural polynomial")
    # Prepending a stage puts the highest coefficient first at execution.
    for c in coefficients:
        start = code.horner(c, start)
    return Writer(tuple(code.ins), start, coefficients, width)


def window_writer(coefficients: Sequence[int]) -> Writer:
    code = _Code()
    end = code.add("finish", [])
    end = code.word([True, False], end)
    end = code.repeated([True, True], end)
    end = code.word([True, False, False], end)
    return _assemble(code, code.repeated([True], end), coefficients, 1)


def input_writer(coefficients: Sequence[int], alphabet: Sequence[TwoPhaseState], *,
                 blank: Hashable, zero: Hashable, one: Hashable, start: Hashable,
                 accept: Hashable, reject: Hashable) -> Writer:
    """The supplied state enumeration must be the fixed Lean stateBits order."""
    code = _Code()
    end = code.add("finish", [])
    def block(symbol, head):
        return state_bits(initial_state(symbol, head), alphabet, accept, reject)
    right = code.add("next_input", ["outer"])
    choices = tuple(code.word(block(g, None), right) for g in (blank, zero, one))
    code.ins[right] = Instruction("next_input", ("outer",), (*choices, end))
    end = code.add("copy", ["acc", "outer"], right)
    heads = tuple(code.word(block(g, start), end) for g in (blank, zero, one))
    end = code.add("head", [], *heads)
    end = code.repeated(block(blank, None), end)
    return _assemble(code, end, coefficients, len(block(blank, None)))


def execute(machine: Writer, x: Sequence[bool]) -> tuple[list[bool], int]:
    """Literal interpreter. It counts each transition, including normalization."""
    tape = dict(enumerate(x))
    head, state, steps = 0, START, 0
    bound = machine.step_bound(len(x))
    while state != HALT:
        if steps >= bound:
            raise RuntimeError("Polynomial transition bound exceeded")
        state, symbol, direction = machine.transition(state, tape.get(head))
        tape[head] = symbol
        head += direction
        steps += 1
    word = []
    while type(tape.get(len(word))) is bool:
        word.append(tape[len(word)])
    if tape.get(len(word)) is not BLANK:
        raise ValueError("Missing blank after output")
    return word, steps
