"""Executable reference writers for the original Part II two-phase W_M.

These functions mirror the canonical encodings in TwoPhaseUniform.lean:
    originalWindowCode p x = latCode 1 (p(|x|)+1) (window (p(|x|))
    originalInputCode M p x = cfgCode (stateBits M) ... (encM M ... x)

In one dimension the lattice bitmap has the exact, constructive closed form
    0 ++ 1^(2L+1) ++ 0       where L = p(|x|).
The prefix is 1^(L+1) ++ 0, so the complete window code has 3L+5 bits.

The initial configuration has 2L+1 encoded cells, ordered left to right,
with a head at the origin and input symbols at 0..|x|-1. `state_bits` is
supplied by the caller and must match the fixed finite-alphabet code chosen
for its MTM. The default representation is intentionally not guessed.

These algorithms are deterministic and require O(poly(|x|)) output work
for each fixed natural-coefficient polynomial and fixed finite machine.
They are EXECUTABLE TEST VECTORS, not a Lean proof of the MTM.ComputesIn
witnesses required for II-10. Do not promote the manuscript claim on
the strength of these functions or their tests.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Hashable, Sequence


@dataclass(frozen=True)
class InitialCell:
    symbol: Hashable
    head_state: Hashable | None
    phase: bool = False


def polynomial_value(coefficients: Sequence[int], n: int) -> int:
    """Evaluate a natural-coefficient polynomial in ascending degree order."""
    if n < 0 or any(c < 0 for c in coefficients):
        raise ValueError("input length and coefficients must be natural numbers")
    value = 0
    for coefficient in reversed(coefficients):
        value = value * n + coefficient
    return value


def original_window_bits(x: Sequence[bool], coefficients: Sequence[int]) -> list[bool]:
    """Canonical latCode with unary radius, separator, and full membership bitmap."""
    L = polynomial_value(coefficients, len(x))
    R = L + 1
    return [True] * R + [False, False] + [True] * (2 * L + 1) + [False]


def enumerated_window_bits(x: Sequence[bool], coefficients: Sequence[int]) -> list[bool]:
    """Independent literal enumeration of Lean's 1D latCode specification."""
    L = polynomial_value(coefficients, len(x))
    R = L + 1
    return [True] * R + [False] + [abs(i) <= L for i in range(-R, R + 1)]


def original_initial_cell(
    x: Sequence[bool],
    i: int,
    *,
    blank: Hashable,
    symbol_of_bit: Callable[[bool], Hashable],
    initial_state: Hashable,
) -> InitialCell:
    """The original encCfg at site i (inside the chosen finite window)."""
    symbol = symbol_of_bit(x[i]) if 0 <= i < len(x) else blank
    head = initial_state if i == 0 else None
    return InitialCell(symbol, head, False)


def original_encoder_bits(
    x: Sequence[bool],
    coefficients: Sequence[int],
    *,
    blank: Hashable,
    symbol_of_bit: Callable[[bool], Hashable],
    initial_state: Hashable,
    state_bits: Callable[[InitialCell], Sequence[bool]],
) -> list[bool]:
    """Bit-output encoder for the original two-phase initial configuration."""
    L = polynomial_value(coefficients, len(x))
    result: list[bool] = []
    width: int | None = None
    for i in range(-L, L + 1):
        cell_code = list(state_bits(original_initial_cell(
            x, i, blank=blank, symbol_of_bit=symbol_of_bit, initial_state=initial_state
        )))
        if width is None:
            width = len(cell_code)
        elif len(cell_code) != width:
            raise ValueError("state_bits must be fixed-width")
        if any(type(bit) is not bool for bit in cell_code):
            raise TypeError("state_bits must produce Boolean bits")
        result.extend(cell_code)
    return result


def enumerated_encoder_bits(
    x: Sequence[bool],
    coefficients: Sequence[int],
    *,
    blank: Hashable,
    symbol_of_bit: Callable[[bool], Hashable],
    initial_state: Hashable,
    state_bits: Callable[[InitialCell], Sequence[bool]],
) -> list[bool]:
    """Literal 1D boxIdx/filter/flatMap reference for the cfgCode definition."""
    L = polynomial_value(coefficients, len(x))
    R = L + 1
    return [
        bit
        for i in range(-R, R + 1)
        if -L <= i <= L
        for bit in state_bits(original_initial_cell(
            x, i, blank=blank, symbol_of_bit=symbol_of_bit, initial_state=initial_state
        ))
    ]
