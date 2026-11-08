"""Executable representation of the original Part II stateBits M.

The finite order supplied by `alphabet` corresponds to the (fixed)
Fintype.equivFin enumeration of S M in the Lean specification. This
module does not infer Lean's implicit enumeration or prove an FP witness.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Hashable, Sequence


@dataclass(frozen=True)
class TwoPhaseState:
    symbol: Hashable
    head: tuple | None
    phase: bool


def enumerate_states(symbols: Sequence[Hashable], states: Sequence[Hashable]) -> tuple[TwoPhaseState, ...]:
    """One explicit finite order on Γ × (Q ⊕ Q×{L,R} ⊕ {⊥}) × Bool."""
    if len(set(symbols)) != len(symbols) or len(set(states)) != len(states):
        raise ValueError("symbol and state enumerations must be injective")
    heads: list[tuple | None] = [None]
    heads.extend(("q", q) for q in states)
    heads.extend(("mark", q, d) for q in states for d in ("L", "R"))
    return tuple(TwoPhaseState(symbol, head, phase)
                 for symbol in symbols for head in heads for phase in (False, True))


def state_bits(s: TwoPhaseState, ordered_alphabet: Sequence[TwoPhaseState],
               accept: Hashable, reject: Hashable) -> list[bool]:
    """Exact tagged one-hot formula used by TwoPhaseDecoder.stateBits.

    The `ordered_alphabet` argument must be the same order as Lean's
    Fintype.equivFin for cross-language bit-for-bit comparison.
    """
    if len(set(ordered_alphabet)) != len(ordered_alphabet):
        raise ValueError("state enumeration must be injective")
    if s not in ordered_alphabet:
        raise ValueError("state not in finite alphabet")
    flags = [True, s.head == ("q", accept), s.head == ("q", reject)]
    return flags + [bit for q in ordered_alphabet for bit in (False, q == s)]


def initial_state(symbol: Hashable, head_state: Hashable | None) -> TwoPhaseState:
    return TwoPhaseState(symbol, None if head_state is None else ("q", head_state), False)


def original_input_bits(x: Sequence[bool], coefficients: Sequence[int],
                        ordered_alphabet: Sequence[TwoPhaseState],
                        *, blank: Hashable, zero: Hashable, one: Hashable,
                        start: Hashable, accept: Hashable, reject: Hashable) -> list[bool]:
    """Full canonical cfgCode for encCfg on [-p(n),p(n)].

    This version has no externally supplied bit encoder and precisely
    implements the three header bits and tagged finite-state identity.
    """
    if any(c < 0 for c in coefficients):
        raise ValueError("natural polynomial required")
    n = len(x)
    radius = 0
    for c in reversed(coefficients):
        radius = radius * n + c
    result: list[bool] = []
    for i in range(-radius, radius + 1):
        symbol = (one if x[i] else zero) if 0 <= i < n else blank
        head = start if i == 0 else None
        result.extend(state_bits(initial_state(symbol, head), ordered_alphabet, accept, reject))
    return result
