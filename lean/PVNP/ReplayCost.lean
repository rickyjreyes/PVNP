import PVNP.PartIIExtended

/-!
# Explicit sequential sweep and polynomial accounting

A single finite WCC global step is made into a concrete serialized output
list (one entry per cell), with extensional correctness. This is an
algorithm-level intermediate representation, not yet a one-tape TM with
a proved instruction-by-instruction simulation. The budget is a separately
specified unit-cost model: list random access is charged up to n+1 work,
and local-rule table lookup is charged up to the machine table description
size. It includes input, witness and description sizes; it cannot be used
as an unqualified TM runtime without a compiler proof.
-/

namespace PVNP.ReplayCost

open PVNP.PartII

variable {S : Type}

/-- A concrete serialized one-round snapshot with exactly n entries. -/
def serializeStep (M : RadiusOneMachine S) {n : Nat}
    (c : Configuration n S) : List S :=
  List.ofFn (step M c)

theorem serializeStep_length (M : RadiusOneMachine S) {n : Nat}
    (c : Configuration n S) :
    (serializeStep M c).length = n := by
  simp [serializeStep]

/-- This is a streaming finite-list emission of exactly the specified
    synchronous global step, not a state encoding chosen per input. -/
theorem serializeStep_correct (M : RadiusOneMachine S) {n : Nat}
    (c : Configuration n S) (i : Fin n) :
    (serializeStep M c).get
      (Fin.cast (serializeStep_length M c).symm i) = step M c i := by
  simp [serializeStep]

/-- The original finite deterministic replay remains exact. -/
theorem replay_deterministic (M : RadiusOneMachine S) {n t : Nat}
    (c : Configuration n S) :
    iterate (step M) (t + 1) c =
      step M (iterate (step M) t c) := rfl

/-- Explicit accounting: n=encoded input length, w=witness size,
    d=rule/decoder description length, cells=working lattice size,
    t=number of global rounds. The expression models an interpreter
    that linearly scans at most 'cells' symbols per requested cell,
    and uses a linearly searched rule table of length d. -/
def totalReplayCharge
    (n w d cells t : Nat) : Nat :=
  n + w + d + cells +
    t * cells * (3 * (cells + 1) + d + 8) + cells

def combinedSize (n w d cells t : Nat) : Nat :=
  n + w + d + cells + t + 16

/-- A proved, fully uniform cubic bound in ALL five counted parameters.
    It bounds the declared interpreter's charge, not an unspecified
    Turing-machine implementation. Constants do NOT depend on input size. -/
theorem totalReplayCharge_cubic
    (n w d cells t : Nat) :
    totalReplayCharge n w d cells t ≤
      4 * (combinedSize n w d cells t) ^ 3 +
        2 * combinedSize n w d cells t := by
  let B := combinedSize n w d cells t
  have hn : n + w + d + cells + cells ≤ 2 * B := by
    dsimp [B, combinedSize]
    omega
  have hmul : t * cells * (3 * (cells + 1) + d + 8) ≤
      B * B * (4 * B) := by
    apply Nat.mul_le_mul
    · apply Nat.mul_le_mul <;> (dsimp [B, combinedSize]; omega)
    · dsimp [B, combinedSize]
      omega
  have hrewrite : B * B * (4 * B) = 4 * B ^ 3 := by ring
  unfold totalReplayCharge
  calc
    n + w + d + cells +
        t * cells * (3 * (cells + 1) + d + 8) + cells ≤
      (n + w + d + cells + cells) +
        B * B * (4 * B) := by omega
    _ ≤ 2 * B + B * B * (4 * B) := by omega
    _ = 4 * B ^ 3 + 2 * B := by rw [hrewrite]; omega
    _ = 4 * (combinedSize n w d cells t) ^ 3 +
          2 * combinedSize n w d cells t := rfl

/-- A separate witness-independent bound: the verifier remains cubic
    in |x|+|w|+|description|+|lattice|+rounds, not necessarily |x| alone.
    For NP, |w| must separately be bounded by a polynomial in |x|. -/
theorem witness_length_must_be_charged
    (n w d cells t : Nat) :
    w ≤ totalReplayCharge n w d cells t := by
  simp [totalReplayCharge]
  omega

/-- Per-step round count equals t, independently of lattice size.
    Total work is not merely t: at least the state snapshot is read. -/
def roundCount (_cells : Nat) (t : Nat) := t

theorem replay_round_count (cells t : Nat) :
    roundCount cells t = t := rfl

end PVNP.ReplayCost
