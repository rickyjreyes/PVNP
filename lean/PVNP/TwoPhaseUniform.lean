import PVNP.TwoPhaseDecoder
import PVNP.PartIIUniformEquiv

/-!
# Original two-phase W_M: exact embedding into the uniform WCC interface

The author's Part II construction uses the alphabet `S M`, the original two-phase
rule `U M`, and the interval `[-L, L]`. This module connects those definitions
to `PartIIUniform.UWCC` without replacing them with the alternative one-cell
machine.

The exact missing obligations are `FP` proofs for the *original* encoder and
window writer. They are explicit arguments here and must not be presented as
unconditional conclusions. The original decoder is supplied by
`TwoPhaseDecoder.decM_fp`, which was already verified in PR #56.
-/

namespace PVNP.TwoPhaseUniform

open PartIITuring PartIITwoPhase PartIIUniform TwoPhaseDecoder

/-- Canonical window code for the original interval, using a polynomial
radius clock. The extra cell of margin is needed by the radius-one rule. -/
def originalWindowCode (p : Polynomial ℕ) (x : List Bool) : List Bool :=
  latCode 1 (p.eval x.length + 1) (window (p.eval x.length))

/-- Canonical initial configuration code of the actual two-phase machine.
The state encoding is injective and fixed-width, not a decision-bit encoder. -/
noncomputable def originalInputCode (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) : List Bool :=
  cfgCode (stateBits M) 1 (p.eval x.length + 1)
    (window (p.eval x.length))
    (fun i => encM M (p.eval x.length) x (i 0))

/-- The *original* `W_M` gives an instance of the uniform interface as
soon as actual polynomial-time transducers for its window and encoder have
been built. These hypotheses are precisely the remaining II-10 obligations.
The decoder uniformity is established unconditionally by PR #56. -/
noncomputable def originalUniform (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p))
    (hEncoder : FP (originalInputCode M p)) : UWCC where
  d := 1
  d_pos := by omega
  r := 1
  S := PartIITwoPhase.S M
  sbd := PartIITwoPhase.sbd M
  U := fun nbr => PartIITwoPhase.U M
    (nbr (fun _ => 0)) (nbr (fun _ => 1)) (nbr (fun _ => 2))
  w := 3 + 2 * Fintype.card (PartIITwoPhase.S M)
  bits := stateBits M
  bits_len := stateBits_length M
  bits_inj := stateBits_injective M
  R := fun n => p.eval n + 1
  Λ := fun n => window (p.eval n)
  decΛ := fun _ => inferInstance
  margin := by
    intro n i hi k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    change |i 0| + (1 : ℤ) ≤ ((p.eval n + 1 : ℕ) : ℤ)
    have hb : |i 0| ≤ (p.eval n : ℤ) := abs_le.mpr hi
    omega
  enc := fun x i => encM M (p.eval x.length) x (i 0)
  dec := fun n C => decM M (p.eval n) (fun i => C (fun _ => i))
  lat_fp := hWindow
  enc_fp := hEncoder
  dec_fp := by
    simpa using decM_fp M p

/-- The author's window is *exactly* the uniform machine's window,
not a replacement cellular automaton. -/
theorem original_window (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (n : ℕ) (i : Fin 1 → ℤ) :
    i ∈ (originalUniform M p hWindow hEncoder).Λ n ↔
      InWin (p.eval n) (i 0) := by
  rfl

/-- The uniform machine has precisely the original decoder, including
accept-before-reject priority on arbitrary configurations. -/
theorem original_decoder (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (n : ℕ) (C : ℤ → PartIITwoPhase.S M) :
    (originalUniform M p hWindow hEncoder).dec n (fun i => C (i 0)) =
      decM M (p.eval n) C := by
  rfl

/-- The original lattice, when restricted to the active window, initializes
to the exact manuscript encoding. -/
theorem original_initial (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (x : List Bool) (i : ℤ) :
    (originalUniform M p hWindow hEncoder).init x (fun _ => i) =
      encM M (p.eval x.length) x i := by
  change (if InWin (p.eval x.length) i then
    encM M (p.eval x.length) x i else PartIITwoPhase.sbd M) =
      encM M (p.eval x.length) x i
  by_cases hi : InWin (p.eval x.length) i
  · simp [hi]
  · simp [hi, encM]

/-- The exact width of the state code used by the original construction. -/
theorem original_state_bits_length (M : MTM) (s : PartIITwoPhase.S M) :
    (stateBits M s).length = 3 + 2 * Fintype.card (PartIITwoPhase.S M) :=
  stateBits_length M s

/-- The original state code is injective. -/
theorem original_state_bits_injective (M : MTM) :
    Function.Injective (stateBits M) :=
  stateBits_injective M

end PVNP.TwoPhaseUniform
