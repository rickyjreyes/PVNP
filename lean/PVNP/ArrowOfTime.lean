import Mathlib

/-!
# III-22: a precise, limited no-go theorem for a global entropy arrow

The Part III arrow-of-time paragraph is an interpretive physical discussion,
not a theorem claiming `P = NP` or `P ≠ NP`. These results isolate one
mathematical issue that can be proved without introducing a physical model:
a reversible update cannot increase the same time-reversal-invariant entropy
strictly at every state.

This establishes **no** statement about actual thermodynamic irreversibility,
WCT dynamics, retrocausality, or the classical complexity classes.
-/

namespace PVNP.ArrowOfTime

variable {State : Type*}

/-- An involutive update with a globally nondecreasing scalar observable
must preserve that observable pointwise. -/
theorem involution_monotone_eq
    (next : State → State) (entropy : State → ℝ)
    (hinv : ∀ s, next (next s) = s)
    (hmono : ∀ s, entropy s ≤ entropy (next s)) (s : State) :
    entropy (next s) = entropy s := by
  have hback := hmono (next s)
  rw [hinv s] at hback
  exact le_antisymm hback (hmono s)

/-- Therefore no scalar observable is *strictly increasing at all states*
under an involution, regardless of the observable's formula. -/
theorem involution_no_global_strict_increase
    (next : State → State) (entropy : State → ℝ)
    (hinv : ∀ s, next (next s) = s) (s : State) :
    ¬ (∀ t, entropy t < entropy (next t)) := by
  intro hstrict
  have hforward := hstrict s
  have hback := hstrict (next s)
  rw [hinv s] at hback
  exact (lt_asymm hforward) hback

/-- A time-reversal symmetry is expressed through a reverse-state map.
The conjugacy law says that an update followed by state reversal and a
second update yields the reversal of the starting state. For an invertible
dynamics this is the usual statement that reversing a trajectory is again
a trajectory traversed in the opposite direction. -/
theorem time_reversal_monotone_eq
    (next reverse : State → State) (entropy : State → ℝ)
    (hconj : ∀ s, next (reverse (next s)) = reverse s)
    (hEntropy : ∀ s, entropy (reverse s) = entropy s)
    (hmono : ∀ s, entropy s ≤ entropy (next s))
    (s : State) :
    entropy (next s) = entropy s := by
  have hback := hmono (reverse (next s))
  rw [hconj s, hEntropy s, hEntropy (next s)] at hback
  exact le_antisymm hback (hmono s)

/-- In particular a time-reversal-invariant observable cannot increase
strictly on *every* trajectory of a time-reversal-symmetric update.
This does not prevent monotone behaviour in a prepared, restricted ensemble. -/
theorem time_reversal_no_global_strict_increase
    (next reverse : State → State) (entropy : State → ℝ)
    (hconj : ∀ s, next (reverse (next s)) = reverse s)
    (hEntropy : ∀ s, entropy (reverse s) = entropy s)
    (s : State) :
    ¬ (∀ t, entropy t < entropy (next t)) := by
  intro hstrict
  have hmono : ∀ t, entropy t ≤ entropy (next t) :=
    fun t => le_of_lt (hstrict t)
  have heq := time_reversal_monotone_eq next reverse entropy hconj hEntropy hmono s
  exact (ne_of_lt (hstrict s)) heq.symm

end PVNP.ArrowOfTime
