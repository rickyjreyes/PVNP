import PVNP.TwoPhaseConstantWindow

/-!
# Phase XIV: general fixed-word original MTM output transducer

This constructs a real single-tape MTM for *every fixed finite output word*
rather than hard-coding a five-bit example.  The machine has `word.length + 2`
finite control states and executes one rightward write transition per bit,
followed by one blank-writing transition.

For a fixed natural radius L, this yields the original canonical window writer
with polynomial bound `Polynomial.C (3*L+6)`. It does not close II-10 for an
arbitrary nonconstant polynomial p, whose radius depends on input length.

The declarations in this module are proof candidates pending a successful
Lean kernel build. The repository's GitHub-hosted runners currently fail before
executing job steps; none of the theorems below may be called kernel-verified
until the pinned-toolchain build and axiom audit complete.
-/

namespace PVNP.TwoPhaseFixedWord

open PVNP.PartIITuring PVNP.PartIIUniform
open PVNP.TwoPhaseUniform PVNP.TwoPhaseWindowWord

/-- One finite control state per written bit, one for writing the terminal
blank, and one halting state. `word` is fixed in the machine definition;
the machine does not use advice depending on input length. -/
def literalMTM (word : List Bool) : MTM where
  Q := Fin (word.length + 2)
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ q _ :=
    if h : q.val < word.length then
      (⟨q.val + 1, by omega⟩, some (word.getD q.val false), .R)
    else
      (⟨word.length + 1, by omega⟩, none, .R)
  q0 := ⟨0, by omega⟩
  qacc := ⟨word.length + 1, by omega⟩
  qrej := ⟨word.length + 1, by omega⟩

/-- Until the word is completely written, the machine has executed exactly
one state transition per output bit, moved the head one cell to the right
per transition and written the corresponding prefix. -/
theorem literal_run_prefix (word x : List Bool) :
    ∀ t : ℕ, t ≤ word.length →
      let C := (literalMTM word).run ((literalMTM word).init x) t
      C.q.val = t ∧ C.head = (t : ℤ) ∧
        ∀ i : ℕ, i < t → C.tape (i : ℤ) = some (word.getD i false) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨rfl, rfl, ?_⟩
      intro i hi
      omega
  | succ t ih =>
      intro ht
      have hlt : t < word.length := by omega
      let M := literalMTM word
      let C := M.run (M.init x) t
      obtain ⟨hq, hh, hp⟩ := ih (by omega)
      have hq' : C.q = (⟨t, by omega⟩ : M.Q) :=
        Fin.ext hq
      have hδ : M.δ C.q (C.tape C.head) =
          ((⟨t + 1, by omega⟩ : M.Q), some (word.getD t false), .R) := by
        rw [hq']
        simp [M, literalMTM, hlt]
      have hs : M.run (M.init x) (t + 1) =
          (⟨Function.update C.tape (t : ℤ) (some (word.getD t false)),
            (t : ℤ) + 1, (⟨t + 1, by omega⟩ : M.Q)⟩ : M.Cfg) := by
        rw [MTM.run_succ]
        change (⟨Function.update C.tape C.head (M.δ C.q (C.tape C.head)).2.1,
          C.head + (M.δ C.q (C.tape C.head)).2.2.shift,
          (M.δ C.q (C.tape C.head)).1⟩ : M.Cfg) = _
        rw [hδ, hh]
        rfl
      rw [hs]
      refine ⟨rfl, by change (t:ℤ)+1 = ((t+1:ℕ):ℤ); simp, ?_⟩
      intro i hi
      by_cases heq : i = t
      · subst i
        simp [Function.update]
      · have hsmall : i < t := by omega
        have hne : (i : ℤ) ≠ (t : ℤ) := by omega
        change Function.update C.tape (t : ℤ) (some (word.getD t false)) (i : ℤ) = _
        rw [Function.update_of_ne hne]
        exact hp i hsmall

/-- After exactly `word.length + 1` transitions, the literal word occupies
cells 0 through length-1, the next cell is blank, and the head has just
entered the halting control. The input can be empty or arbitrarily long. -/
theorem literalMTM_outputs (word x : List Bool) :
    (literalMTM word).Outputs x word (word.length + 1) := by
  let M := literalMTM word
  let C := M.run (M.init x) word.length
  obtain ⟨hq, hh, hp⟩ := literal_run_prefix word x word.length le_rfl
  have hq' : C.q = (⟨word.length, by omega⟩ : M.Q) := Fin.ext hq
  have hδ : M.δ C.q (C.tape C.head) =
      ((⟨word.length + 1, by omega⟩ : M.Q), none, .R) := by
    rw [hq']
    simp [M, literalMTM]
  have hs : M.run (M.init x) (word.length + 1) =
      (⟨Function.update C.tape (word.length : ℤ) none,
        (word.length : ℤ) + 1,
        (⟨word.length + 1, by omega⟩ : M.Q)⟩ : M.Cfg) := by
    rw [MTM.run_succ]
    change (⟨Function.update C.tape C.head (M.δ C.q (C.tape C.head)).2.1,
      C.head + (M.δ C.q (C.tape C.head)).2.2.shift,
      (M.δ C.q (C.tape C.head)).1⟩ : M.Cfg) = _
    rw [hδ, hh]
    rfl
  refine ⟨word.length + 1, le_rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [hs]
      exact Or.inl rfl
    · intro t ht
      have hle : t ≤ word.length := by omega
      have hqT := (literal_run_prefix word x t hle).1
      change ((M.run (M.init x) t).q).val = t at hqT
      have hne : ((M.run (M.init x) t).q).val ≠ word.length + 1 := by omega
      intro hhalt
      rcases hhalt with ha | hr
      · exact hne (by simpa [M, literalMTM] using congrArg Fin.val ha)
      · exact hne (by simpa [M, literalMTM] using congrArg Fin.val hr)
  · rw [hs]
    constructor
    · intro i hi
      change Function.update C.tape (word.length : ℤ) none (i : ℤ) =
        some (word.getD i false)
      rw [Function.update_of_ne (by omega : (i : ℤ) ≠ (word.length : ℤ))]
      exact hp i hi
    · change Function.update C.tape (word.length : ℤ) none (word.length : ℤ) = none
      simp

/-- The canonical original window writer is a genuine constant-time
single-tape transducer for every *fixed* radius L. This is a strict
extension of `zeroWindowCode_fp`, not the arbitrary-polynomial result. -/
theorem constantWindowCode_fp (L : ℕ) :
    FP (originalWindowCode (Polynomial.C L)) := by
  refine ⟨literalMTM (windowWord L), Polynomial.C ((windowWord L).length + 1), ?_⟩
  intro x
  have hword : originalWindowCode (Polynomial.C L) x = windowWord L := by
    simpa using originalWindowCode_eq_windowWord (Polynomial.C L) x
  simpa only [hword, Polynomial.eval_C] using literalMTM_outputs (windowWord L) x

end PVNP.TwoPhaseFixedWord
