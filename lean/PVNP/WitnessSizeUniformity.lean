import PVNP.ComplexityEquivalence

/-!
# Witness-size uniformity and explicit verifier overhead (issue #11)

Explicit input/witness-length quantifiers for the NP correspondence of
`ComplexityEquivalence`:

* `pair_length`: `|pair x w| = 2|x| + 1 + |w|`.
* `pair_length_le`: a witness with `|w| ≤ q(|x|)` gives a verifier input of
  length at most `(2X + 1 + q)(|x|)`.
* `NP_TM_verifier_to_WCC`: a TM verifier running in time `p` becomes a WCC
  verifier for the **same** language with the **same** witness polynomial `q`
  and the **same** time polynomial `p`; its running time measured in `|x|` is
  at most `p ∘ (2X + 1 + q)`.
* `NP_WCC_verifier_to_TM`: the reverse direction with the explicit sweep
  overhead `1 + (p+1)(X + 2p + 5)`.
-/

namespace PVNP.Discrete

theorem pair_length (x w : List Bool) : (pair x w).length = 2 * x.length + 1 + w.length := by
  induction x with
  | nil => simp [pair]; omega
  | cons b x ih =>
    simp only [pair, List.flatMap_cons, List.cons_append, List.length_cons] at ih ⊢
    simp only [List.nil_append, List.length_append, List.length_cons] at ih ⊢
    omega

/-- Polynomials with natural coefficients are monotone on `ℕ`. -/
theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

theorem pair_length_le (q : Polynomial ℕ) (x w : List Bool) (hw : w.length ≤ q.eval x.length) :
    (pair x w).length ≤ (2 * Polynomial.X + 1 + q).eval x.length := by
  rw [pair_length]; simp; omega

/-- TM verifier ⇒ WCC verifier: same language, same witness bound, same time. -/
theorem NP_TM_verifier_to_WCC {L V : Set (List Bool)} {M : TM} {p q : Polynomial ℕ}
    (hM : M.Decides V (fun n => p.eval n))
    (hL : ∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V) :
    M.toWCC.Decides V (fun n => p.eval n) ∧
    (∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V) ∧
    (∀ x w, w.length ≤ q.eval x.length →
      p.eval (pair x w).length ≤ (p.comp (2 * Polynomial.X + 1 + q)).eval x.length) :=
  ⟨M.toWCC_decides hM, hL, fun x w hw => by
    rw [Polynomial.eval_comp]
    exact eval_mono_nat p (pair_length_le q x w hw)⟩

/-- WCC verifier ⇒ TM verifier: same language and witness bound, explicit
quadratic overhead. -/
theorem NP_WCC_verifier_to_TM {L V : Set (List Bool)} {A : WCC} {p q : Polynomial ℕ}
    (hA : A.Decides V (fun n => p.eval n))
    (hL : ∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V) :
    A.toTM.Decides V (fun n => 1 + (p.eval n + 1) * (n + 2 * p.eval n + 5)) ∧
    (∀ x, x ∈ L ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ pair x w ∈ V) :=
  ⟨A.toTM_decides hA, hL⟩

end PVNP.Discrete
