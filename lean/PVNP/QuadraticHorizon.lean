import PVNP.CrossingSATMatrix
import PVNP.SATTarget

/-! Quadratic lower bounds on every sufficiently large input-length budget.
The machine is fixed before the budget is chosen. The witness length need
not equal the budget. -/
namespace PVNP.CrossingSATMatrix

open Discrete Discrete.SATV CrossingSAT SATTarget

private theorem parameter_le_length (n : ℕ) : n ≤ N n := by
  have he : n ≤ n*2^n := by simpa using Nat.mul_le_mul_left n (Nat.one_le_two_pow (n := n))
  unfold N A G; nlinarith

private theorem length_next (n : ℕ) (hn : 4 ≤ n) : N (n+1) ≤ 3 * N n := by
  unfold N A G
  rw [pow_succ]
  generalize 2 ^ n = e
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  ring_nf
  omega

/-- For *every* length budget H above the explicit machine-dependent threshold,
there is a rejected word of length in (H/3,H] taking at least H²/(3456 b_M)
first-answer steps on the original correct one-tape machine. -/
theorem quadratic_every_budget {M : TM} (hM : Correct M SAT_dense) (H : ℕ)
    (hH : N (symbolBits M + 4) ≤ H) :
    ∃ x : List Bool, x.length ≤ H ∧ H < 3*x.length ∧ x ∉ SAT_dense ∧
      H^2 ≤ 3456 * symbolBits M * ftime M x := by
  classical
  have bounded (n : ℕ) : ∃ B : ℕ, ∀ x : List Bool, x.length = n → ftime M x ≤ B := by
    obtain ⟨B,hB⟩ := ((List.finite_length_lt Bool (n+1)).image (ftime M)).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, by simp [hx], rfl⟩⟩
  choose T hT using bounded
  have dec := decides_of_correct_le hM (T := T) (fun x => hT x.length x rfl)
  let n := Nat.findGreatest (fun j => N j ≤ H) H
  have hparam := (parameter_le_length (symbolBits M+4)).trans hH
  have hn : symbolBits M+4 ≤ n := Nat.le_findGreatest hparam hH
  have hN : N n ≤ H := Nat.findGreatest_spec (P := fun j => N j ≤ H) hparam hH
  have hnext : H < N (n+1) := by
    by_contra! hs
    have bad : n+1 ≤ n := Nat.le_findGreatest ((parameter_le_length _).trans hs) hs
    omega
  have hratio := hnext.trans_le (length_next n (by omega))
  have he : n ≤ n*2^n := by simpa using Nat.mul_le_mul_left n (Nat.one_le_two_pow (n := n))
  obtain ⟨S,hS⟩ := quadratic_diagonal dec (n := n) (by omega) (by omega)
  refine ⟨instanceWord S S, by rwa [word_length], by rwa [word_length], ?_, ?_⟩
  · rw [instanceWord_mem (by omega)]
    rintro ⟨e, he, hne⟩; exact hne he
  · calc H^2 ≤ (3*N n)^2 := Nat.pow_le_pow_left hratio.le _
         _ = 9*(N n)^2 := by ring
         _ ≤ 9*(384*symbolBits M*ftime M (instanceWord S S)) := Nat.mul_le_mul_left _ hS
         _ = _ := by ring

end PVNP.CrossingSATMatrix
