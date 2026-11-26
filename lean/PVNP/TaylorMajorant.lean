import Mathlib

/-!
# Majorant bounds for cubic–quintic Taylor recursions

The Taylor coefficients `c_n` of a solution of the finite Fourier Galerkin system of the frozen
cubic–quintic PDE (physical picture `u' = −i(A u + P_S Fnl(u))`) satisfy, after taking norms
with the `H²` algebra bound `‖mulH v w‖ ≤ C_A ‖v‖ ‖w‖` and `‖conj v‖ = ‖v‖`, the scalar
recursion
`(n+1) a_{n+1} ≤ Ω a_n + B (a⋆a⋆a)_n + G (a⋆a⋆a⋆a⋆a)_n`,
where `a_n = ‖c_n‖`, `⋆` is the Cauchy product, `Ω` bounds the free frequencies on `S`,
`B = |β| C_A²` and `G = |γ| C_A⁴`. This module proves the majorant estimate that every
Cauchy–Kovalevskaya-type analyticity proof for such a recursion needs.

* `majorant`: if `0 ≤ a_n`, `a_0 ≤ K` and the recursion holds, then for all `n`
  `a_n ≤ K λ^n / (n+1)²`, with `λ = 4(Ω + 64 B K² + 4096 G K⁴)` (`rate`).
  So the Taylor series has radius of convergence at least `1/λ`, which is polynomial in the
  frequency bound and the radius.
* `taylor_tail_le`: if `0 ≤ h` and `λ h ≤ 1/2`, the Taylor tail after `q` terms is at most
  `2 K (λ h)^{q+1}`. A step of size `1/(2λ)` with `q` terms therefore has local truncation error
  at most `2K·2^{-(q+1)}`.

The engine is the weighted convolution bound `Σ_{i+j=n} w_i w_j ≤ 8 w_n` for
`w_n = 1/(n+1)²` (`weighted_conv_le`), which rests on `Σ w_i ≤ 2` and
`(p+q)² ≤ 2(p² + q²)`.

Scope. This is the scalar estimate. Applying it to the actual Galerkin trajectory needs two
further steps, not formalized here:
1. the trajectory is the sum of its Taylor series, with coefficients obeying the recursion
   (analyticity of polynomial ODE flows);
2. the constants `Ω`, `B`, `G` are identified for the frozen field.
No complexity or simulation theorem is asserted.
-/

namespace PVNP.TaylorMajorant

open Finset

/-- Cauchy product of two sequences. -/
def cauchy (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n+1), a i * b (n - i)

/-- The weight `1/(n+1)²`. -/
noncomputable def wt (n : ℕ) : ℝ := 1 / ((n:ℝ) + 1) ^ 2

theorem wt_pos (n : ℕ) : 0 < wt n := by unfold wt; positivity

theorem wt_zero : wt 0 = 1 := by simp [wt]

theorem cauchy_nonneg {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (n : ℕ) :
    0 ≤ cauchy a b n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hb _)

/-- `Σ_{i<N} 1/(i+1)² ≤ 2 − 1/N`. -/
theorem sum_wt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ range N, wt i ≤ 2 - 1 / (N:ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      norm_num [wt]
    · rw [sum_range_succ]
      have h := ih hpos
      have hN' : (0:ℝ) < N := by exact_mod_cast hpos
      have key : wt N ≤ 1/(N:ℝ) - 1/((N:ℝ)+1) := by
        unfold wt
        rw [div_sub_div _ _ (ne_of_gt hN') (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

theorem sum_wt_le_two (n : ℕ) : ∑ i ∈ range (n+1), wt i ≤ 2 := by
  have h := sum_wt_le (n+1) (by omega)
  have : (0:ℝ) ≤ 1 / ((n+1 : ℕ) : ℝ) := by positivity
  linarith

/-- Pointwise: `w_i w_j ≤ 2 (w_i + w_j)/(n+2)²` when `i + j = n`. -/
theorem wt_mul_le {n i : ℕ} (hi : i ≤ n) :
    wt i * wt (n - i) ≤ 2 * (wt i + wt (n - i)) * (1 / ((n:ℝ) + 2) ^ 2) := by
  unfold wt
  have hcast : ((n - i : ℕ) : ℝ) = (n:ℝ) - i := by rw [Nat.cast_sub hi]
  rw [hcast]
  set p : ℝ := (i:ℝ) + 1 with hp
  set q : ℝ := (n:ℝ) - i + 1 with hq
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by
    rw [hq]
    have : (i:ℝ) ≤ n := by exact_mod_cast hi
    linarith
  have hpq : (n:ℝ) + 2 = p + q := by rw [hp, hq]; ring
  rw [hpq]
  rw [div_mul_div_comm, one_mul]
  have e : 2 * (1 / p ^ 2 + 1 / q ^ 2) * (1 / (p + q) ^ 2) =
      2 * (q ^ 2 + p ^ 2) / (p ^ 2 * q ^ 2 * (p + q) ^ 2) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (p - q), mul_pos hp0 hq0, sq_nonneg (p*q)]

/-- **Weighted convolution bound.** `Σ_{i+j=n} w_i w_j ≤ 8 w_n`. -/
theorem weighted_conv_le (n : ℕ) :
    ∑ i ∈ range (n+1), wt i * wt (n - i) ≤ 8 * wt n := by
  have hrefl : ∑ i ∈ range (n+1), wt (n - i) = ∑ i ∈ range (n+1), wt i := by
    have := Finset.sum_range_reflect (fun i => wt i) (n+1)
    simpa using this
  have hsum : ∑ i ∈ range (n+1), wt i * wt (n - i) ≤
      ∑ i ∈ range (n+1), 2 * (wt i + wt (n - i)) * (1 / ((n:ℝ) + 2) ^ 2) :=
    Finset.sum_le_sum fun i hi => wt_mul_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, hrefl] at hsum
  have h2 := sum_wt_le_two n
  have hc : (0:ℝ) ≤ 1 / ((n:ℝ) + 2) ^ 2 := by positivity
  have hcmp : 1 / ((n:ℝ) + 2) ^ 2 ≤ wt n := by
    unfold wt
    apply one_div_le_one_div_of_le (by positivity)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc _ ≤ 2 * (∑ i ∈ range (n+1), wt i + ∑ i ∈ range (n+1), wt i) *
        (1 / ((n:ℝ) + 2) ^ 2) := hsum
    _ ≤ 2 * (2 + 2) * (1 / ((n:ℝ) + 2) ^ 2) := by gcongr
    _ ≤ 8 * wt n := by nlinarith

/-- **Cauchy-product bound.** -/
theorem cauchy_bound {a b : ℕ → ℝ} {n : ℕ} {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hb0 : ∀ k, 0 ≤ b k)
    (ha : ∀ k ≤ n, a k ≤ A * r ^ k * wt k) (hb : ∀ k ≤ n, b k ≤ B * r ^ k * wt k) :
    cauchy a b n ≤ 8 * A * B * r ^ n * wt n := by
  unfold cauchy
  have hterm : ∀ i ∈ range (n+1), a i * b (n - i) ≤
      A * B * r ^ n * (wt i * wt (n - i)) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := ha i hin
    have h2 := hb (n - i) (Nat.sub_le n i)
    have hpow : r ^ i * r ^ (n - i) = r ^ n := by rw [← pow_add, Nat.add_sub_cancel' hin]
    calc a i * b (n - i) ≤ (A * r ^ i * wt i) * (B * r ^ (n - i) * wt (n - i)) :=
          mul_le_mul h1 h2 (hb0 _) (by have := wt_pos i; positivity)
      _ = A * B * (r ^ i * r ^ (n - i)) * (wt i * wt (n - i)) := by ring
      _ = A * B * r ^ n * (wt i * wt (n - i)) := by rw [hpow]
  calc ∑ i ∈ range (n+1), a i * b (n - i)
      ≤ ∑ i ∈ range (n+1), A * B * r ^ n * (wt i * wt (n - i)) := Finset.sum_le_sum hterm
    _ = A * B * r ^ n * ∑ i ∈ range (n+1), wt i * wt (n - i) := by rw [← Finset.mul_sum]
    _ ≤ A * B * r ^ n * (8 * wt n) :=
        mul_le_mul_of_nonneg_left (weighted_conv_le n) (by positivity)
    _ = 8 * A * B * r ^ n * wt n := by ring

/-- Cubic and quintic Cauchy powers. -/
def c2 (a : ℕ → ℝ) : ℕ → ℝ := cauchy a a
def c3 (a : ℕ → ℝ) : ℕ → ℝ := cauchy a (c2 a)
def c4 (a : ℕ → ℝ) : ℕ → ℝ := cauchy a (c3 a)
def c5 (a : ℕ → ℝ) : ℕ → ℝ := cauchy a (c4 a)

/-- Bounds on all Cauchy powers up to five from a bound on `a` up to index `n`. -/
theorem powers_bound {a : ℕ → ℝ} {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (ha0 : ∀ k, 0 ≤ a k) {n : ℕ} (ha : ∀ k ≤ n, a k ≤ K * r ^ k * wt k) :
    (∀ k ≤ n, c3 a k ≤ (64 * K ^ 3) * r ^ k * wt k) ∧
      (∀ k ≤ n, c5 a k ≤ (4096 * K ^ 5) * r ^ k * wt k) := by
  have n2 : ∀ k, 0 ≤ c2 a k := cauchy_nonneg ha0 ha0
  have n3 : ∀ k, 0 ≤ c3 a k := cauchy_nonneg ha0 n2
  have n4 : ∀ k, 0 ≤ c4 a k := cauchy_nonneg ha0 n3
  have b2 : ∀ k ≤ n, c2 a k ≤ (8 * K ^ 2) * r ^ k * wt k := by
    intro k hk
    have := cauchy_bound hK hK hr ha0 (fun j hj => ha j (hj.trans hk))
      (fun j hj => ha j (hj.trans hk))
    calc c2 a k ≤ 8 * K * K * r ^ k * wt k := this
      _ = _ := by ring
  have b3 : ∀ k ≤ n, c3 a k ≤ (64 * K ^ 3) * r ^ k * wt k := by
    intro k hk
    have := cauchy_bound hK (by positivity) hr n2 (fun j hj => ha j (hj.trans hk))
      (fun j hj => b2 j (hj.trans hk))
    calc c3 a k ≤ 8 * K * (8 * K ^ 2) * r ^ k * wt k := this
      _ = _ := by ring
  have b4 : ∀ k ≤ n, c4 a k ≤ (512 * K ^ 4) * r ^ k * wt k := by
    intro k hk
    have := cauchy_bound hK (by positivity) hr n3 (fun j hj => ha j (hj.trans hk))
      (fun j hj => b3 j (hj.trans hk))
    calc c4 a k ≤ 8 * K * (64 * K ^ 3) * r ^ k * wt k := this
      _ = _ := by ring
  refine ⟨b3, fun k hk => ?_⟩
  have := cauchy_bound hK (by positivity) hr n4 (fun j hj => ha j (hj.trans hk))
    (fun j hj => b4 j (hj.trans hk))
  calc c5 a k ≤ 8 * K * (512 * K ^ 4) * r ^ k * wt k := this
    _ = _ := by ring

/-- The majorant rate `λ = 4(Ω + 64 B K² + 4096 G K⁴)`. -/
def rate (K Ω B G : ℝ) : ℝ := 4 * (Ω + 64 * B * K ^ 2 + 4096 * G * K ^ 4)

theorem wt_step (n : ℕ) : wt n ≤ 4 * ((n:ℝ) + 1) * wt (n + 1) := by
  unfold wt
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  rw [show 4 * ((n:ℝ) + 1) * (1 / ((n:ℝ) + 1 + 1) ^ 2) * ((n:ℝ) + 1) ^ 2 =
      4 * ((n:ℝ) + 1) ^ 3 / ((n:ℝ) + 2) ^ 2 by ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (n:ℝ), mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

/-- **Majorant theorem for cubic–quintic Taylor recursions.** -/
theorem majorant {a : ℕ → ℝ} {K Ω B G : ℝ} (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (ha0 : ∀ n, 0 ≤ a n) (hinit : a 0 ≤ K)
    (hrec : ∀ n : ℕ, ((n:ℝ) + 1) * a (n+1) ≤ Ω * a n + B * c3 a n + G * c5 a n) :
    ∀ n, a n ≤ K * (rate K Ω B G) ^ n * wt n := by
  set r := rate K Ω B G with hrdef
  have hr : 0 ≤ r := by rw [hrdef]; unfold rate; positivity
  have hall : ∀ n, ∀ k ≤ n, a k ≤ K * r ^ k * wt k := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      rw [pow_zero, wt_zero, mul_one, mul_one]
      exact hinit
    | succ n ih =>
      intro k hk
      rcases Nat.lt_or_ge k (n+1) with hlt | hge
      · exact ih k (by omega)
      · have hk' : k = n + 1 := by omega
        subst hk'
        obtain ⟨b3, b5⟩ := powers_bound hK hr ha0 ih
        have hn := hrec n
        have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
        have hw := wt_step n
        have hwn : 0 ≤ wt n := (wt_pos n).le
        have hbound : Ω * a n + B * c3 a n + G * c5 a n ≤
            (r / 4) * K * r ^ n * wt n := by
          have e1 := mul_le_mul_of_nonneg_left (ih n le_rfl) hΩ
          have e2 := mul_le_mul_of_nonneg_left (b3 n le_rfl) hB
          have e3 := mul_le_mul_of_nonneg_left (b5 n le_rfl) hG
          have : (r / 4) * K * r ^ n * wt n =
              Ω * (K * r ^ n * wt n) + B * (64 * K ^ 3 * r ^ n * wt n) +
                G * (4096 * K ^ 5 * r ^ n * wt n) := by
            rw [hrdef]; unfold rate; ring
          rw [this]
          linarith
        have hfinal : (r / 4) * K * r ^ n * wt n ≤
            ((n:ℝ) + 1) * (K * r ^ (n+1) * wt (n+1)) := by
          have hKr : 0 ≤ K * r ^ (n+1) := by positivity
          calc (r / 4) * K * r ^ n * wt n = (K * r ^ (n+1)) * (wt n / 4) := by
                rw [pow_succ]; ring
            _ ≤ (K * r ^ (n+1)) * (((n:ℝ) + 1) * wt (n+1)) := by
                apply mul_le_mul_of_nonneg_left _ hKr
                linarith
            _ = ((n:ℝ) + 1) * (K * r ^ (n+1) * wt (n+1)) := by ring
        have hmul : ((n:ℝ) + 1) * a (n+1) ≤ ((n:ℝ) + 1) * (K * r ^ (n+1) * wt (n+1)) :=
          hn.trans (hbound.trans hfinal)
        exact le_of_mul_le_mul_left hmul hpos
  intro n
  exact hall n n le_rfl

/-- Each Taylor term is at most `K (λ h)^n`. -/
theorem taylor_term_le {a : ℕ → ℝ} {K r h : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hmaj : ∀ n, a n ≤ K * r ^ n * wt n) (n : ℕ) :
    a n * h ^ n ≤ K * (r * h) ^ n := by
  have hw : wt n ≤ 1 := by
    unfold wt
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc a n * h ^ n ≤ (K * r ^ n * wt n) * h ^ n :=
        mul_le_mul_of_nonneg_right (hmaj n) (by positivity)
    _ ≤ (K * r ^ n * 1) * h ^ n := by
        gcongr
    _ = K * (r * h) ^ n := by rw [mul_pow]; ring

/-- **Taylor truncation error.** If `λ h ≤ 1/2`, the tail of the Taylor series after `q` terms
is at most `2 K (λ h)^{q+1}`. -/
theorem taylor_tail_le {a : ℕ → ℝ} {K r h : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hrh : r * h ≤ 1/2) (hmaj : ∀ n, a n ≤ K * r ^ n * wt n) (q N : ℕ) :
    ∑ n ∈ Ico (q+1) N, a n * h ^ n ≤ 2 * K * (r * h) ^ (q+1) := by
  have hx0 : 0 ≤ r * h := mul_nonneg hr hh
  have hx1 : r * h < 1 := by linarith
  calc ∑ n ∈ Ico (q+1) N, a n * h ^ n ≤ ∑ n ∈ Ico (q+1) N, K * (r * h) ^ n :=
        Finset.sum_le_sum fun n _ => taylor_term_le hK hr hh hmaj n
    _ = K * ∑ n ∈ Ico (q+1) N, (r * h) ^ n := by rw [Finset.mul_sum]
    _ ≤ K * ((r * h) ^ (q+1) / (1 - r * h)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hx0 hx1) hK
    _ ≤ K * ((r * h) ^ (q+1) / (1/2)) := by
        gcongr
        linarith
    _ = 2 * K * (r * h) ^ (q+1) := by ring

end PVNP.TaylorMajorant
