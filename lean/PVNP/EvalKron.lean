import Mathlib

/-!
# Kronecker packing of Taylor series of Fourier arrays

The restricted continuum evaluator (#99) computes the Taylor coefficients of the Galerkin system:
for each order `n ≤ q`, an array of Fourier coefficients on a box of modes. A Cauchy product in
the Taylor index combined with a convolution over the modes is computed here by **one
multiplication of two integers**.

* `ex W s n k = n W² + (k₁ + s) + W (k₂ + s)`: the exponent of the term of order `n` at mode `k`,
  for arrays supported on the box `[−s, s]²` (`box s`).
* `kv X W s q f = Σ_{n ≤ q} Σ_{k ∈ box s} f(n, k) X^{ex W s n k}`, over any commutative ring.
* `cprod s f g`: the Cauchy–Fourier product `Σ_{i ≤ n} Σ_{j ∈ box s} f(i, j) g(n − i, k − j)`.
* `kv_mul`: **`kv(f) · kv(g) = kv(f ⋆ g)`**, for arrays supported on boxes of radii `s` and `t`
  and every base and digit width. The product lives on the box of radius `s + t`
  (`supp_cprod`). `kv` is additive and homogeneous (`kv_add`, `kv_smul`, `kv_sub`).
* **Decoding** (`kv_decode`, `digit_sum`). For digit width `W ≥ 2s + 1` and integer
  coefficients in `[−⌊X/2⌋, X − ⌊X/2⌋)`, adding the constant `⌊X/2⌋ Σ_p X^p` (`excess`) turns the
  Kronecker value into a number whose base-`X` digits are `⌊X/2⌋ + f(n, k)` at the exponents of
  `(n, k)` (`ex_digits`, `ex_inj`, `ex_lt`).
-/

namespace PVNP.Eval

open Finset

/-! ### Boxes, exponents and Kronecker values -/

/-- The box of modes `[−s, s]²`. -/
def box (s : ℕ) : Finset (ℤ × ℤ) := Icc (-(s : ℤ)) s ×ˢ Icc (-(s : ℤ)) s

theorem mem_box {s : ℕ} {k : ℤ × ℤ} :
    k ∈ box s ↔ -(s : ℤ) ≤ k.1 ∧ k.1 ≤ s ∧ -(s : ℤ) ≤ k.2 ∧ k.2 ≤ s := by
  simp [box, and_assoc]

/-- The exponent of the term `(n, k)`: Taylor digit `n` of weight `W²`, Fourier digits `k + s`. -/
def ex (W s n : ℕ) (k : ℤ × ℤ) : ℕ := n * (W * W) + (k.1 + s).toNat + W * (k.2 + s).toNat

variable {R : Type*} [CommRing R]

/-- `f` is supported on Taylor indices `n ≤ q` and modes `k ∈ box s`. -/
def Supp (s q : ℕ) (f : ℕ → ℤ × ℤ → R) : Prop := ∀ n k, (q < n ∨ k ∉ box s) → f n k = 0

/-- **The Kronecker value** of a Taylor series of Fourier arrays at the base `X`. -/
def kv (X W s q : ℕ) (f : ℕ → ℤ × ℤ → R) : R :=
  ∑ n ∈ range (q + 1), ∑ k ∈ box s, f n k * (X : R) ^ ex W s n k

/-- **The Cauchy–Fourier product**: `(f ⋆ g)(n, k) = Σ_{i ≤ n} Σ_{j ∈ box s} f(i, j) g(n − i, k − j)`. -/
def cprod (s : ℕ) (f g : ℕ → ℤ × ℤ → R) (n : ℕ) (k : ℤ × ℤ) : R :=
  ∑ i ∈ range (n + 1), ∑ j ∈ box s, f i j * g (n - i) (k - j)

theorem ex_add (W s t i i' : ℕ) {j j' : ℤ × ℤ} (hj : j ∈ box s) (hj' : j' ∈ box t) :
    ex W s i j + ex W t i' j' = ex W (s + t) (i + i') (j + j') := by
  rw [mem_box] at hj hj'
  obtain ⟨a1, a2, a3, a4⟩ := hj
  obtain ⟨b1, b2, b3, b4⟩ := hj'
  unfold ex
  simp only [Prod.fst_add, Prod.snd_add]
  have e1 : (j.1 + j'.1 + ((s + t : ℕ) : ℤ)).toNat = (j.1 + s).toNat + (j'.1 + t).toNat := by
    push_cast; omega
  have e2 : (j.2 + j'.2 + ((s + t : ℕ) : ℤ)).toNat = (j.2 + s).toNat + (j'.2 + t).toNat := by
    push_cast; omega
  rw [e1, e2]; ring

theorem add_mem_box {s t : ℕ} {j j' : ℤ × ℤ} (hj : j ∈ box s) (hj' : j' ∈ box t) :
    j + j' ∈ box (s + t) := by
  rw [mem_box] at hj hj' ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  omega

theorem kv_eq (X W s q : ℕ) (f : ℕ → ℤ × ℤ → R) :
    kv X W s q f = ∑ a ∈ range (q + 1) ×ˢ box s, f a.1 a.2 * (X : R) ^ ex W s a.1 a.2 := by
  unfold kv; rw [Finset.sum_product]

/-- The inner sum of the right side of `kv_mul`, for a fixed first factor. -/
theorem inner_reindex (X W s t q q' : ℕ) {f g : ℕ → ℤ × ℤ → R} (hg : Supp t q' g)
    (a : ℕ × (ℤ × ℤ)) (ha : a ∈ range (q + 1) ×ˢ box s) :
    ∑ b ∈ range (q' + 1) ×ˢ box t,
        f a.1 a.2 * g b.1 b.2 * (X : R) ^ ex W (s + t) (a.1 + b.1) (a.2 + b.2) =
      ∑ c ∈ range (q + q' + 1) ×ˢ box (s + t),
        if a.1 ≤ c.1 then f a.1 a.2 * g (c.1 - a.1) (c.2 - a.2) * (X : R) ^ ex W (s + t) c.1 c.2
        else 0 := by
  have haq : a.1 ≤ q := by have := Finset.mem_range.1 (Finset.mem_product.1 ha).1; omega
  have has : a.2 ∈ box s := (Finset.mem_product.1 ha).2
  refine Finset.sum_bij_ne_zero (fun b _ _ => (a.1 + b.1, a.2 + b.2)) ?_ ?_ ?_ ?_
  · intro b hb _
    dsimp only
    rw [Finset.mem_product] at hb ⊢
    refine ⟨Finset.mem_range.2 ?_, add_mem_box has hb.2⟩
    have := Finset.mem_range.1 hb.1
    omega
  · intro b₁ _ _ b₂ _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (add_left_cancel h.2)
  · intro c hc hne
    have hle : a.1 ≤ c.1 := by
      by_contra h; exact hne (by simp [h])
    rw [if_pos hle] at hne
    have hg' : g (c.1 - a.1) (c.2 - a.2) ≠ 0 := fun h => hne (by rw [h, mul_zero, zero_mul])
    have hmem : c.1 - a.1 < q' + 1 ∧ c.2 - a.2 ∈ box t := by
      by_contra h
      rw [not_and_or, not_lt] at h
      exact hg' (hg _ _ (h.imp (by omega) id))
    have e1 : a.1 + (c.1 - a.1) = c.1 := by omega
    have e2 : a.2 + (c.2 - a.2) = c.2 := by abel
    refine ⟨(c.1 - a.1, c.2 - a.2), Finset.mem_product.2 ⟨Finset.mem_range.2 hmem.1, hmem.2⟩, ?_,
      Prod.ext e1 e2⟩
    dsimp only
    rw [e1, e2]
    exact hne
  · intro b _ _
    dsimp only
    rw [if_pos (by omega), show a.1 + b.1 - a.1 = b.1 by omega,
      show a.2 + b.2 - a.2 = b.2 by abel]

/-- **Kronecker substitution for Taylor series of Fourier arrays.** For any base and digit width,
the product of the Kronecker values is the Kronecker value of the Cauchy–Fourier product. -/
theorem kv_mul (X W s t q q' : ℕ) {f g : ℕ → ℤ × ℤ → R} (hf : Supp s q f) (hg : Supp t q' g) :
    kv X W s q f * kv X W t q' g = kv X W (s + t) (q + q') (cprod s f g) := by
  rw [kv_eq, kv_eq, kv_eq, Finset.sum_mul_sum]
  have step1 : ∀ a ∈ range (q + 1) ×ˢ box s,
      ∑ b ∈ range (q' + 1) ×ˢ box t,
        f a.1 a.2 * (X : R) ^ ex W s a.1 a.2 * (g b.1 b.2 * (X : R) ^ ex W t b.1 b.2) =
      ∑ c ∈ range (q + q' + 1) ×ˢ box (s + t),
        if a.1 ≤ c.1 then f a.1 a.2 * g (c.1 - a.1) (c.2 - a.2) * (X : R) ^ ex W (s + t) c.1 c.2
        else 0 := by
    intro a ha
    rw [← inner_reindex X W s t q q' hg a ha]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← ex_add W s t a.1 b.1 (Finset.mem_product.1 ha).2 (Finset.mem_product.1 hb).2, pow_add]
    ring
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cprod
  rw [← Finset.sum_product', Finset.sum_mul]
  -- Σ_{a ∈ range (q+1) × box s} [a.1 ≤ c.1] F a = Σ_{a ∈ range (c.1+1) × box s} F a
  rw [← Finset.sum_filter]
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha ⊢
    exact ⟨by omega, ha.1.2⟩
  · intro a ha
    rw [Finset.mem_sdiff] at ha
    obtain ⟨h1, h2⟩ := ha
    rw [Finset.mem_product, Finset.mem_range] at h1
    have hq : q < a.1 := by
      by_contra h
      apply h2
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, h1.2⟩, by omega⟩
    rw [hf a.1 a.2 (Or.inl hq), zero_mul, zero_mul]
  · intro a _
    rfl

/-! ### Supports and linearity -/

/-- The product of supported arrays is supported on the sum box. -/
theorem supp_cprod {s t q q' : ℕ} {f g : ℕ → ℤ × ℤ → R} (hf : Supp s q f) (hg : Supp t q' g) :
    Supp (s + t) (q + q') (cprod s f g) := by
  intro n k h
  unfold cprod
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rcases h with h | h
  · by_cases hiq : q < i
    · rw [hf i j (Or.inl hiq), zero_mul]
    · rw [hg (n - i) (k - j) (Or.inl (by omega)), mul_zero]
  · have : k - j ∉ box t := fun hk => h (by
      have := add_mem_box hj hk
      rwa [add_sub_cancel] at this)
    rw [hg (n - i) (k - j) (Or.inr this), mul_zero]

theorem kv_add (X W s q : ℕ) (f g : ℕ → ℤ × ℤ → R) :
    kv X W s q (fun n k => f n k + g n k) = kv X W s q f + kv X W s q g := by
  unfold kv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem kv_smul (X W s q : ℕ) (c : R) (f : ℕ → ℤ × ℤ → R) :
    kv X W s q (fun n k => c * f n k) = c * kv X W s q f := by
  unfold kv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem kv_sub (X W s q : ℕ) (f g : ℕ → ℤ × ℤ → R) :
    kv X W s q (fun n k => f n k - g n k) = kv X W s q f - kv X W s q g := by
  have h := kv_add X W s q f (fun n k => -1 * g n k)
  rw [kv_smul] at h
  rw [show (fun n k => f n k - g n k) = (fun n k => f n k + -1 * g n k) by
    funext n k; ring, h]
  ring

/-- Enlarging the Taylor range does not change the Kronecker value of a supported array. -/
theorem kv_mono_q {X W s q q' : ℕ} {f : ℕ → ℤ × ℤ → R} (hf : Supp s q f) (hq : q ≤ q') :
    kv X W s q' f = kv X W s q f := by
  unfold kv
  symm
  refine Finset.sum_subset (fun x hx => by
    rw [Finset.mem_range] at hx ⊢; omega) fun n _ hnq => ?_
  have h1 : q < n := by
    have := Finset.mem_range.not.1 hnq
    omega
  exact Finset.sum_eq_zero fun k _ => by rw [hf n k (Or.inl h1), zero_mul]

/-! ### Base-`X` digits -/

theorem digits_sum_lt (X : ℕ) (w : ℕ → ℕ) (hw : ∀ p, w p < X) :
    ∀ M : ℕ, ∑ p ∈ range M, w p * X ^ p < X ^ M
  | 0 => by simp
  | M + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have ih := digits_sum_lt X w hw M
    have h1 : w M * X ^ M ≤ (X - 1) * X ^ M :=
      Nat.mul_le_mul_right _ (by have := hw M; omega)
    have hX : 1 ≤ X := by have := hw 0; omega
    calc ∑ p ∈ range M, w p * X ^ p + w M * X ^ M < X ^ M + (X - 1) * X ^ M := by omega
      _ = X ^ M * X := by
        rw [show X ^ M + (X - 1) * X ^ M = (1 + (X - 1)) * X ^ M by ring,
          show 1 + (X - 1) = X by omega, mul_comm]

/-- **Digit extraction**: the `m`-th base-`X` digit of `Σ_{p<M} w_p X^p` is `w_m`. -/
theorem digit_sum (X : ℕ) (w : ℕ → ℕ) (hw : ∀ p, w p < X) (m : ℕ) :
    ∀ M, m < M → (∑ p ∈ range M, w p * X ^ p) / X ^ m % X = w m := by
  intro M hM
  have hX : 0 < X := by have := hw 0; omega
  induction M with
  | zero => omega
  | succ M ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hM with h | h
    · have e : w M * X ^ M = (w M * X ^ (M - m - 1) * X) * X ^ m := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
        congr 2; omega
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact ih h
    · subst h
      have hlt := digits_sum_lt X w hw m
      rw [Nat.add_comm, Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl),
        Nat.mul_div_cancel _ (pow_pos hX m), Nat.div_eq_of_lt hlt, add_zero,
        Nat.mod_eq_of_lt (hw m)]

/-! ### Decoding the packed coefficients -/

/-- The excess constant: `⌊X/2⌋` in each of the first `M` digits. -/
def excess (X M : ℕ) : ℕ := ∑ p ∈ range M, X / 2 * X ^ p

theorem ex_digits {W s : ℕ} (n : ℕ) {k : ℤ × ℤ} (hk : k ∈ box s) (hW : 2 * s + 1 ≤ W) :
    ex W s n k % W = (k.1 + s).toNat ∧ ex W s n k / W % W = (k.2 + s).toNat ∧
      ex W s n k / W / W = n := by
  rw [mem_box] at hk
  have h1 : (k.1 + s).toNat < W := by omega
  have h2 : (k.2 + s).toNat < W := by omega
  have hW0 : 0 < W := by omega
  have e : ex W s n k = (k.1 + s).toNat + W * ((k.2 + s).toNat + W * n) := by
    unfold ex; ring
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  · rw [Nat.add_mul_div_left _ _ hW0, Nat.div_eq_of_lt h1, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  · rw [Nat.add_mul_div_left _ _ hW0, Nat.div_eq_of_lt h1, zero_add,
      Nat.add_mul_div_left _ _ hW0, Nat.div_eq_of_lt h2, zero_add]

/-- The exponent is injective on a supported box. -/
theorem ex_inj {W s : ℕ} (hW : 2 * s + 1 ≤ W) {n n' : ℕ} {k k' : ℤ × ℤ} (hk : k ∈ box s)
    (hk' : k' ∈ box s) (h : ex W s n k = ex W s n' k') : n = n' ∧ k = k' := by
  obtain ⟨a1, a2, a3⟩ := ex_digits n hk hW
  obtain ⟨b1, b2, b3⟩ := ex_digits n' hk' hW
  rw [h] at a1 a2 a3
  rw [mem_box] at hk hk'
  refine ⟨by rw [← a3, b3], Prod.ext ?_ ?_⟩
  · have := a1.symm.trans b1; omega
  · have := a2.symm.trans b2; omega

theorem ex_lt {W s q n : ℕ} {k : ℤ × ℤ} (hk : k ∈ box s) (hW : 2 * s + 1 ≤ W) (hn : n ≤ q) :
    ex W s n k < (q + 1) * (W * W) := by
  rw [mem_box] at hk
  have h1 : (k.1 + s).toNat ≤ W - 1 := by omega
  have h2 : (k.2 + s).toNat ≤ W - 1 := by omega
  have h3 : n * (W * W) ≤ q * (W * W) := Nat.mul_le_mul_right _ hn
  have h4 : W * (k.2 + s).toNat ≤ W * (W - 1) := Nat.mul_le_mul_left _ h2
  have hW1 : 1 ≤ W := by omega
  have e : (q + 1) * (W * W) = q * (W * W) + (W - 1) + W * (W - 1) + 1 := by
    have : W * W = (W - 1) + W * (W - 1) + 1 := by
      rcases Nat.exists_eq_add_of_le hW1 with ⟨c, rfl⟩
      simp only [Nat.add_sub_cancel_left]; ring
    rw [add_mul, one_mul, this]; ring
  unfold ex
  omega

/-- **Decoding.** With digit width `W ≥ 2s + 1` and coefficients in `[−⌊X/2⌋, X − ⌊X/2⌋)`, the
Kronecker value plus the excess constant is a number whose base-`X` digits are the words
`⌊X/2⌋ + f(n, k)` at the exponents of `(n, k)`. -/
theorem kv_decode (X W s q : ℕ) {f : ℕ → ℤ × ℤ → ℤ} (hW : 2 * s + 1 ≤ W)
    (hb : ∀ n k, -((X / 2 : ℕ) : ℤ) ≤ f n k ∧ f n k < ((X - X / 2 : ℕ) : ℤ)) :
    ∃ w : ℕ → ℕ, (∀ p, w p < X) ∧
      kv X W s q f + (excess X ((q + 1) * (W * W)) : ℤ) =
        ((∑ p ∈ range ((q + 1) * (W * W)), w p * X ^ p : ℕ) : ℤ) ∧
      ∀ n ≤ q, ∀ k ∈ box s, (w (ex W s n k) : ℤ) = ((X / 2 : ℕ) : ℤ) + f n k := by
  set M := (q + 1) * (W * W)
  set D := range (q + 1) ×ˢ box s
  let φ : ℕ → ℤ := fun p => ∑ a ∈ D.filter (fun a => ex W s a.1 a.2 = p), f a.1 a.2
  have hfib : ∀ p, φ p = 0 ∨ ∃ a ∈ D, ex W s a.1 a.2 = p ∧ φ p = f a.1 a.2 := by
    intro p
    have hcard : (D.filter (fun a => ex W s a.1 a.2 = p)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb'
      simp only [Finset.mem_filter, Finset.mem_product, D] at ha hb'
      obtain ⟨h1, h2⟩ := ex_inj hW ha.1.2 hb'.1.2 (ha.2.trans hb'.2.symm)
      exact Prod.ext h1 h2
    rcases Finset.card_le_one_iff_subset_singleton.1 hcard with ⟨a, ha⟩
    by_cases hmem : a ∈ D.filter (fun a => ex W s a.1 a.2 = p)
    · right
      have heq : D.filter (fun a => ex W s a.1 a.2 = p) = {a} :=
        Finset.Subset.antisymm ha (Finset.singleton_subset_iff.2 hmem)
      rw [Finset.mem_filter] at hmem
      refine ⟨a, hmem.1, hmem.2, ?_⟩
      show ∑ b ∈ D.filter (fun a => ex W s a.1 a.2 = p), f b.1 b.2 = _
      rw [heq, Finset.sum_singleton]
    · left
      have hempty : D.filter (fun a => ex W s a.1 a.2 = p) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb'
        have := ha hb'
        rw [Finset.mem_singleton] at this
        exact hmem (this ▸ hb')
      show ∑ b ∈ D.filter (fun a => ex W s a.1 a.2 = p), f b.1 b.2 = 0
      rw [hempty, Finset.sum_empty]
  have hφb : ∀ p, -((X / 2 : ℕ) : ℤ) ≤ φ p ∧ φ p < ((X - X / 2 : ℕ) : ℤ) := by
    intro p
    rcases hfib p with h | ⟨a, _, _, h⟩
    · rw [h]
      have h0 := hb 0 (0, 0)
      have hab : (0 : ℤ) < ((X / 2 : ℕ) : ℤ) + ((X - X / 2 : ℕ) : ℤ) := by linarith [h0.1, h0.2]
      have hX : 0 < X := by
        have e : ((X / 2 : ℕ) : ℤ) + ((X - X / 2 : ℕ) : ℤ) = (X : ℤ) := by
          rw [← Nat.cast_add]; congr 1; omega
        rw [e] at hab; exact_mod_cast hab
      exact ⟨neg_nonpos.2 (Nat.cast_nonneg _), by exact_mod_cast (show 0 < X - X / 2 by omega)⟩
    · rw [h]; exact hb a.1 a.2
  let w : ℕ → ℕ := fun p => (((X / 2 : ℕ) : ℤ) + φ p).toNat
  have hw : ∀ p, (w p : ℤ) = ((X / 2 : ℕ) : ℤ) + φ p := fun p =>
    Int.toNat_of_nonneg (by have := hφb p; omega)
  refine ⟨w, fun p => ?_, ?_, ?_⟩
  · have h1 := hw p
    have h2 := hφb p
    have : (w p : ℤ) < X := by push_cast at h1 h2 ⊢; omega
    exact_mod_cast this
  · -- the Kronecker value regrouped by exponent
    have hmaps : ∀ a ∈ D, ex W s a.1 a.2 ∈ range M := fun a ha =>
      Finset.mem_range.2 (ex_lt (Finset.mem_product.1 ha).2 hW
        (by have := Finset.mem_range.1 (Finset.mem_product.1 ha).1; omega))
    have hkv : kv X W s q f = ∑ p ∈ range M, φ p * (X : ℤ) ^ p := by
      rw [kv_eq, ← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun p _ => ?_
      show _ = (∑ a ∈ D.filter (fun a => ex W s a.1 a.2 = p), f a.1 a.2) * (X : ℤ) ^ p
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [(Finset.mem_filter.1 ha).2]
    rw [hkv, excess]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw p]; ring
  · intro n hn k hk
    rw [hw]
    congr 1
    have hfiber : D.filter (fun a => ex W s a.1 a.2 = ex W s n k) = {(n, k)} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hae⟩
        obtain ⟨h1, h2⟩ := ex_inj hW (Finset.mem_product.1 ha).2 hk hae
        exact Prod.ext h1 h2
      · rintro rfl
        exact ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), hk⟩, rfl⟩
    show ∑ a ∈ D.filter (fun a => ex W s a.1 a.2 = ex W s n k), f a.1 a.2 = f n k
    rw [hfiber, Finset.sum_singleton]

end PVNP.Eval
