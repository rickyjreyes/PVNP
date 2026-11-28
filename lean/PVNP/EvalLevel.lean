import PVNP.EvalTaylor

/-!
# Bookkeeping for one order of the integer Taylor recurrence

* `kv_re`, `kv_im`, `kv_cprod_re_im`: the real and imaginary parts of the Kronecker value of a
  Gaussian-integer array, and the complex product on parts (`ac − bd`, `ad + bc`).
* `trunc'`, `supp_trunc'`, `kv_trunc'`: truncation after an order and its Kronecker value.
* `kv_succ`: the Kronecker value over orders `≤ n + 1` splits off the words of order `n + 1`.
* `modeOf`, `modeOf_mem`, `sum_box_eq`: the modes of the box `[−R, R]²` enumerated by one counter
  `p < (2R + 1)²`.
-/

namespace PVNP.Eval

open Finset PVNP.Torus

/-! ### Real and imaginary parts of Gaussian-integer Kronecker values -/

/-- The real part as an additive homomorphism. -/
def reHom : GaussianInt →+ ℤ := AddMonoidHom.mk' Zsqrtd.re Zsqrtd.re_add

/-- The imaginary part as an additive homomorphism. -/
def imHom : GaussianInt →+ ℤ := AddMonoidHom.mk' Zsqrtd.im Zsqrtd.im_add

theorem re_mul_int (z : GaussianInt) (m : ℤ) : (z * (m : GaussianInt)).re = z.re * m := by
  simp [Zsqrtd.re_mul]

theorem im_mul_int (z : GaussianInt) (m : ℤ) : (z * (m : GaussianInt)).im = z.im * m := by
  simp [Zsqrtd.im_mul]

theorem kv_re (X W s q : ℕ) (f : ℕ → Z2 → GaussianInt) :
    (kv X W s q f).re = kv X W s q (fun i k => (f i k).re) := by
  unfold kv
  have h := map_sum reHom (fun n => ∑ k ∈ box s, f n k * (X : GaussianInt) ^ ex W s n k)
    (range (q + 1))
  simp only [reHom, AddMonoidHom.mk'_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h2 := map_sum reHom (fun k => f n k * (X : GaussianInt) ^ ex W s n k) (box s)
  simp only [reHom, AddMonoidHom.mk'_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (X : GaussianInt) ^ ex W s n k = (((X : ℤ) ^ ex W s n k : ℤ) : GaussianInt) by
    push_cast; rfl, re_mul_int]

theorem kv_im (X W s q : ℕ) (f : ℕ → Z2 → GaussianInt) :
    (kv X W s q f).im = kv X W s q (fun i k => (f i k).im) := by
  unfold kv
  have h := map_sum imHom (fun n => ∑ k ∈ box s, f n k * (X : GaussianInt) ^ ex W s n k)
    (range (q + 1))
  simp only [imHom, AddMonoidHom.mk'_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h2 := map_sum imHom (fun k => f n k * (X : GaussianInt) ^ ex W s n k) (box s)
  simp only [imHom, AddMonoidHom.mk'_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (X : GaussianInt) ^ ex W s n k = (((X : ℤ) ^ ex W s n k : ℤ) : GaussianInt) by
    push_cast; rfl, im_mul_int]

/-- **The complex product on registers**: the real and imaginary parts of the Kronecker value of a
Cauchy–Fourier product are the real formulas `ac − bd` and `ad + bc` in the parts of the factors. -/
theorem kv_cprod_re_im (X W s t q q' : ℕ) {f g : ℕ → Z2 → GaussianInt} (hf : Supp s q f)
    (hg : Supp t q' g) :
    kv X W (s + t) (q + q') (fun i k => (cprod s f g i k).re) =
        kv X W s q (fun i k => (f i k).re) * kv X W t q' (fun i k => (g i k).re) -
          kv X W s q (fun i k => (f i k).im) * kv X W t q' (fun i k => (g i k).im) ∧
      kv X W (s + t) (q + q') (fun i k => (cprod s f g i k).im) =
        kv X W s q (fun i k => (f i k).re) * kv X W t q' (fun i k => (g i k).im) +
          kv X W s q (fun i k => (f i k).im) * kv X W t q' (fun i k => (g i k).re) := by
  have h := kv_mul X W s t q q' hf hg
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  rw [Zsqrtd.re_mul, kv_re, kv_re, kv_im, kv_im, kv_re] at hr
  rw [Zsqrtd.im_mul, kv_re, kv_re, kv_im, kv_im, kv_im] at hi
  constructor
  · rw [← hr]; ring
  · rw [← hi]

/-! ### Truncation in the Taylor index -/

/-- The series truncated after the order `n`. -/
def trunc' {R' : Type*} [Zero R'] (n : ℕ) (f : ℕ → Z2 → R') : ℕ → Z2 → R' :=
  fun i k => if i ≤ n then f i k else 0

theorem supp_trunc' {R' : Type*} [CommRing R'] {s : ℕ} {f : ℕ → Z2 → R'} (hf : BoxSupp s f) (n : ℕ) :
    Supp s n (trunc' n f) := by
  intro i k h
  unfold trunc'
  split_ifs with hi
  · rcases h with h | h
    · omega
    · exact hf i k h
  · rfl

theorem kv_trunc' {R' : Type*} [CommRing R'] (X W s n : ℕ) (f : ℕ → Z2 → R') :
    kv X W s n (trunc' n f) = kv X W s n f := by
  unfold kv
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k _ => ?_
  have : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [trunc', this]

/-- **The newest level**: the Kronecker value over orders `≤ n + 1` is that over orders `≤ n` plus
the words of order `n + 1`. -/
theorem kv_succ {R' : Type*} [CommRing R'] (X W s n : ℕ) (f : ℕ → Z2 → R') :
    kv X W s (n + 1) f = kv X W s n f + ∑ k ∈ box s, f (n + 1) k * (X : R') ^ ex W s (n + 1) k := by
  unfold kv
  rw [Finset.sum_range_succ]

/-! ### Enumerating the box by one counter -/

/-- The mode of counter value `p`: `(p mod (2R+1) − R, ⌊p / (2R+1)⌋ − R)`. -/
def modeOf (R p : ℕ) : Z2 := ((p % (2 * R + 1) : ℕ) - (R : ℤ), (p / (2 * R + 1) : ℕ) - (R : ℤ))

theorem modeOf_mem (R p : ℕ) (hp : p < (2 * R + 1) * (2 * R + 1)) : modeOf R p ∈ box R := by
  rw [mem_box]
  have h1 : p % (2 * R + 1) < 2 * R + 1 := Nat.mod_lt _ (by omega)
  have h2 : p / (2 * R + 1) < 2 * R + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
  simp only [modeOf]
  generalize p % (2 * R + 1) = A at h1 ⊢
  generalize p / (2 * R + 1) = B at h2 ⊢
  omega

/-- **Sums over the box are sums over the counter.** -/
theorem sum_box_eq {M : Type*} [AddCommMonoid M] (R : ℕ) (G : Z2 → M) :
    ∑ k ∈ box R, G k = ∑ p ∈ range ((2 * R + 1) * (2 * R + 1)), G (modeOf R p) := by
  symm
  refine Finset.sum_nbij' (modeOf R)
    (fun k => ((k.1 + R).toNat + (2 * R + 1) * (k.2 + R).toNat)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact modeOf_mem R p (Finset.mem_range.1 hp)
  · intro k hk
    rw [mem_box] at hk
    simp only [Finset.mem_range]
    have h1 : (k.1 + R).toNat ≤ 2 * R := by omega
    have h2 : (k.2 + R).toNat ≤ 2 * R := by omega
    nlinarith
  · intro p _
    simp only [modeOf]
    have hdm := Nat.mod_add_div p (2 * R + 1)
    generalize p % (2 * R + 1) = A at hdm ⊢
    generalize p / (2 * R + 1) = B at hdm ⊢
    have hA' : ((A : ℤ) - R + R).toNat = A := by omega
    have hB' : ((B : ℤ) - R + R).toNat = B := by omega
    rw [hA', hB', hdm]
  · intro k hk
    rw [mem_box] at hk
    have h1 : (k.1 + R).toNat < 2 * R + 1 := by omega
    have h0 : 0 < 2 * R + 1 := by omega
    simp only [modeOf]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.add_mul_div_left _ _ h0,
      Nat.div_eq_of_lt h1, zero_add]
    refine Prod.ext ?_ ?_
    · show ((k.1 + R).toNat : ℤ) - R = k.1
      omega
    · show ((k.2 + R).toNat : ℤ) - R = k.2
      omega
  · intro p _
    rfl

end PVNP.Eval
