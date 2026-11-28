import PVNP.GalerkinTaylorSeries
import PVNP.EvalKron

/-!
# The Galerkin Taylor coefficients as an exact integer recurrence

The certified Taylor integrator (`TaylorIntegrator.certified_integrator`) needs each step
`Σ_{n ≤ q} hⁿ c_n(v)` of the Galerkin system, where `c_n = GalerkinTaylor.coeff` are defined
through `mulH`, `conjH`, `Aop` and `trunc` on `ℓ²`. This module rewrites that recurrence as an
**exact recurrence on Gaussian integers**, the form computed by the register-machine evaluator.

* `co_coeff_succ`: the Fourier coefficients `a_n = co L c_n` of data supported on the box
  `[−R, R]²` satisfy
  `a_{n+1} = (n+1)⁻¹ (−i) (ω a_n + 𝟙_box (−β L⁻² ((a a) ā)_n + γ L⁻⁴ ((((a a) a) ā) ā)_n))`
  with explicit Cauchy–Fourier products (`cprod`, `EvalKron`) in the order of `fnlCoeff`
  (`co_cauchyH`, `pr_box`, `co_coeff_supp`).
* `gstep`, `gco`: the integer recurrence `C_{n+1} = −i (μ_n W_k C_n + 𝟙_box (−ν_n cub + ξ_n quin))`
  over `ℤ[i]`, with dispersion numerators `W_k` and integer scalars `μ_n, ν_n, ξ_n`
  (`gpre_eq`, `gco_succ`, `gstep_congr`).
* `gco_eq`, **the bridge**: if `W_k = d_ω ω_k` on the box, `μ_n (n + 1) d_ω = B`,
  `ν_n (n + 1) A² = B β / L²`, `ξ_n (n + 1) A⁴ = B γ / L⁴`, and the initial array is `A` times the
  Fourier coefficients of the data, then **`C_n = A Bⁿ a_n` exactly, for every order `n`**.
  The proof scales the nested products (`cub_scale`, `quin_scale`) and transports them along
  `ℤ[i] → ℂ` (`map_cub`, `map_quin`).
-/

namespace PVNP.Eval

open Finset PVNP.Torus PVNP.GalerkinTaylor PVNP.TorusGalerkin Complex

variable {L : ℝ}

/-! ### Fourier coefficients of the Galerkin Taylor coefficients -/

theorem co_sum' (L : ℝ) {ι : Type*} (s : Finset ι) (v : ι → ℓ2) :
    co L (∑ i ∈ s, v i) = ∑ i ∈ s, co L (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [co_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, ih]

theorem co_trunc' (S : Finset Z2) (v : ℓ2) (k : Z2) :
    co L (trunc S v) k = if k ∈ S then co L v k else 0 := by
  unfold co; rw [trunc_apply]; split_ifs <;> simp

theorem co_Aop (κ : ℝ) (S : Finset Z2) (v : ℓ2) (k : Z2) :
    co L (Aop L κ S v) k = omMul L κ S k * co L v k := by
  unfold co; rw [Aop_apply]; ring

/-- Supported in a box, in every Taylor order. -/
def BoxSupp {R : Type*} [Zero R] (s : ℕ) (f : ℕ → Z2 → R) : Prop := ∀ n k, k ∉ box s → f n k = 0

theorem boxSupp_cprod {R : Type*} [CommRing R] {s t : ℕ} (f : ℕ → Z2 → R) {g : ℕ → Z2 → R}
    (hg : BoxSupp t g) : BoxSupp (s + t) (cprod s f g) := by
  intro n k hk
  unfold cprod
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  have : k - j ∉ box t := fun h => hk (by
    have := add_mem_box hj h
    rwa [add_sub_cancel] at this)
  rw [hg (n - i) (k - j) this, mul_zero]

theorem neg_mem_box {s : ℕ} {k : Z2} (hk : k ∈ box s) : -k ∈ box s := by
  rw [mem_box] at hk ⊢
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

/-- `pr` with a first factor supported in a box is a finite sum over the box. -/
theorem pr_box {a b : Z2 → ℂ} {s : ℕ} (ha : ∀ j, j ∉ box s → a j = 0) (k : Z2) :
    pr L a b k = (L : ℂ)⁻¹ * ∑ j ∈ box s, a j * b (k - j) := by
  unfold pr
  congr 1
  have e : (fun j => a (k - j) * b j) =
      fun j => (fun j' => a j' * b (k - j')) (Equiv.subLeft k j) := by
    funext j; simp [Equiv.subLeft_apply]
  rw [e, Equiv.tsum_eq (Equiv.subLeft k) (fun j' => a j' * b (k - j'))]
  exact tsum_eq_sum (fun j hj => by rw [ha j hj, zero_mul])

/-- **The Fourier coefficients of a Cauchy product of Galerkin states** are `L⁻¹` times the
Cauchy–Fourier product of their Fourier coefficients. -/
theorem co_cauchyH (hL : 0 < L) {X Y : ℕ → ℓ2} {s : ℕ}
    (hX : ∀ i j, j ∉ box s → co L (X i) j = 0) (n : ℕ) (k : Z2) :
    co L (cauchyH L X Y n) k =
      (L : ℂ)⁻¹ * cprod s (fun i => co L (X i)) (fun i => co L (Y i)) n k := by
  unfold cauchyH cprod
  rw [co_sum', Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [co_mulH hL, pr_box (hX i)]

theorem cprod_congr {R : Type*} [CommRing R] (s : ℕ) {f f' g g' : ℕ → Z2 → R} {n : ℕ}
    (hf : ∀ i ≤ n, f i = f' i) (hg : ∀ i ≤ n, g i = g' i) (k : Z2) :
    cprod s f g n k = cprod s f' g' n k := by
  unfold cprod
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hf i hin, hg (n - i) (by omega)]

/-- Geometric weights factor out of a Cauchy–Fourier product. -/
theorem cprod_scale {R : Type*} [CommRing R] (s : ℕ) (f g : ℕ → Z2 → R) (x x' y : R) (n : ℕ)
    (k : Z2) :
    cprod s (fun i j => x * y ^ i * f i j) (fun i j => x' * y ^ i * g i j) n k =
      x * x' * y ^ n * cprod s f g n k := by
  unfold cprod
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : y ^ n = y ^ i * y ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hin]
  rw [this]; ring

theorem cprod_smul_left {R : Type*} [CommRing R] (s : ℕ) (f g : ℕ → Z2 → R) (c : R) (n : ℕ)
    (k : Z2) : cprod s (fun i j => c * f i j) g n k = c * cprod s f g n k := by
  unfold cprod
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cprod_smul_right {R : Type*} [CommRing R] (s : ℕ) (f g : ℕ → Z2 → R) (c : R) (n : ℕ)
    (k : Z2) : cprod s f (fun i j => c * g i j) n k = c * cprod s f g n k := by
  unfold cprod
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Ring homomorphisms commute with Cauchy–Fourier products. -/
theorem map_cprod {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : ℕ)
    (f g : ℕ → Z2 → R) (n : ℕ) (k : Z2) :
    φ (cprod s f g n k) = cprod s (fun i j => φ (f i j)) (fun i j => φ (g i j)) n k := by
  unfold cprod
  simp only [map_sum, map_mul]

theorem co_rsmul (r : ℝ) (v : ℓ2) (k : Z2) : co L (r • v) k = (r : ℂ) * co L v k := by
  unfold co
  rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
  ring

theorem co_csmul (c : ℂ) (v : ℓ2) (k : Z2) : co L (c • v) k = c * co L v k := by
  rw [co_smul]; rfl

theorem co_add' (v w : ℓ2) (k : Z2) : co L (v + w) k = co L v k + co L w k := by
  rw [co_add]; rfl

/-- The Galerkin Taylor coefficients of data supported on the box stay on the box. -/
theorem coeff_supported (κ β γ : ℝ) (R : ℕ) {u₀ : ℓ2} (hu : Supported (box R) u₀) :
    ∀ n, Supported (box R) (coeff L κ β γ (box R) u₀ n)
  | 0 => by rw [coeff_zero]; exact hu
  | n + 1 => by
    intro k hk
    rw [coeff_succ]
    simp only [rhs, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_add, Pi.add_apply, Aop_apply,
      trunc_apply, omMul, if_neg hk]
    simp

theorem co_coeff_supp (κ β γ : ℝ) (R : ℕ) {u₀ : ℓ2} (hu : Supported (box R) u₀) :
    BoxSupp R (fun i => co L (coeff L κ β γ (box R) u₀ i)) := by
  intro n k hk
  show co L (coeff L κ β γ (box R) u₀ n) k = 0
  unfold co
  rw [coeff_supported κ β γ R hu n k hk, zero_div]

theorem rev_boxSupp {s : ℕ} {f : ℕ → Z2 → ℂ} (hf : BoxSupp s f) :
    BoxSupp s (fun i => rev (f i)) := by
  intro n k hk
  show (starRingEnd ℂ) (f n (-k)) = 0
  rw [hf n (-k) (fun h => hk (by have := neg_mem_box h; rwa [neg_neg] at this)), map_zero]

/-- **The recurrence of the Fourier coefficients** of the Galerkin Taylor coefficients, with the
nonlinearity written as explicit Cauchy–Fourier products in the order of `fnlCoeff`. -/
theorem co_coeff_succ (hL : 0 < L) (κ β γ : ℝ) (R : ℕ) {u₀ : ℓ2} (hu : Supported (box R) u₀)
    (n : ℕ) (k : Z2) :
    co L (coeff L κ β γ (box R) u₀ (n + 1)) k =
      (((n : ℝ) + 1)⁻¹ : ℂ) * (-I) * (omMul L κ (box R) k * co L (coeff L κ β γ (box R) u₀ n) k +
        if k ∈ box R then
          -(β : ℂ) * ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) *
            cprod (2 * R) (cprod R (fun i => co L (coeff L κ β γ (box R) u₀ i))
              (fun i => co L (coeff L κ β γ (box R) u₀ i)))
              (fun i => rev (co L (coeff L κ β γ (box R) u₀ i))) n k +
          (γ : ℂ) * ((L : ℂ)⁻¹ * (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * (L : ℂ)⁻¹) *
            cprod (4 * R) (cprod (3 * R) (cprod (2 * R)
              (cprod R (fun i => co L (coeff L κ β γ (box R) u₀ i))
                (fun i => co L (coeff L κ β γ (box R) u₀ i)))
              (fun i => co L (coeff L κ β γ (box R) u₀ i)))
              (fun i => rev (co L (coeff L κ β γ (box R) u₀ i))))
              (fun i => rev (co L (coeff L κ β γ (box R) u₀ i))) n k
        else 0) := by
  set c := coeff L κ β γ (box R) u₀
  set a : ℕ → Z2 → ℂ := fun i => co L (c i)
  have ha : BoxSupp R a := co_coeff_supp κ β γ R hu
  have hcf : (fun i => co L (c i)) = a := rfl
  -- the Fourier coefficients of the nested Cauchy products
  have hQ1 : ∀ i j, co L (cauchyH L c c i) j = (L : ℂ)⁻¹ * cprod R a a i j := fun i j =>
    co_cauchyH hL (fun i j hj => ha i j hj) i j
  have hQ1f : (fun i => co L (cauchyH L c c i)) = fun i j => (L : ℂ)⁻¹ * cprod R a a i j :=
    funext fun i => funext fun j => hQ1 i j
  have hQ1s : BoxSupp (2 * R) (fun i => co L (cauchyH L c c i)) := by
    rw [hQ1f]; intro i j hj; dsimp only
    rw [boxSupp_cprod (s := R) a ha i j (by rwa [show R + R = 2 * R by ring]), mul_zero]
  have hconjf : (fun i => co L (conjSeq c i)) = fun i => rev (a i) :=
    funext fun i => co_conjH L (c i)
  have hQ2 : ∀ i j, co L (cauchyH L (cauchyH L c c) c i) j =
      (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * cprod (2 * R) (cprod R a a) a i j) := by
    intro i j
    rw [co_cauchyH hL (fun i j hj => hQ1s i j hj), hQ1f, hcf, cprod_smul_left]
  have hQ2f : (fun i => co L (cauchyH L (cauchyH L c c) c i)) =
      fun i j => (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * cprod (2 * R) (cprod R a a) a i j) :=
    funext fun i => funext fun j => hQ2 i j
  have hQ2s : BoxSupp (3 * R) (fun i => co L (cauchyH L (cauchyH L c c) c i)) := by
    rw [hQ2f]; intro i j hj; dsimp only
    rw [boxSupp_cprod (s := 2 * R) (cprod R a a) ha i j
      (by rwa [show 2 * R + R = 3 * R by ring]), mul_zero, mul_zero]
  have hQ3 : ∀ i j, co L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c) i) j =
      (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * ((L : ℂ)⁻¹ *
        cprod (3 * R) (cprod (2 * R) (cprod R a a) a) (fun i => rev (a i)) i j)) := by
    intro i j
    rw [co_cauchyH hL (fun i j hj => hQ2s i j hj), hQ2f, hconjf, cprod_smul_left,
      cprod_smul_left]
  have hQ3f : (fun i => co L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c) i)) =
      fun i j => (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * ((L : ℂ)⁻¹ *
        cprod (3 * R) (cprod (2 * R) (cprod R a a) a) (fun i => rev (a i)) i j)) :=
    funext fun i => funext fun j => hQ3 i j
  have hrev : BoxSupp R (fun i => rev (a i)) := rev_boxSupp ha
  have hQ3s : BoxSupp (4 * R) (fun i => co L (cauchyH L (cauchyH L (cauchyH L c c) c)
      (conjSeq c) i)) := by
    rw [hQ3f]; intro i j hj; dsimp only
    rw [boxSupp_cprod (s := 3 * R) (cprod (2 * R) (cprod R a a) a) hrev i j
      (by rwa [show 3 * R + R = 4 * R by ring]), mul_zero, mul_zero, mul_zero]
  have hcub : co L (cauchyH L (cauchyH L c c) (conjSeq c) n) k =
      (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * cprod (2 * R) (cprod R a a) (fun i => rev (a i)) n k) := by
    rw [co_cauchyH hL (fun i j hj => hQ1s i j hj), hQ1f, hconjf, cprod_smul_left]
  have hquin : co L (cauchyH L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c))
      (conjSeq c) n) k =
      (L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * ((L : ℂ)⁻¹ * ((L : ℂ)⁻¹ *
        cprod (4 * R) (cprod (3 * R) (cprod (2 * R) (cprod R a a) a) (fun i => rev (a i)))
          (fun i => rev (a i)) n k))) := by
    rw [co_cauchyH hL (fun i j hj => hQ3s i j hj), hQ3f, hconjf, cprod_smul_left,
      cprod_smul_left, cprod_smul_left]
  -- assemble
  have hs : c (n + 1) = ((n : ℝ) + 1)⁻¹ • rhs L κ β γ (box R) c n :=
    coeff_succ L κ β γ (box R) u₀ n
  rw [hs, co_rsmul]
  simp only [rhs]
  rw [co_csmul, co_add', co_Aop, co_trunc']
  split_ifs with hk
  · simp only [fnlCoeff]
    rw [co_add', co_csmul, co_csmul, hcub, hquin]
    push_cast
    ring
  · push_cast
    ring

/-! ### The cubic and quintic products over a commutative ring -/

/-- The cubic product `((f f) f̄)` for a conjugation-reflection `r`. -/
def cub {R' : Type*} [CommRing R'] (R : ℕ) (f r : ℕ → Z2 → R') : ℕ → Z2 → R' :=
  cprod (2 * R) (cprod R f f) r

/-- The quintic product `((((f f) f) f̄) f̄)`. -/
def quin {R' : Type*} [CommRing R'] (R : ℕ) (f r : ℕ → Z2 → R') : ℕ → Z2 → R' :=
  cprod (4 * R) (cprod (3 * R) (cprod (2 * R) (cprod R f f) f) r) r

theorem cprod_congr' {R' : Type*} [CommRing R'] (s : ℕ) {f f' g g' : ℕ → Z2 → R'} {n : ℕ}
    (hf : ∀ i ≤ n, ∀ j, f i j = f' i j) (hg : ∀ i ≤ n, ∀ j, g i j = g' i j) :
    ∀ i ≤ n, ∀ j, cprod s f g i j = cprod s f' g' i j := by
  intro i hi j
  exact cprod_congr s (fun i' hi' => funext (hf i' (by omega)))
    (fun i' hi' => funext (hg i' (by omega))) j

theorem cub_congr {R' : Type*} [CommRing R'] (R : ℕ) {f f' r r' : ℕ → Z2 → R'} {n : ℕ}
    (hf : ∀ i ≤ n, ∀ j, f i j = f' i j) (hr : ∀ i ≤ n, ∀ j, r i j = r' i j) (k : Z2) :
    cub R f r n k = cub R f' r' n k :=
  cprod_congr' _ (cprod_congr' _ hf hf) hr n le_rfl k

theorem quin_congr {R' : Type*} [CommRing R'] (R : ℕ) {f f' r r' : ℕ → Z2 → R'} {n : ℕ}
    (hf : ∀ i ≤ n, ∀ j, f i j = f' i j) (hr : ∀ i ≤ n, ∀ j, r i j = r' i j) (k : Z2) :
    quin R f r n k = quin R f' r' n k :=
  cprod_congr' _ (cprod_congr' _ (cprod_congr' _ (cprod_congr' _ hf hf) hf) hr) hr n le_rfl k

theorem cprod_scale' {R' : Type*} [CommRing R'] (s : ℕ) (f g : ℕ → Z2 → R') (x x' y : R') :
    cprod s (fun i j => x * y ^ i * f i j) (fun i j => x' * y ^ i * g i j) =
      fun i j => x * x' * y ^ i * cprod s f g i j :=
  funext fun i => funext fun j => cprod_scale s f g x x' y i j

theorem cub_scale {R' : Type*} [CommRing R'] (R : ℕ) (f r : ℕ → Z2 → R') (x y : R') (n : ℕ)
    (k : Z2) :
    cub R (fun i j => x * y ^ i * f i j) (fun i j => x * y ^ i * r i j) n k =
      x * x * x * y ^ n * cub R f r n k := by
  unfold cub
  rw [cprod_scale', cprod_scale]

theorem quin_scale {R' : Type*} [CommRing R'] (R : ℕ) (f r : ℕ → Z2 → R') (x y : R') (n : ℕ)
    (k : Z2) :
    quin R (fun i j => x * y ^ i * f i j) (fun i j => x * y ^ i * r i j) n k =
      x * x * x * x * x * y ^ n * quin R f r n k := by
  unfold quin
  rw [cprod_scale', cprod_scale', cprod_scale', cprod_scale]

theorem map_cub {R' S' : Type*} [CommRing R'] [CommRing S'] (φ : R' →+* S') (R : ℕ)
    (f r : ℕ → Z2 → R') (n : ℕ) (k : Z2) :
    φ (cub R f r n k) = cub R (fun i j => φ (f i j)) (fun i j => φ (r i j)) n k := by
  unfold cub
  rw [map_cprod]
  congr 1
  funext i j
  rw [map_cprod]

theorem map_quin {R' S' : Type*} [CommRing R'] [CommRing S'] (φ : R' →+* S') (R : ℕ)
    (f r : ℕ → Z2 → R') (n : ℕ) (k : Z2) :
    φ (quin R f r n k) = quin R (fun i j => φ (f i j)) (fun i j => φ (r i j)) n k := by
  unfold quin
  rw [map_cprod]
  congr 1
  funext i j
  rw [map_cprod]
  congr 1
  funext i j
  rw [map_cprod]
  congr 1
  funext i j
  rw [map_cprod]

/-! ### The scaled integer recurrence -/

/-- Conjugate reflection of each Taylor coefficient of a Gaussian-integer array. -/
def grev (f : ℕ → Z2 → GaussianInt) : ℕ → Z2 → GaussianInt := fun n k => star (f n (-k))

/-- `−i` as a Gaussian integer. -/
def negI : GaussianInt := ⟨0, -1⟩

/-- **One order of the scaled integer recurrence**: from the integer coefficients of orders
`≤ n`, the coefficient of order `n + 1` at the mode `k`. -/
def gstep (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℤ) (C : ℕ → Z2 → GaussianInt) (n : ℕ) (k : Z2) :
    GaussianInt :=
  negI * (((μ * Wd k : ℤ) : GaussianInt) * C n k +
    if k ∈ box R then ((-ν : ℤ) : GaussianInt) * cub R C (grev C) n k +
      ((ξ : ℤ) : GaussianInt) * quin R C (grev C) n k else 0)

/-- Prefixes of the integer coefficient sequence. -/
def gpre (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℕ → ℤ) (C0 : Z2 → GaussianInt) :
    ℕ → ℕ → Z2 → GaussianInt
  | 0 => fun i k => if i = 0 then C0 k else 0
  | n + 1 => fun i k => if i ≤ n then gpre R Wd μ ν ξ C0 n i k
      else if i = n + 1 then gstep R Wd (μ n) (ν n) (ξ n) (gpre R Wd μ ν ξ C0 n) n k else 0

/-- **The scaled integer Taylor coefficients.** -/
def gco (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℕ → ℤ) (C0 : Z2 → GaussianInt) (n : ℕ) :
    Z2 → GaussianInt :=
  gpre R Wd μ ν ξ C0 n n

theorem gpre_eq (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℕ → ℤ) (C0 : Z2 → GaussianInt) :
    ∀ n i, i ≤ n → gpre R Wd μ ν ξ C0 n i = gco R Wd μ ν ξ C0 i := by
  intro n
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · funext k
      show (if i ≤ n then _ else _) = _
      rw [if_pos (by omega), ih i (by omega)]
    · obtain rfl : i = n + 1 := by omega
      rfl

theorem gstep_congr (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℤ) {C C' : ℕ → Z2 → GaussianInt} {n : ℕ}
    (h : ∀ i ≤ n, ∀ j, C i j = C' i j) (k : Z2) :
    gstep R Wd μ ν ξ C n k = gstep R Wd μ ν ξ C' n k := by
  have hr : ∀ i ≤ n, ∀ j, grev C i j = grev C' i j := fun i hi j => by
    unfold grev; rw [h i hi]
  unfold gstep
  rw [h n le_rfl, cub_congr R h hr, quin_congr R h hr]

theorem gco_succ (R : ℕ) (Wd : Z2 → ℤ) (μ ν ξ : ℕ → ℤ) (C0 : Z2 → GaussianInt) (n : ℕ) :
    gco R Wd μ ν ξ C0 (n + 1) =
      gstep R Wd (μ n) (ν n) (ξ n) (fun i => gco R Wd μ ν ξ C0 i) n := by
  funext k
  show (if n + 1 ≤ n then _ else if n + 1 = n + 1 then _ else _) = _
  rw [if_neg (by omega), if_pos rfl]
  exact gstep_congr R Wd _ _ _ (fun i hi j => by rw [gpre_eq R Wd μ ν ξ C0 n i hi]) k

theorem toComplex_negI : ((negI : GaussianInt) : ℂ) = -I := by
  rw [negI, GaussianInt.toComplex_def']; push_cast; ring

theorem toComplex_grev (C : ℕ → Z2 → GaussianInt) (i : ℕ) (j : Z2) :
    ((grev C i j : GaussianInt) : ℂ) = rev (fun j => (C i j : ℂ)) j := by
  rw [grev, GaussianInt.toComplex_star]; rfl

theorem rev_real_smul (x : ℝ) (f : Z2 → ℂ) (j : Z2) :
    rev (fun j => (x : ℂ) * f j) j = (x : ℂ) * rev f j := by
  simp only [rev, map_mul, Complex.conj_ofReal]

/-- **The integer recurrence computes the Galerkin Taylor coefficients exactly.** Suppose the
dispersion numerators are `W_k = d_ω ω_k` on the box, and the integer scalars of order `n` satisfy
`μ_n (n + 1) d_ω = B`, `ν_n (n + 1) A² = B β / L²` and `ξ_n (n + 1) A⁴ = B γ / L⁴`. If the initial
integer array is `A` times the Fourier coefficients of the data, then the integer coefficient of
order `n` is `A Bⁿ` times the Fourier coefficients of the Galerkin Taylor coefficient of order `n`,
for every `n`. -/
theorem gco_eq (hL : 0 < L) (κ β γ : ℝ) (R : ℕ) {u₀ : ℓ2} (hu : Supported (box R) u₀)
    (Wd : Z2 → ℤ) (μ ν ξ : ℕ → ℤ) (C0 : Z2 → GaussianInt) (A B dω : ℝ)
    (hW : ∀ k ∈ box R, (Wd k : ℝ) = dω * om L κ k)
    (hμ : ∀ n : ℕ, (μ n : ℝ) * ((n : ℝ) + 1) * dω = B)
    (hν : ∀ n : ℕ, (ν n : ℝ) * ((n : ℝ) + 1) * A ^ 2 = B * β / L ^ 2)
    (hξ : ∀ n : ℕ, (ξ n : ℝ) * ((n : ℝ) + 1) * A ^ 4 = B * γ / L ^ 4)
    (h0 : ∀ k, (C0 k : ℂ) = (A : ℂ) * co L u₀ k) :
    ∀ n k, (gco R Wd μ ν ξ C0 n k : ℂ) =
      (A : ℂ) * (B : ℂ) ^ n * co L (coeff L κ β γ (box R) u₀ n) k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · intro k
    rw [pow_zero, mul_one, coeff_zero]
    exact h0 k
  · intro k
    set a : ℕ → Z2 → ℂ := fun i => co L (coeff L κ β γ (box R) u₀ i) with ha_def
    have ha : BoxSupp R a := co_coeff_supp κ β γ R hu
    have hG : ∀ i ≤ n, ∀ j, (gco R Wd μ ν ξ C0 i j : ℂ) = (A : ℂ) * (B : ℂ) ^ i * a i j :=
      fun i hi j => ih i (by omega) j
    have hGr : ∀ i ≤ n, ∀ j, ((grev (fun i => gco R Wd μ ν ξ C0 i) i j : GaussianInt) : ℂ) =
        (A : ℂ) * (B : ℂ) ^ i * rev (a i) j := by
      intro i hi j
      rw [toComplex_grev]
      have e : (fun j => (gco R Wd μ ν ξ C0 i j : ℂ)) = fun j => ((A * B ^ i : ℝ) : ℂ) * a i j :=
        funext fun j => by rw [hG i hi j]; push_cast; ring
      rw [e, rev_real_smul]; push_cast; ring
    -- the cubic and quintic terms
    have hcub : ((cub R (fun i => gco R Wd μ ν ξ C0 i) (grev (fun i => gco R Wd μ ν ξ C0 i)) n k :
        GaussianInt) : ℂ) = (A : ℂ) * A * A * (B : ℂ) ^ n * cub R a (fun i => rev (a i)) n k := by
      rw [map_cub GaussianInt.toComplex]
      rw [cub_congr R (f' := fun i j => (A : ℂ) * (B : ℂ) ^ i * a i j)
        (r' := fun i j => (A : ℂ) * (B : ℂ) ^ i * rev (a i) j) hG hGr]
      exact cub_scale R a (fun i => rev (a i)) _ _ n k
    have hquin : ((quin R (fun i => gco R Wd μ ν ξ C0 i) (grev (fun i => gco R Wd μ ν ξ C0 i)) n k :
        GaussianInt) : ℂ) =
          (A : ℂ) * A * A * A * A * (B : ℂ) ^ n * quin R a (fun i => rev (a i)) n k := by
      rw [map_quin GaussianInt.toComplex]
      rw [quin_congr R (f' := fun i j => (A : ℂ) * (B : ℂ) ^ i * a i j)
        (r' := fun i j => (A : ℂ) * (B : ℂ) ^ i * rev (a i) j) hG hGr]
      exact quin_scale R a (fun i => rev (a i)) _ _ n k
    -- the coefficient identities
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hL0 : (L : ℝ) ≠ 0 := hL.ne'
    rw [gco_succ, gstep, GaussianInt.toComplex_mul, toComplex_negI, GaussianInt.toComplex_add,
      GaussianInt.toComplex_mul, map_intCast, hG n le_rfl k]
    rw [co_coeff_succ hL κ β γ R hu n k]
    by_cases hk : k ∈ box R
    · rw [if_pos hk, if_pos hk, GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
        GaussianInt.toComplex_mul, map_intCast, map_intCast, hcub, hquin]
      simp only [omMul, if_pos hk]
      have e1 : (μ n : ℂ) * (Wd k : ℂ) = (B : ℂ) * ((n : ℂ) + 1)⁻¹ * (om L κ k : ℂ) := by
        have : ((μ n : ℝ) * (Wd k : ℝ)) = B * ((n : ℝ) + 1)⁻¹ * om L κ k := by
          rw [hW k hk, ← hμ n]; field_simp
        have h := congrArg (fun x : ℝ => (x : ℂ)) this
        push_cast at h
        linear_combination h
      have e2 : (ν n : ℂ) * ((A : ℂ) * A) = (B : ℂ) * ((n : ℂ) + 1)⁻¹ * (β : ℂ) / (L : ℂ) ^ 2 := by
        have : ((ν n : ℝ) * (A * A)) = B * ((n : ℝ) + 1)⁻¹ * β / L ^ 2 := by
          rw [show (B * ((n : ℝ) + 1)⁻¹ * β / L ^ 2) = (B * β / L ^ 2) * ((n : ℝ) + 1)⁻¹ by ring,
            ← hν n]; field_simp
        have h := congrArg (fun x : ℝ => (x : ℂ)) this
        push_cast at h
        linear_combination h
      have e3 : (ξ n : ℂ) * ((A : ℂ) * A * A * A) =
          (B : ℂ) * ((n : ℂ) + 1)⁻¹ * (γ : ℂ) / (L : ℂ) ^ 4 := by
        have : ((ξ n : ℝ) * (A * A * A * A)) = B * ((n : ℝ) + 1)⁻¹ * γ / L ^ 4 := by
          rw [show (B * ((n : ℝ) + 1)⁻¹ * γ / L ^ 4) = (B * γ / L ^ 4) * ((n : ℝ) + 1)⁻¹ by ring,
            ← hξ n]; field_simp
        have h := congrArg (fun x : ℝ => (x : ℂ)) this
        push_cast at h
        linear_combination h
      push_cast
      unfold cub quin at *
      linear_combination (-I * (A : ℂ) * (B : ℂ) ^ n * a n k) * e1 +
        (I * (A : ℂ) * (B : ℂ) ^ n * cprod (2 * R) (cprod R a a) (fun i => rev (a i)) n k) * e2 +
        (-I * (A : ℂ) * (B : ℂ) ^ n * cprod (4 * R) (cprod (3 * R) (cprod (2 * R) (cprod R a a) a)
          (fun i => rev (a i))) (fun i => rev (a i)) n k) * e3
    · rw [if_neg hk, if_neg hk]
      simp only [omMul, if_neg hk]
      rw [ha n k hk]
      simp

end PVNP.Eval
