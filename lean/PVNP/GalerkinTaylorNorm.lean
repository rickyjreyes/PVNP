import PVNP.TaylorMajorant
import PVNP.TorusNonlin

/-!
# The frozen nonlinearity obeys the cubic–quintic Taylor majorant

Formal Taylor coefficients of `Fnl(u(t))` along a coefficient sequence `c_n` of `u(t)` are
built from the same products as `Fnl` itself:
`[Fnl]_n = −β [mulH(mulH(c,c), conj c)]_n + γ [mulH(mulH(mulH(mulH(c,c),c), conj c), conj c)]_n`,
where `[mulH(X,Y)]_n = Σ_{i≤n} mulH(X_i, Y_{n−i})` (`cauchyH`) and `conj` acts coefficientwise.
This is `fnlCoeff`.

* `norm_fnlCoeff_le`: `‖[Fnl]_n‖ ≤ |β| C_A² (a⋆a⋆a)_n + |γ| C_A⁴ (a⋆a⋆a⋆a⋆a)_n` for
  `a_n = ‖c_n‖`. The proof uses only the `H²` algebra bound `norm_mulH_le`,
  `‖conjH v‖ = ‖v‖`, and commutativity and monotonicity of the scalar Cauchy product.
* `galerkin_taylor_majorant`: suppose `‖c_0‖ ≤ K` and the Galerkin Taylor recursion holds in
  norm form, `(n+1) ‖c_{n+1}‖ ≤ Ω ‖c_n‖ + ‖[Fnl]_n‖`. This is what
  `(n+1) c_{n+1} = −i(A c_n + P_S [Fnl]_n)` gives when `‖A v‖ ≤ Ω‖v‖` and `P_S` is a contraction.
  Then `‖c_n‖ ≤ K λ^n/(n+1)²` with
  `λ = 4(Ω + 64 |β| C_A² K² + 4096 |γ| C_A⁴ K⁴)`.

Scope. The recursion is a hypothesis on the coefficient sequence. The theorem bounds every
sequence obeying it, in particular the formal Taylor coefficients of the physical-picture
Galerkin system. Showing that the actual Galerkin trajectory equals the sum of that series
(analyticity of polynomial ODE flows) is not formalized here.
-/

namespace PVNP.GalerkinTaylor

open Finset PVNP.Torus PVNP.TaylorMajorant

variable {L : ℝ}

/-- Coefficientwise Cauchy product through `mulH`. -/
noncomputable def cauchyH (L : ℝ) (X Y : ℕ → ℓ2) (n : ℕ) : ℓ2 :=
  ∑ i ∈ range (n+1), mulH L (X i) (Y (n - i))

/-- Coefficientwise conjugation. -/
noncomputable def conjSeq (c : ℕ → ℓ2) : ℕ → ℓ2 := fun k => conjH (c k)

/-- Formal Taylor coefficients of the cubic–quintic nonlinearity along `c`. -/
noncomputable def fnlCoeff (L β γ : ℝ) (c : ℕ → ℓ2) (n : ℕ) : ℓ2 :=
  (-(β : ℂ)) • cauchyH L (cauchyH L c c) (conjSeq c) n +
    (γ : ℂ) • cauchyH L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c)) (conjSeq c) n

theorem cauchy_comm (a b : ℕ → ℝ) (n : ℕ) : cauchy a b n = cauchy b a n := by
  unfold cauchy
  have h := Finset.sum_range_reflect (fun i => b i * a (n - i)) (n+1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.sub_sub_self hin, mul_comm]

theorem cauchy_mono {a a' b b' : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (haa : ∀ k, a k ≤ a' k) (hbb : ∀ k, b k ≤ b' k) (n : ℕ) :
    cauchy a b n ≤ cauchy a' b' n :=
  Finset.sum_le_sum fun i _ =>
    mul_le_mul (haa i) (hbb _) (hb _) ((ha i).trans (haa i))

theorem cauchy_smul_left (s : ℝ) (a b : ℕ → ℝ) (n : ℕ) :
    cauchy (fun k => s * a k) b n = s * cauchy a b n := by
  unfold cauchy
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_cauchyH_le (hL : 0 < L) (X Y : ℕ → ℓ2) (n : ℕ) :
    ‖cauchyH L X Y n‖ ≤ CA L * cauchy (fun k => ‖X k‖) (fun k => ‖Y k‖) n := by
  unfold cauchyH cauchy
  rw [Finset.mul_sum]
  calc ‖∑ i ∈ range (n+1), mulH L (X i) (Y (n - i))‖
      ≤ ∑ i ∈ range (n+1), ‖mulH L (X i) (Y (n - i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n+1), CA L * (‖X i‖ * ‖Y (n - i)‖) :=
        Finset.sum_le_sum fun i _ => by
          have := norm_mulH_le hL (X i) (Y (n - i))
          linarith [this]

theorem norm_conjSeq (c : ℕ → ℓ2) (k : ℕ) : ‖conjSeq c k‖ = ‖c k‖ := norm_conjH _

/-- The norm sequence of a coefficient sequence. -/
noncomputable def nseq (c : ℕ → ℓ2) : ℕ → ℝ := fun k => ‖c k‖

theorem nseq_nonneg (c : ℕ → ℓ2) (k : ℕ) : 0 ≤ nseq c k := norm_nonneg _

/-- One level of the reduction: bounds on the factors give a bound on the product. -/
theorem cauchyH_step (hL : 0 < L) {X Y : ℕ → ℓ2} {p q : ℕ → ℝ}
    (hX : ∀ k, ‖X k‖ ≤ p k) (hY : ∀ k, ‖Y k‖ ≤ q k) (n : ℕ) :
    ‖cauchyH L X Y n‖ ≤ CA L * cauchy p q n := by
  have hC := CA_nonneg hL
  calc ‖cauchyH L X Y n‖ ≤ CA L * cauchy (fun k => ‖X k‖) (fun k => ‖Y k‖) n :=
        norm_cauchyH_le hL X Y n
    _ ≤ CA L * cauchy p q n :=
        mul_le_mul_of_nonneg_left
          (cauchy_mono (fun k => norm_nonneg _) (fun k => norm_nonneg _) hX hY n) hC

/-- **Norm reduction for the actual nonlinearity.** -/
theorem norm_fnlCoeff_le (hL : 0 < L) (β γ : ℝ) (c : ℕ → ℓ2) (n : ℕ) :
    ‖fnlCoeff L β γ c n‖ ≤
      |β| * (CA L) ^ 2 * c3 (nseq c) n + |γ| * (CA L) ^ 4 * c5 (nseq c) n := by
  have hC := CA_nonneg hL
  have a0 : ∀ k, 0 ≤ nseq c k := nseq_nonneg c
  have n2 : ∀ k, 0 ≤ c2 (nseq c) k := cauchy_nonneg a0 a0
  have n3 : ∀ k, 0 ≤ c3 (nseq c) k := cauchy_nonneg a0 n2
  have hc : ∀ k, ‖c k‖ ≤ nseq c k := fun k => le_rfl
  have hcc : ∀ k, ‖conjSeq c k‖ ≤ nseq c k := fun k => (norm_conjSeq c k).le
  have X2 : ∀ k, ‖cauchyH L c c k‖ ≤ CA L * c2 (nseq c) k :=
    fun k => cauchyH_step hL hc hc k
  have lift : ∀ (m : ℕ → ℝ) (s : ℝ) (k : ℕ),
      CA L * cauchy (fun j => s * m j) (nseq c) k = CA L * s * cauchy (nseq c) m k := by
    intro m s k
    rw [cauchy_smul_left, cauchy_comm m (nseq c)]
    ring
  have X3 : ∀ (Y : ℕ → ℓ2), (∀ k, ‖Y k‖ ≤ nseq c k) → ∀ k,
      ‖cauchyH L (cauchyH L c c) Y k‖ ≤ (CA L) ^ 2 * c3 (nseq c) k := by
    intro Y hY k
    have h := cauchyH_step hL X2 hY k
    rw [lift] at h
    calc _ ≤ CA L * CA L * cauchy (nseq c) (c2 (nseq c)) k := h
      _ = (CA L) ^ 2 * c3 (nseq c) k := by unfold c3; ring
  have X4 : ∀ k, ‖cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c) k‖ ≤
      (CA L) ^ 3 * c4 (nseq c) k := by
    intro k
    have h := cauchyH_step hL (X3 c hc) hcc k
    rw [lift] at h
    calc _ ≤ CA L * (CA L) ^ 2 * cauchy (nseq c) (c3 (nseq c)) k := h
      _ = (CA L) ^ 3 * c4 (nseq c) k := by unfold c4; ring
  have X5 : ‖cauchyH L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c)) (conjSeq c) n‖ ≤
      (CA L) ^ 4 * c5 (nseq c) n := by
    have h := cauchyH_step hL X4 hcc n
    rw [lift] at h
    calc _ ≤ CA L * (CA L) ^ 3 * cauchy (nseq c) (c4 (nseq c)) n := h
      _ = (CA L) ^ 4 * c5 (nseq c) n := by unfold c5; ring
  have Xcub := X3 (conjSeq c) hcc n
  have hb : ‖(-(β : ℂ))‖ = |β| := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hg : ‖(γ : ℂ)‖ = |γ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  unfold fnlCoeff
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, hb, hg]
  calc |β| * ‖cauchyH L (cauchyH L c c) (conjSeq c) n‖ +
        |γ| * ‖cauchyH L (cauchyH L (cauchyH L (cauchyH L c c) c) (conjSeq c)) (conjSeq c) n‖
      ≤ |β| * ((CA L) ^ 2 * c3 (nseq c) n) + |γ| * ((CA L) ^ 4 * c5 (nseq c) n) :=
        add_le_add (mul_le_mul_of_nonneg_left Xcub (abs_nonneg _))
          (mul_le_mul_of_nonneg_left X5 (abs_nonneg _))
    _ = _ := by ring

/-- **Taylor majorant for the frozen Galerkin recursion.** -/
theorem galerkin_taylor_majorant (hL : 0 < L) (β γ : ℝ) {c : ℕ → ℓ2} {K Ω : ℝ}
    (hK : 0 ≤ K) (hΩ : 0 ≤ Ω) (h0 : ‖c 0‖ ≤ K)
    (hrec : ∀ n : ℕ, ((n:ℝ) + 1) * ‖c (n+1)‖ ≤ Ω * ‖c n‖ + ‖fnlCoeff L β γ c n‖) :
    ∀ n, ‖c n‖ ≤
      K * (rate K Ω (|β| * (CA L) ^ 2) (|γ| * (CA L) ^ 4)) ^ n * TaylorMajorant.wt n := by
  have hC := CA_nonneg hL
  have h := majorant (a := nseq c) (B := |β| * (CA L) ^ 2) (G := |γ| * (CA L) ^ 4)
    hK hΩ (by positivity) (by positivity) (nseq_nonneg c) h0
    (fun n => (hrec n).trans (by
      have := norm_fnlCoeff_le hL β γ c n
      unfold nseq at this ⊢
      linarith))
  intro n
  exact h n

end PVNP.GalerkinTaylor
