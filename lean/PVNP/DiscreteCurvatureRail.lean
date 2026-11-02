import PVNP.ComplexityEquivalence

/-!
# Curvature rails in the discrete WCC model are vacuous (issues #10, #12; O5–O9)

Let `A` be any finite quiescent radius-one WCC (`PVNP.Discrete.WCC`) and let
`emb : A.S → ℤ` be **any** amplitude embedding of its cell alphabet.  The
discrete curvature (second difference) of a configuration is
`lap c i = emb (c (i-1)) - 2 emb (c i) + emb (c (i+1))`.

* `run_blank_outside`: light cone — after `t` steps on an input of length `n`
  every cell outside `[-t, n + t]` is blank.
* `lap_zero_outside`: hence the curvature density vanishes outside the window
  `[-t-1, n+t+1]`, so the windowed sum is the total discrete curvature.
* `curvature_le`: total discrete curvature at time `t` is at most
  `16 K² (n + 2t + 3)` with `K = Σ_s |emb s|`.
* `P_TM_eq_curvature_rail`: `P_TM` equals the class of languages decided by
  polynomial-time discrete WCCs whose curvature obeys a polynomial rail
  **for every embedding**.  Curvature rails therefore exclude nothing beyond
  time in the discrete model.
* `curvature_lower_bound_is_classical`: a superpolynomial curvature lower bound
  for an NP language in the discrete model would already prove
  `P_TM ≠ NP_TM`.  This is the precise obstruction: discrete-model curvature
  hardness is exactly as hard as classical P ≠ NP.
-/

namespace PVNP.Discrete

namespace WCC

variable (A : WCC)

/-- Discrete curvature density for an amplitude embedding. -/
def lap (emb : A.S → ℤ) (c : ℤ → A.S) (i : ℤ) : ℤ :=
  emb (c (i - 1)) - 2 * emb (c i) + emb (c (i + 1))

/-- Windowed total discrete curvature. -/
def curv (emb : A.S → ℤ) (c : ℤ → A.S) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.Icc a b, (A.lap emb c i) ^ 2

/-- Amplitude scale of an embedding. -/
def Kemb (emb : A.S → ℤ) : ℤ := ∑ s, |emb s|

theorem abs_emb_le (emb : A.S → ℤ) (s : A.S) : |emb s| ≤ A.Kemb emb :=
  Finset.single_le_sum (f := fun s => |emb s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

theorem lap_sq_le (emb : A.S → ℤ) (c : ℤ → A.S) (i : ℤ) :
    (A.lap emb c i) ^ 2 ≤ 16 * (A.Kemb emb) ^ 2 := by
  have h1 := A.abs_emb_le emb (c (i - 1))
  have h2 := A.abs_emb_le emb (c i)
  have h3 := A.abs_emb_le emb (c (i + 1))
  have habs : |A.lap emb c i| ≤ 4 * A.Kemb emb := by
    unfold lap
    calc |emb (c (i - 1)) - 2 * emb (c i) + emb (c (i + 1))|
        ≤ |emb (c (i - 1)) - 2 * emb (c i)| + |emb (c (i + 1))| := abs_add _ _
      _ ≤ |emb (c (i - 1))| + |2 * emb (c i)| + |emb (c (i + 1))| := by
          gcongr; exact abs_sub _ _
      _ ≤ 4 * A.Kemb emb := by rw [abs_mul]; norm_num; linarith
  have := sq_le_sq' (abs_le.1 habs).1 (abs_le.1 habs).2
  nlinarith [this]

theorem curv_le (emb : A.S → ℤ) (c : ℤ → A.S) {a b : ℤ} (hab : a ≤ b + 1) :
    A.curv emb c a b ≤ (b - a + 1) * (16 * (A.Kemb emb) ^ 2) := by
  unfold curv
  calc ∑ i ∈ Finset.Icc a b, (A.lap emb c i) ^ 2
      ≤ ∑ _i ∈ Finset.Icc a b, 16 * (A.Kemb emb) ^ 2 :=
        Finset.sum_le_sum fun i _ => A.lap_sq_le emb c i
    _ = (b - a + 1) * (16 * (A.Kemb emb) ^ 2) := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
        congr 1
        omega

/-! ### Light cone -/

theorem step_blank_outside {c : ℤ → A.S} {a b : ℤ}
    (h : ∀ i, (i < a ∨ b < i) → c i = A.blank) :
    ∀ i, (i < a - 1 ∨ b + 1 < i) → A.step c i = A.blank := by
  intro i hi
  simp only [step]
  rw [h (i - 1) (by omega), h i (by omega), h (i + 1) (by omega), A.quiescent]

theorem init_blank_outside (x : List Bool) :
    ∀ i, (i < 0 ∨ (x.length : ℤ) < i) → A.init x i = A.blank := by
  intro i hi
  simp only [init]
  rw [if_neg (by omega), if_neg (by omega)]

theorem run_blank_outside (x : List Bool) (t : ℕ) :
    ∀ i, (i < -(t : ℤ) ∨ (x.length : ℤ) + t < i) → A.run (A.init x) t i = A.blank := by
  induction t with
  | zero => simpa [run] using A.init_blank_outside x
  | succ t ih =>
    intro i hi
    rw [run_succ]
    exact A.step_blank_outside ih i (by push_cast at hi ⊢; omega)

theorem lap_zero_outside (emb : A.S → ℤ) (x : List Bool) (t : ℕ) (i : ℤ)
    (hi : i < -(t : ℤ) - 1 ∨ (x.length : ℤ) + t + 1 < i) :
    A.lap emb (A.run (A.init x) t) i = 0 := by
  have h := A.run_blank_outside x t
  simp only [lap]
  rw [h (i - 1) (by omega), h i (by omega), h (i + 1) (by omega)]
  ring

/-- Total discrete curvature of the run at time `t`. -/
def runCurv (emb : A.S → ℤ) (x : List Bool) (t : ℕ) : ℤ :=
  A.curv emb (A.run (A.init x) t) (-(t : ℤ) - 1) ((x.length : ℤ) + t + 1)

/-- **Discrete curvature is linearly bounded by the light-cone width.** -/
theorem curvature_le (emb : A.S → ℤ) (x : List Bool) (t : ℕ) :
    A.runCurv emb x t ≤ ((x.length : ℤ) + 2 * t + 3) * (16 * (A.Kemb emb) ^ 2) := by
  have := A.curv_le emb (A.run (A.init x) t)
    (a := -(t : ℤ) - 1) (b := (x.length : ℤ) + t + 1) (by omega)
  unfold runCurv
  convert this using 2; ring

end WCC

/-- Languages decided in polynomial time by discrete WCCs whose discrete
curvature obeys one polynomial rail at every step, **for every** amplitude
embedding of the alphabet. -/
def P_curvRail : Set (Set (List Bool)) :=
  {L | ∃ (A : WCC) (p : Polynomial ℕ), A.Decides L (fun n => p.eval n) ∧
    ∀ emb : A.S → ℤ, ∃ q : Polynomial ℕ, ∀ x : List Bool, ∀ t ≤ p.eval x.length,
      A.runCurv emb x t ≤ ((q.eval x.length : ℕ) : ℤ)}

/-- **Curvature rails are vacuous in the discrete model.** -/
theorem P_TM_eq_curvature_rail : P_curvRail = P_TM := by
  rw [← P_WCC_eq_P_TM]
  ext L
  constructor
  · rintro ⟨A, p, h, -⟩
    exact ⟨A, p, h⟩
  · rintro ⟨A, p, h⟩
    refine ⟨A, p, h, fun emb => ?_⟩
    set K := (A.Kemb emb).toNat
    refine ⟨Polynomial.C (16 * K ^ 2) * (Polynomial.X + 2 * p + 3), fun x t ht => ?_⟩
    have hK : A.Kemb emb = (K : ℤ) := by
      have : 0 ≤ A.Kemb emb := Finset.sum_nonneg fun _ _ => abs_nonneg _
      omega
    have h1 := A.curvature_le emb x t
    rw [hK] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_natCast]
    push_cast
    have ht' : (t : ℤ) ≤ (p.eval x.length : ℕ) := by exact_mod_cast ht
    have hK0 : (0 : ℤ) ≤ 16 * (K : ℤ) ^ 2 := by positivity
    calc A.runCurv emb x t ≤ ((x.length : ℤ) + 2 * t + 3) * (16 * (K : ℤ) ^ 2) := h1
      _ ≤ ((x.length : ℤ) + 2 * (p.eval x.length : ℕ) + 3) * (16 * (K : ℤ) ^ 2) := by
          gcongr
      _ = 16 * (K : ℤ) ^ 2 * ((x.length : ℤ) + 2 * ((p.eval x.length : ℕ) : ℤ) + 3) := by ring

/-- **Obstruction theorem.** If some NP language admits no discrete WCC
decider obeying a polynomial curvature rail, then classical `P ≠ NP`.
Hence a universal discrete curvature lower bound for SAT is exactly as hard
as the classical problem; it cannot be obtained from discrete curvature
considerations alone without resolving `P` versus `NP`. -/
theorem curvature_lower_bound_is_classical (L : Set (List Bool)) (hL : L ∈ NP_TM)
    (hcurv : L ∉ P_curvRail) : P_TM ≠ NP_TM := by
  intro h
  rw [P_TM_eq_curvature_rail, h] at hcurv
  exact hcurv hL

/-- Conversely, any language in `P_TM` has deciders meeting every curvature
rail, so no unconditional superpolynomial discrete curvature lower bound
can hold for it. -/
theorem no_curvature_lower_bound_in_P (L : Set (List Bool)) (hL : L ∈ P_TM) :
    L ∈ P_curvRail := by
  rw [P_TM_eq_curvature_rail]; exact hL

end PVNP.Discrete
