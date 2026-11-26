import PVNP.UniformGalerkinRadius

/-!
# Resource-counted time stepping: stability bootstrap

A finite time-stepping method must control truncation and rounding errors
without assuming that its numerical iterates stay in the stability ball.
This module isolates the discrete Gronwall argument, including the
radius bootstrap. The local defect and arithmetic costs are separate.
-/

namespace PVNP.TorusGalerkin

noncomputable def stepEnvelope (δ A h q : ℝ) (i : ℕ) : ℝ :=
  (δ + (i : ℝ)*q)*Real.exp (A*h*(i : ℝ))

theorem stepEnvelope_nonneg {δ A h q : ℝ} (hδ : 0 ≤ δ) (hq : 0 ≤ q) (i : ℕ) :
    0 ≤ stepEnvelope δ A h q i := by
  unfold stepEnvelope
  positivity

theorem stepEnvelope_mono {δ A h q : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q)
    {i j : ℕ} (hij : i ≤ j) :
    stepEnvelope δ A h q i ≤ stepEnvelope δ A h q j := by
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold stepEnvelope
  apply mul_le_mul
  · exact add_le_add_left (mul_le_mul_of_nonneg_right hij' hq) _
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hij' (mul_nonneg hA hh)
  · positivity
  · positivity

theorem stepEnvelope_succ {δ A h q : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q) (i : ℕ) :
    (1+A*h)*stepEnvelope δ A h q i+q ≤ stepEnvelope δ A h q (i+1) := by
  have hbase : 0 ≤ δ+(i:ℝ)*q := by positivity
  have hf : 1+A*h ≤ Real.exp (A*h) := by linarith [Real.add_one_le_exp (A*h)]
  have hfac : 1 ≤ Real.exp (A*h*((i:ℝ)+1)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hexp : Real.exp (A*h*(i:ℝ))*Real.exp (A*h) =
      Real.exp (A*h*((i:ℝ)+1)) := by rw [← Real.exp_add]; congr 1 <;> ring
  unfold stepEnvelope
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ = (δ+(i:ℝ)*q)*Real.exp (A*h*(i:ℝ))*(1+A*h)+q := by ring
    _ ≤ (δ+(i:ℝ)*q)*Real.exp (A*h*(i:ℝ))*Real.exp (A*h)+q :=
      add_le_add_right (mul_le_mul_of_nonneg_left hf (by positivity)) _
    _ = (δ+(i:ℝ)*q)*Real.exp (A*h*((i:ℝ)+1))+q := by rw [mul_assoc, hexp]
    _ ≤ (δ+(i:ℝ)*q)*Real.exp (A*h*((i:ℝ)+1))+
        q*Real.exp (A*h*((i:ℝ)+1)) := by
      exact add_le_add_left (by simpa using mul_le_mul_of_nonneg_left hfac hq) _
    _ = _ := by ring

/-- The recurrence is only required when the previous error is within
the radius slack. The global budget certifies that it always is. -/
theorem rounded_step_bootstrap {e : ℕ → ℝ} {δ A h q b : ℝ} (N : ℕ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h) (hq : 0 ≤ q)
    (h0 : e 0 ≤ δ)
    (hstep : ∀ i < N, e i ≤ b → e (i+1) ≤ (1+A*h)*e i+q)
    (hbudget : stepEnvelope δ A h q N ≤ b) :
    ∀ i ≤ N, e i ≤ stepEnvelope δ A h q i ∧ e i ≤ b := by
  have hmain : ∀ i ≤ N, e i ≤ stepEnvelope δ A h q i := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa [stepEnvelope] using h0
    | succ i ih =>
      intro hi
      have hi' : i ≤ N := by omega
      have he := ih hi'
      have hb := he.trans ((stepEnvelope_mono hδ hA hh hq hi').trans hbudget)
      exact (hstep i (by omega) hb).trans
        ((add_le_add_right (mul_le_mul_of_nonneg_left he (by positivity)) q).trans
          (stepEnvelope_succ hδ hA hh hq i))
  intro i hi
  exact ⟨hmain i hi, (hmain i hi).trans
    ((stepEnvelope_mono hδ hA hh hq hi).trans hbudget)⟩

/-- Explicit budget split: initial error, Euler local error, and
rounding error each receive one third of the pre-amplification budget. -/
theorem rounded_step_budget {δ A h D ξ T ε : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hD : 0 ≤ D) (hξ : 0 ≤ ξ) (hT : (N:ℝ)*h = T)
    (hinit : δ*Real.exp (A*T) ≤ ε/3)
    (hdisc : D*h*T*Real.exp (A*T) ≤ ε/3)
    (hround : (N:ℝ)*ξ*Real.exp (A*T) ≤ ε/3) :
    stepEnvelope δ A h (D*h^2+ξ) N ≤ ε := by
  unfold stepEnvelope
  have ht : A*h*(N:ℝ) = A*T := by rw [← hT]; ring
  rw [ht]
  have he : (N:ℝ)*(D*h^2+ξ) = D*h*T+(N:ℝ)*ξ := by rw [← hT]; ring
  rw [he]
  linarith only [hinit,hdisc,hround]


open PVNP.Torus Set

theorem galerkin_time_modulus {L κ β γ R M N : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hN : 0 ≤ N) (S : Finset Z2)
    (hm : ∀ k ∈ S, om L κ k ≤ M)
    (hn : ∀ k ∈ nonlinearSupport S, om L κ k ≤ N)
    {v : ℓ2} (hv : ‖v‖ ≤ R) (s t : ℝ) :
    ‖galerkin S L κ β γ s v - galerkin S L κ β γ t v‖ ≤
      LF L β γ R*R*(M+N)*|s-t| := by
  unfold galerkin
  rw [← trunc_sub]
  exact (trunc_norm_le S _).trans
    (finite_Gf_time_modulus hL hR hM hN (trunc_supported S v)
      ((trunc_norm_le S v).trans hv) hm hn s t)

theorem galerkin_speed {L κ β γ R : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (S : Finset Z2) (t : ℝ) {v : ℓ2} (hv : ‖v‖ ≤ R) :
    ‖galerkin S L κ β γ t v‖ ≤ LF L β γ R * R := by
  unfold galerkin
  exact (trunc_norm_le S _).trans
    (norm_Gf_le hL hR t ((trunc_norm_le S v).trans hv))

/-- Local defect of the exact Galerkin trajectory against a single
Euler step, with an explicit (conservative) quadratic bound. -/
theorem galerkin_euler_defect {L κ β γ R M N : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hN : 0 ≤ N) (S : Finset Z2)
    (hm : ∀ k ∈ S, om L κ k ≤ M)
    (hn : ∀ k ∈ nonlinearSupport S, om L κ k ≤ N)
    {W : ℝ → ℓ2}
    (hd : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hb : ∀ t, ‖W t‖ ≤ R) (a h : ℝ) (hh : 0 ≤ h) :
    ‖W (a+h) - (W a + h • galerkin S L κ β γ a (W a))‖ ≤
      (LF L β γ R * (LF L β γ R * R) +
        LF L β γ R * R * (M+N))*h^2 := by
  let A := LF L β γ R
  let d := galerkin S L κ β γ a (W a)
  let D := A*(A*R)+A*R*(M+N)
  have hA : 0 ≤ A := LF_nonneg L β γ R
  have hspeed (s : ℝ) : ‖W s-W a‖ ≤ A*R*|s-a| := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := W) (f' := fun t => galerkin S L κ β γ t (W t))
      (s := (univ : Set ℝ)) (x := a) (y := s) (C := A*R)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t _ => galerkin_speed hL hR S t (hb t))
      convex_univ trivial trivial
    simpa only [Real.norm_eq_abs] using h
  let f : ℝ → ℓ2 := fun s => W s - (W a + (s-a) • d)
  have hfd (s : ℝ) : HasDerivAt f (galerkin S L κ β γ s (W s)-d) s := by
    have hl := ((hasDerivAt_id s).sub_const a).smul_const d
    have hl' : HasDerivAt (fun t => W a + (t-a) • d) d s := by
      simpa only [one_smul] using hl.const_add (W a)
    exact (hd s).sub hl'
  have hder (s : ℝ) (hs : s ∈ Icc a (a+h)) :
      ‖galerkin S L κ β γ s (W s)-d‖ ≤ D*h := by
    have habs : |s-a| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith [hs.2]
    have hs1 := galerkin_lipschitz (κ := κ) (β := β) (γ := γ) hL S s (hb s) (hb a)
    have hs2 := galerkin_time_modulus (β := β) (γ := γ) hL hR hM hN S hm hn (hb a) s a
    calc
      _ ≤ ‖galerkin S L κ β γ s (W s)-galerkin S L κ β γ s (W a)‖ +
        ‖galerkin S L κ β γ s (W a)-d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ A*(A*R*|s-a|)+A*R*(M+N)*|s-a| :=
        add_le_add (hs1.trans (mul_le_mul_of_nonneg_left (hspeed s) hA)) hs2
      _ = D*|s-a| := by dsimp [D]; ring
      _ ≤ D*h := mul_le_mul_of_nonneg_left habs (by dsimp [D]; positivity)
  have hx : a ∈ Icc a (a+h) := ⟨le_rfl,by linarith⟩
  have hy : a+h ∈ Icc a (a+h) := ⟨by linarith,le_rfl⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun s => galerkin S L κ β γ s (W s)-d)
    (s := Icc a (a+h)) (x := a) (y := a+h) (C := D*h)
    (fun s _ => (hfd s).hasDerivWithinAt) hder (convex_Icc _ _) hx hy
  have hf0 : f a = 0 := by simp [f]
  have hf1 : f (a+h) = W (a+h)-(W a+h • d) := by simp [f]
  rw [hf0, sub_zero, hf1, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hh] at hmv
  calc
    _ ≤ D*h*h := hmv
    _ = _ := by dsimp [D,A]; ring


/-- Rounded Euler iterates compared to the actual Galerkin trajectory.
The update defect is a norm bound on the implemented step (including
field evaluation and rounding); it is needed only inside the radius.
The conclusion certifies that no iterate leaves that radius. -/
theorem rounded_galerkin_euler {L κ β γ R M Q h ξ δ b : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hh : 0 ≤ h) (hξ : 0 ≤ ξ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (S : Finset Z2) (hm : ∀ k ∈ S, om L κ k ≤ M)
    (hq : ∀ k ∈ nonlinearSupport S, om L κ k ≤ Q)
    (N : ℕ) {W : ℝ → ℓ2} {x : ℕ → ℓ2}
    (hd : ∀ t, HasDerivAt W (galerkin S L κ β γ t (W t)) t)
    (hW : ∀ t, ‖W t‖ ≤ R)
    (h0 : ‖x 0-W 0‖ ≤ δ)
    (hupdate : ∀ i < N, ‖x i‖ ≤ R+b →
      ‖x (i+1) - (x i+h • galerkin S L κ β γ ((i:ℝ)*h) (x i))‖ ≤ ξ)
    (hbudget : stepEnvelope δ (LF L β γ (R+b)) h
      ((LF L β γ (R+b)*(LF L β γ (R+b)*(R+b))+
        LF L β γ (R+b)*(R+b)*(M+Q))*h^2+ξ) N ≤ b) :
    ∀ i ≤ N, ‖x i-W ((i:ℝ)*h)‖ ≤ stepEnvelope δ (LF L β γ (R+b)) h
      ((LF L β γ (R+b)*(LF L β γ (R+b)*(R+b))+
        LF L β γ (R+b)*(R+b)*(M+Q))*h^2+ξ) i ∧ ‖x i‖ ≤ R+b := by
  let A := LF L β γ (R+b)
  let D := A*(A*(R+b))+A*(R+b)*(M+Q)
  let e : ℕ → ℝ := fun i => ‖x i-W ((i:ℝ)*h)‖
  have hA : 0 ≤ A := LF_nonneg _ _ _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW' (t : ℝ) : ‖W t‖ ≤ R+b := (hW t).trans (by linarith)
  have hxball (i : ℕ) (hi : e i ≤ b) : ‖x i‖ ≤ R+b := by
    have he : x i = (x i-W ((i:ℝ)*h))+W ((i:ℝ)*h) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by dsimp [e] at hi; linarith [hW ((i:ℝ)*h)])
  have hstep (i : ℕ) (hi : i < N) (he : e i ≤ b) :
      e (i+1) ≤ (1+A*h)*e i+(D*h^2+ξ) := by
    let t : ℝ := (i:ℝ)*h
    let u := x i+h • galerkin S L κ β γ t (x i)
    let v := W t+h • galerkin S L κ β γ t (W t)
    have ht : ((i+1:ℕ):ℝ)*h = t+h := by push_cast; dsimp [t]; ring
    have hu : ‖x (i+1)-u‖ ≤ ξ := hupdate i hi (hxball i he)
    have hv : ‖v-W (t+h)‖ ≤ D*h^2 := by
      rw [norm_sub_rev]
      exact galerkin_euler_defect hL (add_nonneg hR hb) hM hQ S hm hq hd hW' t h hh
    have huv : ‖u-v‖ ≤ (1+A*h)*e i := by
      have hg := galerkin_lipschitz (κ := κ) (β := β) (γ := γ) hL S t (hxball i he) (hW' t)
      have heq : u-v = (x i-W t)+h •
          (galerkin S L κ β γ t (x i)-galerkin S L κ β γ t (W t)) := by
        dsimp [u,v]; rw [smul_sub]; abel
      rw [heq]
      calc
        _ ≤ ‖x i-W t‖ + ‖h •
          (galerkin S L κ β γ t (x i)-galerkin S L κ β γ t (W t))‖ :=
            norm_add_le _ _
        _ ≤ e i + h*(A*e i) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          exact add_le_add_left (mul_le_mul_of_nonneg_left hg hh) _
        _ = _ := by ring
    dsimp [e]
    rw [ht]
    calc
      _ ≤ ‖x (i+1)-u‖+‖u-W (t+h)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖x (i+1)-u‖+(‖u-v‖+‖v-W (t+h)‖) :=
        add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _
      _ ≤ ξ+((1+A*h)*e i+D*h^2) := add_le_add hu (add_le_add huv hv)
      _ = _ := by ring
  have h := rounded_step_bootstrap (e := e) N hδ hA hh
    (add_nonneg (mul_nonneg hD (sq_nonneg h)) hξ)
    (by
      have hz : ((0:ℕ):ℝ) * h = 0 := by rw [Nat.cast_zero, zero_mul]
      show ‖x 0 - W (((0:ℕ):ℝ) * h)‖ ≤ δ
      rw [hz]
      exact h0) hstep hbudget
  intro i hi
  exact ⟨(h i hi).1,hxball i (h i hi).2⟩

end PVNP.TorusGalerkin
