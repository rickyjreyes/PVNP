import PVNP.UniformSimRound

/-!
# Milestone 5, part 13: the whole simulation and its running time

* `rounds`: while the decoder outputs `none`, the program iterates rounds; after `T` rounds the
  invariant holds for `C_{t₀+T}`.
* `sim_halts`: if the decoder first outputs `some b` at time `t`, the sweep program halts with
  answer `b`, at a cost bounded by `timePoly hC` evaluated at `n + t + 1`.
* `toTM_firstAnswer_of_dec`: the compiled single-tape machine `σ.prog.toTM` first answers `b`
  within `timePoly hC (n + t + 1)` steps (`thm:wcc_to_tm`, `T_{M_W}(n) ≤ q_W(n + T_W(n) + 1)`).
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-- **The rounds.** -/
theorem rounds (hC : σ.Correct) (x : List Bool) :
    ∀ (T t0 : ℕ) (l : List (Cell σ)), σ.Good x t0 l →
      (∀ s < T, σ.W.dec x.length (σ.W.cfg x (t0 + s)) = none) →
      ∃ (l' : List (Cell σ)) (k : ℕ), RN σ.prog (.dprep, l) (.dprep, l') k ∧
        k ≤ T * σ.roundCost hC x ∧ l'.length ≤ l.length + T * hC.pD.eval x.length ∧
        σ.Good x (t0 + T) l' := by
  intro T
  induction T with
  | zero =>
    intro t0 l hg _
    exact ⟨l, 0, RN.refl _, by simp, by simp, by simpa using hg⟩
  | succ T ih =>
    intro t0 l hg hnone
    obtain ⟨l1, k1, hrn1, hk1, _, hlen1, hg1⟩ :=
      σ.round_spec hC x t0 l hg (by simpa using hnone 0 (by omega))
    obtain ⟨l2, k2, hrn2, hk2, hlen2, hg2⟩ := ih (t0 + 1) l1 hg1
      (fun s hs => by rw [show t0 + 1 + s = t0 + (s + 1) by ring]; exact hnone (s + 1) (by omega))
    refine ⟨l2, k1 + k2, hrn1.trans hrn2, by rw [Nat.succ_mul]; omega, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [show t0 + (T + 1) = t0 + 1 + T by ring]; exact hg2

/-! ### The time polynomial -/

/-- Bound for `max(n,1) + p_L(n) + p_E(n)`. -/
noncomputable def pA (hC : σ.Correct) : Polynomial ℕ := Polynomial.X + 1 + hC.pL + hC.pE

/-- Bound for the list length after the pre-round phases. -/
noncomputable def pL0 (hC : σ.Correct) : Polynomial ℕ := Polynomial.C (σ.W.w + 3) * σ.pA hC

/-- Bound for the round trips of one round. -/
noncomputable def pRC (hC : σ.Correct) : Polynomial ℕ :=
  Polynomial.C (1 + σ.K * σ.W.d * σ.W.r * 3 ^ σ.W.d) * σ.pL0 hC +
    Polynomial.C (4 + 2 * σ.K) + hC.pD

/-- Bound for all round trips. -/
noncomputable def pK (hC : σ.Correct) : Polynomial ℕ :=
  Polynomial.C (σ.W.w + 6) * σ.pA hC + Polynomial.C 8 + Polynomial.X * σ.pRC hC + σ.pL0 hC +
    hC.pD

/-- Bound for the final list length. -/
noncomputable def pLen (hC : σ.Correct) : Polynomial ℕ :=
  σ.pL0 hC + Polynomial.X * hC.pD + hC.pD

/-- **The time polynomial** `q_W`: the compiled machine answers within `q_W(n + t + 1)` steps. -/
noncomputable def timePoly (hC : σ.Correct) : Polynomial ℕ :=
  (σ.pK hC + 1) * (2 * σ.pLen hC + 3) + 2

theorem pow_side_le (R d : ℕ) : (2 * side R + 1) ^ d ≤ 3 ^ d * side R ^ d := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by have := side_pos R; omega) d

/-- **End-to-end simulation.**  If the decoder of `W` first outputs `some b` on `C_t`, the sweep
program halts on `x` with answer `b`, at a cost `C` with `C + 2 ≤ q_W(n + t + 1)`. -/
theorem sim_halts (hC : σ.Correct) (x : List Bool) (hg : σ.guard = false ∨ PS.run .tag x = .ok)
    (t : ℕ) (hnone : ∀ s < t, σ.W.dec x.length (σ.W.cfg x s) = none) (b : Bool)
    (hb : σ.W.dec x.length (σ.W.cfg x t) = some b) :
    ∃ C, σ.prog.Halts (σ.prog.start, x.map σ.prog.lift) b C ∧
      C + 2 ≤ (σ.timePoly hC).eval (x.length + t + 1) := by
  obtain ⟨l0, k0, hrn0, hg0, hk0, hlen0⟩ := σ.pre_round hC x hg
  obtain ⟨l1, k1, hrn1, hk1, hlen1, hg1⟩ := σ.rounds hC x t 0 l0 hg0 (by simpa using hnone)
  rw [zero_add] at hg1
  obtain ⟨l3, k2, hrn2, hk2, hlen3, hstep⟩ := σ.round_halt hC x t l1 hg1 b hb
  obtain ⟨C, hC', hCle⟩ := RN.halts ((hrn0.trans hrn1).trans hrn2) hstep
  refine ⟨C, hC', ?_⟩
  -- bounds in terms of `m = n + t + 1`
  set m := x.length + t + 1 with hm
  set n := x.length with hn
  have hnm : n ≤ m := by omega
  have htm : t ≤ m := by omega
  have hpL := eval_mono_nat hC.pL hnm
  have hpE := eval_mono_nat hC.pE hnm
  have hpD := eval_mono_nat hC.pD hnm
  have hA : max n 1 + hC.pL.eval n + hC.pE.eval n ≤ (σ.pA hC).eval m := by
    simp only [pA, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have : max n 1 ≤ m + 1 := by omega
    omega
  have hL0 : l0.length ≤ (σ.pL0 hC).eval m := by
    simp only [pL0, Polynomial.eval_mul, Polynomial.eval_C]
    exact le_trans hlen0 (Nat.mul_le_mul_left _ hA)
  have hBd : σ.Bx x ≤ (σ.pL0 hC).eval m := by have := hg0.boxIn; omega
  have hMl : (σ.Mx x).length ≤ (σ.pL0 hC).eval m :=
    le_trans (mems_length_le σ.W.d (σ.Rx x) (σ.W.Λ x.length)) hBd
  have hRC : σ.roundCost hC x ≤ (σ.pRC hC).eval m := by
    simp only [roundCost, pRC, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have h1 := pow_side_le (σ.Rx x) σ.W.d
    have h2 : 3 ^ σ.W.d * side (σ.Rx x) ^ σ.W.d ≤ 3 ^ σ.W.d * (σ.pL0 hC).eval m :=
      Nat.mul_le_mul_left _ hBd
    have h3 : σ.K * (σ.W.d * σ.W.r * (2 * side (σ.Rx x) + 1) ^ σ.W.d) ≤
        σ.K * σ.W.d * σ.W.r * 3 ^ σ.W.d * (σ.pL0 hC).eval m := by
      calc σ.K * (σ.W.d * σ.W.r * (2 * side (σ.Rx x) + 1) ^ σ.W.d)
          ≤ σ.K * (σ.W.d * σ.W.r * (3 ^ σ.W.d * (σ.pL0 hC).eval m)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans h1 h2))
        _ = σ.K * σ.W.d * σ.W.r * 3 ^ σ.W.d * (σ.pL0 hC).eval m := by ring
    nlinarith
  have hk : k0 + k1 + k2 ≤ (σ.pK hC).eval m := by
    simp only [pK, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have h1 : k1 ≤ m * (σ.pRC hC).eval m :=
      le_trans hk1 (Nat.mul_le_mul htm hRC)
    have h0 : k0 ≤ (σ.W.w + 6) * (σ.pA hC).eval m + 6 :=
      le_trans hk0 (by have := Nat.mul_le_mul_left (σ.W.w + 6) hA; omega)
    omega
  have hl : l3.length ≤ (σ.pLen hC).eval m := by
    simp only [pLen, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    have : t * hC.pD.eval n ≤ m * hC.pD.eval m := Nat.mul_le_mul htm hpD
    omega
  simp only [timePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  have := Nat.mul_le_mul (Nat.add_le_add_right hk 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hl) 3)
  simp only [] at hCle
  omega

/-- **`thm:wcc_to_tm`.**  The compiled single-tape machine first answers `b` within
`q_W(n + t + 1)` steps, where `t` is the first decision time of `W`. -/
theorem toTM_firstAnswer_of_dec (hC : σ.Correct) (x : List Bool)
    (hg : σ.guard = false ∨ PS.run .tag x = .ok)
    (t : ℕ) (hnone : ∀ s < t, σ.W.dec x.length (σ.W.cfg x s) = none) (b : Bool)
    (hb : σ.W.dec x.length (σ.W.cfg x t) = some b) :
    FirstAnswer (σ.prog.toTM.out x) ((σ.timePoly hC).eval (x.length + t + 1)) b := by
  obtain ⟨C, hH, hC'⟩ := σ.sim_halts hC x hg t hnone b hb
  obtain ⟨s, hs, h1, h2⟩ := Prog.toTM_firstAnswer σ.prog x hH
  exact ⟨s, le_trans hs hC', h1, h2⟩

end Spec

end PVNP.UniformSim
