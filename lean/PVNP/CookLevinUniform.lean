import PVNP.CookLevinDecide
import PVNP.CrossingSAT
import PVNP.PSubsetNP

/-!
# CL-1: the uniform Cook–Levin theorem for `SAT_dense`

For every `L ∈ NP_TM`, `CookLevinTableau.cookLevin` gives a verifier `d.M` and polynomials
`d.q`, `d.t` with `x ∈ L ↔ d.inst x ∈ SAT_dense`.  `CookLevinGen.gen_run` shows that the sweep
program `genCtrl d` writes `d.inst x` within `genBound d |x|` round trips.  `CookLevinDecide`
runs that program and then simulates a decider of `SAT_dense` on its output.

This file instantiates the construction with a polynomial-time decider of `SAT_dense` and bounds
the whole cost by one polynomial:

* `NP_TM_subset_P_TM_of_SAT`: `SAT_dense ∈ P_TM → NP_TM ⊆ P_TM`;
* `SAT_mem_P_TM_iff`: `SAT_dense ∈ P_TM ↔ P_TM = NP_TM`;
* `satLowerBound_iff_P_ne_NP`: `SATLowerBound ↔ P_TM ≠ NP_TM`.

Everything is uniform: the decider is one fixed single-tape Turing machine
(`Prog.toTM (decProg (genCtrl d) S)`), with one polynomial time bound.  Neither `SATLowerBound`
nor `P_TM ≠ NP_TM` is asserted; the last theorem only identifies them.
-/

namespace PVNP.CookLevin.Gen

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.UniformSim PVNP.PartI PVNP.CookLevin
open PVNP.PartIITuring PVNP.Discrete.SATV Polynomial

/-! ## A polynomial bound -/

section Poly

variable (d : Data)

/-- `K T` as a polynomial in `n`. -/
noncomputable def pK : Polynomial ℕ := (d.t + 1) * (2 * d.t + 3)

/-- The length of the instance as a polynomial in `n`. -/
noncomputable def pI : Polynomial ℕ :=
  pK d * (C (nT d.M) * (pK d * C (G d.M) * 3))

/-- `stepBound` of a Horner phase as a polynomial in `n`. -/
noncomputable def pSB (P : HPar) : Polynomial ℕ :=
  C (6 + 2 * P.cs.sum) + C P.cs.sum * (X + 1) ^ P.cs.length * (4 * X + 4)

/-- The generator bound as a polynomial in `n`. -/
noncomputable def pG : Polynomial ℕ :=
  4 + C (hcoeffs (d.t + 1)).length * pSB (hparT d.t) + C (hcoeffs d.q).length * pSB (hparQ d.q) +
    (8 * d.t + 21) + pK d * (5 + C (nT d.M) * (pK d * (6 * C (G d.M) + 9) + 2))

theorem pK_eval (n : ℕ) : (pK d).eval n = K (d.t.eval n) := by
  simp [pK, K, W]

theorem pI_eval (x : List Bool) (n : ℕ) :
    (pI d).eval n = (instOf d.M x (d.q.eval n) (d.t.eval n)).length := by
  rw [instOf, inst_length]
  simp only [pI, eval_mul, eval_C, pK_eval, numVars, eval_ofNat]
  try ring

theorem pSB_eval (P : HPar) (n : ℕ) : (pSB P).eval n = HPar.stepBound P n := by
  simp only [pSB, HPar.stepBound, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one,
    eval_ofNat]

theorem pG_eval (n : ℕ) : (pG d).eval n = genBound d n := by
  simp only [pG, genBound, eval_add, eval_mul, eval_C, eval_ofNat, pSB_eval, pK_eval, mainBound]

/-- The final bound, for a decider halting within `c · max(m, 1)^e` on inputs of length `m`. -/
noncomputable def pFin (c e : ℕ) : Polynomial ℕ :=
  (pG d + C c * (pI d + 1) ^ e + 2) * (2 * (X + pG d + C c * (pI d + 1) ^ e + 1) + 3) + 2

theorem pFin_eval (c e n : ℕ) : (pFin d c e).eval n =
    ((pG d).eval n + (C c * (pI d + 1) ^ e).eval n + 2) *
      (2 * (n + (pG d).eval n + (C c * (pI d + 1) ^ e).eval n + 1) + 3) + 2 := by
  simp only [pFin, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]

end Poly

/-! ## The uniform reduction -/

theorem genDone_stepP (d : Data) (l : List Cell) :
    (genCtrl d).prog.stepP (genDone d, l) = .inr (true, l) := by
  rw [Ctrl.stepP_eq, genDone_exit]; rfl

/-- **CL-1 (uniform Cook–Levin, decision form).**  If `SAT_dense` is decided in polynomial time by
an ordinary Turing machine, so is every language of `NP_TM`. -/
theorem NP_TM_subset_P_TM_of_SAT (hS : SAT_dense ∈ P_TM) : NP_TM ⊆ P_TM := by
  intro L hL
  obtain ⟨d, -, -, hd⟩ := cookLevin hL
  obtain ⟨S, c, e, -, -, hhalt, hacc⟩ := P_TM_subset_P_Turing hS
  refine ⟨(decProg (genCtrl d) S).toTM, pFin d c e, fun x => ?_⟩
  obtain ⟨hT, hiff⟩ := hd x
  obtain ⟨l', k, hrn, hk, I⟩ := gen_run d x hT
  set y := instOf d.M x (d.q.eval x.length) (d.t.eval x.length) with hy
  have hyl : y.length < l'.length := I.op.1
  have hout : ∀ (j : ℕ) (hj : j < l'.length), l'[j].out = y[j]? := by
    intro j hj
    refine (I.out j hj).trans ?_
    split_ifs with h
    · rfl
    · rw [List.getElem?_eq_none (by omega)]
  obtain ⟨t, ht, hft⟩ := hhalt y
  obtain ⟨Cst, hC, hCle⟩ := dec_halts (genCtrl d) S x y hrn (genDone_stepP d l') hyl hout hft
  obtain ⟨s, hs, h1, h2⟩ := Prog.toTM_firstAnswer _ x hC
  refine ⟨decide ((S.run (S.init y) t).q = S.qacc), ⟨s, le_trans hs ?_, h1, h2⟩, ?_⟩
  · -- the time bound
    have hk' : k ≤ (pG d).eval x.length := by rw [pG_eval]; exact hk
    have ht' : t ≤ (C c * (pI d + 1) ^ e).eval x.length := by
      simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one]
      rw [pI_eval d x]
      refine le_trans ht (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      rw [← hy]; omega
    show Cst + 2 ≤ (pFin d c e).eval x.length
    rw [pFin_eval]
    have := Nat.mul_le_mul (show k + t + 2 ≤ (pG d).eval x.length +
        (C c * (pI d + 1) ^ e).eval x.length + 2 by omega)
      (show 2 * (x.length + k + t + 1) + 3 ≤ 2 * (x.length + (pG d).eval x.length +
        (C c * (pI d + 1) ^ e).eval x.length + 1) + 3 by omega)
    omega
  · -- the answer
    rw [decide_eq_true_iff, ← S.accepts_iff_of_firstHalt hft, hacc y, hiff]
    rfl

/-- `SAT_dense` is in `P_TM` exactly when `P_TM = NP_TM`. -/
theorem SAT_mem_P_TM_iff : SAT_dense ∈ P_TM ↔ P_TM = NP_TM := by
  constructor
  · intro h
    exact Set.Subset.antisymm P_TM_subset_NP_TM (NP_TM_subset_P_TM_of_SAT h)
  · intro h
    rw [h]
    exact SAT_dense_mem_NP_TM

/-- **The SAT lower bound is the classical separation.** -/
theorem satLowerBound_iff_P_ne_NP : PVNP.CrossingSAT.SATLowerBound ↔ P_TM ≠ NP_TM := by
  unfold PVNP.CrossingSAT.SATLowerBound
  rw [SAT_mem_P_TM_iff]

end PVNP.CookLevin.Gen
