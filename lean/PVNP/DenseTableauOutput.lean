import PVNP.CookLevinMain
import PVNP.PartIIUniform

/-! A barrier to a particular time-hierarchy strategy: materializing the
existing dense Cook–Levin tableau already charges a fourth power of its
time horizon. This concerns the reduction machine, independently of how
an arbitrary SAT decider treats the resulting word. -/
namespace PVNP.DenseTableauOutput
open PartIITuring Discrete Discrete.SATV CookLevin CookLevin.Gen

theorem untouched (A : MTM) (x : List Bool) {j : ℤ} (t : ℕ) (hj : (t:ℤ) ≤ j) :
    (A.run (A.init x) t).tape j = A.inputTape x j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MTM.run_succ]
    have hh := (abs_le.mp (PartIITwoPhase.head_bound A x t)).2
    have hn : j ≠ (A.run (A.init x) t).head := by omega
    simp only [MTM.step, Function.update_of_ne hn]
    exact ih (by omega)

theorem bound_of_output (A : MTM) (x y : List Bool) (B : ℕ) (h : A.Outputs x y B) :
    y.length ≤ max x.length B := by
  obtain ⟨t,ht,_,hshow,_⟩ := h
  by_contra! hf
  have hx := (le_max_left x.length B).trans_lt hf
  have hb := (le_max_right x.length B).trans_lt hf
  let j := y.length-1
  have hj : j < y.length := by dsimp [j]; omega
  have hpos : (t:ℤ) ≤ (j:ℤ) := by dsimp [j]; omega
  have hblank : A.inputTape x (j:ℤ) = A.blank := by
    simp [MTM.inputTape, show ¬(j:ℤ) < x.length by dsimp [j]; omega]
  have a := hshow j hj
  rw [untouched A x t hpos, hblank] at a
  exact A.inp_ne_blank _ a.symm

theorem quartic_length (M : TM) (x : List Bool) (Q T : ℕ) :
    (T+1)^4 ≤ (encDense (numVars M T) (phi M x Q T)).length := by
  rw [inst_length]
  have hK : (T+1)*(T+1) ≤ K T := by
    unfold K W; exact Nat.mul_le_mul_left _ (by omega)
  have hG : 1 ≤ G M := by unfold G; omega
  have hN : 1 ≤ nT M := nT_pos M
  calc
    (T+1)^4 = ((T+1)*(T+1))*((T+1)*(T+1)) := by ring
    _ ≤ K T * K T := Nat.mul_le_mul hK hK
    _ ≤ K T * (nT M * (numVars M T * 3)) := by
      apply Nat.mul_le_mul_left
      change K T ≤ nT M * (K T * G M * 3)
      calc K T = 1*(K T*1*1) := by simp
           _ ≤ _ := by gcongr; omega

/-- A literal bit-output transducer for this tableau cannot achieve a
subquartic output bound by parallelizing the subsequent decision procedure. -/
theorem quartic_writer (A : MTM) (M : TM) (x : List Bool) (Q T B : ℕ)
    (h : A.Outputs x (encDense (numVars M T) (phi M x Q T)) B)
    (hx : x.length < (T+1)^4) : (T+1)^4 ≤ B := by
  have hp := (quartic_length M x Q T).trans (bound_of_output A x _ B h)
  omega
end PVNP.DenseTableauOutput
