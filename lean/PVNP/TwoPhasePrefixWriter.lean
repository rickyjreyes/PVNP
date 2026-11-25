import PVNP.TwoPhaseFixedWord

/-! The canonical original input writer on any fixed interval. Its finite
control remembers a bounded prefix, returns to the origin and overwrites
the actual Part II state code followed by the required blank. -/
namespace PVNP.TwoPhasePrefixWriter
open PartIITuring PartIIUniform PartIITwoPhase TwoPhaseUniform TwoPhaseDecoder TwoPhaseFixedWord

abbrev Memory (m : ℕ) := Fin m → Option Bool

inductive State (m w : ℕ)
  | read (i : Fin (m+1)) (mem : Memory m)
  | back (i : Fin (m+1)) (mem : Memory m)
  | put (i : Fin (w+1)) (mem : Memory m)
  | done
  deriving DecidableEq, Fintype

variable {m w : ℕ}

private def delta (f : Memory m → List Bool) :
    State m w → Option Bool → State m w × Option Bool × Mv
  | .read i v, a =>
    if h : i.val < m then
      (.read ⟨i+1, by omega⟩ (Function.update v ⟨i,h⟩ a), a, .R)
    else (.back ⟨m, by omega⟩ v, a, .L)
  | .back i v, a =>
    if i.val = 0 then (.put 0 v, a, .R)
    else (.back ⟨i.val-1, by omega⟩ v, a, .L)
  | .put i v, _ =>
    if h : i.val < w then (.put ⟨i+1, by omega⟩ v, (f v)[i.val]?, .R)
    else (.done, (f v)[i.val]?, .R)
  | .done, a => (.done, a, .R)

def machine (m w : ℕ) (f : Memory m → List Bool) : MTM where
  Q := State m w
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank := fun _ => Option.some_ne_none _
  δ := delta f
  q0 := .read 0 (fun _ => none)
  qacc := .done
  qrej := .done

def memoryAt (x : List Bool) (t : ℕ) : Memory m :=
  fun i => if i.val < t then x[i.val]? else none

private theorem nextPrefix (x : List Bool) (j : Fin m) :
    Function.update (memoryAt x j.val) j x[j.val]? = memoryAt x (j.val+1) := by
  funext i
  by_cases h : i = j
  · subst i; simp [memoryAt]
  · have hne : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [Function.update_of_ne h, memoryAt]
    split_ifs <;> first | rfl | omega

section Run
variable (f : Memory m → List Bool) (x : List Bool)
local notation "D" => machine m w f

private theorem inputCell (j : ℕ) : (D).inputTape x j = x[j]? := by
  by_cases h : j < x.length <;> simp [MTM.inputTape, machine, h]

private theorem scan (k : ℕ) (hk : k ≤ m) :
    (D).run ((D).init x) k = ⟨(D).inputTape x,k,.read ⟨k,by omega⟩ (memoryAt x k)⟩ := by
  induction k with
  | zero =>
    simp [MTM.run_zero, MTM.init, machine]
    funext i; simp [memoryAt]
  | succ k ih =>
    rw [MTM.run_succ, ih (by omega)]
    have h : k < m := by omega
    simp [MTM.step, machine, delta, h, Mv.shift, Function.update_eq_self]
    exact (inputCell (w := w) f x k) ▸ nextPrefix x ⟨k,h⟩

private theorem turn (k : ℕ) (hk : k ≤ m) :
    (D).run ((D).init x) (m+1+k) =
      ⟨(D).inputTape x, (m : ℤ)-1-k, .back ⟨m-k,by omega⟩ (memoryAt x m)⟩ := by
  induction k with
  | zero =>
    simp only [Nat.add_zero,Nat.sub_zero,Nat.cast_zero,sub_zero]
    rw [MTM.run_succ, scan f x m le_rfl]
    simp [MTM.step, machine, delta, Mv.shift, sub_eq_add_neg, Function.update_eq_self]
  | succ k ih =>
    rw [show m+1+(k+1) = (m+1+k)+1 by omega, MTM.run_succ, ih (by omega)]
    have h : m-k ≠ 0 := by omega
    simp [MTM.step, machine, delta, h, Mv.shift, Function.update_eq_self]
    omega

private def patched (T : ℤ → Option Bool) (y : List Bool) (k : ℕ) (i : ℤ) :=
  if 0 ≤ i ∧ i < (k : ℤ) then y[i.toNat]? else T i

private theorem patch_next (T : ℤ → Option Bool) (y : List Bool) (k : ℕ) :
    Function.update (patched T y k) (k : ℤ) y[k]? = patched T y (k+1) := by
  funext i
  by_cases h : i = k
  · subst i; simp [patched]
  · rw [Function.update_of_ne h]; unfold patched
    split_ifs <;> first | rfl | omega

private theorem writing (k : ℕ) (hk : k ≤ w) :
    (D).run ((D).init x) (2*m+2+k) =
      ⟨patched ((D).inputTape x) (f (memoryAt x m)) k, k, .put ⟨k,by omega⟩ (memoryAt x m)⟩ := by
  induction k with
  | zero =>
    rw [show 2*m+2+0 = (m+1+m)+1 by omega, MTM.run_succ, turn f x m le_rfl]
    have ht : patched ((D).inputTape x) (f (memoryAt x m)) 0 = (D).inputTape x := by
      funext i; simp [patched]
    rw [ht]
    simp [MTM.step, machine, delta, Mv.shift, Function.update_eq_self]
  | succ k ih =>
    rw [show 2*m+2+(k+1) = (2*m+2+k)+1 by omega, MTM.run_succ, ih (by omega)]
    have h : k < w := by omega
    simp [MTM.step, machine, delta, h, Mv.shift, patch_next]

theorem outputs (hw : (f (memoryAt x m)).length ≤ w) :
    (D).Outputs x (f (memoryAt x m)) (2*m+2+w+1) := by
  let y := f (memoryAt x m)
  have last : (D).run ((D).init x) (2*m+2+w+1) =
      ⟨patched ((D).inputTape x) y (w+1), (w:ℤ)+1, .done⟩ := by
    rw [MTM.run_succ, writing f x w le_rfl]
    simp [MTM.step, machine, delta, Mv.shift, patch_next, y]
  refine ⟨_, le_rfl, ⟨by rw [last]; exact Or.inl rfl, ?_⟩, ?_, ?_⟩
  · intro s hs
    by_cases hr : s ≤ m
    · rw [scan f x s hr]; simp [MTM.Halting, machine]
    · by_cases hb : s ≤ 2*m+1
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m+1 ≤ s by omega)
        rw [turn f x k (by omega)]; simp [MTM.Halting, machine]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2*m+2 ≤ s by omega)
        rw [writing f x k (by omega)]; simp [MTM.Halting, machine]
  · intro i hi
    rw [last]
    have hj : (i:ℤ) < (w:ℤ)+1 := by omega
    simp [patched, hj, y, machine, hi]
  · rw [last]
    have hj : ((f (memoryAt x m)).length:ℤ) < (w:ℤ)+1 := by omega
    simp [patched, hj, y, machine]
end Run

private def recover {m : ℕ} (v : Memory m) : List Bool := (List.ofFn v).filterMap id

private theorem recover_input (m : ℕ) (x : List Bool) :
    recover (fun i : Fin m => x[i.val]?) = x.take m := by
  induction m generalizing x with
  | zero => simp [recover]
  | succ m ih =>
    cases x with
    | nil => simp [recover, List.ofFn_const]
    | cons b x => simp [recover, List.ofFn_succ, Fin.val_succ, ← ih x, recover]

private theorem captured (x : List Bool) :
    recover (memoryAt (m := m) x m) = x.take m := by
  change recover (fun i : Fin m => if i.val < m then x[i.val]? else none) = _
  simpa only [Fin.isLt, if_true] using recover_input m x

private theorem input_take (M : MTM) (x : List Bool) (L : ℕ) (i : ℤ) (hi : i ≤ L) :
    M.inputTape (x.take (L+1)) i = M.inputTape x i := by
  by_cases hn : 0 ≤ i
  · have hj : i.toNat < L+1 := by omega
    have hlen : (i < ((x.take (L+1)).length : ℤ)) ↔ i < (x.length : ℤ) := by
      simp only [List.length_take, Nat.cast_min, Nat.cast_add, Nat.cast_one, lt_min_iff]
      omega
    simp only [MTM.inputTape, hn, true_and, hlen, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
  · simp [MTM.inputTape, hn]

theorem originalInputCode_take (M : MTM) (L : ℕ) (x : List Bool) :
    originalInputCode M (Polynomial.C L) (x.take (L+1)) = originalInputCode M (Polynomial.C L) x := by
  simp only [originalInputCode_eq_encCfg, Polynomial.eval_C]
  congr 1
  funext i
  by_cases h : InWin L (i 0)
  · simp [encCfg, h, MTM.init, input_take M x L (i 0) h.2]
  · simp [encCfg, h]

theorem encoder_fp (M : MTM) (L : ℕ) : FP (originalInputCode M (Polynomial.C L)) := by
  let w := (2*(L+1)+1)*(3+2*Fintype.card (PartIITwoPhase.S M))
  let f : Memory (L+1) → List Bool := fun v => originalInputCode M (Polynomial.C L) (recover v)
  refine ⟨machine (L+1) w f, Polynomial.C (2*(L+1)+2+w+1), fun x => ?_⟩
  have bound : (f (memoryAt x (L+1))).length ≤ w := by
    simpa [f,w] using originalInputCode_length_le M (Polynomial.C L) (recover (memoryAt x (L+1)))
  have h := outputs (w := w) f x bound
  simpa only [f, captured, originalInputCode_take, Polynomial.eval_C] using h

noncomputable def fixedUniform (M : MTM) (L : ℕ) : UWCC :=
  originalUniform M (Polynomial.C L) (constantWindowCode_fp L) (encoder_fp M L)

theorem fixed_output (M : MTM) (L : ℕ) (x : List Bool) (t : ℕ) :
    (fixedUniform M L).dec x.length ((fixedUniform M L).cfg x t) = outW M L x t := by
  simpa [fixedUniform] using original_output M (Polynomial.C L) (constantWindowCode_fp L) (encoder_fp M L) x t

end PVNP.TwoPhasePrefixWriter
