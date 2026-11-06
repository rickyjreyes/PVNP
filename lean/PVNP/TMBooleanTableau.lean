import PVNP.BooleanNetwork
import PVNP.TMtoWCC
import PVNP.CrossingCapacity

/-! Boolean circuits for arbitrary first-answer single-tape machines. The
evaluation window is built backwards from every possible final head position.
Each additional row has one extra cell on both sides, so no artificial boundary
or cyclic identification affects the result. -/
namespace PVNP.TMBooleanTableau

open PVNP.Discrete PVNP.BooleanNetwork

variable (M : TM)

abbrev Cell := M.Γ × Option M.Λ

private def stop : TM := { M with
  δ := fun q a => if answerOf (M.acc q) (M.rej q) = none then M.δ q a else none }

private def liftCfg (c : M.Cfg) : (stop M).Cfg := ⟨c.q, c.tape, c.head⟩

private theorem lift_next (c : M.Cfg) (h : M.ans c = none) :
    (stop M).next (liftCfg M c) = liftCfg M (M.next c) := by
  change answerOf (M.acc c.q) (M.rej c.q) = none at h
  cases he : M.δ c.q (c.tape c.head) with
  | none => simp [TM.next, TM.step, stop, liftCfg, h, he]
  | some v => simp [TM.next, TM.step, stop, liftCfg, h, he]

private theorem stop_answer (x : List Bool) (t : ℕ) (b : Bool) (h : FirstAnswer (M.out x) t b) :
    (stop M).out x t = some b := by
  obtain ⟨s, hst, hs, before⟩ := h
  have agree (j : ℕ) (hj : j ≤ s) :
      (stop M).run ((stop M).init x) j = liftCfg M (M.run (M.init x) j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [TM.run_succ, TM.run_succ, ih (by omega), lift_next M _ (before j (by omega))]
  let c := M.run (M.init x) s
  have hs' : answerOf (M.acc c.q) (M.rej c.q) = some b := hs
  have fixed : (stop M).next (liftCfg M c) = liftCfg M c := by
    simp [TM.next, TM.step, liftCfg, stop, hs']
  have stays (j : ℕ) : (stop M).run (liftCfg M c) j = liftCfg M c := by
    induction j with
    | zero => rfl
    | succ j ih => rw [TM.run_succ, ih, fixed]
  unfold TM.out
  rw [show t = s + (t-s) by omega, TM.run_add, agree s le_rfl, stays]
  exact hs

private def initGate (n : ℕ) (z : ℤ) (s : Cell M) : Expr (Fin n) :=
  let head := if z = 0 then some M.start else none
  if h : 0 ≤ z ∧ z < n then
    Expr.bitMap ⟨z.toNat, by omega⟩ (decide ((M.inp false, head) = s))
      (decide ((M.inp true, head) = s))
  else .lit (decide ((M.blank, head) = s))

private theorem init_eval (x : Fin n → Bool) (z : ℤ) (s : Cell M) :
    (initGate M n z s).eval x = decide (M.encode (M.init (List.ofFn x)) z = s) := by
  unfold initGate TM.encode TM.init TM.inputTape
  simp only [List.length_ofFn]
  split_ifs with h₁ h₂ h₃ <;> simp_all [Expr.bitMap_eval, Expr.eval]
  all_goals split <;> simp_all
  all_goals have : 0 < n := by omega
  all_goals simp [this]

private theorem init_size (n : ℕ) (z : ℤ) (s : Cell M) : (initGate M n z s).size ≤ 2 := by
  unfold initGate
  dsimp only
  split_ifs
  all_goals first | exact Expr.bitMap_size _ _ _ | simp [Expr.size]

private abbrev Row (w : ℕ) := Fin w × Cell M

private noncomputable def localGate {w : ℕ} (j : Fin w) (s : Cell M) : Expr (Row M (w+2)) :=
  Expr.any (Expr.elems (Cell M × Cell M × Cell M)) fun v =>
    if M.cellRule v.1 v.2.1 v.2.2 = s then
      .conj (.var (⟨j.val, by omega⟩, v.1))
        (.conj (.var (⟨j.val+1, by omega⟩, v.2.1)) (.var (⟨j.val+2, by omega⟩, v.2.2)))
    else .lit false

private theorem local_eval {w : ℕ} (j : Fin w) (s : Cell M) (a : Fin (w+2) → Cell M) :
    (localGate M j s).eval (fun z => decide (a z.1 = z.2)) = decide
      (M.cellRule (a ⟨j.val, by omega⟩) (a ⟨j.val+1, by omega⟩) (a ⟨j.val+2, by omega⟩) = s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [localGate, Expr.eval_any, Expr.mem_elems, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l,c,r⟩,h⟩
    split_ifs at h with rule
    · simp only [Expr.eval, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [h.1, h.2.1, h.2.2] using rule
    · contradiction
  · intro h
    refine ⟨(a ⟨j.val, by omega⟩, a ⟨j.val+1, by omega⟩, a ⟨j.val+2, by omega⟩), ?_⟩
    simp [h, Expr.eval]

private def gateBudget := 2 + 6 * Fintype.card (Cell M × Cell M × Cell M)

private theorem local_size {w : ℕ} (j : Fin w) (s : Cell M) :
    (localGate M j s).size ≤ gateBudget M := by
  have hg : ∀ v : Cell M × Cell M × Cell M, (if M.cellRule v.1 v.2.1 v.2.2 = s then
      (Expr.conj (.var (⟨j.val, by omega⟩, v.1)) (.conj (.var (⟨j.val+1, by omega⟩, v.2.1))
        (.var (⟨j.val+2, by omega⟩, v.2.2))) : Expr (Row M (w+2))) else .lit false).size ≤ 5 := by
    intro v; split_ifs <;> simp [Expr.size]
  have hb := Expr.size_any (Expr.elems _) _ hg
  rw [Expr.length_elems] at hb
  exact hb.trans (by unfold gateBudget; omega)

-- At time t the required interval starts at z and contains w cells.
private noncomputable def row (n : ℕ) : (t : ℕ) → (z : ℤ) → (w : ℕ) → Net (Fin n) (Row M w)
  | 0, z, _ => .layer (fun p => initGate M n (z+p.1.val) p.2)
  | t+1, z, w => .seq (row n t (z-1) (w+2)) (.layer (fun p => localGate M p.1 p.2))

private theorem row_eval (x : Fin n → Bool) (t : ℕ) (z : ℤ) (w : ℕ) (p : Row M w) :
    (row M n t z w).eval x p = decide (M.encode (M.run (M.init (List.ofFn x)) t) (z+p.1.val) = p.2) := by
  induction t generalizing w z with
  | zero => exact init_eval M x _ _
  | succ t ih =>
    let c := M.run (M.init (List.ofFn x)) t
    let a (j : Fin (w+2)) := M.encode c ((z-1) + j.val)
    have he : (row M n t (z-1) (w+2)).eval x = fun q => decide (a q.1 = q.2) := funext (ih _ _)
    change (localGate M p.1 p.2).eval ((row M n t (z-1) (w+2)).eval x) = _
    rw [he, local_eval, TM.run_succ]
    have hr := congrFun (M.toWCC_step_encode c) (z+p.1.val)
    change M.cellRule (M.encode c (z+p.1.val-1)) (M.encode c (z+p.1.val))
      (M.encode c (z+p.1.val+1)) = M.encode (M.next c) (z+p.1.val) at hr
    dsimp only [a]
    push_cast
    rw [show z-1+p.1.val = z+p.1.val-1 by omega,
      show z-1+(p.1.val+1) = z+p.1.val by omega, show z-1+(p.1.val+2) = z+p.1.val+1 by omega, hr]

private def cellBudget := Fintype.card (Cell M) * gateBudget M

private theorem row_size (n t : ℕ) (z : ℤ) (w : ℕ) :
    (row M n t z w).size ≤ (t+1)*(w+2*t)*cellBudget M := by
  have layer_bound {w' : ℕ} {I : Type} (f : Row M w' → Expr I) (h : ∀ p, (f p).size ≤ gateBudget M) :
      (Net.layer f).size ≤ w'*cellBudget M := by
    change ∑ p, (f p).size ≤ _
    calc _ ≤ ∑ _p : Row M w', gateBudget M := Finset.sum_le_sum (fun i _ => h i)
         _ = _ := by simp [Row, cellBudget, Nat.mul_assoc]
  induction t generalizing w z with
  | zero =>
    simpa [row] using layer_bound (w' := w) (fun p => initGate M n (z+p.1.val) p.2)
      (fun p => (init_size M _ _ _).trans (by unfold gateBudget; omega))
  | succ t ih =>
    have prev := ih (z-1) (w+2)
    have cur := layer_bound (w' := w) (fun p => localGate M p.1 p.2) (fun p => local_size M _ _)
    change (row M n t (z-1) (w+2)).size + (Net.layer _).size ≤ _
    have eqn : w+2+2*t = w+2*(t+1) := by ring
    rw [eqn] at prev
    calc _ ≤ _ := Nat.add_le_add prev cur
         _ ≤ (t+1)*(w+2*(t+1))*cellBudget M + (w+2*(t+1))*cellBudget M :=
           Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
         _ = _ := by ring

private theorem reached (x : List Bool) (t : ℕ) :
    -((t : ℕ) : ℤ) ≤ (M.run (M.init x) t).head ∧ (M.run (M.init x) t).head ≤ t := by
  induction t with
  | zero => simp [TM.run, TM.init]
  | succ t ih =>
    rw [TM.run_succ]
    have := PVNP.CrossingCapacity.one_tape_head_speed M (M.run (M.init x) t)
    push_cast
    omega

private noncomputable def readout (t : ℕ) : Expr (Row M (2*t+1)) :=
  Expr.any (Expr.elems (Row M (2*t+1))) fun p => if M.cellAcc p.2 then .var p else .lit false

private noncomputable def plain (n t : ℕ) : Net (Fin n) Unit :=
  .seq (row M n t (-(t : ℤ)) (2*t+1)) (.layer (fun _ => readout M t))

private theorem plain_eval (x : Fin n → Bool) (t : ℕ) :
    (plain M n t).eval x () = M.acc (M.run (M.init (List.ofFn x)) t).q := by
  let c := M.run (M.init (List.ofFn x)) t
  have ran := reached M (List.ofFn x) t
  change - (t : ℤ) ≤ c.head ∧ c.head ≤ t at ran
  apply Bool.eq_iff_iff.mpr
  change (readout M t).eval ((row M n t (-(t:ℤ)) (2*t+1)).eval x) = true ↔ _
  rw [readout, Expr.eval_any]
  constructor
  · rintro ⟨⟨j,s⟩, _, hs⟩
    split_ifs at hs with ha
    · change (row M n t (-(t:ℤ)) (2*t+1)).eval x (j,s) = true at hs
      rw [row_eval, decide_eq_true_eq] at hs
      change M.encode c (-(t:ℤ)+j.val) = s at hs
      subst s
      change M.cellAcc (M.encode c (-(t:ℤ)+j.val)) = true at ha
      by_cases h : -(t:ℤ)+j.val = c.head
      · simpa [TM.encode, TM.cellAcc, h, c] using ha
      · simp [TM.encode, TM.cellAcc, h] at ha
    · contradiction
  · intro ha
    let j : Fin (2*t+1) := ⟨(c.head+t).toNat, by omega⟩
    have pos : -(t:ℤ) + j.val = c.head := by dsimp [j]; omega
    refine ⟨(j,M.encode c c.head), Expr.mem_elems _, ?_⟩
    have ok : M.cellAcc (M.encode c c.head) = true := by simpa [TM.cellAcc, TM.encode, c] using ha
    simp only [ok, if_true, Expr.eval]
    rw [row_eval, pos]
    simp [c]

private def K := cellBudget M + 2 * Fintype.card (Cell M) + 1

private theorem plain_size (n t : ℕ) : (plain M n t).size ≤ K M * (t+1)*(4*t+2) := by
  have hr := row_size M n t (-(t:ℤ)) (2*t+1)
  have hread := Expr.size_any (Expr.elems (Row M (2*t+1)))
    (fun p => if M.cellAcc p.2 then Expr.var p else Expr.lit false) (k := 1)
    (fun p => by dsimp only; split_ifs <;> simp [Expr.size])
  rw [Expr.length_elems, show Fintype.card (Row M (2*t+1)) = (2*t+1)*Fintype.card (Cell M) by rw [Fintype.card_prod, Fintype.card_fin]] at hread
  change (row M n t _ _).size + (∑ _ : Unit, (readout M t).size) ≤ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  change (readout M t).size ≤ _ at hread
  unfold K
  nlinarith [hr, hread, Nat.zero_le (cellBudget M), Nat.zero_le (Fintype.card (Cell M))]

/-- An ordinary bounded-fan-in Boolean DAG for the first answer by time t. -/
noncomputable def circuit (n t : ℕ) : Net (Fin n) Unit := plain (stop M) n t

def machineConstant := K (stop M)

theorem circuit_size (n t : ℕ) :
    (circuit M n t).size ≤ machineConstant M * (t+1)*(4*t+2) := plain_size _ _ _

theorem circuit_first (x : Fin n → Bool) (t : ℕ) (b : Bool) (hb : FirstAnswer (M.out (List.ofFn x)) t b) :
    (circuit M n t).eval x () = b := by
  have hs := stop_answer M _ t b hb
  rw [circuit, plain_eval]
  unfold TM.out TM.ans answerOf at hs
  split_ifs at hs <;> cases b <;> simp_all

theorem P_TM_subset_PPoly : P_TM ⊆ PPoly := by
  rintro L ⟨M,p,hM⟩
  refine ⟨Polynomial.C (machineConstant M) * (p+1) * (4*p+2), fun n =>
    ⟨circuit M n (p.eval n), by simpa using circuit_size M n (p.eval n), fun x => ?_⟩⟩
  obtain ⟨b,hb,hl⟩ := hM (List.ofFn x)
  rw [List.length_ofFn] at hb
  rw [circuit_first M x _ b hb]
  exact hl

end PVNP.TMBooleanTableau
