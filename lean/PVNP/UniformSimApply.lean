import PVNP.UniformSimRot

/-!
# Milestone 5, part 11: windows and the local rule

* `tasks_shift`: the rotation tasks of offset `v` shift by `δ_v = Σ_a (v_a − r)·B^a`.
* `tasks_loop`: the tasks of an offset run from `taskEntry` to `wsave`.
* `offset_loop`: for every offset `v`, the window `win v` of each cell receives the `cur` value of
  the cell `δ_v` further along the list.
* `apply_trip`: the local rule is applied on the box.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-- Shift of a rotation task: `±B^a`. -/
def taskShift (B : ℕ) (a : Fin σ.W.d × Bool) : ℤ := (if a.2 then 1 else -1) * (B : ℤ) ^ (a.1 : ℕ)

/-- The cyclic shift of offset `v`: `δ_v = Σ_a (v_a − r)·B^a`. -/
def delta (B : ℕ) (v : σ.Off) : ℤ := ∑ a : Fin σ.W.d, ((v a : ℤ) - σ.W.r) * (B : ℤ) ^ (a : ℕ)

theorem tasks_shift (B : ℕ) (v : σ.Off) :
    ((σ.tasks v).map (σ.taskShift B)).sum = σ.delta B v := by
  unfold tasks delta
  rw [sum_map_flatMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
  simp only [taskShift]
  by_cases h : σ.W.r < (v a : ℕ)
  · rw [decide_eq_true h, if_pos rfl, Int.natAbs_of_nonneg (by omega)]
    ring
  · rw [decide_eq_false h, if_neg (by simp), Int.ofNat_natAbs_of_nonpos (by omega)]
    ring

/-- **The tasks of one offset.** -/
theorem tasks_loop (i : Fin σ.K) (o B : ℕ) (l0 : List (Cell σ)) (hr : σ.RulerOK o B l0) :
    ∀ (q t : ℕ), t + q = (σ.tasks (σ.offs i)).length → ∀ (l : List (Cell σ)) (s : ℤ),
      σ.TS l0 s l →
      ∃ (l' : List (Cell σ)) (c : ℕ), RN σ.prog (σ.taskEntry i t, l) (.wsave i, l') c ∧
        c ≤ q * (2 * B + 1) ^ σ.W.d ∧
        σ.TS l0 (s + (((σ.tasks (σ.offs i)).drop t).map (σ.taskShift B)).sum) l' := by
  intro q
  induction q with
  | zero =>
    intro t ht l s hts
    have e : σ.taskEntry i t = .wsave i := by unfold taskEntry; rw [dif_neg (by omega)]
    rw [e, List.drop_eq_nil_of_le (by omega)]
    exact ⟨l, 0, RN.refl _, Nat.zero_le _, by simpa using hts⟩
  | succ q ih =>
    intro t ht l s hts
    have htl : t < (σ.tasks (σ.offs i)).length := by omega
    have htN : t < σ.NT := by
      have := σ.tasks_length_le (σ.offs i); show t < σ.W.d * σ.W.r + 1; omega
    have e : σ.taskEntry i t = σ.startRot i ⟨t, htN⟩ (σ.task i t).1 := by
      unfold taskEntry; rw [dif_pos htl]
    obtain ⟨l1, hrn1, hts1, -⟩ := σ.rot_level i ⟨t, htN⟩ o B l0 hr (σ.task i t).1.val le_rfl l s hts
    simp only [Fin.eta] at hrn1
    rw [σ.retRot_top i ⟨t, htN⟩] at hrn1
    obtain ⟨l2, c, hrn2, hc, hts2⟩ := ih (t + 1) (by omega) l1 _ hts1
    refine ⟨l2, rotCost B (σ.task i t).1.val + c, ?_, ?_, ?_⟩
    · rw [e]; exact hrn1.trans hrn2
    · have h1 := rotCost_le B (σ.task i t).1.val
      have h2 : (2 * B + 1) ^ ((σ.task i t).1.val) ≤ (2 * B + 1) ^ σ.W.d :=
        Nat.pow_le_pow_right (by omega) (σ.task i t).1.isLt.le
      nlinarith
    · rw [List.drop_eq_getElem_cons htl, List.map_cons, List.sum_cons]
      have ht : (σ.tasks (σ.offs i))[t] = σ.task i t := by
        simp only [task, List.getD_eq_getElem _ _ htl]
      rw [ht]
      convert hts2 using 1
      simp only [taskShift]
      ring

/-! ### Copy, save, apply -/

theorem wcopy_trip (i : Fin σ.K) (l : List (Cell σ)) :
    σ.prog.stepP (.wcopy i, l) = .inl (σ.taskEntry i 0, (σ.prog.trip (.wcopy i) l).1) ∧
      (σ.prog.trip (.wcopy i) l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.wcopy i) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.wcopy i) l).1[j] = {l[j] with tmp := l[j].cur} := by
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get (.wcopy i) (fun _ _ => rfl) (fun _ => rfl) l
    (fun _ => σ.buf0) rfl (fun _ _ => rfl)
  exact ⟨σ.stepP_inl_of rfl, hlen, fun j hj hj' => hget j hj' hj⟩

theorem wsave_trip (i : Fin σ.K) (l : List (Cell σ)) :
    σ.prog.stepP (.wsave i, l) =
        .inl ((if h : i.val + 1 < σ.K then .wcopy ⟨i.val + 1, h⟩ else .apply),
          (σ.prog.trip (.wsave i) l).1) ∧
      (σ.prog.trip (.wsave i) l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.wsave i) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.wsave i) l).1[j] =
          {l[j] with win := Function.update l[j].win (σ.offs i) l[j].tmp} := by
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get (.wsave i) (fun _ _ => rfl) (fun _ => rfl) l
    (fun _ => σ.buf0) rfl (fun _ _ => rfl)
  refine ⟨σ.stepP_inl_of ?_, hlen, fun j hj hj' => hget j hj' hj⟩
  by_cases h : i.val + 1 < σ.K <;> simp [next, h]

theorem apply_trip (l : List (Cell σ)) :
    σ.prog.stepP (.apply, l) = .inl (.dprep, (σ.prog.trip .apply l).1) ∧
      (σ.prog.trip .apply l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip .apply l).1.length) (hj' : j < l.length),
        (σ.prog.trip .apply l).1[j] =
          {l[j] with
            cur := if l[j].box then (if l[j].mem then σ.W.U l[j].win else σ.W.sbd) else l[j].cur} := by
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get .apply (fun _ _ => rfl) (fun _ => rfl) l
    (fun _ => σ.buf0) rfl (fun _ _ => rfl)
  exact ⟨σ.stepP_inl_of rfl, hlen, fun j hj hj' => hget j hj' hj⟩

/-! ### The offset loop -/

/-- Erasure of the window fields. -/
def eraseW (c : Cell σ) : Cell σ :=
  {c with tmp := σ.W.sbd, cnt := fun _ => false, win := fun _ => σ.W.sbd}

/-- State of the offset loop before offset `i`. -/
structure OffSt (B : ℕ) (lD : List (Cell σ)) (i : ℕ) (l : List (Cell σ)) : Prop where
  len : l.length = lD.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lD.length), σ.eraseW l[j] = σ.eraseW lD[j]
  win : ∀ (j : ℕ) (hj : j < l.length) (i' : Fin σ.K), i'.val < i →
    l[j].win (σ.offs i') = (lD.getD (cyc lD.length j (σ.delta B (σ.offs i'))) σ.dflt).cur

theorem eraseW_fields {a b : Cell σ} (h : σ.eraseW a = σ.eraseW b) :
    a.fst = b.fst ∧ a.rfst = b.rfst ∧ a.rul = b.rul ∧ a.cur = b.cur := by
  have h1 := congrArg Cell.fst h
  have h2 := congrArg Cell.rfst h
  have h3 := congrArg Cell.rul h
  have h4 := congrArg Cell.cur h
  exact ⟨h1, h2, h3, h4⟩

theorem eraseW_of_eraseT {a b : Cell σ} (h : σ.eraseT a = σ.eraseT b) : σ.eraseW a = σ.eraseW b := by
  have := congrArg (fun c : Cell σ => {c with win := fun _ => σ.W.sbd}) h
  exact this

theorem RulerOK.of_eraseW {o B : ℕ} {lD l : List (Cell σ)} (hr : σ.RulerOK o B lD)
    (hlen : l.length = lD.length)
    (hf : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < lD.length), σ.eraseW l[j] = σ.eraseW lD[j]) :
    σ.RulerOK o B l := by
  refine ⟨by have := hr.pos; omega, by have := hr.room; omega, hr.B_pos, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_⟩
  · rw [(σ.eraseW_fields (hf j hj (by omega))).1, hr.fst j (by omega)]
  · rw [(σ.eraseW_fields (hf j hj (by omega))).2.1, hr.rfst j (by omega)]
  · rw [(σ.eraseW_fields (hf j hj (by omega))).2.2.1, hr.rul j (by omega)]

/-- One offset: copy, rotate, save. -/
theorem offset_step (i : Fin σ.K) (o B : ℕ) (lD l : List (Cell σ)) (hr : σ.RulerOK o B lD)
    (hs : σ.OffSt B lD i.val l) :
    ∃ (l' : List (Cell σ)) (c : ℕ),
      RN σ.prog (.wcopy i, l) ((if h : i.val + 1 < σ.K then .wcopy ⟨i.val + 1, h⟩ else .apply), l')
        c ∧ c ≤ 2 + σ.W.d * σ.W.r * (2 * B + 1) ^ σ.W.d ∧ σ.OffSt B lD (i.val + 1) l' := by
  have hlen := hs.len
  have hrl := hr.of_eraseW σ hs.len hs.frame
  -- copy
  obtain ⟨hs1, hlen1, hget1⟩ := σ.wcopy_trip i l
  set l1 : List (Cell σ) := (σ.prog.trip (.wcopy i) l).1 with hl1
  have hts1 : σ.TS l 0 l1 := ⟨hlen1, fun j hj hj' => by rw [hget1 j hj hj']; rfl,
    fun j hj => by rw [hget1 j hj (by omega), cyc_zero (by omega), List.getD_eq_getElem]⟩
  -- rotate
  obtain ⟨l2, c, hrn2, hc, hts2⟩ := σ.tasks_loop i o B l hrl (σ.tasks (σ.offs i)).length 0
    (by omega) l1 0 hts1
  rw [List.drop_zero, σ.tasks_shift, zero_add] at hts2
  -- save
  obtain ⟨hs3, hlen3, hget3⟩ := σ.wsave_trip i l2
  have hlen2 := hts2.len
  refine ⟨_, 1 + c + 1, (RN.single hs1).trans (hrn2.trans (RN.single hs3)), ?_, ?_⟩
  · have := σ.tasks_length_le (σ.offs i)
    have h2 : c ≤ σ.W.d * σ.W.r * (2 * B + 1) ^ σ.W.d :=
      le_trans hc (Nat.mul_le_mul_right _ this)
    omega
  refine ⟨by rw [hlen3, hlen2, hlen], fun j hj hj' => ?_, fun j hj i' hi' => ?_⟩
  · rw [hget3 j hj (by omega)]
    have h := σ.eraseW_of_eraseT (hts2.frame j (by omega) (by omega))
    rw [← hs.frame j (by omega) hj', ← h]
    rfl
  · rw [hget3 j hj (by omega)]
    simp only
    have hT := hts2.frame j (by omega) (by omega)
    have hwin : l2[j].win = l[j].win := by
      have := congrArg Cell.win hT
      exact this
    by_cases hii : i' = i
    · subst hii
      rw [Function.update_self, hts2.tmp j (by omega), hlen]
      by_cases hp : cyc lD.length j (σ.delta B (σ.offs i')) < l.length
      · rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ (by omega)]
        exact (σ.eraseW_fields (hs.frame _ hp (by omega))).2.2.2
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    · have hne : σ.offs i' ≠ σ.offs i := fun h => hii (by
        have := (finFunctionFinEquiv.symm).injective h
        exact this)
      rw [Function.update_of_ne hne, hwin]
      exact hs.win j (by omega) i' (by
        have : i'.val ≠ i.val := fun h => hii (Fin.ext h)
        omega)

/-- **The offset loop**: all windows are filled. -/
theorem offset_loop (o B : ℕ) (lD : List (Cell σ)) (hr : σ.RulerOK o B lD) :
    ∀ (q i : ℕ) (hi : i < σ.K), i + q + 1 = σ.K → ∀ l : List (Cell σ), σ.OffSt B lD i l →
      ∃ (l' : List (Cell σ)) (c : ℕ), RN σ.prog (.wcopy ⟨i, hi⟩, l) (.apply, l') c ∧
        c ≤ (q + 1) * (2 + σ.W.d * σ.W.r * (2 * B + 1) ^ σ.W.d) ∧ σ.OffSt B lD σ.K l' := by
  intro q
  induction q with
  | zero =>
    intro i hi hiq l hs
    obtain ⟨l', c, hrn, hc, hs'⟩ := σ.offset_step ⟨i, hi⟩ o B lD l hr hs
    rw [dif_neg (show ¬ (⟨i, hi⟩ : Fin σ.K).val + 1 < σ.K by simp; omega)] at hrn
    exact ⟨l', c, hrn, by omega, by simpa [show i + 1 = σ.K by omega] using hs'⟩
  | succ q ih =>
    intro i hi hiq l hs
    obtain ⟨l1, c1, hrn1, hc1, hs1⟩ := σ.offset_step ⟨i, hi⟩ o B lD l hr hs
    rw [dif_pos (show (⟨i, hi⟩ : Fin σ.K).val + 1 < σ.K by simp; omega)] at hrn1
    obtain ⟨l2, c2, hrn2, hc2, hs2⟩ := ih (i + 1) (by omega) (by omega) l1 hs1
    refine ⟨l2, c1 + c2, hrn1.trans hrn2, ?_, hs2⟩
    nlinarith

theorem offs_surj (v : σ.Off) : ∃ i : Fin σ.K, σ.offs i = v :=
  ⟨finFunctionFinEquiv v, by simp [offs]⟩

theorem OffSt.win_all {B : ℕ} {lD l : List (Cell σ)} (hs : σ.OffSt B lD σ.K l) (j : ℕ)
    (hj : j < l.length) (v : σ.Off) :
    l[j].win v = (lD.getD (cyc lD.length j (σ.delta B v)) σ.dflt).cur := by
  obtain ⟨i, rfl⟩ := σ.offs_surj v
  exact hs.win j hj i i.isLt

/-- The neighbours of a member cell are box cells at the shifted positions. -/
theorem member_nbr (x : List Bool) (idx : ℕ) (hidx : idx < σ.Bx x)
    (hmem : site σ.W.d (σ.Rx x) idx ∈ σ.W.Λ x.length) (v : σ.Off) :
    ∃ idx' : ℕ, idx' < σ.Bx x ∧ (idx' : ℤ) = idx + σ.delta (side (σ.Rx x)) v ∧
      site σ.W.d (σ.Rx x) idx' = site σ.W.d (σ.Rx x) idx + σ.W.offset v := by
  obtain ⟨idx', h1, h2, h3⟩ := nbr_idx σ.W.d (σ.Rx x) σ.W.r idx hidx v (fun k => by
    have hm := σ.W.margin x.length _ hmem k
    have hv := (v k).isLt
    have hb : |((v k : ℕ) : ℤ) - σ.W.r| ≤ σ.W.r := by rw [abs_le]; constructor <;> omega
    calc |site σ.W.d (σ.Rx x) idx k + (((v k : ℕ) : ℤ) - σ.W.r)|
        ≤ |site σ.W.d (σ.Rx x) idx k| + |((v k : ℕ) : ℤ) - σ.W.r| := abs_add_le _ _
      _ ≤ σ.Rx x := by simp only [Rx]; linarith)
  refine ⟨idx', h1, by rw [h2]; rfl, funext fun k => ?_⟩
  rw [h3 k]
  rfl

end Spec

end PVNP.UniformSim
