import PVNP.UniformSimPack

/-!
# Milestone 5, part 10: cyclic rotations of the window track

* `TS l0 s l`: the `tmp` track of `l` holds the `cur` track of `l0` cyclically shifted by `s`.
* `rotU_trip`: a unit rotation shifts by `±1`.
* `rot_level`: a level-`k` rotation, nested over the ruler of `B` cells, shifts by `±B^k`.
* `tasks_loop`: the rotation tasks of offset `v` shift by `δ_v = Σ_a (v_a − r)·B^a`.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-! ### Cyclic indices -/

/-- Cyclic index `(j + s) mod ℓ`. -/
def cyc (ℓ j : ℕ) (s : ℤ) : ℕ := (((j : ℤ) + s) % (ℓ : ℤ)).toNat

theorem cyc_lt {ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℕ) (s : ℤ) : cyc ℓ j s < ℓ := by
  unfold cyc
  have h1 := Int.emod_nonneg ((j : ℤ) + s) (show (ℓ : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos ((j : ℤ) + s) (show (0 : ℤ) < ℓ by omega)
  omega

theorem cyc_cast {ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℕ) (s : ℤ) :
    (cyc ℓ j s : ℤ) = ((j : ℤ) + s) % (ℓ : ℤ) := by
  unfold cyc
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem cyc_zero {ℓ j : ℕ} (hj : j < ℓ) : cyc ℓ j 0 = j := by
  have := cyc_cast (show 0 < ℓ by omega) j 0
  rw [add_zero, Int.emod_eq_of_lt (by omega) (by omega)] at this
  exact_mod_cast this

theorem cyc_of_lt {ℓ j : ℕ} {s : ℤ} (h0 : 0 ≤ (j : ℤ) + s) (h1 : (j : ℤ) + s < ℓ) :
    (cyc ℓ j s : ℤ) = j + s := by
  rw [cyc_cast (by omega), Int.emod_eq_of_lt h0 h1]

theorem cyc_shift {ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℕ) (s : ℤ) (e : ℤ) :
    cyc ℓ (cyc ℓ j e) s = cyc ℓ j (e + s) := by
  have h := cyc_cast hℓ (cyc ℓ j e) s
  rw [cyc_cast hℓ j e, Int.emod_add_emod] at h
  have h' := cyc_cast hℓ j (e + s)
  have : ((cyc ℓ (cyc ℓ j e) s : ℕ) : ℤ) = ((cyc ℓ j (e + s) : ℕ) : ℤ) := by
    rw [h, h', add_assoc]
  exact_mod_cast this

/-- Sums over a concatenation. -/
theorem sum_map_flatMap {α β : Type} (f : α → List β) (g : β → ℤ) :
    ∀ L : List α, ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: L => by simp [List.flatMap_cons, sum_map_flatMap f g L]

namespace Spec

variable (σ : Spec)

/-! ### General round trips -/

theorem trip_gen (i : Ins σ) (he : ∀ b, σ.ext i b = none) (l : List (Cell σ))
    (bufAt bufR : ℕ → Buf σ) (h0 : bufAt 0 = σ.buf0)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (σ.fwd i (bufAt j) l[j]).2 = bufAt (j + 1))
    (hend : bufR l.length = bufAt l.length)
    (hbstep : ∀ (j : ℕ) (hj : j < l.length),
      (σ.bwd i (bufR (j + 1)) (σ.fwd i (bufAt j) l[j]).1).2 = bufR j) :
    (σ.prog.trip i l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip i l).1.length) (hj' : j < l.length),
        (σ.prog.trip i l).1[j] = (σ.bwd i (bufR (j + 1)) (σ.fwd i (bufAt j) l[j]).1).1 := by
  have hlen : (fscan (σ.fwd i) σ.buf0 l).1.length = l.length := fscan_length _ _ _
  have hfb : (fscan (σ.fwd i) σ.buf0 l).2 = bufR (fscan (σ.fwd i) σ.buf0 l).1.length := by
    rw [hlen, hend, ← h0]; exact fscan_spec_buf _ l bufAt hstep
  have hT : σ.prog.trip i l =
      bscan (σ.bwd i) (bufR (fscan (σ.fwd i) σ.buf0 l).1.length) (fscan (σ.fwd i) σ.buf0 l).1 := by
    rw [trip_def, he, Option.toList_none, List.append_nil, hfb]
  have hget : ∀ (j : ℕ) (hj : j < l.length),
      (fscan (σ.fwd i) σ.buf0 l).1[j]'(by omega) = (σ.fwd i (bufAt j) l[j]).1 := by
    intro j hj
    simpa [h0] using fscan_spec_get _ l bufAt hstep j hj
  have hst' : ∀ (j : ℕ) (hj : j < (fscan (σ.fwd i) σ.buf0 l).1.length),
      (σ.bwd i (bufR (j + 1)) (fscan (σ.fwd i) σ.buf0 l).1[j]).2 = bufR j := by
    intro j hj
    rw [hget j (by omega)]
    exact hbstep j (by omega)
  refine ⟨by rw [hT, bscan_length, hlen], fun j hj hj' => ?_⟩
  have e := bscan_spec_get (σ.bwd i) (fscan (σ.fwd i) σ.buf0 l).1 bufR hst' j (by omega)
  refine (List.getElem_of_eq (congrArg Prod.fst hT) _).trans (e.trans ?_)
  rw [hget j hj']

/-! ### The shift invariant -/

/-- Erasure of the rotation fields. -/
def eraseT (c : Cell σ) : Cell σ := {c with tmp := σ.W.sbd, cnt := fun _ => false}

/-- `l` is `l0` with the `tmp` track holding the `cur` track of `l0` cyclically shifted by `s`. -/
structure TS (l0 : List (Cell σ)) (s : ℤ) (l : List (Cell σ)) : Prop where
  len : l.length = l0.length
  frame : ∀ (j : ℕ) (hj : j < l.length) (hj' : j < l0.length), σ.eraseT l[j] = σ.eraseT l0[j]
  tmp : ∀ (j : ℕ) (hj : j < l.length), l[j].tmp = (l0.getD (cyc l0.length j s) σ.dflt).cur

theorem eraseT_fields {a b : Cell σ} (h : σ.eraseT a = σ.eraseT b) :
    a.fst = b.fst ∧ a.rfst = b.rfst ∧ a.rul = b.rul := by
  have h1 := congrArg Cell.fst h
  have h2 := congrArg Cell.rfst h
  have h3 := congrArg Cell.rul h
  exact ⟨h1, h2, h3⟩

/-! ### Unit rotations -/

/-- A unit rotation (level `0`). -/
theorem rotU_trip (i : Fin σ.K) (t : Fin σ.NT) (l0 l : List (Cell σ)) (s : ℤ)
    (hts : σ.TS l0 s l) (hℓ : 0 < l0.length)
    (hfst : ∀ (j : ℕ) (hj : j < l0.length), l0[j].fst = decide (j = 0)) :
    σ.prog.stepP (.rotU i t, l) = .inl (σ.retRot i t ⟨0, σ.W.d_pos⟩, (σ.prog.trip (.rotU i t) l).1) ∧
      σ.TS l0 (s + if (σ.task i t).2 then 1 else -1) (σ.prog.trip (.rotU i t) l).1 ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.rotU i t) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.rotU i t) l).1[j].cnt = l[j].cnt := by
  have hlen := hts.len
  have hfl : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0) := fun j hj => by
    rw [(σ.eraseT_fields (hts.frame j hj (by omega))).1, hfst j (by omega)]
  refine ⟨σ.stepP_inl_of rfl, ?_⟩
  suffices h : σ.TS l0 (s + if (σ.task i t).2 then 1 else -1) (σ.prog.trip (.rotU i t) l).1 ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.rotU i t) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.rotU i t) l).1[j].cnt = l[j].cnt from h
  by_cases hdir : (σ.task i t).2 = true
  · -- left
    rw [if_pos hdir]
    let bufAt : ℕ → Buf σ := fun j =>
      {σ.buf0 with cS := if j = 0 then none else some (l.getD 0 σ.dflt).tmp}
    let bufR : ℕ → Buf σ := fun j =>
      {σ.buf0 with cS := some (l.getD (j % l.length) σ.dflt).tmp}
    have hf : ∀ (j : ℕ) (hj : j < l.length), σ.fwd (.rotU i t) (bufAt j) l[j] = (l[j], bufAt (j + 1)) := by
      intro j hj
      simp only [fwd, hdir, if_true, hfl j hj, bufAt]
      by_cases h0 : j = 0
      · subst h0; simp [List.getElem?_eq_getElem hj]
      · simp [h0]
    obtain ⟨hlen', hget⟩ := σ.trip_gen (.rotU i t) (fun _ => rfl) l bufAt bufR rfl
      (fun j hj => by rw [hf j hj]) (by simp [bufAt, bufR, show l.length ≠ 0 by omega])
      (fun j hj => by
        rw [hf j hj]
        simp only [bwd, hdir, if_true, bufR, Nat.mod_eq_of_lt hj, List.getD_eq_getElem _ _ hj])
    refine ⟨⟨by rw [hlen', hlen], fun j hj hj' => ?_, fun j hj => ?_⟩, fun j hj hj' => ?_⟩
    · rw [hget j hj (by omega), hf j (by omega)]
      simp only [bwd, hdir, if_true]
      exact hts.frame j (by omega) hj'
    · rw [hget j hj (by omega), hf j (by omega)]
      simp only [bwd, hdir, if_true, bufR, Option.getD_some]
      have hm : (j + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
      rw [List.getD_eq_getElem _ _ hm, hts.tmp _ hm, hlen]
      congr 2
      rw [show s + 1 = 1 + s by ring, ← cyc_shift hℓ j s 1]
      congr 1
    · rw [hget j hj hj', hf j hj']
      simp only [bwd, hdir, if_true]
  · -- right
    have hdir' : (σ.task i t).2 = false := by simpa using hdir
    rw [if_neg hdir]
    let bufAt : ℕ → Buf σ := fun j =>
      {σ.buf0 with cS := if j = 0 then none else some (l.getD (j - 1) σ.dflt).tmp}
    have hf : ∀ (j : ℕ) (hj : j < l.length), σ.fwd (.rotU i t) (bufAt j) l[j] =
        ({l[j] with tmp := (bufAt j).cS.getD l[j].tmp}, bufAt (j + 1)) := by
      intro j hj
      simp only [fwd, hdir', bufAt, Bool.false_eq_true, if_false]
      simp [List.getElem?_eq_getElem hj]
    obtain ⟨hlen', hget, -⟩ := σ.trip_const_bwd (.rotU i t) (fun _ => rfl)
      (fun b a => by simp only [bwd, hdir', Bool.false_eq_true, if_false])
      l bufAt (by simp [bufAt, buf0]) (fun j hj => by rw [hf j hj])
    refine ⟨⟨by rw [hlen', hlen], fun j hj hj' => ?_, fun j hj => ?_⟩, fun j hj hj' => ?_⟩
    · rw [hget j hj (by omega), hf j (by omega)]
      simp only [bwd, hdir', Bool.false_eq_true, if_false]
      split_ifs <;> exact hts.frame j (by omega) hj'
    · rw [hget j hj (by omega), hf j (by omega)]
      simp only [bwd, hdir', Bool.false_eq_true, if_false, hfl j (by omega)]
      by_cases h0 : j = 0
      · subst h0
        simp only [decide_true, if_true, bufAt, show l.length ≠ 0 by omega, if_false,
          Option.getD_some]
        rw [List.getD_eq_getElem _ _ (by omega), hts.tmp _ (by omega), hlen]
        congr 2
        have h1 := cyc_cast hℓ (l0.length - 1) s
        have h2 := cyc_cast hℓ 0 (s + -1)
        have : ((l0.length - 1 : ℕ) : ℤ) + s = ((0 : ℕ) : ℤ) + (s + -1) + l0.length := by
          push_cast [show 1 ≤ l0.length by omega]; ring
        rw [this, Int.add_emod_right] at h1
        exact_mod_cast h1.trans h2.symm
      · simp only [h0, decide_false, Bool.false_eq_true, if_false, bufAt, Option.getD_some]
        rw [List.getD_eq_getElem _ _ (by omega), hts.tmp _ (by omega)]
        congr 2
        have h1 := cyc_cast hℓ (j - 1) s
        have h2 := cyc_cast hℓ j (s + -1)
        have : ((j - 1 : ℕ) : ℤ) + s = (j : ℤ) + (s + -1) := by
          push_cast [show 1 ≤ j by omega]; ring
        rw [this] at h1
        exact_mod_cast h1.trans h2.symm
    · rw [hget j hj hj', hf j hj']
      simp only [bwd, hdir', Bool.false_eq_true, if_false]
      split_ifs <;> rfl

/-! ### Counter trips -/

theorem rotI_trip (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d) (l : List (Cell σ)) :
    σ.prog.stepP (.rotI i t k, l) =
        .inl (σ.startRot i t ⟨k.val - 1, by omega⟩, (σ.prog.trip (.rotI i t k) l).1) ∧
      (σ.prog.trip (.rotI i t k) l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.rotI i t k) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.rotI i t k) l).1[j] = {l[j] with cnt := Function.update l[j].cnt k l[j].rfst} := by
  obtain ⟨hlen, hget, -⟩ := σ.trip_fwd_get (.rotI i t k) (fun _ _ => rfl) (fun _ => rfl) l
    (fun _ => σ.buf0) rfl (fun _ _ => rfl)
  exact ⟨σ.stepP_inl_of rfl, hlen, fun j hj hj' => hget j hj' hj⟩

/-- Buffer of a counter advance after `j` cells, counter at `p`. -/
def bufA (o B p j : ℕ) : Buf σ :=
  {σ.buf0 with
    f1 := decide (j = p + 1)
    f2 := decide (p + 1 < j ∧ o ≤ p + 1 ∧ p + 1 < o + B)}

theorem rotA_trip (i : Fin σ.K) (t : Fin σ.NT) (k : Fin σ.W.d) (o B p : ℕ) (l : List (Cell σ))
    (hcnt : ∀ (j : ℕ) (hj : j < l.length), l[j].cnt k = decide (j = p))
    (hrul : ∀ (j : ℕ) (hj : j < l.length), l[j].rul = decide (o ≤ j ∧ j < o + B)) :
    σ.prog.stepP (.rotA i t k, l) =
        .inl ((if decide (p + 1 < l.length ∧ o ≤ p + 1 ∧ p + 1 < o + B) then
            σ.startRot i t ⟨k.val - 1, by omega⟩ else σ.retRot i t k),
          (σ.prog.trip (.rotA i t k) l).1) ∧
      (σ.prog.trip (.rotA i t k) l).1.length = l.length ∧
      ∀ (j : ℕ) (hj : j < (σ.prog.trip (.rotA i t k) l).1.length) (hj' : j < l.length),
        (σ.prog.trip (.rotA i t k) l).1[j] =
          {l[j] with cnt := Function.update l[j].cnt k (decide (j = p + 1))} := by
  have hc : ∀ (j : ℕ) (hj : j < l.length), σ.fwd (.rotA i t k) (σ.bufA o B p j) l[j] =
      ({l[j] with cnt := Function.update l[j].cnt k (decide (j = p + 1))},
        σ.bufA o B p (j + 1)) := by
    intro j hj
    simp only [fwd, bufA, hcnt j hj, hrul j hj, Prod.mk.injEq, true_and]
    congr 1
    · exact decide_eq_decide.2 (by omega)
    · dec_omega
  obtain ⟨hlen, hget, hbuf⟩ := σ.trip_fwd_get (.rotA i t k) (fun _ _ => rfl) (fun _ => rfl) l
    (σ.bufA o B p) (by simp [bufA, buf0]) (fun j hj => by rw [hc j hj])
  refine ⟨σ.stepP_inl_of ?_, hlen, fun j hj hj' => by rw [hget j hj' hj, hc j hj']⟩
  rw [hbuf]
  simp only [next, bufA]
  split <;> rfl

/-! ### Nested rotations -/

/-- Round trips of a rotation of level `k` over a ruler of `B` cells. -/
def rotCost (B : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + B * (rotCost B k + 1)

theorem rotCost_le (B : ℕ) : ∀ k, rotCost B k ≤ (2 * B + 1) ^ k
  | 0 => le_rfl
  | k + 1 => by
    have ih := rotCost_le B k
    have h1 : 1 ≤ (2 * B + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    simp only [rotCost, pow_succ]
    nlinarith

theorem startRot_zero (i : Fin σ.K) (t : Fin σ.NT) (h : 0 < σ.W.d) :
    σ.startRot i t ⟨0, h⟩ = .rotU i t := by simp [startRot]

theorem startRot_succ (i : Fin σ.K) (t : Fin σ.NT) (k : ℕ) (h : k + 1 < σ.W.d) :
    σ.startRot i t ⟨k + 1, h⟩ = .rotI i t ⟨k + 1, h⟩ := by simp [startRot]

theorem retRot_lt (i : Fin σ.K) (t : Fin σ.NT) (k : ℕ) (hk : k < (σ.task i t).1.val) :
    σ.retRot i t ⟨k, by have := (σ.task i t).1.isLt; omega⟩ =
      .rotA i t ⟨k + 1, by have := (σ.task i t).1.isLt; omega⟩ := by
  unfold retRot
  rw [if_neg (fun h => by rw [← h] at hk; exact lt_irrefl _ hk),
    dif_pos (show k + 1 < σ.W.d by have := (σ.task i t).1.isLt; omega)]

theorem retRot_top (i : Fin σ.K) (t : Fin σ.NT) :
    σ.retRot i t (σ.task i t).1 = σ.taskEntry i (t.val + 1) := by
  unfold retRot
  rw [if_pos rfl]

/-- The ruler and cell-`0` facts used by the rotations. -/
structure RulerOK (o B : ℕ) (l0 : List (Cell σ)) : Prop where
  pos : 0 < l0.length
  room : o + B ≤ l0.length
  B_pos : 1 ≤ B
  fst : ∀ (j : ℕ) (hj : j < l0.length), l0[j].fst = decide (j = 0)
  rfst : ∀ (j : ℕ) (hj : j < l0.length), l0[j].rfst = decide (j = o)
  rul : ∀ (j : ℕ) (hj : j < l0.length), l0[j].rul = decide (o ≤ j ∧ j < o + B)

theorem TS.rulerFacts {l0 l : List (Cell σ)} {s : ℤ} {o B : ℕ} (hts : σ.TS l0 s l)
    (hr : σ.RulerOK o B l0) (j : ℕ) (hj : j < l.length) :
    l[j].rfst = decide (j = o) ∧ l[j].rul = decide (o ≤ j ∧ j < o + B) := by
  have hlen := hts.len
  have h := σ.eraseT_fields (hts.frame j hj (by omega))
  exact ⟨h.2.1.trans (hr.rfst j (by omega)), h.2.2.trans (hr.rul j (by omega))⟩

/-- **Level-`k` rotation**: from `startRot` to `retRot` the `tmp` track is shifted by `±B^k`;
counters above level `k` are untouched. -/
theorem rot_level (i : Fin σ.K) (t : Fin σ.NT) (o B : ℕ) (l0 : List (Cell σ))
    (hr : σ.RulerOK o B l0) :
    ∀ (k : ℕ) (hk : k ≤ (σ.task i t).1.val) (l : List (Cell σ)) (s : ℤ), σ.TS l0 s l →
      ∃ l', RN σ.prog (σ.startRot i t ⟨k, lt_of_le_of_lt hk (σ.task i t).1.isLt⟩, l)
          (σ.retRot i t ⟨k, lt_of_le_of_lt hk (σ.task i t).1.isLt⟩, l') (rotCost B k) ∧
        σ.TS l0 (s + (if (σ.task i t).2 then 1 else -1) * (B : ℤ) ^ k) l' ∧
        ∀ (j : ℕ) (hj : j < l'.length) (hj' : j < l.length) (k' : Fin σ.W.d), k < k'.val →
          l'[j].cnt k' = l[j].cnt k' := by
  intro k
  induction k with
  | zero =>
    intro hk l s hts
    obtain ⟨hst, hts', hcnt⟩ := σ.rotU_trip i t l0 l s hts hr.pos hr.fst
    refine ⟨_, ?_, by simpa using hts', fun j hj hj' k' _ => by rw [hcnt j hj hj']⟩
    rw [σ.startRot_zero i t]
    exact RN.single hst
  | succ k ih =>
    intro hk l s hts
    have hkd : k + 1 < σ.W.d := lt_of_le_of_lt hk (σ.task i t).1.isLt
    have hka : k < (σ.task i t).1.val := by omega
    have hlen := hts.len
    -- the counter of level `k + 1` starts on the first ruler cell
    obtain ⟨hs1, hlen1, hget1⟩ := σ.rotI_trip i t ⟨k + 1, hkd⟩ l
    set l1 : List (Cell σ) := (σ.prog.trip (.rotI i t ⟨k + 1, hkd⟩) l).1 with hl1
    have hts1 : σ.TS l0 s l1 := ⟨by rw [hlen1, hlen],
      fun j hj hj' => by rw [hget1 j hj (by omega)]; exact hts.frame j (by omega) hj',
      fun j hj => by rw [hget1 j hj (by omega)]; exact hts.tmp j (by omega)⟩
    have hc1 : ∀ (j : ℕ) (hj : j < l1.length), l1[j].cnt ⟨k + 1, hkd⟩ = decide (j = o + 0) :=
      fun j hj => by
        rw [hget1 j hj (by omega)]
        simp [(hts.rulerFacts σ hr j (by omega)).1]
    have hn1 : σ.startRot i t ⟨(⟨k + 1, hkd⟩ : Fin σ.W.d).val - 1, by omega⟩ =
        σ.startRot i t ⟨k, by omega⟩ := by congr 1
    rw [hn1] at hs1
    -- the loop over the ruler
    have inner : ∀ (q m : ℕ), m + q + 1 = B → ∀ (l' : List (Cell σ)) (s' : ℤ), σ.TS l0 s' l' →
        (∀ (j : ℕ) (hj : j < l'.length), l'[j].cnt ⟨k + 1, hkd⟩ = decide (j = o + m)) →
        ∃ l'', RN σ.prog (σ.startRot i t ⟨k, by omega⟩, l')
            (σ.retRot i t ⟨k + 1, hkd⟩, l'') ((q + 1) * (rotCost B k + 1)) ∧
          σ.TS l0 (s' + (q + 1) * ((if (σ.task i t).2 then 1 else -1) * (B : ℤ) ^ k)) l'' ∧
          ∀ (j : ℕ) (hj : j < l''.length) (hj' : j < l'.length) (k' : Fin σ.W.d),
            k + 1 < k'.val → l''[j].cnt k' = l'[j].cnt k' := by
      intro q
      induction q with
      | zero =>
        intro m hmq l' s' hts' hc'
        obtain ⟨l2, hrn2, hts2, hcnt2⟩ := ih (by omega) l' s' hts'
        rw [σ.retRot_lt i t k hka] at hrn2
        have hc2 : ∀ (j : ℕ) (hj : j < l2.length), l2[j].cnt ⟨k + 1, hkd⟩ = decide (j = o + m) :=
          fun j hj => by
            rw [hcnt2 j hj (by rw [hts'.len, ← hts2.len]; exact hj) ⟨k + 1, hkd⟩ (by simp)]
            exact hc' j _
        obtain ⟨hs3, hlen3, hget3⟩ := σ.rotA_trip i t ⟨k + 1, hkd⟩ o B (o + m) l2 hc2
          (fun j hj => (hts2.rulerFacts σ hr j hj).2)
        have hlen2 := hts2.len
        have hroom := hr.room
        rw [decide_eq_false (by omega)] at hs3
        simp only [Bool.false_eq_true, if_false] at hs3
        refine ⟨_, by simpa using hrn2.trans (RN.single hs3), ?_, fun j hj hj' k' hk' => ?_⟩
        · refine ⟨by rw [hlen3, hlen2], fun j hj hj' => ?_, fun j hj => ?_⟩
          · rw [hget3 j hj (by omega)]; exact hts2.frame j (by omega) hj'
          · rw [hget3 j hj (by omega), hts2.tmp j (by omega)]; congr 3; ring
        · rw [hget3 j hj (by omega)]
          simp only
          rw [Function.update_of_ne (fun h => by rw [h] at hk'; simp at hk')]
          exact hcnt2 j (by omega) hj' k' (by omega)
      | succ q ihq =>
        intro m hmq l' s' hts' hc'
        obtain ⟨l2, hrn2, hts2, hcnt2⟩ := ih (by omega) l' s' hts'
        rw [σ.retRot_lt i t k hka] at hrn2
        have hc2 : ∀ (j : ℕ) (hj : j < l2.length), l2[j].cnt ⟨k + 1, hkd⟩ = decide (j = o + m) :=
          fun j hj => by
            rw [hcnt2 j hj (by rw [hts'.len, ← hts2.len]; exact hj) ⟨k + 1, hkd⟩ (by simp)]
            exact hc' j _
        obtain ⟨hs3, hlen3, hget3⟩ := σ.rotA_trip i t ⟨k + 1, hkd⟩ o B (o + m) l2 hc2
          (fun j hj => (hts2.rulerFacts σ hr j hj).2)
        have hlen2 := hts2.len
        have hroom := hr.room
        rw [decide_eq_true (by omega), if_pos rfl] at hs3
        have hn3 : σ.startRot i t ⟨(⟨k + 1, hkd⟩ : Fin σ.W.d).val - 1, by omega⟩ =
            σ.startRot i t ⟨k, by omega⟩ := by congr 1
        rw [hn3] at hs3
        set l3 : List (Cell σ) := (σ.prog.trip (.rotA i t ⟨k + 1, hkd⟩) l2).1 with hl3
        have hts3 : σ.TS l0 (s' + (if (σ.task i t).2 then 1 else -1) * (B : ℤ) ^ k) l3 :=
          ⟨by rw [hlen3, hlen2], fun j hj hj' => by
            rw [hget3 j hj (by omega)]; exact hts2.frame j (by omega) hj',
            fun j hj => by rw [hget3 j hj (by omega)]; exact hts2.tmp j (by omega)⟩
        have hc3 : ∀ (j : ℕ) (hj : j < l3.length),
            l3[j].cnt ⟨k + 1, hkd⟩ = decide (j = o + (m + 1)) := fun j hj => by
          rw [hget3 j hj (by omega)]
          simp only [Function.update_self]
          exact decide_eq_decide.2 (by omega)
        obtain ⟨l4, hrn4, hts4, hcnt4⟩ := ihq (m + 1) (by omega) l3 _ hts3 hc3
        have hl4 := hts4.len
        have hl3 := hts3.len
        refine ⟨l4, ?_, ?_, fun j hj hj' k' hk' => ?_⟩
        · have := (hrn2.trans (RN.single hs3)).trans hrn4
          convert this using 1
          ring
        · convert hts4 using 1
          push_cast
          ring
        · rw [hcnt4 j hj (by omega) k' hk', hget3 j (by omega) (by omega)]
          simp only
          rw [Function.update_of_ne (fun h => by rw [h] at hk'; simp at hk')]
          exact hcnt2 j (by omega) hj' k' (by omega)
    have hB := hr.B_pos
    obtain ⟨l', hrn', hts', hcnt'⟩ := inner (B - 1) 0 (by omega) l1 s hts1 hc1
    refine ⟨l', ?_, ?_, fun j hj hj' k' hk' => ?_⟩
    · rw [σ.startRot_succ i t k hkd]
      have := (RN.single hs1).trans hrn'
      convert this using 1
      simp only [rotCost]
      rw [show B - 1 + 1 = B by omega]
    · convert hts' using 2
      rw [show ((B - 1 : ℕ) : ℤ) + 1 = (B : ℤ) by push_cast [show 1 ≤ B by omega]; ring]
      ring
    · rw [hcnt' j hj (by omega) k' hk', hget1 j (by omega) (by omega)]
      simp only
      rw [Function.update_of_ne (fun h => by rw [h] at hk'; simp at hk')]

end Spec

end PVNP.UniformSim
