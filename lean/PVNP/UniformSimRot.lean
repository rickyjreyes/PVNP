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
      σ.TS l0 (s + if (σ.task i t).2 then 1 else -1) (σ.prog.trip (.rotU i t) l).1 := by
  have hlen := hts.len
  have hfl : ∀ (j : ℕ) (hj : j < l.length), l[j].fst = decide (j = 0) := fun j hj => by
    rw [(σ.eraseT_fields (hts.frame j hj (by omega))).1, hfst j (by omega)]
  refine ⟨σ.stepP_inl_of rfl, ?_⟩
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
    refine ⟨by rw [hlen', hlen], fun j hj hj' => ?_, fun j hj => ?_⟩
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
    refine ⟨by rw [hlen', hlen], fun j hj hj' => ?_, fun j hj => ?_⟩
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

end Spec

end PVNP.UniformSim
