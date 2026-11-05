import PVNP.UniformSimSem

/-!
# Milestone 5, part 4: scans with known buffers, and box index arithmetic

* `fscan_spec_get`, `fscan_spec_buf`, `bscan_spec_get`, `bscan_spec_buf`: a scan whose buffer
  sequence is known in closed form.
* `site_bound`, `nbr_idx`: the flattened index of a radius-`r` neighbour of a box site is the
  site's index plus `δ_v = Σ_k (v_k − r)·(2R+1)^k`.
* `mems`, `cfgCode_block`, `latCode_get`: the members of the box in flattened order, the blocks of
  the canonical configuration code, and the layout of the lattice description.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

/-! ### Scans with a known buffer sequence -/

section ScanSpec

variable {D B : Type} (f : B → D → D × B) (l : List D)

theorem fscan_spec (bufAt : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufAt j) l[j]).2 = bufAt (j + 1)) :
    ∀ j ≤ l.length, (fscan f (bufAt 0) (l.take j)).2 = bufAt j := by
  intro j
  induction j with
  | zero => intro _; simp [fscan]
  | succ j ih =>
    intro hj
    rw [fscan_take_succ f _ l j (by omega), ih (by omega), hstep j (by omega)]

theorem fscan_spec_get (bufAt : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufAt j) l[j]).2 = bufAt (j + 1))
    (j : ℕ) (hj : j < l.length) :
    (fscan f (bufAt 0) l).1[j]'(by rw [fscan_length]; exact hj) = (f (bufAt j) l[j]).1 := by
  rw [fscan_getElem f _ l j hj, fscan_spec f l bufAt hstep j hj.le]

theorem fscan_spec_buf (bufAt : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufAt j) l[j]).2 = bufAt (j + 1)) :
    (fscan f (bufAt 0) l).2 = bufAt l.length := by
  rw [fscan_snd_eq_take, fscan_spec f l bufAt hstep _ le_rfl]

theorem bscan_spec (bufR : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufR (j + 1)) l[j]).2 = bufR j) :
    ∀ k ≤ l.length,
      (bscan f (bufR l.length) (l.drop (l.length - k))).2 = bufR (l.length - k) := by
  intro k
  induction k with
  | zero => intro _; simp [bscan]
  | succ k ih =>
    intro hk
    have e := bscan_drop_snd f (bufR l.length) l (l.length - (k + 1)) (by omega)
    rw [show l.length - (k + 1) + 1 = l.length - k by omega, ih (by omega)] at e
    rw [e]
    have := hstep (l.length - (k + 1)) (by omega)
    rw [show l.length - (k + 1) + 1 = l.length - k by omega] at this
    exact this

theorem bscan_spec_get (bufR : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufR (j + 1)) l[j]).2 = bufR j)
    (j : ℕ) (hj : j < l.length) :
    (bscan f (bufR l.length) l).1[j]'(by rw [bscan_length]; exact hj) =
      (f (bufR (j + 1)) l[j]).1 := by
  rw [bscan_getElem f _ l j hj]
  have := bscan_spec f l bufR hstep (l.length - (j + 1)) (by omega)
  rw [show l.length - (l.length - (j + 1)) = j + 1 by omega] at this
  rw [this]

theorem bscan_spec_buf (bufR : ℕ → B)
    (hstep : ∀ (j : ℕ) (hj : j < l.length), (f (bufR (j + 1)) l[j]).2 = bufR j) :
    (bscan f (bufR l.length) l).2 = bufR 0 := by
  have := bscan_spec f l bufR hstep l.length le_rfl
  simpa using this

end ScanSpec

/-! ### Box index arithmetic -/

section Box

theorem side_pos (R : ℕ) : 0 < side R := by unfold side; omega

theorem site_digit (d R idx : ℕ) (h : idx < side R ^ d) (k : Fin d) :
    site d R idx k = ((finFunctionFinEquiv.symm (⟨idx, h⟩ : Fin (side R ^ d)) k : ℕ) : ℤ) - R := by
  simp [site, finFunctionFinEquiv_symm_apply_val]

theorem site_bound (d R idx : ℕ) (k : Fin d) :
    -(R : ℤ) ≤ site d R idx k ∧ site d R idx k ≤ R := by
  have h := Nat.mod_lt (idx / side R ^ (k : ℕ)) (side_pos R)
  unfold site
  set m := idx / side R ^ (k : ℕ) % side R
  unfold side at h
  omega

/-- **Neighbour index**: the radius-`r` neighbour `site idx + (v − r)` of a box site, when it lies in
the box, has flattened index `idx + Σ_k (v_k − r)·(2R+1)^k`. -/
theorem nbr_idx (d R r idx : ℕ) (h : idx < side R ^ d) (v : Fin d → Fin (2 * r + 1))
    (hin : ∀ k, |site d R idx k + ((v k : ℤ) - r)| ≤ R) :
    ∃ idx' : ℕ, idx' < side R ^ d ∧
      (idx' : ℤ) = idx + ∑ k : Fin d, ((v k : ℤ) - r) * (side R : ℤ) ^ (k : ℕ) ∧
      ∀ k, site d R idx' k = site d R idx k + ((v k : ℤ) - r) := by
  set f := finFunctionFinEquiv.symm (⟨idx, h⟩ : Fin (side R ^ d)) with hf
  have hg : ∀ k, (site d R idx k + ((v k : ℤ) - r) + R).toNat < side R := by
    intro k
    have := hin k
    rw [abs_le] at this
    unfold side
    omega
  set g : Fin d → Fin (side R) := fun k => ⟨_, hg k⟩ with hg'
  have hgv : ∀ k, ((g k : ℕ) : ℤ) = (f k : ℤ) + ((v k : ℤ) - r) := by
    intro k
    have := hin k
    rw [abs_le] at this
    simp only [hg']
    rw [Int.toNat_of_nonneg (by omega), site_digit d R idx h k]
    ring
  refine ⟨finFunctionFinEquiv g, (finFunctionFinEquiv g).isLt, ?_, fun k => ?_⟩
  · have hidx : (idx : ℤ) = ∑ k : Fin d, ((f k : ℕ) : ℤ) * (side R : ℤ) ^ (k : ℕ) := by
      have := finFunctionFinEquiv_apply f
      rw [hf, Equiv.apply_symm_apply] at this
      exact_mod_cast this
    rw [finFunctionFinEquiv_apply, hidx]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hgv k]
    ring
  · rw [site_digit d R _ (finFunctionFinEquiv g).isLt k]
    simp only [Fin.eta, Equiv.symm_apply_apply]
    rw [hgv k, site_digit d R idx h k]
    ring

end Box

/-! ### Members, configuration codes, lattice descriptions -/

section Codes

variable (d R : ℕ) (Λ : Set (Fin d → ℤ)) [DecidablePred (· ∈ Λ)]

/-- Member indices of the box in flattened order. -/
def mems : List ℕ := (boxIdx d R).filter fun idx => decide (site d R idx ∈ Λ)

theorem mem_mems {idx : ℕ} : idx ∈ mems d R Λ ↔ idx < side R ^ d ∧ site d R idx ∈ Λ := by
  simp [mems, boxIdx]

theorem mems_sorted : (mems d R Λ).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem mems_lt_iff (i j : ℕ) (hi : i < (mems d R Λ).length) (hj : j < (mems d R Λ).length) :
    (mems d R Λ)[i] < (mems d R Λ)[j] ↔ i < j := by
  have hs := List.pairwise_iff_getElem.1 (mems_sorted d R Λ)
  constructor
  · intro h
    by_contra h'
    rcases Nat.lt_or_ge j i with h'' | h''
    · have := hs j i hj hi h''; omega
    · have : i = j := by omega
      subst this; omega
  · exact hs i j hi hj

theorem mems_le_iff (i j : ℕ) (hi : i < (mems d R Λ).length) (hj : j < (mems d R Λ).length) :
    (mems d R Λ)[i] ≤ (mems d R Λ)[j] ↔ i ≤ j := by
  have := mems_lt_iff d R Λ j i hj hi
  constructor
  · intro h; by_contra h'; have := this.2 (by omega); omega
  · intro h; by_contra h'; have := this.1 (by omega); omega

theorem mems_get_mem (i : ℕ) (hi : i < (mems d R Λ).length) :
    (mems d R Λ)[i] < side R ^ d ∧ site d R (mems d R Λ)[i] ∈ Λ :=
  (mem_mems d R Λ).1 (List.getElem_mem hi)

theorem mems_length_le : (mems d R Λ).length ≤ side R ^ d := by
  have := List.length_filter_le (fun idx => decide (site d R idx ∈ Λ)) (boxIdx d R)
  simpa [mems, boxIdx] using this

/-- Element `m·w + k` of a concatenation of length-`w` blocks. -/
theorem flatMap_block {α β : Type} (f : α → List β) (w : ℕ) (hf : ∀ a, (f a).length = w) :
    ∀ (l : List α) (m k : ℕ) (_hm : m < l.length) (_hk : k < w),
      (l.flatMap f)[m * w + k]? = (f l[m])[k]?
  | a :: l, 0, k, _, hk => by
    simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
    rw [List.getElem?_append_left (by rw [hf]; exact hk)]
  | a :: l, m + 1, k, hm, hk => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by rw [hf, Nat.succ_mul]; omega), hf,
      show (m + 1) * w + k - w = m * w + k by rw [Nat.succ_mul]; omega]
    exact flatMap_block f w hf l m k (by simp at hm; omega) hk

theorem flatMap_length_const {α β : Type} (f : α → List β) (w : ℕ) (hf : ∀ a, (f a).length = w)
    (l : List α) : (l.flatMap f).length = l.length * w := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf, Nat.succ_mul]; ring

variable {S : Type} (bits : S → List Bool) (w : ℕ) (hw : ∀ s, (bits s).length = w)

theorem cfgCode_eq (C : (Fin d → ℤ) → S) :
    cfgCode bits d R Λ C = (mems d R Λ).flatMap fun idx => bits (C (site d R idx)) := rfl

include hw in
theorem cfgCode_length (C : (Fin d → ℤ) → S) :
    (cfgCode bits d R Λ C).length = (mems d R Λ).length * w := by
  rw [cfgCode_eq]
  exact flatMap_length_const _ w (fun _ => hw _) _

include hw in
theorem cfgCode_block (C : (Fin d → ℤ) → S) (m k : ℕ) (hm : m < (mems d R Λ).length)
    (hk : k < w) :
    (cfgCode bits d R Λ C)[m * w + k]? = (bits (C (site d R (mems d R Λ)[m])))[k]? := by
  rw [cfgCode_eq]
  exact flatMap_block (fun idx => bits (C (site d R idx))) w (fun _ => hw _) _ m k hm hk

theorem latCode_length : (latCode d R Λ).length = R + 1 + side R ^ d := by
  simp [latCode, boxIdx]
  omega

theorem latCode_pre (j : ℕ) (hj : j < R) : (latCode d R Λ)[j]? = some true := by
  unfold latCode
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

theorem latCode_sep : (latCode d R Λ)[R]? = some false := by
  unfold latCode
  rw [List.getElem?_append_right (by simp)]
  simp

theorem latCode_box (idx : ℕ) (h : idx < side R ^ d) :
    (latCode d R Λ)[R + 1 + idx]? = some (decide (site d R idx ∈ Λ)) := by
  unfold latCode
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, show R + 1 + idx - R = idx + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_map]
  simp [boxIdx, h]

end Codes

/-! ### Symbols -/

theorem Spec.symBit_inp (M : MTM) (b : Bool) : Spec.symBit M (M.inp b) = b := by
  cases b
  · simp only [Spec.symBit, decide_eq_false_iff_not]
    exact fun h => Bool.false_ne_true (M.inp_inj h)
  · simp [Spec.symBit]

theorem Spec.inSym_some (M : MTM) (b : Bool) : Spec.inSym M (some b) = M.inp b := rfl

theorem Spec.inSym_none (M : MTM) : Spec.inSym M none = M.blank := rfl

end PVNP.UniformSim
