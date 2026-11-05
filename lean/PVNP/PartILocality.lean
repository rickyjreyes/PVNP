import Mathlib

/-!
# Part I, §"Constructive Depth": `lem:local_growth` and `lem:clause_flip`

**Lemma `lem:local_growth` (Part I).** "Let `W` have interaction radius `r`. Then
`supp(C_{t+1}) ⊆ supp(C_t)^{+r}`. In particular
`|supp(C_t)| ≤ |supp(C_0)| + O(r t |∂ supp(C_0)|)`."

* `supp_step_subset`: the inclusion holds for every `r`-local rule that is **quiescent**
  (an all-background neighbourhood stays background). The manuscript's proof uses this
  implicitly.
* `local_growth_needs_quiescence`: without quiescence the inclusion is false (a constant rule).
* `linear_growth_false_d2`: the "in particular" bound is **false in dimension 2** (Part I's
  lattices have `d = 2` or `3`). The quiescent radius-one OR rule from a single seed has support
  `[-t,t]²` of size `(2t+1)²`, which exceeds `1 + K·t·B` for every constant `K` and every value
  `B` of the boundary size of the seed.
* `support_poly_bound`: the corrected statement, `|supp(C_t)| ≤ |supp(C_0)| · (2rt+1)^d`
  (linear in `t` only for `d = 1`).

**Lemma `lem:clause_flip` (Part I).** `clause_flip_local` and `clause_flip_rounds`.
`parallel_flips` makes the remark after it precise: a synchronous local rule may change all `m`
clause signatures in one round, so locality alone gives no `T ≥ k` bound.
-/

namespace PVNP.PartILocality

/-- Lattice sites of `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

variable {d : ℕ} {S : Type*}

/-- The closed `ℓ∞` ball of radius `r` around `i`. -/
def nbhd (r : ℕ) (i : Site d) : Set (Site d) := {j | ∀ k, |j k - i k| ≤ r}

/-- The `r`-thickening `X^{+r}`. -/
def thicken (r : ℕ) (X : Set (Site d)) : Set (Site d) := {j | ∃ i ∈ X, j ∈ nbhd r i}

/-- `G` is an `r`-local global update: `(G C)(i)` depends only on `C` on `N_r(i)`. -/
def IsLocal (r : ℕ) (G : (Site d → S) → (Site d → S)) : Prop :=
  ∀ C C' i, (∀ j ∈ nbhd r i, C j = C' j) → G C i = G C' i

/-- Quiescence of the background symbol `s₀`. -/
def Quiescent (r : ℕ) (s₀ : S) (G : (Site d → S) → (Site d → S)) : Prop :=
  ∀ C i, (∀ j ∈ nbhd r i, C j = s₀) → G C i = s₀

/-- Symbolic support. -/
def supp (s₀ : S) (C : Site d → S) : Set (Site d) := {i | C i ≠ s₀}

theorem mem_nbhd_comm (r : ℕ) (i j : Site d) : j ∈ nbhd r i ↔ i ∈ nbhd r j := by
  simp only [nbhd, Set.mem_setOf_eq]
  exact forall_congr' fun k => by rw [abs_sub_comm]

/-- **`lem:local_growth`, first statement**, under the quiescence hypothesis used by the proof. -/
theorem supp_step_subset (r : ℕ) (s₀ : S) (G : (Site d → S) → (Site d → S))
    (hq : Quiescent r s₀ G) (C : Site d → S) : supp s₀ (G C) ⊆ thicken r (supp s₀ C) := by
  intro i hi
  by_contra hc
  apply hi
  apply hq C i
  intro j hj
  by_contra hCj
  exact hc ⟨j, hCj, (mem_nbhd_comm r i j).1 hj⟩

/-- Without quiescence the inclusion fails: the constant rule `C ↦ (fun _ => true)` is local for
every radius, and creates support from an empty support. -/
theorem local_growth_needs_quiescence (r : ℕ) :
    ∃ G : (Site d → Bool) → (Site d → Bool), IsLocal r G ∧
      ∃ C, ¬ supp false (G C) ⊆ thicken r (supp false C) := by
  refine ⟨fun _ _ => true, fun _ _ _ _ => rfl, fun _ => false, fun h => ?_⟩
  obtain ⟨i, hi, -⟩ := h (show (0 : Site d) ∈ supp false (fun _ => true) by simp [supp])
  exact hi rfl

theorem thicken_thicken (r s : ℕ) (X : Set (Site d)) :
    thicken r (thicken s X) ⊆ thicken (s + r) X := by
  rintro j ⟨i, ⟨x, hx, hi⟩, hj⟩
  refine ⟨x, hx, fun k => ?_⟩
  have h1 := hi k
  have h2 := hj k
  calc |j k - x k| = |(j k - i k) + (i k - x k)| := by ring_nf
    _ ≤ |j k - i k| + |i k - x k| := abs_add _ _
    _ ≤ r + s := add_le_add h2 h1
    _ = ((s + r : ℕ) : ℤ) := by push_cast; ring

theorem supp_iterate_subset (r : ℕ) (s₀ : S) (G : (Site d → S) → (Site d → S))
    (hq : Quiescent r s₀ G) (C : Site d → S) :
    ∀ t, supp s₀ (G^[t] C) ⊆ thicken (r * t) (supp s₀ C)
  | 0 => by
    intro i hi
    exact ⟨i, hi, fun k => by simp⟩
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    refine (supp_step_subset r s₀ G hq _).trans ?_
    intro j ⟨i, hi, hj⟩
    have := thicken_thicken r (r * t) (supp s₀ C) ⟨i, supp_iterate_subset r s₀ G hq C t hi, hj⟩
    rwa [show r * t + r = r * (t + 1) by ring] at this

/-! ### The corrected polynomial bound -/

/-- The box `N_R(i)` as a finset. -/
def boxF (R : ℕ) (i : Site d) : Finset (Site d) :=
  Fintype.piFinset fun k => Finset.Icc (i k - R) (i k + R)

theorem mem_boxF (R : ℕ) (i j : Site d) : j ∈ boxF R i ↔ j ∈ nbhd R i := by
  simp only [boxF, Fintype.mem_piFinset, Finset.mem_Icc, nbhd, Set.mem_setOf_eq, abs_le]
  exact forall_congr' fun k => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem card_boxF (R : ℕ) (i : Site d) : (boxF R i).card = (2 * R + 1) ^ d := by
  simp only [boxF, Fintype.card_piFinset, Int.card_Icc]
  have h : ∀ x : Fin d, (i x + R + 1 - (i x - R)).toNat = 2 * R + 1 := fun x => by omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Corrected `lem:local_growth`**: for a quiescent `r`-local rule and a finite initial support,
`|supp(C_t)| ≤ |supp(C_0)| · (2rt+1)^d`. -/
theorem support_poly_bound (r : ℕ) (s₀ : S) (G : (Site d → S) → (Site d → S))
    (hq : Quiescent r s₀ G) (C : Site d → S) (X : Finset (Site d)) (hX : supp s₀ C ⊆ X) (t : ℕ) :
    ∃ Y : Finset (Site d), supp s₀ (G^[t] C) ⊆ Y ∧ Y.card ≤ X.card * (2 * (r * t) + 1) ^ d := by
  refine ⟨X.biUnion (boxF (r * t)), ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, hji⟩ := supp_iterate_subset r s₀ G hq C t hj
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨i, hX hi, (mem_boxF _ i j).2 hji⟩
  · calc (X.biUnion (boxF (r * t))).card ≤ ∑ i ∈ X, (boxF (r * t) i).card := Finset.card_biUnion_le
      _ = X.card * (2 * (r * t) + 1) ^ d := by simp [card_boxF]

/-! ### The linear bound is false in dimension two -/

/-- Offsets `{-1, 0, 1}` for a `Fin 3` digit. -/
def off (v : Fin 3) : ℤ := (v : ℤ) - 1

/-- The quiescent radius-one OR rule on `ℤ²`. -/
def orRule (C : Site 2 → Bool) (i : Site 2) : Bool :=
  decide (∃ v : Fin 2 → Fin 3, C (fun k => i k + off (v k)) = true)

/-- The indicator of the box `[-t, t]²`. -/
def boxInd (t : ℕ) (i : Site 2) : Bool := decide (∀ k, |i k| ≤ t)

theorem off_abs (v : Fin 3) : |off v| ≤ 1 := by
  unfold off; fin_cases v <;> simp

theorem orRule_box (t : ℕ) : orRule (boxInd t) = boxInd (t + 1) := by
  funext i
  simp only [orRule, boxInd]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv⟩ k
    have h1 := hv k
    have h2 := off_abs (v k)
    have h3 := abs_add (i k + off (v k)) (-off (v k))
    simp only [add_neg_cancel_right, abs_neg] at h3
    push_cast
    linarith
  · intro h
    -- move each coordinate one step toward the origin
    refine ⟨fun k => if i k > t then 0 else if i k < -(t : ℤ) then 2 else 1, fun k => ?_⟩
    have hk := h k
    push_cast at hk
    rw [abs_le] at hk ⊢
    simp only [off]
    split_ifs with h1 h2 <;> simp <;> constructor <;> linarith

theorem orRule_local : IsLocal (d := 2) 1 orRule := by
  intro C C' i h
  simp only [orRule]
  congr 1
  apply propext
  refine exists_congr fun v => ?_
  rw [h _ (fun k => by simpa using off_abs (v k))]

theorem orRule_quiescent : Quiescent (d := 2) 1 false orRule := by
  intro C i h
  simp only [orRule, decide_eq_false_iff_not, not_exists]
  intro v hv
  rw [h _ (fun k => by simpa using off_abs (v k))] at hv
  exact Bool.false_ne_true hv

theorem iterate_orRule (t : ℕ) : orRule^[t] (boxInd 0) = boxInd t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, orRule_box]

/-- The support of the box indicator, as a finset. -/
def boxSet (t : ℕ) : Finset (Site 2) := Fintype.piFinset fun _ => Finset.Icc (-(t : ℤ)) t

theorem supp_boxInd (t : ℕ) : supp false (boxInd t) = ↑(boxSet t) := by
  ext i
  simp only [supp, boxInd, Set.mem_setOf_eq, ne_eq, Bool.not_eq_false, decide_eq_true_eq, boxSet,
    Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_boxSet (t : ℕ) : (boxSet t).card = (2 * t + 1) ^ 2 := by
  simp only [boxSet, Fintype.card_piFinset, Int.card_Icc]
  have h : ((t : ℤ) + 1 - -(t : ℤ)).toNat = 2 * t + 1 := by omega
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`lem:local_growth`, second statement, is false for `d = 2`.**  For the quiescent radius-one
OR rule from a single seed, `|supp(C_t)| = (2t+1)²`, and for every constant `K` and every
boundary size `B` of the seed there is a time with `|supp(C_t)| > |supp(C_0)| + K · r · t · B`. -/
theorem linear_growth_false_d2 :
    IsLocal (d := 2) 1 orRule ∧ Quiescent (d := 2) 1 false orRule ∧
      (supp false (boxInd 0) = ↑(boxSet 0) ∧ (boxSet 0).card = 1) ∧
      (∀ t, supp false (orRule^[t] (boxInd 0)) = ↑(boxSet t) ∧ (boxSet t).card = (2 * t + 1) ^ 2) ∧
      ∀ K B : ℕ, ∃ t : ℕ, 1 + K * 1 * t * B < (2 * t + 1) ^ 2 := by
  refine ⟨orRule_local, orRule_quiescent, ⟨supp_boxInd 0, by rw [card_boxSet]; norm_num⟩,
    fun t => ⟨by rw [iterate_orRule, supp_boxInd], card_boxSet t⟩, fun K B => ⟨K * B + 1, ?_⟩⟩
  nlinarith [Nat.zero_le (K * B)]

/-! ### Lemma `lem:clause_flip` -/

/-- **`lem:clause_flip`, first statement.**  A signature that depends only on the configuration on
`R j` changes only if some cell of `R j` changes. -/
theorem clause_flip_local {X : Type*} {J : Type*} (R : J → Set X) (σ : J → (X → S) → Bool)
    (hσ : ∀ j C C', (∀ i ∈ R j, C i = C' i) → σ j C = σ j C') (j : J) (C C' : X → S)
    (h : σ j C ≠ σ j C') : ∃ i ∈ R j, C i ≠ C' i := by
  by_contra hc
  push_neg at hc
  exact h (hσ j C C' hc)

/-- **`lem:clause_flip`, second statement.**  If at most `b` signatures change per round, the
number `k` of signatures altered after `T` rounds satisfies `k ≤ T b`, hence `T ≥ ⌈k/b⌉`. -/
theorem clause_flip_rounds {X : Type*} {J : Type*} [Fintype J] [DecidableEq J]
    (σ : J → (X → S) → Bool) (C : ℕ → X → S) (b : ℕ)
    (hb : ∀ t, (Finset.univ.filter fun j => σ j (C (t + 1)) ≠ σ j (C t)).card ≤ b) (T : ℕ) :
    (Finset.univ.filter fun j => σ j (C T) ≠ σ j (C 0)).card ≤ T * b := by
  have hsub : (Finset.univ.filter fun j => σ j (C T) ≠ σ j (C 0)) ⊆
      (Finset.range T).biUnion fun t => Finset.univ.filter fun j => σ j (C (t + 1)) ≠ σ j (C t) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hc
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists, not_and, not_not] at hc
    have : ∀ t ≤ T, σ j (C t) = σ j (C 0) := by
      intro t ht
      induction t with
      | zero => rfl
      | succ t ih => rw [hc t (by omega), ih (by omega)]
    exact hj (this T le_rfl)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Finset.range T, (Finset.univ.filter fun j => σ j (C (t + 1)) ≠ σ j (C t)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Finset.range T, b := Finset.sum_le_sum fun t _ => hb t
    _ = T * b := by simp

theorem clause_flip_ceil {k T b : ℕ} (hb : 1 ≤ b) (h : k ≤ T * b) : (k + b - 1) / b ≤ T := by
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  calc k + b - 1 ≤ T * b + (b - 1) := by omega
    _ = b * T + (b - 1) := by ring

/-- **Remark after `lem:clause_flip`.**  A synchronous local rule of radius `0` (flip every cell)
changes all `m` single-cell clause signatures in one round: locality alone does not give
`T ≥ k`. -/
theorem parallel_flips (m : ℕ) :
    let C : ℕ → Fin m → Bool := fun t i => decide (t % 2 = 1) && (i = i)
    (Finset.univ.filter fun j : Fin m => C 1 j ≠ C 0 j).card = m := by
  simp

end PVNP.PartILocality
