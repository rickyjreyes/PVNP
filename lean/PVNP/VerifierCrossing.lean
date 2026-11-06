import PVNP.CrossingSATSets

/-!
# Phase IX: the crossing-information invariant is attained by a language in `P_TM`

**Candidate invariant tested.** "Many distinguishable states across a cut", formalized in
Phase VIII as *crossing information*: at each of `G` distinct cuts, every decider has injective
decision traces (`CrossingSAT.dtrace`) on a family of `F` inputs of length `N`
(`CrossingInfo L N F G`). `CrossingSATSets.fooling_time_bound` converts it into time
`T(N) ≥ G·ℓ/2` whenever `2(|Λ×Dir|+1)^ℓ ≤ F`.

**Both implications tested.**

* *Every correct SAT decider incurs the invariant.* True; this is Phase VIII
  (`crossingInfo_SAT_dense`, restated here from `CrossingSATSets.dtraceSet_injective`).
* *Incurring the invariant forces superpolynomial time.* **False.** The verification language
  `V_SAT` (Part III `L_check`), which is in `P_TM` (`SATV.V_SAT_mem_P_TM`, decided by `satTM`
  within `2(N+3)²` steps), incurs the invariant at quadratic level:
  `CrossingInfo V_SAT (13n+1) (2ⁿ) (6n+1)` (`crossingInfo_V_SAT`), within a constant factor of
  the information-theoretic maximum (`G·log₂F = (6n+1)·n ≥ N²/30`, `vsat_info_quadratic`).
  Consequently every single-tape decider of `V_SAT` needs `Ω(N²/log|Λ|)` steps
  (`vsat_time_lower_bound_sq`), matching `satTM` up to the `log|Λ|` factor. This is more crossing
  information than the near-quadratic `Ω(N²/(log N·log|Λ|))` that Phase VIII certifies for
  `SAT_dense`.

**Conclusion (`crossingInfo_not_superpolynomial`).** No argument whose only input about `L` is
crossing information can show `L ∉ P_TM`: a polynomial-time language carries as much of it as
the method can certify for `SAT_dense`.

The family: the formula `exC a ∧ (z₀ ∨ ¬z₀ ∨ ¬z₀)` (exclude the point `a`, then one padding
tautology) paired with the witness `b`. It is accepted iff `b ≠ a`; the diagonal `b = a` is
rejected, and rejection splicing (`CrossingSATSets.splice_nmem`) at any cut inside the doubled
padding makes the decision traces injective on all `2ⁿ` diagonal instances.
-/

namespace PVNP.VerifierCrossing

open PVNP.Discrete PVNP.Discrete.TM PVNP.Discrete.SATV PVNP.PartI PVNP.CrossingTrace
open PVNP.CrossingHennie PVNP.CrossingSAT PVNP.CrossingSATSets

/-! ### The invariant -/

/-- **Crossing information** of `L` at length `N`: a family of `F` inputs of length `N` and
`G` distinct cuts at each of which every decider of `L` (within any time bound) has injective
decision traces on the family. -/
def CrossingInfo (L : Set (List Bool)) (N F G : ℕ) : Prop :=
  ∃ (x : Fin F → List Bool) (cut : ℕ → ℤ), Function.Injective cut ∧
    (∀ i, (x i).length = N) ∧
    ∀ (M : TM) (T : ℕ → ℕ), M.Decides L T → ∀ j < G, Function.Injective fun i => dtrace M (cut j) (x i)

/-- Crossing information forces time, through the Phase VIII double counting. -/
theorem time_of_crossingInfo {L : Set (List Bool)} {N F G : ℕ} (h : CrossingInfo L N F G)
    {M : TM} {T : ℕ → ℕ} (hM : M.Decides L T) {ℓ : ℕ}
    (hℓ : 2 * (Fintype.card (M.Λ × Dir) + 1) ^ ℓ ≤ F) : G * ℓ ≤ 2 * T N := by
  obtain ⟨x, cut, hcut, hlen, hinj⟩ := h
  refine fooling_time_bound (M := M) x cut hcut (fun i => ?_) (hinj M T hM) (by simpa using hℓ)
  obtain ⟨b, hfa, -⟩ := hM (x i)
  have := (ftime_spec hfa).1
  rwa [hlen i] at this

/-- Re-indexing a family by an equivalence preserves injectivity of decision traces. -/
theorem crossingInfo_of_equiv {L : Set (List Bool)} {N G : ℕ} {ι : Type*} [Fintype ι]
    (x : ι → List Bool) (cut : ℕ → ℤ) (hcut : Function.Injective cut)
    (hlen : ∀ i, (x i).length = N)
    (hinj : ∀ (M : TM) (T : ℕ → ℕ), M.Decides L T → ∀ j < G,
      Function.Injective fun i => dtrace M (cut j) (x i)) :
    CrossingInfo L N (Fintype.card ι) G := by
  set e := (Fintype.equivFin ι).symm
  refine ⟨fun k => x (e k), cut, hcut, fun k => hlen _, fun M T hM j hj k k' hk => ?_⟩
  exact e.injective (hinj M T hM j hj hk)

/-! ### `SAT_dense` carries the invariant (Phase VIII) -/

/-- Phase VIII, restated: `SAT_dense` has crossing information `2ⁿ` bits at `3ng + 1` cuts of
inputs of length `3n(2·2ⁿ + g)`. -/
theorem crossingInfo_SAT_dense (n g : ℕ) (hn : 1 ≤ n) :
    CrossingInfo SAT_dense (3 * n * (2 * 2 ^ n + g)) (2 ^ 2 ^ n) (3 * n * g + 1) := by
  rw [← card_sets n]
  exact crossingInfo_of_equiv (fun S : Finset (Pt n) => encSet n g S S) (cutSet n)
    (cutSet_injective n) (fun S => length_encSet n g S S)
    (fun M T hM j hj => dtraceSet_injective hM hn (by omega))

/-! ### The verifier family -/

/-- `pair` doubles the formula bits. -/
def dbl (x : List Bool) : List Bool := x.flatMap fun b => [true, b]

theorem dbl_append (x y : List Bool) : dbl (x ++ y) = dbl x ++ dbl y := by
  simp [dbl, List.flatMap_append]

theorem length_dbl (x : List Bool) : (dbl x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [dbl] at ih ⊢; rw [ih]; ring

/-- Exclude the point `a`, then one padding tautology. -/
def vForm {n : ℕ} (a : Pt n) : Formula := [exC a, tautC 0]

/-- The verifier instance: the formula `vForm a` paired with the witness `w`. -/
def vInst {n : ℕ} (a : Pt n) (w : List Bool) : List Bool := pair (encDense n (vForm a)) w

/-- The `a`-part of the input. -/
def vA {n : ℕ} (a : Pt n) : List Bool := dbl (encClause n (exC a))

/-- The doubled padding clause. -/
def vP (n : ℕ) : List Bool := dbl (encClause n (tautC 0))

theorem length_vA {n : ℕ} (a : Pt n) : (vA a).length = 6 * n := by
  rw [vA, length_dbl, encClause_length]; ring

theorem length_vP (n : ℕ) : (vP n).length = 6 * n := by
  rw [vP, length_dbl, encClause_length]; ring

theorem vInst_layout {n : ℕ} (a : Pt n) (w : List Bool) :
    vInst a w = vA a ++ vP n ++ false :: w := by
  simp only [vInst, pair, vForm, encDense, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← dbl, dbl_append, vA, vP, List.append_assoc]

theorem vInst_split {n : ℕ} (a : Pt n) (w : List Bool) (j : ℕ) :
    vInst a w = (vA a ++ (vP n).take j) ++ ((vP n).drop j ++ false :: w) := by
  rw [vInst_layout, List.append_assoc, List.append_assoc, ← List.append_assoc (List.take _ _),
    List.take_append_drop]

theorem length_vInst {n : ℕ} (a : Pt n) (b : Pt n) :
    (vInst a (List.ofFn b)).length = 13 * n + 1 := by
  rw [vInst_layout, List.length_append, List.length_append, length_vA, length_vP]
  simp; ring

theorem vForm_vars {n : ℕ} (hn : 1 ≤ n) (a : Pt n) : ∀ c ∈ vForm a, ∀ l ∈ c, l.1 < n := by
  intro c hc l hl
  simp only [vForm, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · rw [exC, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact i.isLt
  · simp only [tautC, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> simpa using hn

theorem getD_ofFn {n : ℕ} (b : Pt n) : (fun i : Fin n => (List.ofFn b).getD (i : ℕ) false) = b := by
  funext i
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- **Membership**: the instance is accepted iff the witness differs from the excluded point. -/
theorem vInst_mem_iff {n : ℕ} (hn : 1 ≤ n) (a b : Pt n) :
    vInst a (List.ofFn b) ∈ V_SAT ↔ b ≠ a := by
  have hchk : chkFrom (List.ofFn b) (encDense n (vForm a)) 0 false true = true ↔ b ≠ a := by
    rw [chk_formula (List.ofFn b) n hn (by simp) _ (vForm_vars hn a)]
    simp only [vForm, evalFormula, evalClause_tautC, Bool.and_true]
    rw [evalClause_exC, getD_ofFn]
  constructor
  · rintro ⟨x, w, heq, hc⟩
    obtain ⟨rfl, rfl⟩ := pair_injective heq
    exact hchk.1 hc
  · intro h
    exact ⟨_, _, rfl, hchk.2 h⟩

theorem vInst_diag_nmem {n : ℕ} (hn : 1 ≤ n) (a : Pt n) : vInst a (List.ofFn a) ∉ V_SAT := by
  rw [vInst_mem_iff hn]; exact fun h => h rfl

/-- The cut `6n + j` inside the doubled padding. -/
def vCut (n j : ℕ) : ℤ := ((6 * n + j : ℕ) : ℤ)

theorem vCut_injective (n : ℕ) : Function.Injective (vCut n) := by
  intro j j' h; unfold vCut at h; omega

/-- **Mixed rejection for the verifier family.** Equal decision traces of the rejected diagonal
instances `(a, a)` and `(a', a')` at a cut in the padding force `(a, a')` to be rejected, i.e.
`a' = a`. -/
theorem vsat_mixed {M : TM} {T : ℕ → ℕ} (hM : M.Decides V_SAT T) {n j : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ 6 * n) (a a' : Pt n)
    (htr : dtrace M (vCut n j) (vInst a (List.ofFn a)) =
      dtrace M (vCut n j) (vInst a' (List.ofFn a'))) : a = a' := by
  have hx := decides_false hM (vInst_diag_nmem hn a)
  have hy := decides_false hM (vInst_diag_nmem hn a')
  set u := vA a ++ (vP n).take j
  set u' := vA a' ++ (vP n).take j
  set v := (vP n).drop j ++ false :: List.ofFn a
  set v' := (vP n).drop j ++ false :: List.ofFn a'
  have ex : vInst a (List.ofFn a) = u ++ v := vInst_split a _ j
  have ey : vInst a' (List.ofFn a') = u' ++ v' := vInst_split a' _ j
  have ez : vInst a (List.ofFn a') = u ++ v' := vInst_split a _ j
  have hlu : u.length = 6 * n + j := by
    rw [List.length_append, length_vA, List.length_take, length_vP, min_eq_left hj]
  have hlu' : u'.length = u.length := by
    rw [hlu, List.length_append, length_vA, List.length_take, length_vP, min_eq_left hj]
  have hu0 : 0 < u.length := by rw [hlu]; omega
  have hcut : vCut n j = (u.length : ℤ) := by rw [vCut, hlu]
  rw [ex] at hx
  rw [ey] at hy
  unfold dtrace at htr
  rw [ex, ey, hcut] at htr
  have hnm := splice_nmem M hM u v u' v' hu0 hlu' hx.2.1 hx.2.2 hy.2.1 hy.2.2 htr
  rw [← ez, vInst_mem_iff hn] at hnm
  exact (not_not.1 hnm).symm

/-- **Injectivity on the `2ⁿ` diagonal instances**, at every cut in the doubled padding. -/
theorem dtraceV_injective {M : TM} {T : ℕ → ℕ} (hM : M.Decides V_SAT T) {n j : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ 6 * n) :
    Function.Injective fun a : Pt n => dtrace M (vCut n j) (vInst a (List.ofFn a)) :=
  fun a a' h => vsat_mixed hM hn hj a a' h

theorem card_pt (n : ℕ) : Fintype.card (Pt n) = 2 ^ n := by simp

/-- **`V_SAT` carries quadratic crossing information.** -/
theorem crossingInfo_V_SAT (n : ℕ) (hn : 1 ≤ n) :
    CrossingInfo V_SAT (13 * n + 1) (2 ^ n) (6 * n + 1) := by
  rw [← card_pt n]
  exact crossingInfo_of_equiv (fun a : Pt n => vInst a (List.ofFn a)) (vCut n)
    (vCut_injective n) (fun a => length_vInst a a)
    (fun M T hM j hj => dtraceV_injective hM hn (by omega))

/-- The verifier family is within a constant factor of the information-theoretic maximum:
`N² ≤ 30·G·log₂F` with `N = 13n+1`, `G = 6n+1`, `log₂F = n`. -/
theorem vsat_info_quadratic (n : ℕ) (hn : 1 ≤ n) : (13 * n + 1) ^ 2 ≤ 30 * ((6 * n + 1) * n) := by
  nlinarith

/-! ### Time lower bounds for the polynomial-time language `V_SAT` -/

/-- **Single-tape lower bound for `V_SAT`.** -/
theorem vsat_time_lower_bound {M : TM} {T : ℕ → ℕ} (hM : M.Decides V_SAT T) {n ℓ : ℕ}
    (hn : 1 ≤ n) (hℓ : 2 * (Fintype.card (M.Λ × Dir) + 1) ^ ℓ ≤ 2 ^ n) :
    (6 * n + 1) * ℓ ≤ 2 * T (13 * n + 1) :=
  time_of_crossingInfo (crossingInfo_V_SAT n hn) hM hℓ

/-- **Quadratic form**: with `L = ⌊log₂(|Λ×Dir| + 1)⌋ + 1`,
`(6n + 1)·⌊(n − 1)/L⌋ ≤ 2T(13n + 1)`, i.e. `T(N) = Ω(N²/log|Λ|)` for every single-tape decider
of `V_SAT`, although `satTM` decides `V_SAT` within `2(N+3)²`. -/
theorem vsat_time_lower_bound_sq {M : TM} {T : ℕ → ℕ} (hM : M.Decides V_SAT T) {n : ℕ}
    (hn : 1 ≤ n) :
    (6 * n + 1) * ((n - 1) / (Nat.log 2 (Fintype.card (M.Λ × Dir) + 1) + 1)) ≤
      2 * T (13 * n + 1) := by
  set C := Fintype.card (M.Λ × Dir)
  set L := Nat.log 2 (C + 1) + 1
  set ℓ := (n - 1) / L
  have hC : C + 1 < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have hLℓ : L * ℓ ≤ n - 1 := Nat.mul_div_le (n - 1) L
  have hℓ : 2 * (C + 1) ^ ℓ ≤ 2 ^ n := by
    calc 2 * (C + 1) ^ ℓ ≤ 2 * (2 ^ L) ^ ℓ :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hC.le ℓ)
      _ = 2 * 2 ^ (L * ℓ) := by rw [← pow_mul]
      _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hLℓ)
      _ = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  exact vsat_time_lower_bound hM hn hℓ

/-- **No-go for the crossing-information invariant.** A language in `P_TM`, decided by an
explicit single-tape machine in time `2(N+3)²`, carries crossing information
`CrossingInfo L (13n+1) (2ⁿ) (6n+1)` for every `n ≥ 1`, i.e. a constant fraction of the
information-theoretic maximum. Hence "`L` carries quadratic crossing information" does not
imply `L ∉ P_TM`. -/
theorem crossingInfo_not_superpolynomial :
    ∃ L ∈ P_TM, satTM.Decides L (fun N => 2 * (N + 3) ^ 2) ∧
      ∀ n, 1 ≤ n → CrossingInfo L (13 * n + 1) (2 ^ n) (6 * n + 1) :=
  ⟨V_SAT, V_SAT_mem_P_TM, satTM_decides, crossingInfo_V_SAT⟩

end PVNP.VerifierCrossing
