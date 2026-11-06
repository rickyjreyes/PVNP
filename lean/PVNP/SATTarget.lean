import PVNP.CrossingSAT
import PVNP.PartISeparation

/-!
# Phase IX: the exact target statement

The remaining premise of the separation transfer is `CrossingSAT.SATLowerBound`, i.e.
`SAT_dense ∉ P_TM`. Phase IX states the target in the *per-input* form

  every machine `M` that decides `SAT_dense` (on every input, with no time bound imposed)
  satisfies: for every exponent `k`, every constant `C > 0` and every length threshold `N₀`,
  some input `x` with `|x| ≥ N₀` has first-answer time `T_M(x) > C·|x|^k`.

This file proves that the per-input form is *equivalent* to `SATLowerBound`, using only the
repository's own definitions (`DecidesAt`, `FirstAnswer`, `TM.Decides`, `P_TM`). The time
`T_M(x)` is the first-answer time `CrossingSAT.ftime M x`, the step at which `M` first displays
an answer, which is the time notion `TM.Decides` bounds.

Nothing here proves `SATLowerBound`; the theorems fix the target exactly and show that the
`∀ M ∃ x` quantifier structure and the class-membership formulation say the same thing.

* `Correct M L`: `M` gives the correct first answer on every input, in finite time.
* `SATSuperpolynomial`: the per-input target, with natural-number constants.
* `SATSuperpolynomialReal`: the same with real constants `C > 0`.
* `mem_P_TM_of_eventually_le`: a correct decider whose first-answer time is bounded by a
  polynomial on all sufficiently long inputs already witnesses membership in `P_TM`
  (finitely many short inputs are absorbed into the constant term).
* `satLowerBound_iff_superpolynomial`, `superpolynomial_iff_real`: the equivalences.
* `satLowerBound_iff_wccDepth`, `satLowerBound_iff_wccdDepth`: the target is exactly Part I
  `conj:wcc_depth` (`PartISeparation.WCCDepth`) for `SAT_dense`, in the 1-D and `(1+d)`-D
  discrete WCC models.
-/

namespace PVNP.SATTarget

open PVNP.Discrete PVNP.Discrete.TM PVNP.Discrete.SATV PVNP.CrossingSAT

/-- `M` is a *correct* decider for `L`: on every input it eventually displays a first answer,
and that answer is the membership bit. No time bound is imposed. -/
def Correct (M : TM) (L : Set (List Bool)) : Prop :=
  ∀ x : List Bool, ∃ T : ℕ, DecidesAt (M.out x) T x L

/-- **Phase IX target** (per-input form, natural constants): every correct decider of
`SAT_dense` exceeds `C·|x|^k` first-answer steps on arbitrarily long inputs. -/
def SATSuperpolynomial : Prop :=
  ∀ M : TM, Correct M SAT_dense → ∀ k C N₀ : ℕ, 0 < C →
    ∃ x : List Bool, N₀ ≤ x.length ∧ C * x.length ^ k < ftime M x

/-- **Phase IX target** with real constants `C > 0`. -/
def SATSuperpolynomialReal : Prop :=
  ∀ M : TM, Correct M SAT_dense → ∀ (k : ℕ) (C : ℝ), 0 < C → ∀ N₀ : ℕ,
    ∃ x : List Bool, N₀ ≤ x.length ∧ C * (x.length : ℝ) ^ k < (ftime M x : ℝ)

/-- A decider within any time bound is correct. -/
theorem correct_of_decides {M : TM} {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T) :
    Correct M L := fun x => ⟨T x.length, hM x⟩

/-- A correct decider gives its answer exactly at `ftime`. -/
theorem decidesAt_ftime {M : TM} {L : Set (List Bool)} (hM : Correct M L) (x : List Bool) :
    DecidesAt (M.out x) (ftime M x) x L := by
  obtain ⟨T, b, hfa, hb⟩ := hM x
  obtain ⟨-, hs, hs0⟩ := ftime_spec hfa
  exact ⟨b, ⟨ftime M x, le_rfl, hs, hs0⟩, hb⟩

/-- Enlarging the time bound preserves a decision. -/
theorem decidesAt_mono {out : ℕ → Option Bool} {T T' : ℕ} {x : List Bool} {L : Set (List Bool)}
    (h : DecidesAt out T x L) (hT : T ≤ T') : DecidesAt out T' x L := by
  obtain ⟨b, ⟨s, hs, hsb, hs0⟩, hb⟩ := h
  exact ⟨b, ⟨s, hs.trans hT, hsb, hs0⟩, hb⟩

/-- The first-answer time of a decider is at most its time bound. -/
theorem ftime_le_of_decides {M : TM} {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T)
    (x : List Bool) : ftime M x ≤ T x.length := by
  obtain ⟨b, hfa, -⟩ := hM x
  exact (ftime_spec hfa).1

/-- A correct decider with time bound `T` on every input decides within `T`. -/
theorem decides_of_correct_le {M : TM} {L : Set (List Bool)} (hM : Correct M L) {T : ℕ → ℕ}
    (hT : ∀ x : List Bool, ftime M x ≤ T x.length) : M.Decides L T :=
  fun x => decidesAt_mono (decidesAt_ftime hM x) (hT x)

/-- **Finite exceptions do not matter.** If a correct decider's first-answer time is bounded by
a polynomial on all inputs of length at least `N₀`, then `L ∈ P_TM` (the finitely many shorter
inputs are absorbed into the constant term; the machine is not modified). -/
theorem mem_P_TM_of_eventually_le {M : TM} {L : Set (List Bool)} (hM : Correct M L)
    (p : Polynomial ℕ) (N₀ : ℕ)
    (hp : ∀ x : List Bool, N₀ ≤ x.length → ftime M x ≤ p.eval x.length) : L ∈ P_TM := by
  obtain ⟨K, hK⟩ := ((List.finite_length_lt Bool N₀).image (ftime M)).bddAbove
  refine ⟨M, p + Polynomial.C K, decides_of_correct_le hM fun x => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  by_cases hx : N₀ ≤ x.length
  · exact (hp x hx).trans (Nat.le_add_right _ _)
  · have : ftime M x ≤ K := hK ⟨x, by simpa using hx, rfl⟩
    exact this.trans (Nat.le_add_left _ _)

/-- A natural-coefficient polynomial is dominated by `p(1)·n^deg p` for `n ≥ 1`. -/
theorem eval_le_eval_one_mul (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))

/-- Every natural-coefficient polynomial is eventually below `n^(deg p + 1)`. -/
theorem eval_le_pow_succ (p : Polynomial ℕ) {n : ℕ} (hn : p.eval 1 + 1 ≤ n) :
    p.eval n ≤ n ^ (p.natDegree + 1) := by
  calc p.eval n ≤ p.eval 1 * n ^ p.natDegree := eval_le_eval_one_mul p (by omega)
    _ ≤ n * n ^ p.natDegree := Nat.mul_le_mul_right _ (by omega)
    _ = n ^ (p.natDegree + 1) := by ring

/-- **Exact target equivalence.** `SAT_dense ∉ P_TM` holds iff every correct decider of
`SAT_dense` exceeds every polynomial `C·|x|^k` on arbitrarily long inputs. -/
theorem satLowerBound_iff_superpolynomial : SATLowerBound ↔ SATSuperpolynomial := by
  constructor
  · intro h M hM k C N₀ hC
    by_contra hcon
    push_neg at hcon
    apply h
    refine mem_P_TM_of_eventually_le hM (Polynomial.C C * Polynomial.X ^ k) N₀ fun x hx => ?_
    simpa using hcon x hx
  · intro h hP
    obtain ⟨M, p, hM⟩ := hP
    obtain ⟨x, hx, hlt⟩ :=
      h M (correct_of_decides hM) (p.natDegree + 1) 1 (p.eval 1 + 1) Nat.one_pos
    have h1 := ftime_le_of_decides hM x
    have h2 := eval_le_pow_succ p hx
    simp only [one_mul] at hlt
    omega

/-- Natural and real constants give the same target. -/
theorem superpolynomial_iff_real : SATSuperpolynomial ↔ SATSuperpolynomialReal := by
  constructor
  · intro h M hM k C hC N₀
    obtain ⟨x, hx, hlt⟩ := h M hM k (⌈C⌉₊) N₀ (Nat.ceil_pos.2 hC)
    refine ⟨x, hx, ?_⟩
    have hlt' : ((⌈C⌉₊ * x.length ^ k : ℕ) : ℝ) < (ftime M x : ℝ) := by exact_mod_cast hlt
    push_cast at hlt'
    have hCle : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    have hpow : (0 : ℝ) ≤ (x.length : ℝ) ^ k := by positivity
    calc C * (x.length : ℝ) ^ k ≤ (⌈C⌉₊ : ℝ) * (x.length : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hCle hpow
      _ < ftime M x := hlt'
  · intro h M hM k C N₀ hC
    obtain ⟨x, hx, hlt⟩ := h M hM k (C : ℝ) (by exact_mod_cast hC) N₀
    refine ⟨x, hx, ?_⟩
    exact_mod_cast hlt

/-- The real-constant target is also equivalent to `SATLowerBound`. -/
theorem satLowerBound_iff_superpolynomialReal : SATLowerBound ↔ SATSuperpolynomialReal :=
  satLowerBound_iff_superpolynomial.trans superpolynomial_iff_real

/-- **The target is `conj:wcc_depth` for `SAT_dense`** (uniform 1-D discrete WCC). -/
theorem satLowerBound_iff_wccDepth : SATLowerBound ↔ PartISeparation.WCCDepth SAT_dense := by
  unfold SATLowerBound
  exact (PartISeparation.WCCDepth_iff_not_P_TM SAT_dense).symm

/-- The same on the lattice `ℤ^(1+d)` (multidimensional discrete WCC). -/
theorem satLowerBound_iff_wccdDepth (d : ℕ) :
    SATLowerBound ↔ PartISeparation.WCCDDepth d SAT_dense := by
  unfold SATLowerBound
  exact (PartISeparation.WCCDDepth_iff_not_P_TM d SAT_dense).symm

/-- The target would give the classical-model separation through the proved transfer. -/
theorem P_ne_NP_of_superpolynomial (h : SATSuperpolynomial) : P_TM ≠ NP_TM :=
  P_ne_NP_of_satLowerBound (satLowerBound_iff_superpolynomial.2 h)

end PVNP.SATTarget
