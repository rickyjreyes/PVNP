import PVNP.CrossingSAT

/-!
# Phase VIII: the strongest single-tape SAT bound obtainable from crossing sequences

`CrossingSAT` uses the diagonal family `(a, ¬a)`, whose members are *accepted* and carry `n`
bits across a cut; on the dense encoding (`3n` bits per clause) this gives
`T(N) = Ω(N^{3/2} / log |Λ|)`.  Here the fooling family is chosen so that **the information that
must cross every cut is linear in the input length**, which is the most any crossing-sequence
argument can force:

* a generic double-counting theorem (`fooling_time_bound`): if decision traces are injective on a
  family of size `F` at `G` distinct cuts, then `G·ℓ ≤ 2T` whenever `2(|Λ×Dir| + 1)^ℓ ≤ F`;
* the rejection form of the splicing theorem (`splice_nmem`);
* the **set family**: for `S, S' ⊆ {0,1}ⁿ`, `setFormula n g S S'` is the CNF whose first block
  excludes every point outside `S` (one clause of width `n` per point) and whose last block
  excludes every point of `S'`; it is satisfiable iff `S ⊄ S'` (`encSet_mem_iff`).  The diagonal
  instances `(S, S)` are **unsatisfiable**, the crossed ones are satisfiable unless `S ⊆ S'`, so
  rejection splicing makes decision traces injective on `2^{2ⁿ}` instances (`dtraceSet_injective`).

**Theorem (`sat_time_lower_bound_sets`).**  For every machine `M` deciding `SAT_dense` within
`T`, every `n ≥ 1`, `g`, and `ℓ` with `2(|Λ×Dir| + 1)^ℓ ≤ 2^{2ⁿ}`,

  `(3ng + 1) · ℓ ≤ 2 · T(3n(2·2ⁿ + g))`.

With `g = 2ⁿ` (`N = 9n2ⁿ`, `sat_time_lower_bound_near_sq`) this reads
`T(N) ≥ (3n2ⁿ + 1)⌊(2ⁿ − 1)/L⌋/2 ≈ N² / (54 · n · L)`, `n ≤ log₂ N`, `L = ⌊log₂(3|Λ|+1)⌋ + 1`:
**`T(N) = Ω(N² / (log N · log |Λ|))`**.

**Ceiling.** At one cut a decision trace is a word over `Λ × Dir`, and injectivity on a family of
inputs of length `N` can force at most `log_{3|Λ|+1} 2^N ≤ N` crossings; there are at most `N + 1`
cuts.  So crossing-sequence counting can never certify more than `O(N²)` single-tape steps — the
bound above is optimal for the method up to the logarithmic factors, and it is a fixed polynomial.
-/

namespace PVNP.CrossingSATSets

open PVNP.Discrete PVNP.Discrete.SATV PVNP.PartI PVNP.CrossingTrace PVNP.CrossingHennie
open PVNP.CrossingSAT

/-! ### Generic double counting -/

/-- **Fooling-family time bound.**  Injective decision traces at `G` distinct cuts on a family of
`F` inputs force `G·ℓ ≤ 2T` whenever `2(|Λ×Dir|+1)^ℓ ≤ F`. -/
theorem fooling_time_bound {M : TM} {ι : Type*} [Fintype ι] (x : ι → List Bool)
    (cut : ℕ → ℤ) (hcut : Function.Injective cut) {G Tb ℓ : ℕ}
    (htime : ∀ i, ftime M (x i) ≤ Tb)
    (hinj : ∀ j < G, Function.Injective fun i => dtrace M (cut j) (x i))
    (hℓ : 2 * (Fintype.card (M.Λ × Dir) + 1) ^ ℓ ≤ Fintype.card ι) :
    G * ℓ ≤ 2 * Tb := by
  classical
  set C := Fintype.card (M.Λ × Dir)
  set F := Fintype.card ι
  set f : ι → ℕ → ℕ := fun i j => (dtrace M (cut j) (x i)).length
  have hrow : ∀ i, ∑ j ∈ Finset.range G, f i j ≤ Tb := by
    intro i
    have hs := sum_trace_length_le M ((Finset.range G).image cut) (ftime M (x i)) (M.init (x i))
    rw [Finset.sum_image (fun j _ j' _ h => hcut h)] at hs
    exact hs.trans (htime i)
  have hcol : ∀ j ∈ Finset.range G, ℓ * F ≤ ℓ * (C + 1) ^ ℓ + ∑ i, f i j := by
    intro j hj
    have hinj' := hinj j (Finset.mem_range.1 hj)
    set short := (Finset.univ : Finset ι).filter fun i => f i j < ℓ
    have hshort : short.card ≤ (C + 1) ^ ℓ := by
      have hmap : Set.InjOn (fun i : ι =>
          (fun k : Fin ℓ => (dtrace M (cut j) (x i))[k.val]?)) short := by
        intro i hi i' hi' h
        exact hinj' (eq_of_padded_eq (Finset.mem_filter.1 hi).2.le (Finset.mem_filter.1 hi').2.le h)
      have := Finset.card_le_card_of_injOn _ (fun i _ => Finset.mem_univ _) hmap
      simpa [Fintype.card_fun, Fintype.card_option, C] using this
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (fun i => f i j < ℓ)
    rw [Finset.card_univ] at hsplit
    have hlong : ℓ * ((Finset.univ : Finset ι).filter fun i => ¬ f i j < ℓ).card ≤ ∑ i, f i j := by
      calc ℓ * ((Finset.univ : Finset ι).filter fun i => ¬ f i j < ℓ).card
          = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => ¬ f i j < ℓ), ℓ := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => ¬ f i j < ℓ), f i j :=
            Finset.sum_le_sum fun i hi => by have := (Finset.mem_filter.1 hi).2; omega
        _ ≤ ∑ i, f i j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
    calc ℓ * F = ℓ * short.card +
          ℓ * ((Finset.univ : Finset ι).filter fun i => ¬ f i j < ℓ).card := by
          rw [← mul_add, hsplit]
      _ ≤ ℓ * (C + 1) ^ ℓ + ∑ i, f i j := add_le_add (Nat.mul_le_mul_left _ hshort) hlong
  have htot : G * (ℓ * F) ≤ G * (ℓ * (C + 1) ^ ℓ) + F * Tb := by
    have h1 := Finset.sum_le_sum hcol
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_comm] at h1
    have h2 : ∑ i : ι, ∑ j ∈ Finset.range G, f i j ≤ ∑ _i : ι, Tb :=
      Finset.sum_le_sum fun i _ => hrow i
    have h3 : ∑ _i : ι, Tb = F * Tb := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hpos : 0 < F := by
    have : 0 < 2 * (C + 1) ^ ℓ := by positivity
    omega
  have key : G * ℓ * F ≤ 2 * Tb * F := by
    have := Nat.mul_le_mul_left (G * ℓ) hℓ
    nlinarith
  exact Nat.le_of_mul_le_mul_right key hpos

/-! ### Rejection splicing -/

/-- If two non-members of a decided language have equal crossing traces at the cut `|u|` up to
their first answers, then the mixed input `u ++ v'` is also a non-member. -/
theorem splice_nmem (M : TM) {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T)
    (u v u' v' : List Bool) (hu0 : 0 < u.length) (hu : u'.length = u.length)
    {sx sy : ℕ}
    (hx : M.out (u ++ v) sx = some false) (hx0 : ∀ r < sx, M.out (u ++ v) r = none)
    (hy : M.out (u' ++ v') sy = some false) (hy0 : ∀ r < sy, M.out (u' ++ v') r = none)
    (htr : trace M (u.length : ℤ) (M.init (u ++ v)) sx =
      trace M (u.length : ℤ) (M.init (u' ++ v')) sy) :
    u ++ v' ∉ L := by
  obtain ⟨sz, -, hz0, hz⟩ := hennie M u v u' v' hu0 hu hx hx0 hy hy0 htr
  simp only [ite_self] at hz
  obtain ⟨b, hfa, hb⟩ := hM (u ++ v')
  have := firstAnswer_unique hfa hz hz0
  intro hmem
  have := hb.2 hmem
  simp_all

theorem decides_false {M : TM} {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T)
    {x : List Bool} (hx : x ∉ L) :
    ftime M x ≤ T x.length ∧ M.out x (ftime M x) = some false ∧
      ∀ r < ftime M x, M.out x r = none := by
  obtain ⟨b, hfa, hb⟩ := hM x
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd (hb.1 rfl) hx
  subst hbf
  exact ftime_spec hfa

/-! ### The set family -/

/-- Points of `{0,1}ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → Bool

/-- A fixed enumeration of all `2ⁿ` points. -/
noncomputable def pts (n : ℕ) : List (Pt n) := (Finset.univ : Finset (Pt n)).toList

/-- The width-`n` clause excluding the point `p`: `⋁ᵢ (zᵢ ≠ pᵢ)`. -/
def exC {n : ℕ} (p : Pt n) : Clause := List.ofFn fun i : Fin n => ((i : ℕ), !p i)

/-- First block: exclude every point outside `S` (solutions `= S`). -/
noncomputable def blockSA {n : ℕ} (S : Finset (Pt n)) : Formula :=
  (pts n).map fun p => if p ∈ S then tautC 0 else exC p

/-- Last block: exclude every point of `S'` (solutions `= complement of S'`). -/
noncomputable def blockSB {n : ℕ} (S' : Finset (Pt n)) : Formula :=
  (pts n).map fun p => if p ∈ S' then exC p else tautC 0

/-- The set-family CNF. -/
noncomputable def setFormula (n g : ℕ) (S S' : Finset (Pt n)) : Formula :=
  blockSA S ++ pad g ++ blockSB S'

/-- The set-family instance of `SAT_dense`. -/
noncomputable def encSet (n g : ℕ) (S S' : Finset (Pt n)) : List Bool :=
  encDense n (setFormula n g S S')

theorem mem_pts {n : ℕ} (p : Pt n) : p ∈ pts n := Finset.mem_toList.2 (Finset.mem_univ p)

theorem length_pts (n : ℕ) : (pts n).length = 2 ^ n := by
  simp [pts, Finset.length_toList]

theorem evalClause_exC (w : ℕ → Bool) {n : ℕ} (p : Pt n) :
    evalClause w (exC p) = true ↔ (fun i : Fin n => w i) ≠ p := by
  rw [evalClause_eq_any, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hv⟩ heq
    rw [exC, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    have h := congrFun heq i
    simp only at h
    simp [evalLiteral, literalTrue, h] at hv
  · intro hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    refine ⟨((i : ℕ), !p i), by rw [exC, List.mem_ofFn]; exact ⟨i, rfl⟩, ?_⟩
    cases h : w i <;> cases hp : p i <;> simp_all [evalLiteral, literalTrue]

theorem setFormula_sat_iff (n g : ℕ) (S S' : Finset (Pt n)) :
    satisfiable (setFormula n g S S') ↔ ∃ z, z ∈ S ∧ z ∉ S' := by
  constructor
  · rintro ⟨w, hw⟩
    rw [evalFormula_iff] at hw
    set z : Pt n := fun i => w i
    refine ⟨z, ?_, ?_⟩
    · by_contra hz
      have := hw (exC z) (by
        simp only [setFormula, blockSA, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨z, mem_pts z, by simp [hz]⟩))
      exact (evalClause_exC w z).1 this rfl
    · intro hz
      have := hw (exC z) (by
        simp only [setFormula, blockSB, List.mem_append, List.mem_map]
        exact Or.inr ⟨z, mem_pts z, by simp [hz]⟩)
      exact (evalClause_exC w z).1 this rfl
  · rintro ⟨z, hzS, hzS'⟩
    refine ⟨fun j => if h : j < n then z ⟨j, h⟩ else false, ?_⟩
    have hres : (fun i : Fin n => (fun j => if h : j < n then z ⟨j, h⟩ else false) (i : ℕ)) = z := by
      funext i; simp [i.isLt]
    rw [evalFormula_iff]
    intro c hc
    simp only [setFormula, blockSA, blockSB, pad, List.mem_append, List.mem_map,
      List.mem_replicate] at hc
    rcases hc with (⟨p, -, rfl⟩ | ⟨-, rfl⟩) | ⟨p, -, rfl⟩
    · by_cases hp : p ∈ S
      · simp only [hp, ↓reduceIte, evalClause_tautC]
      · simp only [hp, ↓reduceIte]
        rw [evalClause_exC, hres]
        rintro rfl; exact hp hzS
    · exact evalClause_tautC _ _
    · by_cases hp : p ∈ S'
      · simp only [hp, ↓reduceIte]
        rw [evalClause_exC, hres]
        rintro rfl; exact hzS' hp
      · simp only [hp, ↓reduceIte, evalClause_tautC]

theorem setFormula_vars (n g : ℕ) (hn : 1 ≤ n) (S S' : Finset (Pt n)) :
    ∀ c ∈ setFormula n g S S', ∀ l ∈ c, l.1 < n := by
  intro c hc l hl
  simp only [setFormula, blockSA, blockSB, pad, List.mem_append, List.mem_map,
    List.mem_replicate] at hc
  have htaut : ∀ l ∈ tautC 0, l.1 < n := by
    intro l hl; simp [tautC] at hl; rcases hl with rfl | rfl <;> simp <;> omega
  have hex : ∀ p : Pt n, ∀ l ∈ exC p, l.1 < n := by
    intro p l hl
    rw [exC, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact i.isLt
  rcases hc with (⟨p, -, rfl⟩ | ⟨-, rfl⟩) | ⟨p, -, rfl⟩
  · split_ifs at hl
    · exact htaut l hl
    · exact hex p l hl
  · exact htaut l hl
  · split_ifs at hl
    · exact hex p l hl
    · exact htaut l hl

/-- **Membership**: `encSet n g S S' ∈ SAT_dense ↔ S ⊄ S'`. -/
theorem encSet_mem_iff (n g : ℕ) (hn : 1 ≤ n) (S S' : Finset (Pt n)) :
    encSet n g S S' ∈ SAT_dense ↔ ∃ z, z ∈ S ∧ z ∉ S' :=
  (encDense_mem_SAT_iff n hn _ (setFormula_vars n g hn S S')).trans (setFormula_sat_iff n g S S')

theorem encSet_diag_nmem (n g : ℕ) (hn : 1 ≤ n) (S : Finset (Pt n)) : encSet n g S S ∉ SAT_dense := by
  rw [encSet_mem_iff n g hn]
  rintro ⟨z, h1, h2⟩
  exact h2 h1

/-! ### Layout of the set family -/

noncomputable def partSA {n : ℕ} (S : Finset (Pt n)) : List Bool := encDense n (blockSA S)

noncomputable def partSB {n : ℕ} (S' : Finset (Pt n)) : List Bool := encDense n (blockSB S')

theorem encSet_layout (n g : ℕ) (S S' : Finset (Pt n)) :
    encSet n g S S' = partSA S ++ partP n g ++ partSB S' := by
  simp only [encSet, setFormula, encDense_append, partSA, partP, partSB]

theorem length_partSA {n : ℕ} (S : Finset (Pt n)) : (partSA S).length = 3 * n * 2 ^ n := by
  simp [partSA, length_encDense, blockSA, length_pts]

theorem length_partSB {n : ℕ} (S : Finset (Pt n)) : (partSB S).length = 3 * n * 2 ^ n := by
  simp [partSB, length_encDense, blockSB, length_pts]

theorem length_encSet (n g : ℕ) (S S' : Finset (Pt n)) :
    (encSet n g S S').length = 3 * n * (2 * 2 ^ n + g) := by
  rw [encSet_layout, List.length_append, List.length_append, length_partSA, length_partP,
    length_partSB]
  ring

theorem encSet_split (n g j : ℕ) (S S' : Finset (Pt n)) :
    encSet n g S S' = (partSA S ++ (partP n g).take j) ++ ((partP n g).drop j ++ partSB S') := by
  rw [encSet_layout, List.append_assoc, List.append_assoc, ← List.append_assoc (List.take _ _),
    List.take_append_drop]

/-- The cut `3n·2ⁿ + j` inside the padding. -/
def cutSet (n j : ℕ) : ℤ := ((3 * n * 2 ^ n + j : ℕ) : ℤ)

theorem cutSet_injective (n : ℕ) : Function.Injective (cutSet n) := by
  intro j j' h; unfold cutSet at h; omega

/-! ### Rejection splicing on the set family -/

/-- **Mixed rejection.**  Equal decision traces of the (unsatisfiable) diagonal instances
`(S, S)` and `(S', S')` at a cut in the padding force the crossed instance `(S, S')` to be
unsatisfiable, i.e. `S ⊆ S'`. -/
theorem set_mixed {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ 3 * n * g) (S S' : Finset (Pt n))
    (htr : dtrace M (cutSet n j) (encSet n g S S) = dtrace M (cutSet n j) (encSet n g S' S')) :
    S ⊆ S' := by
  have hx := decides_false hM (encSet_diag_nmem n g hn S)
  have hy := decides_false hM (encSet_diag_nmem n g hn S')
  set u := partSA S ++ (partP n g).take j
  set u' := partSA S' ++ (partP n g).take j
  set v := (partP n g).drop j ++ partSB S
  set v' := (partP n g).drop j ++ partSB S'
  have ex : encSet n g S S = u ++ v := encSet_split n g j _ _
  have ey : encSet n g S' S' = u' ++ v' := encSet_split n g j _ _
  have ez : encSet n g S S' = u ++ v' := encSet_split n g j _ _
  have hlu : u.length = 3 * n * 2 ^ n + j := by
    rw [List.length_append, length_partSA, List.length_take, length_partP, min_eq_left hj]
  have hlu' : u'.length = u.length := by
    rw [hlu, List.length_append, length_partSA, List.length_take, length_partP, min_eq_left hj]
  have hu0 : 0 < u.length := by rw [hlu]; positivity
  have hcut : cutSet n j = (u.length : ℤ) := by rw [cutSet, hlu]
  rw [ex] at hx
  rw [ey] at hy
  unfold dtrace at htr
  rw [ex, ey, hcut] at htr
  have hnm := splice_nmem M hM u v u' v' hu0 hlu' hx.2.1 hx.2.2 hy.2.1 hy.2.2 htr
  rw [← ez, encSet_mem_iff n g hn] at hnm
  intro z hz
  by_contra hz'
  exact hnm ⟨z, hz, hz'⟩

/-- **Injectivity on `2^{2ⁿ}` instances**, at every cut in the padding. -/
theorem dtraceSet_injective {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ 3 * n * g) :
    Function.Injective fun S : Finset (Pt n) => dtrace M (cutSet n j) (encSet n g S S) := by
  intro S S' h
  exact Finset.Subset.antisymm (set_mixed hM hn hj S S' h) (set_mixed hM hn hj S' S h.symm)

/-! ### The near-quadratic lower bound -/

theorem card_sets (n : ℕ) : Fintype.card (Finset (Pt n)) = 2 ^ 2 ^ n := by
  simp [Fintype.card_finset]

/-- **Single-tape `SAT_dense` lower bound from the set family.** -/
theorem sat_time_lower_bound_sets {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T)
    {n g ℓ : ℕ} (hn : 1 ≤ n) (hℓ : 2 * (Fintype.card (M.Λ × Dir) + 1) ^ ℓ ≤ 2 ^ 2 ^ n) :
    (3 * n * g + 1) * ℓ ≤ 2 * T (3 * n * (2 * 2 ^ n + g)) := by
  refine fooling_time_bound (M := M) (fun S : Finset (Pt n) => encSet n g S S) (cutSet n)
    (cutSet_injective n) (fun S => ?_) (fun j hj => ?_) (by rw [card_sets]; exact hℓ)
  · have hx := decides_false hM (encSet_diag_nmem n g hn S)
    rw [length_encSet] at hx
    exact hx.1
  · exact dtraceSet_injective hM hn (by omega)

/-- **The near-quadratic form** (`g = 2ⁿ`, `N = 9n·2ⁿ`): with `L = ⌊log₂(|Λ×Dir| + 1)⌋ + 1`,
`(3n·2ⁿ + 1)·⌊(2ⁿ − 1)/L⌋ ≤ 2T(9n·2ⁿ)`, i.e. `T(N) = Ω(N²/(log N · log|Λ|))`. -/
theorem sat_time_lower_bound_near_sq {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T)
    {n : ℕ} (hn : 1 ≤ n) :
    (3 * n * 2 ^ n + 1) * ((2 ^ n - 1) / (Nat.log 2 (Fintype.card (M.Λ × Dir) + 1) + 1)) ≤
      2 * T (9 * n * 2 ^ n) := by
  set C := Fintype.card (M.Λ × Dir)
  set L := Nat.log 2 (C + 1) + 1
  set ℓ := (2 ^ n - 1) / L
  have hC : C + 1 < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have hLℓ : L * ℓ ≤ 2 ^ n - 1 := Nat.mul_div_le (2 ^ n - 1) L
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hℓ : 2 * (C + 1) ^ ℓ ≤ 2 ^ 2 ^ n := by
    calc 2 * (C + 1) ^ ℓ ≤ 2 * (2 ^ L) ^ ℓ :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hC.le ℓ)
      _ = 2 * 2 ^ (L * ℓ) := by rw [← pow_mul]
      _ ≤ 2 * 2 ^ (2 ^ n - 1) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hLℓ)
      _ = 2 ^ 2 ^ n := by rw [← pow_succ']; congr 1; omega
  have h := sat_time_lower_bound_sets hM (g := 2 ^ n) hn hℓ
  have e : 3 * n * (2 * 2 ^ n + 2 ^ n) = 9 * n * 2 ^ n := by ring
  rw [e] at h
  exact h

end PVNP.CrossingSATSets
