import PVNP.CrossingHennie
import PVNP.SATVerifier

/-!
# Phase VIII: from the splicing theorem to SAT — mixed acceptance and a time lower bound

**Encoding.**  For `a, b ∈ {0,1}ⁿ` and a padding length `g`, `splitFormula n g a b` is the
width-3 CNF over variables `z₀ … z_{n-1}`

  `⋀ᵢ Aᵢ(a) ∧ ⋀_{g} (z₀ ∨ ¬z₀ ∨ ¬z₀) ∧ ⋀ᵢ Bᵢ(b)`,

with `Aᵢ(a) = (zᵢ ∨ zᵢ ∨ zᵢ)` if `aᵢ = 1` and the tautology `(zᵢ ∨ ¬zᵢ ∨ ¬zᵢ)` otherwise, and
`Bᵢ(b) = (¬zᵢ ∨ ¬zᵢ ∨ ¬zᵢ)` if `bᵢ = 1` and the tautology otherwise.  It is the split 3-CNF
of `PVNP.SplitSATCapacity` with every block padded to a fixed number of clauses.  The input
string `encSplit n g a b = encDense n (splitFormula n g a b)` is an instance of the repository's
ordinary CNF-SAT language `SATV.SAT_dense` (dense clause encoding, `3n` bits per clause):

* `encSplit_mem_iff`: `encSplit n g a b ∈ SAT_dense ↔ ∃ z, splitThreeSat a b z`
  (`↔ a ∩ b = ∅`);
* `encSplit_layout`: the `a`-block occupies exactly the first `3n²` cells, then `3ng` padding
  cells, then the `b`-block — a spatially separated layout of total length `3n(2n + g)`.

**Mixed acceptance** (`diag_mixed`), derived from `CrossingHennie.splice_mem` — no splicing
assumption: if `M` decides `SAT_dense` and two diagonal instances `(a, ¬a)`, `(a', ¬a')` have equal
crossing traces up to their first answers at any cut inside the padding, then `(a, ¬a')` is
satisfiable.  Hence (`dtrace_injective`) the decision traces are injective on the `2ⁿ` diagonal
instances, and (`hmixed_of_halting`) the premise `hmixed` of `CrossingDiagonal` holds for every
SAT decider that halts when it answers, making `diagonal_trace_capacity` unconditional for it.

**Time lower bound** (`sat_time_lower_bound`): for every single-tape machine `M` deciding
`SAT_dense` within `T`, every `n ≥ 1`, `g` and `ℓ` with `2(|Λ×Dir| + 1)^ℓ ≤ 2ⁿ`,

  `(3ng + 1) · ℓ ≤ 2 · T(3n(2n + g))`.

With `g = n` this is `T(N) = Ω(N^{3/2} / log |Λ|)` along `N = 9n²` (`sat_time_lower_bound_sq`),
and in particular no single-tape machine decides `SAT_dense` in linear time
(`sat_not_linear_time`).  These are **fixed-polynomial** lower bounds for the single-tape model;
they do not show `SAT_dense ∉ P_TM` (see `pvnp/proofs/phase-viii-separation-status.md`).
-/

namespace PVNP.CrossingSAT

open PVNP.Discrete PVNP.Discrete.SATV PVNP.PartI PVNP.CrossingTrace PVNP.CrossingHennie
open PVNP.SplitSATCapacity PVNP.CrossingCapacity

/-! ### The padded split 3-CNF -/

/-- `zᵢ ∨ zᵢ ∨ zᵢ`. -/
def posC (i : ℕ) : Clause := [(i, true), (i, true), (i, true)]

/-- `¬zᵢ ∨ ¬zᵢ ∨ ¬zᵢ`. -/
def negC (i : ℕ) : Clause := [(i, false), (i, false), (i, false)]

/-- The tautology `zᵢ ∨ ¬zᵢ ∨ ¬zᵢ`. -/
def tautC (i : ℕ) : Clause := [(i, true), (i, false), (i, false)]

/-- Alice's block: one clause per index. -/
def blockA {n : ℕ} (a : Bits n) : Formula :=
  List.ofFn fun i : Fin n => if a i then posC i else tautC i

/-- Bob's block: one clause per index. -/
def blockB {n : ℕ} (b : Bits n) : Formula :=
  List.ofFn fun i : Fin n => if b i then negC i else tautC i

/-- Neutral padding. -/
def pad (g : ℕ) : Formula := List.replicate g (tautC 0)

/-- The padded split 3-CNF. -/
def splitFormula (n g : ℕ) (a b : Bits n) : Formula := blockA a ++ pad g ++ blockB b

/-- **The spatially separated SAT instance** (an input string of `SAT_dense`). -/
def encSplit (n g : ℕ) (a b : Bits n) : List Bool := encDense n (splitFormula n g a b)

theorem evalClause_posC (z : ℕ → Bool) (i : ℕ) : evalClause z (posC i) = z i := by
  cases h : z i <;> simp [posC, evalClause, evalLiteral, literalTrue, h]

theorem evalClause_negC (z : ℕ → Bool) (i : ℕ) : evalClause z (negC i) = !z i := by
  cases h : z i <;> simp [negC, evalClause, evalLiteral, literalTrue, h]

theorem evalClause_tautC (z : ℕ → Bool) (i : ℕ) : evalClause z (tautC i) = true := by
  cases h : z i <;> simp [tautC, evalClause, evalLiteral, literalTrue, h]

theorem evalFormula_iff (z : ℕ → Bool) (F : Formula) :
    evalFormula z F = true ↔ ∀ c ∈ F, evalClause z c = true := by
  induction F with
  | nil => simp [evalFormula]
  | cons c F ih => simp [evalFormula, ih]

/-- The padded split formula is satisfiable exactly when the two private sets are disjoint. -/
theorem splitFormula_sat_iff (n g : ℕ) (a b : Bits n) :
    satisfiable (splitFormula n g a b) ↔ PVNP.Communication.disjoint a b := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [evalFormula_iff] at hz
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    have ha' : a i = true := by simpa using ha
    have hb' : b i = true := by simpa using hb
    have h1 := hz (posC i) (by
      simp only [splitFormula, blockA, List.mem_append, List.mem_ofFn]
      exact Or.inl (Or.inl ⟨i, by simp [ha']⟩))
    have h2 := hz (negC i) (by
      simp only [splitFormula, blockB, List.mem_append, List.mem_ofFn]
      exact Or.inr ⟨i, by simp [hb']⟩)
    rw [evalClause_posC] at h1
    rw [evalClause_negC, h1] at h2
    exact Bool.noConfusion h2
  · intro hd
    refine ⟨fun j => if h : j < n then a ⟨j, h⟩ else false, ?_⟩
    rw [evalFormula_iff]
    intro c hc
    simp only [splitFormula, blockA, blockB, pad, List.mem_append, List.mem_ofFn,
      List.mem_replicate] at hc
    rcases hc with (⟨i, rfl⟩ | ⟨-, rfl⟩) | ⟨i, rfl⟩
    · by_cases ha : a i = true
      · simp only [ha, ↓reduceIte, evalClause_posC, i.isLt, ↓reduceDIte]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, evalClause_tautC]
    · exact evalClause_tautC _ _
    · by_cases hb : b i = true
      · simp only [hb, ↓reduceIte, evalClause_negC, i.isLt, ↓reduceDIte]
        rcases hd i with h | h
        · simp [h]
        · rw [hb] at h; exact absurd h (by decide)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, evalClause_tautC]

theorem splitFormula_vars (n g : ℕ) (hn : 1 ≤ n) (a b : Bits n) :
    ∀ c ∈ splitFormula n g a b, ∀ l ∈ c, l.1 < n := by
  intro c hc l hl
  simp only [splitFormula, blockA, blockB, pad, List.mem_append, List.mem_ofFn,
    List.mem_replicate] at hc
  rcases hc with (⟨i, rfl⟩ | ⟨-, rfl⟩) | ⟨i, rfl⟩
  · split_ifs at hl <;> simp [posC, tautC] at hl <;> rcases hl with rfl | rfl <;> simp
  · simp [tautC] at hl; rcases hl with rfl | rfl <;> simp <;> omega
  · split_ifs at hl <;> simp [negC, tautC] at hl <;> rcases hl with rfl | rfl <;> simp

/-- **Relation to the ordinary SAT language**: the encoded instance belongs to `SAT_dense` iff
the split 3-CNF of `SplitSATCapacity` is satisfiable. -/
theorem encSplit_mem_iff (n g : ℕ) (hn : 1 ≤ n) (a b : Bits n) :
    encSplit n g a b ∈ SAT_dense ↔ ∃ z : Bits n, splitThreeSat a b z :=
  (encDense_mem_SAT_iff n hn _ (splitFormula_vars n g hn a b)).trans
    ((splitFormula_sat_iff n g a b).trans (split_three_sat_iff_disjoint a b).symm)

theorem encSplit_diag_mem (n g : ℕ) (hn : 1 ≤ n) (a : Bits n) :
    encSplit n g a (fun i => !a i) ∈ SAT_dense :=
  (encSplit_mem_iff n g hn _ _).2 (diagonal_split_sat a)

/-! ### Layout -/

theorem length_slotBits (n : ℕ) (c : Clause) (j : ℕ) : (slotBits n c j).length = 3 := rfl

theorem length_encClause (n : ℕ) (c : Clause) : (encClause n c).length = 3 * n := by
  unfold encClause
  rw [List.length_flatMap]
  simp only [length_slotBits, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul]
  ring

theorem length_encDense (n : ℕ) (F : Formula) : (encDense n F).length = 3 * n * F.length := by
  unfold encDense
  rw [List.length_flatMap]
  simp only [length_encClause, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem encDense_append (n : ℕ) (F G : Formula) :
    encDense n (F ++ G) = encDense n F ++ encDense n G := List.flatMap_append

/-- The `a`-part of the input. -/
def partA (n : ℕ) (a : Bits n) : List Bool := encDense n (blockA a)

/-- The padding part. -/
def partP (n g : ℕ) : List Bool := encDense n (pad g)

/-- The `b`-part of the input. -/
def partB (n : ℕ) (b : Bits n) : List Bool := encDense n (blockB b)

theorem encSplit_layout (n g : ℕ) (a b : Bits n) :
    encSplit n g a b = partA n a ++ partP n g ++ partB n b := by
  simp only [encSplit, splitFormula, encDense_append, partA, partP, partB]

theorem length_partA (n : ℕ) (a : Bits n) : (partA n a).length = 3 * n * n := by
  simp [partA, length_encDense, blockA]

theorem length_partP (n g : ℕ) : (partP n g).length = 3 * n * g := by
  simp [partP, length_encDense, pad]

theorem length_partB (n : ℕ) (b : Bits n) : (partB n b).length = 3 * n * n := by
  simp [partB, length_encDense, blockB]

theorem length_encSplit (n g : ℕ) (a b : Bits n) :
    (encSplit n g a b).length = 3 * n * (2 * n + g) := by
  rw [encSplit_layout, List.length_append, List.length_append, length_partA, length_partP,
    length_partB]
  ring

/-- Splitting the input at the cut `3n² + j`, `j ≤ 3ng`, inside the padding. -/
theorem encSplit_split (n g j : ℕ) (a b : Bits n) :
    encSplit n g a b = (partA n a ++ (partP n g).take j) ++ ((partP n g).drop j ++ partB n b) := by
  rw [encSplit_layout, List.append_assoc, List.append_assoc, ← List.append_assoc (List.take _ _),
    List.take_append_drop]

theorem length_left (n g j : ℕ) (hj : j ≤ 3 * n * g) (a : Bits n) :
    (partA n a ++ (partP n g).take j).length = 3 * n * n + j := by
  rw [List.length_append, length_partA, List.length_take, length_partP, min_eq_left hj]

/-! ### First-answer times and decision traces -/

open Classical in
/-- The first time at which `M` displays an answer on `x` (`0` if it never does). -/
noncomputable def ftime (M : TM) (x : List Bool) : ℕ :=
  if h : ∃ s, M.out x s ≠ none then Nat.find h else 0

/-- The crossing trace at the cut `κ` up to the first answer: the complete decision record. -/
noncomputable def dtrace (M : TM) (κ : ℤ) (x : List Bool) : List (M.Λ × Dir) :=
  trace M κ (M.init x) (ftime M x)

theorem ftime_spec {M : TM} {x : List Bool} {T : ℕ} {b : Bool}
    (h : FirstAnswer (M.out x) T b) :
    ftime M x ≤ T ∧ M.out x (ftime M x) = some b ∧ ∀ r < ftime M x, M.out x r = none := by
  obtain ⟨s, hsT, hs, hs0⟩ := h
  have hex : ∃ s, M.out x s ≠ none := ⟨s, by rw [hs]; exact Option.some_ne_none b⟩
  have hfind : Nat.find hex = s := by
    rw [Nat.find_eq_iff]
    refine ⟨by rw [hs]; exact Option.some_ne_none b, fun r hr => ?_⟩
    rw [hs0 r hr]; simp
  have hft : ftime M x = s := by
    unfold ftime; rw [dif_pos hex]; exact hfind
  rw [hft]
  exact ⟨hsT, hs, hs0⟩

/-- Members of a decided language answer `true` at `ftime`, within the time bound. -/
theorem decides_true {M : TM} {L : Set (List Bool)} {T : ℕ → ℕ} (hM : M.Decides L T)
    {x : List Bool} (hx : x ∈ L) :
    ftime M x ≤ T x.length ∧ M.out x (ftime M x) = some true ∧
      ∀ r < ftime M x, M.out x r = none := by
  obtain ⟨b, hfa, hb⟩ := hM x
  have hbt : b = true := hb.2 hx
  subst hbt
  exact ftime_spec hfa

/-! ### Mixed acceptance for the diagonal family, from the splicing theorem -/

/-- The cut `3n² + j` inside the padding. -/
def cutAt (n j : ℕ) : ℤ := ((3 * n * n + j : ℕ) : ℤ)

/-- **Mixed acceptance.**  If `M` decides `SAT_dense` and the diagonal instances `(a, ¬a)` and
`(a', ¬a')` have equal decision traces at a cut inside the padding, then the crossed instance
`(a, ¬a')` is satisfiable. -/
theorem diag_mixed {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ 3 * n * g) (a a' : Bits n)
    (htr : dtrace M (cutAt n j) (encSplit n g a (fun i => !a i)) =
      dtrace M (cutAt n j) (encSplit n g a' (fun i => !a' i))) :
    ∃ z : Bits n, splitThreeSat a (fun i => !a' i) z := by
  rw [← encSplit_mem_iff n g hn]
  have hx := decides_true hM (encSplit_diag_mem n g hn a)
  have hy := decides_true hM (encSplit_diag_mem n g hn a')
  set u := partA n a ++ (partP n g).take j
  set u' := partA n a' ++ (partP n g).take j
  set v := (partP n g).drop j ++ partB n (fun i => !a i)
  set v' := (partP n g).drop j ++ partB n (fun i => !a' i)
  have ex : encSplit n g a (fun i => !a i) = u ++ v := encSplit_split n g j _ _
  have ey : encSplit n g a' (fun i => !a' i) = u' ++ v' := encSplit_split n g j _ _
  have ez : encSplit n g a (fun i => !a' i) = u ++ v' := encSplit_split n g j _ _
  have hlu : u.length = 3 * n * n + j := length_left n g j hj a
  have hlu' : u'.length = u.length := by rw [length_left n g j hj a', hlu]
  have hu0 : 0 < u.length := by rw [hlu]; nlinarith
  have hcut : cutAt n j = (u.length : ℤ) := by rw [cutAt, hlu]
  rw [ex] at hx
  rw [ey] at hy
  rw [ez]
  unfold dtrace at htr
  rw [ex, ey, hcut] at htr
  exact splice_mem M hM u v u' v' hu0 hlu' hx.2.1 hx.2.2 hy.2.1 hy.2.2 htr

/-- **Injectivity of decision traces on the diagonal family**, at every cut in the padding. -/
theorem dtrace_injective {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ 3 * n * g) :
    Function.Injective fun a : Bits n =>
      dtrace M (cutAt n j) (encSplit n g a (fun i => !a i)) := by
  intro a a' heq
  have h1 := diag_mixed hM hn hj a a' heq
  have h2 := diag_mixed hM hn hj a' a heq.symm
  exact PVNP.Communication.cross_disjoint_implies_eq a a'
    ((split_three_sat_iff_disjoint _ _).1 h1) ((split_three_sat_iff_disjoint _ _).1 h2)

/-! ### Discharging the premise of `CrossingDiagonal` -/

theorem trace_succ_length (M : TM) (κ : ℤ) (c : M.Cfg) (t : ℕ) :
    (trace M κ c (t + 1)).length =
      (if event M κ c = none then 0 else 1) + (trace M κ (M.next c) t).length := by
  cases h : event M κ c <;> simp [trace, h, add_comm]

theorem trace_add (M : TM) (κ : ℤ) : ∀ (s r : ℕ) (c : M.Cfg),
    trace M κ c (s + r) = trace M κ c s ++ trace M κ (M.run c s) r := by
  intro s
  induction s with
  | zero => intro r c; simp [trace]; rfl
  | succ s ih =>
    intro r c
    rw [show s + 1 + r = (s + r) + 1 by omega, run_succ_left]
    cases h : event M κ c <;> simp [trace, h, ih]

theorem event_of_step_none {M : TM} {κ : ℤ} {c : M.Cfg} (h : M.step c = none) :
    event M κ c = none := by
  have hn : M.next c = c := by simp [TM.next, h]
  unfold event
  have h1 : ¬ CrossRight M κ c := by unfold CrossRight; rw [hn]; omega
  have h2 : ¬ CrossLeft M κ c := by unfold CrossLeft; rw [hn]; omega
  rw [if_neg h1, if_neg h2]

theorem trace_of_step_none {M : TM} {κ : ℤ} {c : M.Cfg} (h : M.step c = none) :
    ∀ t, trace M κ c t = [] := by
  have hn : M.next c = c := by simp [TM.next, h]
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [trace, event_of_step_none h, hn, ih]

/-- For a machine that halts when it answers, the record over any window `t ≥ ftime` is the
decision trace. -/
theorem inputTrace_eq_dtrace {M : TM} (hhalt : ∀ c : M.Cfg, M.ans c ≠ none → M.step c = none)
    {κ : ℤ} {x : List Bool} {t : ℕ} (hans : M.out x (ftime M x) ≠ none) (ht : ftime M x ≤ t) :
    inputTrace M κ x t = dtrace M κ x := by
  unfold inputTrace dtrace
  obtain ⟨r, rfl⟩ : ∃ r, t = ftime M x + r := ⟨t - ftime M x, by omega⟩
  rw [trace_add, trace_of_step_none (hhalt _ hans), List.append_nil]

theorem eq_of_padded_eq {X : Type*} {l₁ l₂ : List X} {t : ℕ} (h₁ : l₁.length ≤ t)
    (h₂ : l₂.length ≤ t) (h : (fun i : Fin t => l₁[i.val]?) = fun i : Fin t => l₂[i.val]?) :
    l₁ = l₂ := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < t
  · exact congrFun h ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem dtrace_length_le (M : TM) (κ : ℤ) (x : List Bool) :
    (dtrace M κ x).length ≤ ftime M x := trace_length_le M κ _ _

/-- **The mixed-acceptance premise `hmixed` of `CrossingDiagonal` holds** for every
`SAT_dense` decider that halts when it answers, with the encoding `encSplit n g`, any cut in
the padding and any window `t ≥ T(3n(2n + g))`. -/
theorem hmixed_of_halting {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T)
    (hhalt : ∀ c : M.Cfg, M.ans c ≠ none → M.step c = none) {n g j t : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ 3 * n * g) (ht : T (3 * n * (2 * n + g)) ≤ t) :
    ∀ a b : Bits n,
      record M (cutAt n j) (encSplit n g a (fun i => !a i)) t =
        record M (cutAt n j) (encSplit n g b (fun i => !b i)) t →
      (∃ z : Bits n, splitThreeSat a (fun i => !b i) z) ∧
      (∃ z : Bits n, splitThreeSat b (fun i => !a i) z) := by
  intro a b hrec
  have hx := decides_true hM (encSplit_diag_mem n g hn a)
  have hy := decides_true hM (encSplit_diag_mem n g hn b)
  rw [length_encSplit] at hx hy
  have ex := inputTrace_eq_dtrace (κ := cutAt n j) hhalt
    (by rw [hx.2.1]; exact Option.some_ne_none _) (hx.1.trans ht)
  have ey := inputTrace_eq_dtrace (κ := cutAt n j) hhalt
    (by rw [hy.2.1]; exact Option.some_ne_none _) (hy.1.trans ht)
  have htr : dtrace M (cutAt n j) (encSplit n g a (fun i => !a i)) =
      dtrace M (cutAt n j) (encSplit n g b (fun i => !b i)) := by
    unfold record at hrec
    rw [ex, ey] at hrec
    exact eq_of_padded_eq ((dtrace_length_le _ _ _).trans (hx.1.trans ht))
      ((dtrace_length_le _ _ _).trans (hy.1.trans ht)) hrec
  exact ⟨diag_mixed hM hn hj a b htr, diag_mixed hM hn hj b a htr.symm⟩

/-- `CrossingDiagonal.diagonal_trace_capacity`, now **unconditional** for halting deciders. -/
theorem diagonal_capacity_halting {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T)
    (hhalt : ∀ c : M.Cfg, M.ans c ≠ none → M.step c = none) {n g j t : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ 3 * n * g) (ht : T (3 * n * (2 * n + g)) ≤ t) :
    2 ^ n ≤ (Fintype.card (M.Λ × Dir) + 1) ^ t :=
  PVNP.CrossingDiagonal.diagonal_trace_capacity M (cutAt n j) (encSplit n g)
    (hmixed_of_halting hM hhalt hn hj ht)

/-- The same capacity bound for **every** `SAT_dense` decider, using decision traces. -/
theorem diagonal_capacity {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ 3 * n * g) :
    2 ^ n ≤ (Fintype.card (M.Λ × Dir) + 1) ^ T (3 * n * (2 * n + g)) := by
  set t := T (3 * n * (2 * n + g))
  have hlen : ∀ a : Bits n, (dtrace M (cutAt n j) (encSplit n g a (fun i => !a i))).length ≤ t :=
    fun a => by
      have hx := decides_true hM (encSplit_diag_mem n g hn a)
      rw [length_encSplit] at hx
      exact (dtrace_length_le _ _ _).trans hx.1
  have hinj : Function.Injective fun a : Bits n =>
      (fun i : Fin t => (dtrace M (cutAt n j) (encSplit n g a (fun i => !a i)))[i.val]?) := by
    intro a a' h
    exact dtrace_injective hM hn hj (eq_of_padded_eq (hlen a) (hlen a') h)
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa [Bits, Fintype.card_fun, Fintype.card_option] using hcard

/-! ### Many cuts: crossing events at distinct cuts use distinct steps -/

theorem event_ne_none_iff {M : TM} {κ : ℤ} {c : M.Cfg} :
    event M κ c ≠ none ↔ CrossRight M κ c ∨ CrossLeft M κ c := by
  unfold event
  by_cases hr : CrossRight M κ c
  · simp [hr]
  · by_cases hl : CrossLeft M κ c <;> simp [hr, hl]

theorem event_cut_unique {M : TM} {c : M.Cfg} {κ κ' : ℤ} (h : event M κ c ≠ none)
    (h' : event M κ' c ≠ none) : κ = κ' := by
  rw [event_ne_none_iff] at h h'
  rcases h with h | h <;> rcases h' with h' | h'
  · have := right_crossing_adjacent M κ c h
    have := right_crossing_adjacent M κ' c h'
    omega
  · have := right_crossing_adjacent M κ c h
    have := left_crossing_adjacent M κ' c h'
    omega
  · have := left_crossing_adjacent M κ c h
    have := right_crossing_adjacent M κ' c h'
    omega
  · have := left_crossing_adjacent M κ c h
    have := left_crossing_adjacent M κ' c h'
    omega

/-- **Total crossing count**: during `t` steps, the crossing events at all cuts of a finite set
together number at most `t`. -/
theorem sum_trace_length_le (M : TM) (S : Finset ℤ) :
    ∀ (t : ℕ) (c : M.Cfg), ∑ κ ∈ S, (trace M κ c t).length ≤ t := by
  intro t
  induction t with
  | zero => intro c; simp [trace]
  | succ t ih =>
    intro c
    simp_rw [trace_succ_length]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ κ ∈ S, (if event M κ c = none then 0 else 1) ≤ 1 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
      exact Finset.card_le_one.2 fun κ hκ κ' hκ' =>
        event_cut_unique (Finset.mem_filter.1 hκ).2 (Finset.mem_filter.1 hκ').2
    have h2 := ih (M.next c)
    omega

/-! ### The multi-cut time lower bound -/

theorem cutAt_injective (n : ℕ) : Function.Injective (cutAt n) := by
  intro j j' h
  unfold cutAt at h
  omega

/-- **Single-tape time lower bound for `SAT_dense`.**  For every `n ≥ 1`, padding `g` and `ℓ`
with `2 (|Λ × Dir| + 1)^ℓ ≤ 2ⁿ`, every machine deciding `SAT_dense` within `T` satisfies
`(3ng + 1) ℓ ≤ 2 T(3n(2n + g))`. -/
theorem sat_time_lower_bound {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n g ℓ : ℕ}
    (hn : 1 ≤ n) (hℓ : 2 * (Fintype.card (M.Λ × Dir) + 1) ^ ℓ ≤ 2 ^ n) :
    (3 * n * g + 1) * ℓ ≤ 2 * T (3 * n * (2 * n + g)) := by
  set C := Fintype.card (M.Λ × Dir)
  set N := 3 * n * (2 * n + g)
  set G := 3 * n * g + 1
  set x : Bits n → List Bool := fun a => encSplit n g a (fun i => !a i)
  set f : Bits n → ℕ → ℕ := fun a j => (dtrace M (cutAt n j) (x a)).length
  -- (i) per input: the crossing events at the `G` cuts fit into the first answer time
  have hrow : ∀ a, ∑ j ∈ Finset.range G, f a j ≤ T N := by
    intro a
    have hx := decides_true hM (encSplit_diag_mem n g hn a)
    rw [length_encSplit] at hx
    have hs := sum_trace_length_le M ((Finset.range G).image (cutAt n)) (ftime M (x a))
      (M.init (x a))
    rw [Finset.sum_image (fun j _ j' _ h => cutAt_injective n h)] at hs
    exact hs.trans hx.1
  -- (ii) per cut: few inputs have short traces
  have hcol : ∀ j ∈ Finset.range G, ℓ * 2 ^ n ≤ ℓ * (C + 1) ^ ℓ + ∑ a, f a j := by
    intro j hj
    have hj' : j ≤ 3 * n * g := by simp [G] at hj; omega
    have hinj := dtrace_injective hM hn hj'
    set short := (Finset.univ : Finset (Bits n)).filter fun a => f a j < ℓ
    have hshort : short.card ≤ (C + 1) ^ ℓ := by
      have hmap : Set.InjOn (fun a : Bits n =>
          (fun i : Fin ℓ => (dtrace M (cutAt n j) (x a))[i.val]?)) short := by
        intro a ha a' ha' h
        have ha1 := (Finset.mem_filter.1 ha).2
        have ha2 := (Finset.mem_filter.1 ha').2
        exact hinj (eq_of_padded_eq ha1.le ha2.le h)
      have := Finset.card_le_card_of_injOn _ (fun a _ => Finset.mem_univ _) hmap
      simpa [Fintype.card_fun, Fintype.card_option, C] using this
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Bits n))) (fun a => f a j < ℓ)
    have huniv : (Finset.univ : Finset (Bits n)).card = 2 ^ n := by
      simp [Bits]
    have hlong : ℓ * ((Finset.univ : Finset (Bits n)).filter fun a => ¬ f a j < ℓ).card ≤
        ∑ a, f a j := by
      calc ℓ * ((Finset.univ : Finset (Bits n)).filter fun a => ¬ f a j < ℓ).card
          = ∑ a ∈ (Finset.univ : Finset (Bits n)).filter (fun a => ¬ f a j < ℓ), ℓ := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ a ∈ (Finset.univ : Finset (Bits n)).filter (fun a => ¬ f a j < ℓ), f a j :=
            Finset.sum_le_sum fun a ha => by
              have := (Finset.mem_filter.1 ha).2; omega
        _ ≤ ∑ a, f a j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
    rw [huniv] at hsplit
    calc ℓ * 2 ^ n = ℓ * short.card +
          ℓ * ((Finset.univ : Finset (Bits n)).filter fun a => ¬ f a j < ℓ).card := by
          rw [← mul_add, hsplit]
      _ ≤ ℓ * (C + 1) ^ ℓ + ∑ a, f a j := add_le_add (Nat.mul_le_mul_left _ hshort) hlong
  -- (iii) double counting
  have htot : G * (ℓ * 2 ^ n) ≤ G * (ℓ * (C + 1) ^ ℓ) + 2 ^ n * T N := by
    have h1 := Finset.sum_le_sum hcol
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_comm] at h1
    have h2 : ∑ a : Bits n, ∑ j ∈ Finset.range G, f a j ≤ ∑ _a : Bits n, T N :=
      Finset.sum_le_sum fun a _ => hrow a
    have h3 : ∑ _a : Bits n, T N = 2 ^ n * T N := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      simp [Bits]
    omega
  have hpos : 0 < 2 ^ n := by positivity
  have key : G * ℓ * 2 ^ n ≤ 2 * T N * 2 ^ n := by
    have := Nat.mul_le_mul_left (G * ℓ) hℓ
    nlinarith
  exact Nat.le_of_mul_le_mul_right key hpos

/-- **The `N^{3/2}` form** (`g = n`, `N = 9n²`): with `Λ'` the record alphabet `Λ × Dir` and
`L = ⌊log₂(|Λ'| + 1)⌋ + 1`, `(3n² + 1) ⌊(n - 1)/L⌋ ≤ 2 T(9n²)`. -/
theorem sat_time_lower_bound_sq {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n : ℕ}
    (hn : 1 ≤ n) :
    (3 * n * n + 1) * ((n - 1) / (Nat.log 2 (Fintype.card (M.Λ × Dir) + 1) + 1)) ≤
      2 * T (9 * n * n) := by
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
      _ = 2 ^ n := by
          rw [← pow_succ']; congr 1; omega
  have h := sat_time_lower_bound hM (g := n) hn hℓ
  have e : 3 * n * (2 * n + n) = 9 * n * n := by ring
  rw [e] at h
  have e2 : 3 * n * n + 1 = 3 * n * n + 1 := rfl
  linarith [h]

/-- **No single-tape machine decides `SAT_dense` in linear time.** -/
theorem sat_not_linear_time {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) (C : ℕ) :
    ∃ N, C * N < T N := by
  set L := Nat.log 2 (Fintype.card (M.Λ × Dir) + 1) + 1
  set n := L * (6 * C + 6) + 1
  have hn : 1 ≤ n := by omega
  have hL : 0 < L := by omega
  have hdiv : (n - 1) / L = 6 * C + 6 := by
    rw [show n - 1 = L * (6 * C + 6) by omega, Nat.mul_div_cancel_left _ hL]
  have h := sat_time_lower_bound_sq hM hn
  rw [hdiv] at h
  refine ⟨9 * n * n, ?_⟩
  nlinarith

end PVNP.CrossingSAT
