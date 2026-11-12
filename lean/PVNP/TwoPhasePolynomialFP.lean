import PVNP.TwoPhasePolynomialOutputs

/-!
# II-10: the original polynomial-radius writers are polynomial-time transducers

For every polynomial `p` and every machine `M` of `def:tm`:

* `windowMTM_outputs`: the actual machine `windowMTM p` writes exactly
  `TwoPhaseUniform.originalWindowCode p x`;
* `inputMTM_outputs`: the actual machine `inputMTM M p` writes exactly
  `TwoPhaseUniform.originalInputCode M p x`;

both under the `MTM.Outputs` convention (first halt, output word followed by a blank), within the
polynomial transition bounds `windowTime` and `inputTime`. Hence

* `originalWindowCode_fp : FP (originalWindowCode p)`,
* `originalInputCode_fp : FP (originalInputCode M p)`,

and the author's two-phase machine `W_M` is a uniform WCC machine with no remaining hypothesis
(`originalWM`). `originalWM_decides` is `thm:tm_to_wcc` for that machine: it decides the language
of `M` within `2·c·max(n,1)^k` updates.
-/

namespace PVNP.TwoPhasePolynomialWriter

open PartIITuring PartIIUniform PartIITwoPhase TwoPhaseDecoder Polynomial

/-! ## The Horner value and polynomial bounds -/

/-- The accumulator value computed by the stages is `p(n)`. -/
theorem hv_coeffs (p : Polynomial ℕ) (n : ℕ) : hv (coeffs p) n = p.eval n := by
  rw [← writer_clock_eq_polynomial p n]
  unfold hv CookLevin.Gen.horner
  rw [List.foldl_reverse]

/-- `hv cs` as a polynomial in the input length. -/
noncomputable def hvP : List ℕ → Polynomial ℕ
  | [] => 0
  | c :: rest => hvP rest * X + C c

theorem hvP_eval (cs : List ℕ) (n : ℕ) : (hvP cs).eval n = hv cs n := by
  induction cs with
  | nil => simp [hvP, hv]
  | cons c rest ih => simp [hvP, hv_cons, ih]

/-- `ic cs` as a polynomial. -/
noncomputable def icP : List ℕ → Polynomial ℕ
  | [] => 0
  | c :: rest => icP rest + (hvP rest * (2 * X + 3) + C c + 4)

theorem icP_eval (cs : List ℕ) (n : ℕ) : (icP cs).eval n = ic cs n := by
  induction cs with
  | nil => simp [icP, ic]
  | cons c rest ih => simp [icP, ic, ih, hvP_eval]

/-- A polynomial bound for `hb cs`. -/
noncomputable def hbP : List ℕ → Polynomial ℕ
  | [] => 0
  | c :: rest => hbP rest + (hvP rest * X + C c)

theorem hb_le (cs : List ℕ) (n : ℕ) : hb cs n ≤ (hbP cs).eval n := by
  induction cs with
  | nil => simp [hb, hbP]
  | cons c rest ih =>
    simp only [hb, hbP, eval_add, eval_mul, eval_X, eval_C, hvP_eval]
    omega

theorem outputs_mono {M : MTM} {z y : List Bool} {B B' : ℕ} (h : M.Outputs z y B)
    (hB : B ≤ B') : M.Outputs z y B' := by
  obtain ⟨t, ht, h1, h2⟩ := h
  exact ⟨t, le_trans ht hB, h1, h2⟩

/-! ## The lattice-window writer -/

/-- Polynomial transition bound of the window writer. -/
noncomputable def windowTime (cs : List ℕ) : Polynomial ℕ :=
  2 * X + 4 + (icP cs + (5 * hvP cs + 9)) * (2 * (X + hbP cs + (3 * hvP cs + 5)) + 4) +
    (3 * hvP cs + 5 + 1)

theorem winTail_length (R : ℕ) : (winTail R).length = 3 * R + 5 := by
  simp only [winTail, List.length_append, length_flatten_replicate, List.length_cons,
    List.length_nil]
  omega

theorem window_outputs (cs : List ℕ) (x : List Bool) :
    (build (assemble cs windowBody)).Outputs x (winTail (hv cs x.length))
      ((windowTime cs).eval x.length) := by
  refine outputs_mono (assemble_outputs cs windowBody_emits x) ?_
  show 2 * x.length + 4 + (ic cs x.length + (5 * hv cs x.length + 9)) *
      (2 * (x.length + hb cs x.length + (winTail (hv cs x.length)).length) + 4) +
      ((winTail (hv cs x.length)).length + 1) ≤ _
  rw [winTail_length]
  simp only [windowTime, eval_add, eval_mul, eval_X, eval_ofNat, eval_one, icP_eval, hvP_eval]
  have := hb_le cs x.length
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) _

theorem flatten_ones (R : ℕ) : (List.replicate R [true]).flatten = List.replicate R true := by
  induction R with
  | zero => rfl
  | succ R ih => rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_succ]; rfl

theorem flatten_twos (R : ℕ) :
    (List.replicate R [true, true]).flatten = List.replicate (2 * R) true := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (R + 1) = 2 * R + 1 + 1 by ring,
      List.replicate_succ, List.replicate_succ]
    rfl

theorem bitmap_eq (m : ℕ) :
    (List.range (m + 2)).map (fun j => decide (0 < j ∧ j < m + 1)) =
      false :: (List.replicate m true ++ [false]) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    rcases i with _ | k
    · simp
    · rw [List.getElem_cons_succ]
      have hk : k < m + 1 := by simp at h1; omega
      by_cases hkm : k < m
      · rw [List.getElem_append_left (by simpa using hkm), List.getElem_replicate]
        simp
        omega
      · have hkeq : k = m := by omega
        subst hkeq
        rw [List.getElem_append_right (by simp)]
        simp

theorem bitmap_window (L : ℕ) :
    (List.range (2 * (L + 1) + 1)).map (fun j => decide (0 < j ∧ j < 2 * (L + 1))) =
      false :: (List.replicate (2 * L + 1) true ++ [false]) := by
  have h := bitmap_eq (2 * L + 1)
  have e1 : 2 * (L + 1) + 1 = 2 * L + 1 + 2 := by ring
  have e2 : 2 * (L + 1) = 2 * L + 1 + 1 := by ring
  rw [e1, e2]
  exact h

/-- The word written by the window body is the canonical lattice word. -/
theorem winTail_eq_windowWord (R : ℕ) : winTail R = TwoPhaseWindowWord.windowWord R := by
  unfold winTail TwoPhaseWindowWord.windowWord
  rw [flatten_ones, flatten_twos, bitmap_window, List.replicate_succ' (n := R),
    List.replicate_succ' (n := 2 * R)]
  simp

/-- **The actual window writer** outputs exactly the original lattice code, at its first halt,
within `windowTime`. -/
theorem windowMTM_outputs (p : Polynomial ℕ) (x : List Bool) :
    (windowMTM p).Outputs x (TwoPhaseUniform.originalWindowCode p x)
      ((windowTime (coeffs p)).eval x.length) := by
  have h := window_outputs (coeffs p) x
  rw [hv_coeffs, winTail_eq_windowWord,
    ← TwoPhaseWindowWord.originalWindowCode_eq_windowWord] at h
  exact h

/-- **`FP` for the original lattice-window writer**, for every polynomial radius. -/
theorem originalWindowCode_fp (p : Polynomial ℕ) :
    FP (TwoPhaseUniform.originalWindowCode p) :=
  ⟨windowMTM p, windowTime (coeffs p), windowMTM_outputs p⟩

/-! ## The initial-configuration writer -/

/-- The tape symbol of an optional input bit. -/
def symOf (M : MTM) : Option Bool → M.Γ
  | none => M.blank
  | some b => M.inp b

/-- The fixed-width code of a cell of the initial configuration. -/
noncomputable def blkOf (M : MTM) (v : Option Bool) (head : Bool) : List Bool :=
  stateBits M (symOf M v, if head then some (.inl M.q0) else none, false)

/-- The input body of the actual machine is the generic one with the Part II state codes. -/
theorem inputBody_eq (M : MTM) : inputBody M = inputBodyG (blkOf M) := rfl

theorem blkOf_length (M : MTM) (v : Option Bool) (h : Bool) :
    (blkOf M v h).length = 3 + 2 * Fintype.card (S M) := stateBits_length M _

theorem inW_length {blk : Option Bool → Bool → List Bool} {w : ℕ}
    (hblk : ∀ v h, (blk v h).length = w) (x : List Bool) (R : ℕ) :
    (inW blk x R).length = (2 * R + 1) * w := by
  simp only [inW, List.length_append, length_flatten_replicate, hblk,
    length_flatMap_range (fun i => hblk _ _)]
  ring

/-- Polynomial transition bound of the input writer. -/
noncomputable def inputTime (M : MTM) (cs : List ℕ) : Polynomial ℕ :=
  2 * X + 4 + (icP cs + (2 * hvP cs * C (3 + 2 * Fintype.card (S M) + 1) +
      C (3 + 2 * Fintype.card (S M)) + 5)) *
    (2 * (X + hbP cs + (2 * hvP cs + 1) * C (3 + 2 * Fintype.card (S M))) + 4) +
    ((2 * hvP cs + 1) * C (3 + 2 * Fintype.card (S M)) + 1)

theorem input_outputs (M : MTM) (cs : List ℕ) (x : List Bool) :
    (build (assemble cs (inputBody M))).Outputs x (inW (blkOf M) x (hv cs x.length))
      ((inputTime M cs).eval x.length) := by
  rw [inputBody_eq]
  refine outputs_mono (assemble_outputs cs
    (inputBodyG_emits (blkOf M) _ (blkOf_length M)) x) ?_
  show 2 * x.length + 4 + (ic cs x.length + (2 * hv cs x.length *
        (3 + 2 * Fintype.card (S M) + 1) + (3 + 2 * Fintype.card (S M)) + 5)) *
      (2 * (x.length + hb cs x.length + (inW (blkOf M) x (hv cs x.length)).length) + 4) +
      ((inW (blkOf M) x (hv cs x.length)).length + 1) ≤ _
  rw [inW_length (blkOf_length M)]
  simp only [inputTime, eval_add, eval_mul, eval_X, eval_C, eval_ofNat, eval_one, icP_eval,
    hvP_eval]
  have := hb_le cs x.length
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) _

/-! ### The configuration word is the original input code -/

theorem filter_interior (m : ℕ) :
    (List.range (m + 2)).filter (fun j => decide (0 < j ∧ j < m + 1)) =
      (List.range m).map (· + 1) := by
  have hcomp : ((fun j => decide (0 < j ∧ j < m + 1)) ∘ Nat.succ) = fun i => decide (i < m) := by
    funext i
    simp only [Function.comp, decide_eq_decide]
    constructor
    · intro h; omega
    · intro h; exact ⟨Nat.succ_pos _, by omega⟩
  rw [List.range_succ_eq_map, List.filter_cons, if_neg (by simp), List.filter_map, hcomp,
    List.range_succ, List.filter_append,
    List.filter_eq_self.2 (fun a ha => by simpa using ha)]
  simp

theorem flatMap_const_range (w : List Bool) (L : ℕ) :
    (List.range L).flatMap (fun _ => w) = (List.replicate L w).flatten := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatten_append]
    simp

/-- A word indexed by the window `[−L, L]`, split into its left part, centre and right part. -/
theorem flatMap_window (F : ℤ → List Bool) (L : ℕ) (w : List Bool)
    (hleft : ∀ i : ℕ, i < L → F ((i : ℤ) - L) = w) :
    (List.range (2 * L + 1)).flatMap (fun i : ℕ => F ((i : ℤ) - L)) =
      (List.replicate L w).flatten ++ F 0 ++
        (List.range L).flatMap (fun k : ℕ => F ((k : ℤ) + 1)) := by
  rw [show 2 * L + 1 = L + (L + 1) by ring, List.range_add, List.flatMap_append,
    List.flatMap_map, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    List.flatMap_congr (fun i hi => hleft i (List.mem_range.1 hi)), flatMap_const_range,
    List.append_assoc]
  congr 1
  congr 1
  · congr 1
    push_cast
    ring
  · apply List.flatMap_congr
    intro k _
    congr 1
    push_cast
    ring

theorem encM_blk_left (M : MTM) (L : ℕ) (x : List Bool) (i : ℕ) (hi : i < L) :
    stateBits M (encM M L x ((i : ℤ) - L)) = blkOf M none false := by
  have hw : InWin L ((i : ℤ) - L) := ⟨by omega, by omega⟩
  have h0 : ¬ ((i : ℤ) - L = 0) := by omega
  have h1 : ¬ (1 ≤ (i : ℤ) - L ∧ (i : ℤ) - L ≤ (x.length : ℤ) - 1) := by omega
  simp only [encM, if_pos hw, if_neg h0, if_neg h1]
  rfl

theorem encM_blk_center (M : MTM) (L : ℕ) (x : List Bool) :
    stateBits M (encM M L x 0) = blkOf M x[0]? true := by
  have hw : InWin L (0 : ℤ) := ⟨by omega, by omega⟩
  simp only [encM, if_pos hw, if_true]
  cases x with
  | nil => simp [MTM.inputTape, blkOf, symOf]
  | cons b x => simp [MTM.inputTape, blkOf, symOf]

theorem encM_blk_right (M : MTM) (L : ℕ) (x : List Bool) (k : ℕ) (hk : k < L) :
    stateBits M (encM M L x ((k : ℤ) + 1)) = blkOf M x[k + 1]? false := by
  have hw : InWin L ((k : ℤ) + 1) := ⟨by omega, by omega⟩
  have h0 : ¬ ((k : ℤ) + 1 = 0) := by omega
  have ht : ((k : ℤ) + 1).toNat = k + 1 := by omega
  simp only [encM, if_pos hw, if_neg h0, ht]
  by_cases hx : k + 1 < x.length
  · have h1 : 1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ (x.length : ℤ) - 1 := by omega
    rw [if_pos h1, List.getElem?_eq_getElem hx, List.getD_eq_getElem _ _ hx]
    rfl
  · have h1 : ¬ (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ (x.length : ℤ) - 1) := by omega
    rw [if_neg h1, List.getElem?_eq_none (by omega)]
    rfl

/-- The word written by the input body is the original canonical input code. -/
theorem inW_eq_originalInputCode (M : MTM) (p : Polynomial ℕ) (x : List Bool) :
    inW (blkOf M) x (p.eval x.length) = TwoPhaseUniform.originalInputCode M p x := by
  show inW (blkOf M) x (p.eval x.length) =
    cfgCode (stateBits M) 1 (p.eval x.length + 1) (window (p.eval x.length))
      (fun i => encM M (p.eval x.length) x (i 0))
  generalize p.eval x.length = L
  unfold cfgCode
  have hbox : boxIdx 1 (L + 1) = List.range (2 * L + 1 + 2) := by
    simp only [boxIdx, side, pow_one]
    congr 1
  have hfilter : (boxIdx 1 (L + 1)).filter (fun idx => decide (site 1 (L + 1) idx ∈ window L)) =
      (List.range (2 * L + 1)).map (· + 1) := by
    rw [hbox, ← filter_interior]
    apply List.filter_congr
    intro j hj
    have hj' : j < 2 * (L + 1) + 1 := by have := List.mem_range.1 hj; omega
    rw [TwoPhaseWindowShape.original_window_bit L j hj']
    simp only [decide_eq_decide]
    omega
  rw [hfilter, List.flatMap_map]
  have hsite : ∀ i ∈ List.range (2 * L + 1),
      stateBits M (encM M L x (site 1 (L + 1) (i + 1) 0)) =
        stateBits M (encM M L x ((i : ℤ) - L)) := by
    intro i hi
    have hi' : i + 1 < 2 * (L + 1) + 1 := by have := List.mem_range.1 hi; omega
    rw [TwoPhaseWindowShape.site_one_coordinate L (i + 1) hi']
    congr 2
    push_cast
    ring
  rw [List.flatMap_congr hsite,
    flatMap_window (fun j => stateBits M (encM M L x j)) L (blkOf M none false)
      (fun i hi => encM_blk_left M L x i hi),
    encM_blk_center, List.flatMap_congr (fun k hk => encM_blk_right M L x k (List.mem_range.1 hk))]
  rfl

/-- **The actual input writer** outputs exactly the original canonical input code, at its first
halt, within `inputTime`. -/
theorem inputMTM_outputs (M : MTM) (p : Polynomial ℕ) (x : List Bool) :
    (inputMTM M p).Outputs x (TwoPhaseUniform.originalInputCode M p x)
      ((inputTime M (coeffs p)).eval x.length) := by
  have h := input_outputs M (coeffs p) x
  rw [hv_coeffs, inW_eq_originalInputCode] at h
  exact h

/-- **`FP` for the original encoder**, for every machine and every polynomial radius. -/
theorem originalInputCode_fp (M : MTM) (p : Polynomial ℕ) :
    FP (TwoPhaseUniform.originalInputCode M p) :=
  ⟨inputMTM M p, inputTime M (coeffs p), inputMTM_outputs M p⟩

/-! ## The author's `W_M` is a uniform WCC machine -/

/-- **The original two-phase machine `W_M`** as a uniform discrete WCC machine in the sense of
`def:wcc_machine`, with its own alphabet, rule, window, encoder and decoder, and with all three
uniformity witnesses proved. -/
noncomputable def originalWM (M : MTM) (p : Polynomial ℕ) : UWCC :=
  TwoPhaseUniform.originalUniform M p (originalWindowCode_fp p) (originalInputCode_fp M p)

/-- **`thm:tm_to_wcc` for the author's machine.** If `M` halts within `c·max(n,1)^k` and decides
`Lang`, and the radius polynomial dominates that bound, then `W_M` gives its first decision
within `2·c·max(n,1)^k` updates, and that decision is the membership bit. -/
theorem originalWM_decides (M : MTM) (p : Polynomial ℕ) {Lang : Set (List Bool)} {c k : ℕ}
    (hTime : ∀ x, M.HaltsWithin x (c * max x.length 1 ^ k))
    (hCorrect : ∀ x, M.Accepts x ↔ x ∈ Lang) (hRadius : ∀ n, c * max n 1 ^ k ≤ p.eval n)
    (x : List Bool) :
    PVNP.Discrete.DecidesAt
      (fun t => (originalWM M p).dec x.length ((originalWM M p).cfg x t))
      (2 * (c * max x.length 1 ^ k)) x Lang :=
  TwoPhaseUniform.original_uniform_decides M p _ _ hTime hCorrect hRadius x

/-- A radius polynomial dominating `c·max(n,1)^k`. -/
noncomputable def radiusPoly (c k : ℕ) : Polynomial ℕ := C c * (X + 1) ^ k

theorem radiusPoly_ge (c k n : ℕ) : c * max n 1 ^ k ≤ (radiusPoly c k).eval n := by
  simp only [radiusPoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **`P_Turing ⊆ P^disc` through the author's own construction.** Every language of the
corrected `def:pturing` is decided, in the uniform model, by the original two-phase machine of
one of its deciders. -/
theorem P_Turing_subset_P_disc_original {Lang : Set (List Bool)} (h : Lang ∈ P_Turing) :
    ∃ (M : MTM) (c k : ℕ), (∀ x, M.Accepts x ↔ x ∈ Lang) ∧
      ∀ x, ∃ t ≤ 2 * (c * max x.length 1 ^ k),
        (∀ s < t, (originalWM M (radiusPoly c k)).dec x.length
          ((originalWM M (radiusPoly c k)).cfg x s) = none) ∧
        ∃ b, (originalWM M (radiusPoly c k)).dec x.length
          ((originalWM M (radiusPoly c k)).cfg x t) = some b ∧ (b = true ↔ x ∈ Lang) := by
  obtain ⟨M, c, k, -, -, hTime, hCorrect⟩ := h
  refine ⟨M, c, k, hCorrect, fun x => ?_⟩
  obtain ⟨b, ⟨t, ht, hb, hnone⟩, hbL⟩ :=
    originalWM_decides M (radiusPoly c k) hTime hCorrect (radiusPoly_ge c k) x
  exact ⟨t, ht, hnone, b, hb, hbL⟩

/-- **The original machine is a `P^disc` witness.** With the radius polynomial `radiusPoly c k`
the first decision of `W_M` appears within the polynomial `2·radiusPoly c k`, so `W_M` itself (and
not a substitute machine) places the language of `M` in `P^disc` of `def:pwcc`. -/
theorem originalWM_mem_P_disc (M : MTM) {Lang : Set (List Bool)} {c k : ℕ}
    (hTime : ∀ x, M.HaltsWithin x (c * max x.length 1 ^ k))
    (hCorrect : ∀ x, M.Accepts x ↔ x ∈ Lang) :
    ∀ x, ∃ t ≤ (C 2 * radiusPoly c k).eval x.length,
      (∀ s < t, (originalWM M (radiusPoly c k)).dec x.length
        ((originalWM M (radiusPoly c k)).cfg x s) = none) ∧
      ∃ b, (originalWM M (radiusPoly c k)).dec x.length
        ((originalWM M (radiusPoly c k)).cfg x t) = some b ∧ (b = true ↔ x ∈ Lang) := by
  intro x
  obtain ⟨b, ⟨t, ht, hb, hnone⟩, hbL⟩ :=
    originalWM_decides M (radiusPoly c k) hTime hCorrect (radiusPoly_ge c k) x
  refine ⟨t, le_trans ht ?_, hnone, b, hb, hbL⟩
  rw [eval_mul, eval_C]
  exact Nat.mul_le_mul_left _ (radiusPoly_ge c k x.length)

/-- `P_Turing ⊆ P^disc`, with the author's two-phase machine as the witness. -/
theorem P_Turing_subset_P_disc_by_original : P_Turing ⊆ P_disc := by
  intro Lang h
  obtain ⟨M, c, k, -, -, hTime, hCorrect⟩ := h
  exact ⟨originalWM M (radiusPoly c k), C 2 * radiusPoly c k,
    originalWM_mem_P_disc M hTime hCorrect⟩

end PVNP.TwoPhasePolynomialWriter
