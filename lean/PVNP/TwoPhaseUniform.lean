import PVNP.TwoPhaseDecoder
import PVNP.PartIIUniformEquiv

/-!
# Original two-phase W_M: exact embedding into the uniform WCC interface

The author's Part II construction uses the alphabet `S M`, the original two-phase
rule `U M`, and the interval `[-L, L]`. This module connects those definitions
to `PartIIUniform.UWCC` without replacing them with the alternative one-cell
machine.

The exact missing obligations are `FP` proofs for the *original* encoder and
window writer. They are explicit arguments here and must not be presented as
unconditional conclusions. The original decoder is supplied by
`TwoPhaseDecoder.decM_fp`, which was already verified in PR #56.
-/

namespace PVNP.TwoPhaseUniform

open PartIITuring PartIITwoPhase PartIIUniform TwoPhaseDecoder

/-- Canonical window code for the original interval, using a polynomial
radius clock. The extra cell of margin is needed by the radius-one rule. -/
def originalWindowCode (p : Polynomial ℕ) (x : List Bool) : List Bool :=
  latCode 1 (p.eval x.length + 1) (window (p.eval x.length))

/-- Canonical initial configuration code of the actual two-phase machine.
The state encoding is injective and fixed-width, not a decision-bit encoder. -/
noncomputable def originalInputCode (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) : List Bool :=
  cfgCode (stateBits M) 1 (p.eval x.length + 1)
    (window (p.eval x.length))
    (fun i => encM M (p.eval x.length) x (i 0))

/-- The *original* `W_M` gives an instance of the uniform interface as
soon as actual polynomial-time transducers for its window and encoder have
been built. These hypotheses are precisely the remaining II-10 obligations.
The decoder uniformity is established unconditionally by PR #56. -/
noncomputable def originalUniform (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p))
    (hEncoder : FP (originalInputCode M p)) : UWCC where
  d := 1
  d_pos := by omega
  r := 1
  S := PartIITwoPhase.S M
  sbd := PartIITwoPhase.sbd M
  U := fun nbr => PartIITwoPhase.U M
    (nbr (fun _ => 0)) (nbr (fun _ => 1)) (nbr (fun _ => 2))
  w := 3 + 2 * Fintype.card (PartIITwoPhase.S M)
  bits := stateBits M
  bits_len := stateBits_length M
  bits_inj := stateBits_injective M
  R := fun n => p.eval n + 1
  Λ := fun n => window (p.eval n)
  decΛ := fun _ => inferInstance
  margin := by
    intro n i hi k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    change |i 0| + (1 : ℤ) ≤ ((p.eval n + 1 : ℕ) : ℤ)
    have hb : |i 0| ≤ (p.eval n : ℤ) := abs_le.mpr hi
    omega
  enc := fun x i => encM M (p.eval x.length) x (i 0)
  dec := fun n C => decM M (p.eval n) (fun i => C (fun _ => i))
  lat_fp := hWindow
  enc_fp := hEncoder
  dec_fp := by
    simpa using decM_fp M p

/-- The author's window is *exactly* the uniform machine's window,
not a replacement cellular automaton. -/
theorem original_window (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (n : ℕ) (i : Fin 1 → ℤ) :
    i ∈ (originalUniform M p hWindow hEncoder).Λ n ↔
      InWin (p.eval n) (i 0) := by
  rfl

/-- The uniform machine has precisely the original decoder, including
accept-before-reject priority on arbitrary configurations. -/
theorem original_decoder (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (n : ℕ) (C : ℤ → PartIITwoPhase.S M) :
    (originalUniform M p hWindow hEncoder).dec n (fun i => C (i 0)) =
      decM M (p.eval n) C := by
  rfl

/-- The original lattice, when restricted to the active window, initializes
to the exact manuscript encoding. -/
theorem original_initial (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (x : List Bool) (i : ℤ) :
    (originalUniform M p hWindow hEncoder).init x (fun _ => i) =
      encM M (p.eval x.length) x i := by
  change (if InWin (p.eval x.length) i then
    encM M (p.eval x.length) x i else PartIITwoPhase.sbd M) =
      encM M (p.eval x.length) x i
  by_cases hi : InWin (p.eval x.length) i
  · simp [hi]
  · simp [hi, encM]

/-- One update of the actual `UWCC` model agrees with the author's
radius-one rule at every lattice site, not only on reachable configurations. -/
theorem original_step (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (n : ℕ) (C : ℤ → PartIITwoPhase.S M) (i : ℤ) :
    (originalUniform M p hWindow hEncoder).step n (fun j => C (j 0))
        (fun _ => i) = stepW M (p.eval n) C i := by
  classical
  simp [UWCC.step, originalUniform, UWCC.offset,
    PartIITwoPhase.stepW, window, Pi.add_apply]

/-- Repeated synchronous `UWCC` updates of the original construction agree
with the author's `runW` on the complete one-dimensional lattice. This is
conditional only on the explicit encoder/window FP witnesses used to build
the uniform machine. -/
theorem original_cfg (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (x : List Bool) (t : ℕ) :
    (originalUniform M p hWindow hEncoder).cfg x t =
      (fun i => runW M (p.eval x.length)
        (encM M (p.eval x.length) x) t (i 0)) := by
  let W : UWCC := originalUniform M p hWindow hEncoder
  change W.cfg x t = _
  induction t with
  | zero =>
      funext i
      have hi : i = (fun _ => i 0) := by
        funext j
        fin_cases j
        rfl
      rw [hi]
      change W.init x (fun _ => i 0) = encM M (p.eval x.length) x (i 0)
      exact original_initial M p hWindow hEncoder x (i 0)
  | succ t ih =>
      have hs : W.cfg x (t + 1) = W.step x.length (W.cfg x t) := by
        unfold UWCC.cfg
        rw [Function.iterate_succ_apply']
      rw [hs, ih]
      funext i
      have hi : i = (fun _ => i 0) := by
        funext j
        fin_cases j
        rfl
      rw [hi]
      change (originalUniform M p hWindow hEncoder).step x.length
        (fun j => runW M (p.eval x.length) (encM M (p.eval x.length) x) t (j 0))
          (fun _ => i 0) =
        runW M (p.eval x.length) (encM M (p.eval x.length) x) (t + 1) (i 0)
      rw [original_step M p hWindow hEncoder]
      rw [runW_succ]

/-- The uniform machine's output stream is precisely the manuscript's
original `outW`, not merely equal on special reachable accepting states. -/
theorem original_output (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    (x : List Bool) (t : ℕ) :
    (originalUniform M p hWindow hEncoder).dec x.length
      ((originalUniform M p hWindow hEncoder).cfg x t) =
        outW M (p.eval x.length) x t := by
  rw [original_cfg M p hWindow hEncoder x t]
  exact original_decoder M p hWindow hEncoder x.length
    (runW M (p.eval x.length) (encM M (p.eval x.length) x) t)

/-- Given the original encoder and window FP witnesses, the *actual* W_M
constructed above decides exactly the source Turing language, with intrinsic
first-answer latency at most two WCC rounds per TM step. The two writer FP
hypotheses are not discharged by this theorem. -/
theorem original_uniform_decides (M : MTM) (p : Polynomial ℕ)
    (hWindow : FP (originalWindowCode p)) (hEncoder : FP (originalInputCode M p))
    {Lang : Set (List Bool)} {c k : ℕ}
    (hTime : ∀ x, M.HaltsWithin x (c * max x.length 1 ^ k))
    (hCorrect : ∀ x, M.Accepts x ↔ x ∈ Lang)
    (hRadius : ∀ n, c * max n 1 ^ k ≤ p.eval n)
    (x : List Bool) :
    PVNP.Discrete.DecidesAt
      (fun t => (originalUniform M p hWindow hEncoder).dec x.length
        ((originalUniform M p hWindow hEncoder).cfg x t))
      (2 * (c * max x.length 1 ^ k)) x Lang := by
  obtain ⟨T, hT, hf⟩ := hTime x
  obtain ⟨hout, hbefore⟩ :=
    runtime M (p.eval x.length) hf (hT.trans (hRadius x.length))
  refine ⟨_, ⟨2 * T, by omega, ?_, ?_⟩, ?_⟩
  · rw [original_output]
    exact hout
  · intro s hs
    rw [original_output]
    exact hbefore s hs
  · rw [decide_eq_true_iff, ← hCorrect x, M.accepts_iff_of_firstHalt hf]

/-- The exact width of the state code used by the original construction. -/
theorem original_state_bits_length (M : MTM) (s : PartIITwoPhase.S M) :
    (stateBits M s).length = 3 + 2 * Fintype.card (PartIITwoPhase.S M) :=
  stateBits_length M s

/-- The original state code is injective. -/
theorem original_state_bits_injective (M : MTM) :
    Function.Injective (stateBits M) :=
  stateBits_injective M

/-- The word representing the original lattice window contains a unary
radius prefix, a separator, and one membership bit per bounding-box cell. -/
theorem originalWindowCode_length (p : Polynomial ℕ) (x : List Bool) :
    (originalWindowCode p x).length =
      (p.eval x.length + 1) + 1 + (2 * (p.eval x.length + 1) + 1) := by
  simp [originalWindowCode, latCode, boxIdx, side]

/-- The original input code is the canonical code of the manuscript's
initial Turing configuration, not an independently chosen encoder. -/
theorem originalInputCode_eq_encCfg (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) :
    originalInputCode M p x =
      cfgCode (stateBits M) 1 (p.eval x.length + 1)
        (window (p.eval x.length))
        (fun i => encCfg M (p.eval x.length) (M.init x) (i 0)) := by
  simp only [originalInputCode, encM_eq]

/-- Fixed-width encoded state lists scale linearly in their number of
cells; this statement is independent of the chosen finite machine. -/
theorem stateBits_flatMap_length (M : MTM)
    (l : List (PartIITwoPhase.S M)) :
    (l.flatMap (stateBits M)).length =
      l.length * (3 + 2 * Fintype.card (PartIITwoPhase.S M)) := by
  induction l with
  | nil => simp
  | cons s l ih =>
      simp [ih, stateBits_length, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]

/-- The output length of the original canonical encoder is bounded by
the box size times the fixed state-code width. This is a *length* theorem,
not an FP witness for the encoder's TM transition count. -/
theorem originalInputCode_length_le (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) :
    (originalInputCode M p x).length ≤
      (2 * (p.eval x.length + 1) + 1) *
        (3 + 2 * Fintype.card (PartIITwoPhase.S M)) := by
  let R := p.eval x.length + 1
  let ids := ((boxIdx 1 R).filter
    (fun idx => decide (site 1 R idx ∈ window (p.eval x.length))))
  let cells : List (PartIITwoPhase.S M) :=
    ids.map (fun idx => encM M (p.eval x.length) x (site 1 R idx 0))
  have hlen : (originalInputCode M p x).length =
      cells.length * (3 + 2 * Fintype.card (PartIITwoPhase.S M)) := by
    simpa [originalInputCode, cfgCode, cells, ids, R, List.flatMap_map] using
      stateBits_flatMap_length M cells
  have hids : ids.length ≤ 2 * R + 1 := by
    have h := List.length_filter_le
      (fun idx => decide (site 1 R idx ∈ window (p.eval x.length))) (boxIdx 1 R)
    simpa [ids, boxIdx, side] using h
  have hcells : cells.length ≤ 2 * R + 1 := by
    simpa [cells] using hids
  rw [hlen]
  exact Nat.mul_le_mul_right _ hcells

/-- A polynomial certificate for the exact number of bits in the original
lattice's unary-prefix-plus-bitmap description. -/
noncomputable def originalWindowLengthPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  3 * p + 5

theorem originalWindowCode_polynomial_length (p : Polynomial ℕ) (x : List Bool) :
    (originalWindowCode p x).length =
      (originalWindowLengthPoly p).eval x.length := by
  rw [originalWindowCode_length]
  simp [originalWindowLengthPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

/-- A polynomial certificate for the total *output length* of the author's
canonical encoder. This does not discharge the `MTM.ComputesIn` runtime
obligation; that requires a concrete finite-control writer. -/
noncomputable def originalEncoderLengthPoly (M : MTM) (p : Polynomial ℕ) :
    Polynomial ℕ :=
  (2 * p + 3) * Polynomial.C (3 + 2 * Fintype.card (PartIITwoPhase.S M))

theorem originalInputCode_polynomial_length (M : MTM) (p : Polynomial ℕ)
    (x : List Bool) :
    (originalInputCode M p x).length ≤
      (originalEncoderLengthPoly M p).eval x.length := by
  calc
    (originalInputCode M p x).length
      ≤ (2 * (p.eval x.length + 1) + 1) *
          (3 + 2 * Fintype.card (PartIITwoPhase.S M)) :=
            originalInputCode_length_le M p x
    _ = (originalEncoderLengthPoly M p).eval x.length := by
      simp [originalEncoderLengthPoly, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_ofNat]
      omega

end PVNP.TwoPhaseUniform
