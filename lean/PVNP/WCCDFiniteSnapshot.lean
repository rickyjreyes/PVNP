import PVNP.WCCDFiniteSupport

/-!
# D-1: a computable finite-snapshot interpreter for multidimensional WCC

This module establishes the finite coordinate representation, exact
synchronous update, and exact existential output, including accepting or
rejecting quiescent cells outside the represented rectangle.

It does **not** prove a polynomial-step single-tape TM implementation.
The remaining D-1 bridge is the finite-program-to-TM compiler and the
explicit polynomial cost bound.
-/

namespace PVNP.Discrete.WCCD

/-- Rectangular addresses used after `t` rounds.  Unlike subtypes of an
infinite lattice, this is a manifestly finite, computable product type. -/
abbrev Box (d : ℕ) (x : List Bool) (t : ℕ) :=
  Fin (x.length + 2 * t + 1) × (Fin d → Fin (2 * t + 1))

/-- Interpret an address as the actual signed lattice site. -/
def point {d : ℕ} (x : List Bool) (t : ℕ) (q : Box d x t) : Site d :=
  ((q.1 : ℤ) - (t : ℤ), fun i => (q.2 i : ℤ) - (t : ℤ))

/-- Every represented site lies in the finite causal box. -/
theorem point_inCone {d : ℕ} (x : List Bool) (t : ℕ) (q : Box d x t) :
    InCone x t (point x t q) := by
  have hfirst := q.1.isLt
  refine ⟨?_, ?_, ?_⟩
  · dsimp [point]; omega
  · dsimp [point]; omega
  · intro i
    have hi := (q.2 i).isLt
    dsimp [point]
    constructor <;> omega

/-- Encode a site inside the causal box by nonnegative bounded indices. -/
def index {d : ℕ} (x : List Bool) (t : ℕ) (p : Site d)
    (hp : InCone x t p) : Box d x t :=
  (⟨(p.1 + (t : ℤ)).toNat, by have h := hp.1; have k := hp.2.1; omega⟩,
    fun i => ⟨(p.2 i + (t : ℤ)).toNat, by
      have h := hp.2.2 i
      omega⟩)

/-- Decoding an in-bounds lattice site recovers its signed coordinates. -/
theorem point_index {d : ℕ} (x : List Bool) (t : ℕ) (p : Site d)
    (hp : InCone x t p) : point x t (index x t p hp) = p := by
  apply Prod.ext
  · dsimp [point, index]
    have h := hp.1
    omega
  · funext i
    dsimp [point, index]
    have h := hp.2.2 i
    omega

/-- Encoding a represented address recovers the exact address. -/
theorem index_point {d : ℕ} (x : List Bool) (t : ℕ) (q : Box d x t) :
    index x t (point x t q) (point_inCone x t q) = q := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [index, point]
    have h := q.1.isLt
    omega
  · funext i
    apply Fin.ext
    dsimp [index, point]
    have h := (q.2 i).isLt
    omega

/-- The exact number of cells in the causal rectangle. -/
theorem box_card (d : ℕ) (x : List Bool) (t : ℕ) :
    Fintype.card (Box d x t) =
      (x.length + 2 * t + 1) * (2 * t + 1) ^ d := by
  simp [Box, Fintype.card_prod, Fintype.card_fun]

/-- Constructive decidability of membership in the finite causal rectangle.
The only quantified coordinates range over the finite type `Fin d`. -/
instance decidableInCone {d : ℕ} (x : List Bool) (t : ℕ) (p : Site d) :
    Decidable (InCone x t p) := by
  unfold InCone
  letI : Decidable (∀ i : Fin d,
      -(t : ℤ) ≤ p.2 i ∧ p.2 i ≤ (t : ℤ)) :=
    Fintype.decidableForallFintype
  infer_instance

/-- A finite array of states indexed by all sites in the rectangle. -/
abbrev Snapshot {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :=
  Box d x t → A.S

/-- Recover the corresponding infinite configuration with blank exterior. -/
def read {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) (p : Site d) : A.S :=
  if h : InCone x t p then s (index x t p h) else A.blank

theorem read_point {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) (q : Box d x t) :
    A.read x t s (point x t q) = s q := by
  simp only [read, dif_pos (point_inCone x t q), index_point]

/-- The finite snapshot of the original infinite evolution. -/
def snapshot {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :
    A.Snapshot x t :=
  fun q => A.run (A.init x) t (point x t q)

/-- The infinite reconstruction of a snapshot is exactly the original run. -/
theorem read_snapshot {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (p : Site d) :
    A.read x t (A.snapshot x t) p = A.run (A.init x) t p := by
  by_cases hp : InCone x t p
  · simp only [read, dif_pos hp, snapshot, point_index]
  · simp only [read, dif_neg hp, A.run_blank_outside x t p hp]

/-- A finite synchronous update.  Each lookup outside the previous box
returns the quiescent blank.  This is an actual finite-state function,
not an invocation of the infinite evolution. -/
def advance {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) : A.Snapshot x (t + 1) :=
  fun q =>
    A.rule (fun u =>
      A.read x t s
        ((point x (t + 1) q).1 + off u.1,
         fun i => (point x (t + 1) q).2 i + off (u.2 i)))

/-- The independently defined finite update commutes with the infinite
synchronous WCC evolution, for every input and every number of rounds. -/
theorem advance_snapshot {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :
    A.advance x t (A.snapshot x t) = A.snapshot x (t + 1) := by
  funext q
  change A.rule (fun u =>
      A.read x t (A.snapshot x t)
        ((point x (t + 1) q).1 + off u.1,
          fun i => (point x (t + 1) q).2 i + off (u.2 i))) =
      A.run (A.init x) (t + 1) (point x (t + 1) q)
  rw [A.run_succ]
  change A.rule _ = A.rule _
  congr 1
  funext u
  exact A.read_snapshot x t _

/-- A finite Boolean predicate checks the box and the infinite blank
exterior.  Thus a blank that accepts/rejects is never overlooked. -/
def hasWitness {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) (P : A.S → Bool) : Bool :=
  decide (P A.blank = true ∨ ∃ q : Box d x t, P (s q) = true)

/-- Exact equivalence between the finite test and the existential test on
the infinite, blank-extended lattice. -/
theorem hasWitness_iff {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) (P : A.S → Bool) :
    (P A.blank = true ∨ ∃ q : Box d x t, P (s q) = true) ↔
      ∃ p : Site d, P (A.read x t s p) = true := by
  constructor
  · rintro (hb | ⟨q, hq⟩)
    · let p : Site d := (-(t : ℤ) - 1, fun _ => 0)
      have hout : ¬ InCone x t p := by
        intro hp
        have hh := hp.1
        dsimp [p] at hh
        omega
      exact ⟨p, by simpa only [read, dif_neg hout] using hb⟩
    · exact ⟨point x t q, by simpa only [A.read_point] using hq⟩
  · rintro ⟨p, hp⟩
    by_cases h : InCone x t p
    · right
      exact ⟨index x t p h, by simpa only [read, dif_pos h] using hp⟩
    · left
      simpa only [read, dif_neg h] using hp

open Classical in
theorem hasWitness_correct {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) (P : A.S → Bool) :
    A.hasWitness x t s P =
      decide (∃ p : Site d, P (A.read x t s p) = true) := by
  classical
  exact decide_eq_decide.2 (A.hasWitness_iff x t s P)

/-- Finite output preserving acceptance precedence. -/
def finiteOutput {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ)
    (s : A.Snapshot x t) : Option Bool :=
  answerOf (A.hasWitness x t s A.acc) (A.hasWitness x t s A.rej)

/-- The finite output equals the original global existential output, even
when the quiescent blank is accepting/rejecting. -/
theorem finiteOutput_snapshot {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :
    A.finiteOutput x t (A.snapshot x t) = A.out x t := by
  unfold finiteOutput WCCD.out WCCD.outCfg
  rw [A.hasWitness_correct, A.hasWitness_correct]
  simpa only [A.read_snapshot]

/-- Actual finite replay, using only the finite initial array and
the finite update routine (no reference to the infinite run). -/
def replay {d : ℕ} (A : WCCD d) (x : List Bool) :
    (t : ℕ) → A.Snapshot x t
  | 0 => fun q => A.init x (point x 0 q)
  | t + 1 => A.advance x t (A.replay x t)

/-- Every finite replay snapshot is identical to the infinite evolution
on its full causal box. -/
theorem replay_correct {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :
    A.replay x t = A.snapshot x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change A.advance x t (A.replay x t) = A.snapshot x (t + 1)
      rw [ih, A.advance_snapshot]

/-- Exact equality of the full finite output stream with WCCD's output
stream.  In particular the shared first-answer semantics is preserved. -/
theorem replay_output {d : ℕ} (A : WCCD d) (x : List Bool) (t : ℕ) :
    A.finiteOutput x t (A.replay x t) = A.out x t := by
  rw [A.replay_correct, A.finiteOutput_snapshot]

end PVNP.Discrete.WCCD
