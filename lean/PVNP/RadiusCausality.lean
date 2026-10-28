import PVNP.LocalityLowerBound

/-!
# Radius-r locality and readout lower bounds (Issue #10)

A synchronous update uses a fixed finite alphabet, a fixed radius r,
a blank outside a Fin n tape, and a local rule with exactly 2*r+1
arguments, represented as a list. A formal scanning convention is used:
offset 0 denotes position i+r, offset 2*r denotes position i-r;
positions outside the finite tape use blank. No encoding/readout is free.
-/

namespace PVNP.RadiusCausality

open PVNP.PartII
open PVNP.LocalityLowerBound

variable {S : Type}

structure RadiusMachine (S : Type) (r : Nat) where
  blank : S
  localRule : List S → S

def windowSample (M : RadiusMachine S r) {n : Nat}
    (c : Configuration n S) (i : Fin n) (off : Nat) : S :=
  if h : off ≤ i.val + r then
    if h' : i.val + r - off < n then c ⟨i.val + r - off, h'⟩
    else M.blank
  else M.blank

def step (M : RadiusMachine S r) {n : Nat}
    (c : Configuration n S) : Configuration n S :=
  fun i => M.localRule ((List.range (2 * r + 1)).map
    (windowSample M c i))

theorem windowSample_prefix (M : RadiusMachine S r) {n k : Nat}
    (c d : Configuration n S)
    (h : prefixAgree c d (k + r))
    (i : Fin n) (hi : i.val < k) (off : Nat) :
    windowSample M c i off = windowSample M d i off := by
  unfold windowSample
  split_ifs with hbound hinside
  · exact h ⟨_, hinside⟩ (by change i.val + r - off < k + r; omega)
  · rfl
  · rfl

/-- Radius-r finite dependency cone shrinks an agreement prefix by r. -/
theorem prefix_step (M : RadiusMachine S r) {n k : Nat}
    (c d : Configuration n S)
    (h : prefixAgree c d (k + r)) :
    prefixAgree (step M c) (step M d) k := by
  intro i hi
  have hs : (windowSample M c i) = (windowSample M d i) := by
    funext off
    exact windowSample_prefix M c d h i hi off
  simp only [step]
  rw [hs]

/-- Full causal cone: from t*r+k initially matching cells, k remain
    indistinguishable after t rounds, uniformly over rules and sizes. -/
theorem prefix_iterate (M : RadiusMachine S r) {n : Nat}
    (c d : Configuration n S) :
    ∀ t k : Nat, prefixAgree c d (t * r + k) →
      prefixAgree (iterate (step M) t c) (iterate (step M) t d) k := by
  intro t
  induction t with
  | zero =>
      intro k h
      simpa [iterate] using h
  | succ t ih =>
      intro k h
      change prefixAgree
        (step M (iterate (step M) t c))
        (step M (iterate (step M) t d)) k
      apply prefix_step M
      apply ih (k + r)
      have heq : t * r + (k + r) = (t + 1) * r + k := by
        simp only [Nat.succ_mul]
        omega
      rw [heq]
      exact h

/-- Any decoder restricted to the first m output cells inherits the
    uniform finite-speed bound. The decoder may be arbitrarily complex. -/
theorem prefix_decoder_equal (M : RadiusMachine S r) {n : Nat}
    (c d : Configuration n S) (t m : Nat)
    (hsize : m ≤ n) (h : prefixAgree c d (t * r + m))
    (decode : (Fin m → S) → Bool) :
    decode (fun i => (iterate (step M) t c) ⟨i.val, by omega⟩) =
      decode (fun i => (iterate (step M) t d) ⟨i.val, by omega⟩) := by
  have hp := prefix_iterate M c d t m h
  congr 1
  funext i
  exact hp ⟨i.val, by omega⟩ i.isLt

def allFalse (n : Nat) : Configuration n Bool := fun _ => false

def oneAt (n j : Nat) : Configuration n Bool :=
  fun i => decide (i.val = j)

/-- An adversarial pair of length n=t*r+m+1, differing in the last
    site, always has identical first-m readout after t rounds. -/
theorem far_bit_indistinguishable (r t m : Nat)
    (M : RadiusMachine Bool r) (decode : (Fin m → Bool) → Bool) :
    decode (fun i => (iterate (step M) t
      (allFalse (t * r + m + 1))) ⟨i.val, by omega⟩) =
    decode (fun i => (iterate (step M) t
      (oneAt (t * r + m + 1) (t * r + m))) ⟨i.val, by omega⟩) := by
  apply prefix_decoder_equal M _ _ t m (by omega)
  intro i hi
  have hne : i.val ≠ t * r + m := by omega
  simp [allFalse, oneAt, hne]

/-- Strongest direct-input conclusion: no rule and no prefix-m decoder
    can decide the last bit of ALL configurations of length t*r+m+1
    within t rounds. This charges r and m explicitly. -/
theorem no_prefix_decoder_last_bit (r t m : Nat)
    (M : RadiusMachine Bool r) (decode : (Fin m → Bool) → Bool) :
    ¬ (∀ c : Configuration (t * r + m + 1) Bool,
        decode (fun i => (iterate (step M) t c)
          ⟨i.val, by omega⟩) =
        c ⟨t * r + m, by omega⟩) := by
  intro hall
  have hzero := hall (allFalse (t * r + m + 1))
  have hone := hall (oneAt (t * r + m + 1) (t * r + m))
  have heq := far_bit_indistinguishable r t m M decode
  have hz : decode (fun i => (iterate (step M) t
      (allFalse (t * r + m + 1))) ⟨i.val, by omega⟩) = false := by
    simpa [allFalse] using hzero
  have ho : decode (fun i => (iterate (step M) t
      (oneAt (t * r + m + 1) (t * r + m))) ⟨i.val, by omega⟩) = true := by
    simpa [oneAt] using hone
  rw [hz, ho] at heq
  cases heq

/-- Explicit counterexample to transferring this lower bound to
    uncharged nonlocal *input encodings*: copy the far bit to cell 0.
    An arbitrary decoder may now read that bit at round zero. -/
def copyFar {n : Nat} (c : Configuration n Bool)
    (target : Fin n) : Configuration n Bool :=
  fun i => if i.val = 0 then c target else c i

theorem shortcut_encoding_reads_far_at_zero {n : Nat}
    (hn : 0 < n) (c : Configuration n Bool) (target : Fin n) :
    copyFar c target ⟨0, hn⟩ = c target := by
  simp [copyFar]

/-- Unrestricted input preprocessors can decide any Boolean predicate
    in their output encoding. This is an adversarial nonuniform/unpaid
    encoding countermodel, not a uniform polynomial-time algorithm. -/
theorem uncharged_encoder_decides_any_language
    {Input : Type} (answer : Input → Bool) :
    ∃ encoder : Input → Configuration 1 Bool,
      ∀ x, encoder x ⟨0, by norm_num⟩ = answer x := by
  exact ⟨(fun x _ => answer x), (by intro x; rfl)⟩

/-- A decoder may inspect any finite list of sites, not necessarily a
    contiguous block, as long as every observed site lies inside the
    explicitly paid prefix. This allows multiple separated outputs. -/
theorem sparse_decoder_equal (M : RadiusMachine S r) {n : Nat}
    (c d : Configuration n S) (t m outputCount : Nat)
    (observed : Fin outputCount → Fin n)
    (hsite : ∀ j, (observed j).val < m)
    (h : prefixAgree c d (t * r + m))
    (decode : (Fin outputCount → S) → Bool) :
    decode (fun j => (iterate (step M) t c) (observed j)) =
      decode (fun j => (iterate (step M) t d) (observed j)) := by
  have hp := prefix_iterate M c d t m h
  congr 1
  funext j
  exact hp (observed j) (hsite j)


/-- Input preprocessing cannot be free when its own local update has
    a declared finite radius. The total information cone is the sum of
    the encoding and computation cones, with potentially different radii. -/
theorem two_stage_prefix
    (encoder : RadiusMachine S encoderRadius)
    (computer : RadiusMachine S computeRadius)
    {n : Nat} (c d : Configuration n S)
    (encoderRounds computeRounds m : Nat)
    (h : prefixAgree c d
      (encoderRounds * encoderRadius + computeRounds * computeRadius + m)) :
    prefixAgree
      (iterate (step computer) computeRounds
        (iterate (step encoder) encoderRounds c))
      (iterate (step computer) computeRounds
        (iterate (step encoder) encoderRounds d))
      m := by
  apply prefix_iterate computer _ _ computeRounds m
  apply prefix_iterate encoder _ _ encoderRounds
    (computeRounds * computeRadius + m)
  simpa [Nat.add_assoc] using h

/-- A decoder of the first m cells inherits the *sum* of both
    local computation and local preprocessing latency costs. -/
theorem two_stage_prefix_decoder_equal
    (encoder : RadiusMachine S encoderRadius)
    (computer : RadiusMachine S computeRadius)
    {n : Nat} (c d : Configuration n S)
    (encoderRounds computeRounds m : Nat)
    (hm : m ≤ n)
    (h : prefixAgree c d
      (encoderRounds * encoderRadius + computeRounds * computeRadius + m))
    (decode : (Fin m → S) → Bool) :
    decode (fun i =>
      (iterate (step computer) computeRounds
        (iterate (step encoder) encoderRounds c)) ⟨i.val, by omega⟩) =
    decode (fun i =>
      (iterate (step computer) computeRounds
        (iterate (step encoder) encoderRounds d)) ⟨i.val, by omega⟩) := by
  apply prefix_decoder_equal computer _ _ computeRounds m hm decode
  exact prefix_iterate encoder c d encoderRounds
    (computeRounds * computeRadius + m)
    (by simpa [Nat.add_assoc] using h)

/-- A more flexible size bound: for any tape length n with
    t*r+m<n, the last bit lies outside the readout's causal cone. -/
theorem no_prefix_decoder_last_bit_general
    (r t m n : Nat) (hfar : t * r + m < n)
    (M : RadiusMachine Bool r) (decode : (Fin m → Bool) → Bool) :
    ¬ (∀ c : Configuration n Bool,
        decode (fun i =>
          (iterate (step M) t c) ⟨i.val, by omega⟩) =
          c ⟨n - 1, by omega⟩) := by
  intro hall
  have hp : prefixAgree (allFalse n) (oneAt n (n - 1))
      (t * r + m) := by
    intro i hi
    have hne : i.val ≠ n - 1 := by omega
    simp [allFalse, oneAt, hne]
  have heq := prefix_decoder_equal M (allFalse n)
    (oneAt n (n - 1)) t m (by omega) hp decode
  have hz : decode (fun i =>
      (iterate (step M) t (allFalse n)) ⟨i.val, by omega⟩) = false := by
    simpa [allFalse] using (hall (allFalse n))
  have ho : decode (fun i =>
      (iterate (step M) t (oneAt n (n - 1))) ⟨i.val, by omega⟩) = true := by
    simpa [oneAt] using (hall (oneAt n (n - 1)))
  rw [hz, ho] at heq
  cases heq

end PVNP.RadiusCausality
