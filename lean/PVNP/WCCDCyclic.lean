import PVNP.WCCDFiniteSupport

/-!
# D-1: exact flattening of a multidimensional WCC onto a cyclic array

Fix `A : WCCD d`, an input `x` of length `n`, a horizon `G`, the base
`M = n + 2G + 3`, and any length `N ≥ M^(d+1)`.  The linear map

`flat M p = p₀ + Σₖ p_{k+1} M^(k+1)`

sends the lattice `ℤ^(1+d)` to `ℤ/Nℤ`; on the causal box `InCone x (G+1)`
it is injective (`flat_inj`, a balanced base-`M` digit argument).  The
*cyclic* automaton on `ℤ/Nℤ` with neighbourhood offsets `flat M (off u)`
(`cstep`) therefore reproduces the multidimensional run exactly for every
`t ≤ G` (`cyclic_exact`), including the blank exterior, and has the same
existential output (`cyclic_out`).

This is the mathematical content that lets an ordinary single-tape machine
simulate the `(1+d)`-dimensional automaton with one-dimensional cyclic
rotations only (see `PVNP.WCCDSweep`).  No property of the simulating machine
is assumed here.
-/

namespace PVNP.Discrete.WCCD

/-! ### Balanced base-`M` digits -/

theorem digits_bound (M : ℕ) (hM : 1 ≤ M) :
    ∀ (m : ℕ) (e : Fin m → ℤ), (∀ k, |e k| ≤ (M : ℤ) - 1) →
      |∑ k, e k * (M : ℤ) ^ (k : ℕ)| ≤ (M : ℤ) ^ m - 1
  | 0, e, _ => by simp
  | m + 1, e, he => by
    rw [Fin.sum_univ_succ]
    have ih := digits_bound M hM m (fun k => e k.succ) (fun k => he k.succ)
    have h0 := he 0
    have hrest : ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k.succ : ℕ) =
        (M : ℤ) * ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.val_succ, pow_succ]; ring
    rw [hrest]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have hMz : (0 : ℤ) ≤ (M : ℤ) := by positivity
    calc |e 0 + (M : ℤ) * ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ)|
        ≤ |e 0| + |(M : ℤ) * ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ)| := abs_add_le _ _
      _ = |e 0| + (M : ℤ) * |∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ)| := by
          rw [abs_mul, abs_of_nonneg hMz]
      _ ≤ ((M : ℤ) - 1) + (M : ℤ) * ((M : ℤ) ^ m - 1) := by gcongr
      _ = (M : ℤ) ^ (m + 1) - 1 := by ring

theorem digits_zero (M : ℕ) (hM : 1 ≤ M) :
    ∀ (m : ℕ) (e : Fin m → ℤ), (∀ k, |e k| < (M : ℤ)) →
      ∑ k, e k * (M : ℤ) ^ (k : ℕ) = 0 → ∀ k, e k = 0
  | 0, e, _, _ => fun k => k.elim0
  | m + 1, e, he, hs => by
    rw [Fin.sum_univ_succ] at hs
    have hrest : ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k.succ : ℕ) =
        (M : ℤ) * ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.val_succ, pow_succ]; ring
    rw [hrest] at hs
    simp only [Fin.val_zero, pow_zero, mul_one] at hs
    have hdvd : (M : ℤ) ∣ e 0 := ⟨-∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ), by linarith⟩
    have h0 : e 0 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have hb := he 0
      rw [hc, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ M)] at hb
      have : |c| < 1 := by
        by_contra hc1
        push_neg at hc1
        nlinarith
      have : c = 0 := by
        rcases abs_lt.mp this with ⟨h1, h2⟩; omega
      rw [hc, this, mul_zero]
    rw [h0, zero_add] at hs
    have hMpos : (M : ℤ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hs' : ∑ k : Fin m, e k.succ * (M : ℤ) ^ (k : ℕ) = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hMpos
      · exact h
    have ih := digits_zero M hM m (fun k => e k.succ) (fun k => he k.succ) hs'
    intro k
    refine Fin.cases h0 (fun k => ih k) k

/-! ### The flattening map -/

/-- Flattening weights: axis `0` has weight `1`, transverse axis `k` has
weight `M^(k+1)`. -/
def flat {d : ℕ} (M : ℕ) (p : Site d) : ℤ := p.1 + ∑ k : Fin d, p.2 k * (M : ℤ) ^ (k.val + 1)

/-- The flattening map as a digit expansion with `d + 1` digits. -/
theorem flat_eq_digits {d : ℕ} (M : ℕ) (p : Site d) :
    flat M p = ∑ k : Fin (d + 1), (Fin.cons p.1 p.2 : Fin (d + 1) → ℤ) k * (M : ℤ) ^ (k : ℕ) := by
  rw [Fin.sum_univ_succ]
  simp [flat, Fin.val_succ]

theorem flat_sub {d : ℕ} (M : ℕ) (p q : Site d) :
    flat M p - flat M q = flat M (p.1 - q.1, fun k => p.2 k - q.2 k) := by
  simp only [flat, sub_mul, Finset.sum_sub_distrib]; ring

theorem flat_add {d : ℕ} (M : ℕ) (p q : Site d) :
    flat M (p.1 + q.1, fun k => p.2 k + q.2 k) = flat M p + flat M q := by
  simp only [flat, add_mul, Finset.sum_add_distrib]; ring

/-- Neighbourhood offset vector of a Moore index. -/
def offv {d : ℕ} (u : Fin 3 × (Fin d → Fin 3)) : Site d := (off u.1, fun k => off (u.2 k))

/-- Base used for horizon `G` on input `x`. -/
def base (x : List Bool) (G : ℕ) : ℕ := x.length + 2 * G + 3

theorem base_pos (x : List Bool) (G : ℕ) : 3 ≤ base x G := by unfold base; omega

/-- **Injectivity on the causal box.**  Two sites of `InCone x (G+1)` with
the same flattened residue modulo any `N ≥ M^(d+1)` coincide. -/
theorem flat_inj {d : ℕ} (x : List Bool) (G N : ℕ) (hN : base x G ^ (d + 1) ≤ N)
    {p q : Site d} (hp : InCone x (G + 1) p) (hq : InCone x (G + 1) q)
    (h : ((flat (base x G) p : ℤ) : ZMod N) = (flat (base x G) q : ℤ)) : p = q := by
  set M := base x G with hMdef
  have hM : 3 ≤ M := base_pos x G
  set e : Site d := (p.1 - q.1, fun k => p.2 k - q.2 k) with he
  have hdiff : flat M p - flat M q = flat M e := flat_sub M p q
  -- digit bounds
  have hdig : ∀ k : Fin (d + 1), |(Fin.cons e.1 e.2 : Fin (d + 1) → ℤ) k| ≤ (M : ℤ) - 1 := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [Fin.cons_zero, he]
      rcases hp with ⟨hp1, hp2, -⟩; rcases hq with ⟨hq1, hq2, -⟩
      rw [abs_le]; constructor <;> push_cast [hMdef, base] at * <;> omega
    · simp only [Fin.cons_succ, he]
      have hpk := hp.2.2 k; have hqk := hq.2.2 k
      rw [abs_le]; constructor <;> push_cast [hMdef, base] at * <;> omega
  have hbound := digits_bound M (by omega) (d + 1) _ hdig
  rw [← flat_eq_digits] at hbound
  -- divisibility by N
  have hdvd : (N : ℤ) ∣ flat M e := by
    rw [← hdiff]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h.symm
  have hNle : (M : ℤ) ^ (d + 1) ≤ N := by exact_mod_cast hN
  have hzero : flat M e = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    have : |c| < 1 := by
      by_contra hc1
      push_neg at hc1
      have hNpos : (0 : ℤ) < N := by
        have : (0 : ℤ) < (M : ℤ) ^ (d + 1) := by positivity
        linarith
      rw [hc, abs_mul, abs_of_pos hNpos] at hbound
      nlinarith
    have : c = 0 := by rcases abs_lt.mp this with ⟨h1, h2⟩; omega
    rw [hc, this, mul_zero]
  rw [flat_eq_digits] at hzero
  have hz := digits_zero M (by omega) (d + 1) _
    (fun k => lt_of_le_of_lt (hdig k) (by omega)) hzero
  apply Prod.ext
  · have := hz 0; simp only [Fin.cons_zero, he] at this; omega
  · funext k; have := hz k.succ; simp only [Fin.cons_succ, he] at this; omega

/-! ### The cyclic automaton -/

variable {d : ℕ} (A : WCCD d)

/-- One synchronous step of the cyclic automaton on `ℤ/Nℤ`. -/
def cstep (N M : ℕ) (c : ZMod N → A.S) : ZMod N → A.S :=
  fun z => A.rule fun u => c (z + ((flat M (offv u) : ℤ) : ZMod N))

/-- Iterated cyclic steps. -/
def crun (N M : ℕ) (c : ZMod N → A.S) (t : ℕ) : ZMod N → A.S := (A.cstep N M)^[t] c

theorem crun_succ (N M : ℕ) (c : ZMod N → A.S) (t : ℕ) :
    A.crun N M c (t + 1) = A.cstep N M (A.crun N M c t) := by
  simp [crun, Function.iterate_succ_apply']

/-- Cyclic initial array: the input written on cells `0, …, n-1`
(origin marker in cell `0`), blank elsewhere. -/
def cinit (N : ℕ) (x : List Bool) : ZMod N → A.S := fun z =>
  if z.val = 0 then A.origin x.head?
  else if z.val < x.length then A.inp (x.getD z.val false) else A.blank

theorem flat_axis {d : ℕ} (M j : ℕ) : flat M ((j : ℤ), (0 : Fin d → ℤ)) = j := by
  simp [flat]

theorem inCone_axis (x : List Bool) (t j : ℕ) (hj : j ≤ x.length) :
    InCone x t ((j : ℤ), (0 : Fin d → ℤ)) := by
  refine ⟨by omega, by omega, fun i => ?_⟩
  simp

theorem flat_offv_add (M : ℕ) (p : Site d) (u : Fin 3 × (Fin d → Fin 3)) :
    flat M p + flat M (offv u) = flat M (p.1 + off u.1, fun k => p.2 k + off (u.2 k)) := by
  rw [← flat_add]; rfl

theorem inCone_offv (x : List Bool) (t : ℕ) (p : Site d) (u : Fin 3 × (Fin d → Fin 3))
    (hp : InCone x t p) : InCone x (t + 1) (p.1 + off u.1, fun k => p.2 k + off (u.2 k)) := by
  rcases hp with ⟨h1, h2, h3⟩
  have hb := off_bounds u.1
  refine ⟨by push_cast; omega, by push_cast; omega, fun i => ?_⟩
  have hbi := off_bounds (u.2 i)
  have := h3 i
  constructor <;> push_cast <;> omega

theorem inCone_sub_offv (x : List Bool) (t : ℕ) (q : Site d) (u : Fin 3 × (Fin d → Fin 3))
    (hq : InCone x t q) : InCone x (t + 1) (q.1 - off u.1, fun k => q.2 k - off (u.2 k)) := by
  rcases hq with ⟨h1, h2, h3⟩
  have hb := off_bounds u.1
  refine ⟨by push_cast; omega, by push_cast; omega, fun i => ?_⟩
  have hbi := off_bounds (u.2 i)
  have := h3 i
  constructor <;> push_cast <;> omega

theorem inCone_mono (x : List Bool) {t t' : ℕ} (h : t ≤ t') (p : Site d) (hp : InCone x t p) :
    InCone x t' p := by
  rcases hp with ⟨h1, h2, h3⟩
  refine ⟨by omega, by omega, fun i => ?_⟩
  have := h3 i
  constructor <;> omega

/-- **Exact flattening.**  For every `t ≤ G` the cyclic run agrees with the
multidimensional run on the whole causal box, and is blank on every residue
not hit by the time-`t` cone. -/
theorem cyclic_exact (x : List Bool) (G N : ℕ) [NeZero N] (hN : base x G ^ (d + 1) ≤ N) :
    ∀ t, t ≤ G →
      (∀ p, InCone x (G + 1) p →
        A.crun N (base x G) (A.cinit N x) t ((flat (base x G) p : ℤ) : ZMod N) =
          A.run (A.init x) t p) ∧
      (∀ z : ZMod N, (∀ p : Site d, InCone x t p → ((flat (base x G) p : ℤ) : ZMod N) ≠ z) →
        A.crun N (base x G) (A.cinit N x) t z = A.blank) := by
  set M := base x G with hMdef
  have hM : 3 ≤ M := base_pos x G
  have hlenN : x.length < N := by
    have : M ≤ M ^ (d + 1) := Nat.le_self_pow (by omega) M
    have : x.length < M := by simp only [hMdef, base]; omega
    omega
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun p hp => ?_, fun z hz => ?_⟩
    · -- initial array versus the lattice initial configuration
      simp only [crun, Function.iterate_zero, id, WCCD.run]
      by_cases hax : p.2 = 0 ∧ 0 ≤ p.1 ∧ (p.1 < x.length ∨ p.1 = 0)
      · obtain ⟨h2, h1, h3⟩ := hax
        obtain ⟨j, hj⟩ : ∃ j : ℕ, p.1 = j := ⟨p.1.toNat, by omega⟩
        have hpj : p = ((j : ℤ), 0) := Prod.ext hj h2
        subst hpj
        have hjN : j < N := by rcases h3 with h3 | h3 <;> omega
        rw [flat_axis]
        have hval : ((j : ℤ) : ZMod N).val = j := by
          rw [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hjN]
        simp only [cinit, hval, WCCD.init, if_true]
        by_cases hj0 : j = 0
        · subst hj0; simp
        · have hjl : j < x.length := by rcases h3 with h3 | h3 <;> omega
          rw [if_neg hj0, if_pos hjl, if_neg (by exact_mod_cast hj0),
            if_pos ⟨by omega, by exact_mod_cast hjl⟩]
          simp
      · -- off the input segment: both sides blank
        have hinit : A.init x p = A.blank := by
          simp only [WCCD.init]
          by_cases h2 : p.2 = 0
          · rw [if_pos h2]
            push_neg at hax
            have := hax h2
            rw [if_neg (by omega), if_neg (by omega)]
          · rw [if_neg h2]
        rw [hinit]
        simp only [cinit]
        set z : ZMod N := ((flat M p : ℤ) : ZMod N) with hz
        have hzv : z.val < N := ZMod.val_lt z
        by_cases h0 : z.val = 0 ∨ z.val < x.length
        · exfalso
          -- z is the residue of an axis site; injectivity gives p on the axis
          have hjc : InCone x (G + 1) (((z.val : ℕ) : ℤ), (0 : Fin d → ℤ)) :=
            inCone_axis x (G + 1) z.val (by rcases h0 with h0 | h0 <;> omega)
          have heq : ((flat M p : ℤ) : ZMod N) =
              ((flat M (((z.val : ℕ) : ℤ), (0 : Fin d → ℤ)) : ℤ) : ZMod N) := by
            rw [flat_axis, Int.cast_natCast, ZMod.natCast_zmod_val]
          have := flat_inj x G N hN hp hjc heq
          apply hax
          rw [this]
          refine ⟨rfl, by positivity, ?_⟩
          rcases h0 with h0 | h0
          · right; simp [h0]
          · left; show (((z.val : ℕ) : ℤ)) < x.length; exact_mod_cast h0
        · push_neg at h0
          rw [if_neg h0.1, if_neg (by omega)]
    · simp only [crun, Function.iterate_zero, id, cinit]
      have hzv : z.val < N := ZMod.val_lt z
      by_cases h0 : z.val = 0 ∨ z.val < x.length
      · exfalso
        have hjc : InCone x 0 (((z.val : ℕ) : ℤ), (0 : Fin d → ℤ)) :=
          inCone_axis x 0 z.val (by rcases h0 with h0 | h0 <;> omega)
        apply hz _ hjc
        rw [flat_axis, Int.cast_natCast, ZMod.natCast_zmod_val]
      · push_neg at h0
        rw [if_neg h0.1, if_neg (by omega)]
  | succ t ih =>
    intro ht
    obtain ⟨iha, ihb⟩ := ih (by omega)
    refine ⟨fun p hp => ?_, fun z hz => ?_⟩
    · rw [A.crun_succ, A.run_succ]
      simp only [cstep, WCCD.step]
      congr 1
      funext u
      rw [← Int.cast_add, flat_offv_add]
      set q : Site d := (p.1 + off u.1, fun k => p.2 k + off (u.2 k)) with hq
      by_cases hqc : InCone x (G + 1) q
      · exact iha q hqc
      · -- q is outside the box: both sides are blank
        have hqt : ¬ InCone x t q := fun h => hqc (inCone_mono x (by omega) q h)
        rw [A.run_blank_outside x t q hqt]
        apply ihb
        intro r hr heq
        -- r = q would follow from injectivity applied to r - off u and p
        have hr' := inCone_sub_offv x t r u hr
        have hpr : (r.1 - off u.1, fun k => r.2 k - off (u.2 k)) = p := by
          apply flat_inj x G N hN (inCone_mono x (by omega) _ hr') hp
          have h1 : flat M (r.1 - off u.1, fun k => r.2 k - off (u.2 k)) =
              flat M r - flat M (offv u) := by
            rw [flat_sub]; rfl
          have h2 : flat M p = flat M q - flat M (offv u) := by
            rw [hq, ← flat_offv_add]; ring
          rw [h1, h2, Int.cast_sub, Int.cast_sub, heq]
        apply hqc
        have : q = r := by
          rw [hq, ← hpr]
          apply Prod.ext
          · simp
          · funext k; simp
        rw [this]
        exact inCone_mono x (by omega) r hr
    · rw [A.crun_succ]
      simp only [cstep]
      have hall : (fun u : Fin 3 × (Fin d → Fin 3) => A.crun N M (A.cinit N x) t
          (z + ((flat M (offv u) : ℤ) : ZMod N))) = fun _ => A.blank := by
        funext u
        apply ihb
        intro r hr heq
        apply hz (r.1 - off u.1, fun k => r.2 k - off (u.2 k)) (inCone_sub_offv x t r u hr)
        have h1 : flat M (r.1 - off u.1, fun k => r.2 k - off (u.2 k)) =
            flat M r - flat M (offv u) := by
          rw [flat_sub]; rfl
        rw [h1, Int.cast_sub, heq]
        ring
      rw [hall, A.quiescent]

/-- **Exact output.**  The existential output of the cyclic array (with the
blank exterior accounted for) is the multidimensional output, for `t ≤ G`. -/
theorem cyclic_out (x : List Bool) (G N : ℕ) [NeZero N] (hN : base x G ^ (d + 1) ≤ N)
    (t : ℕ) (ht : t ≤ G) (P : A.S → Bool) :
    (P A.blank = true ∨ ∃ z : ZMod N, P (A.crun N (base x G) (A.cinit N x) t z) = true) ↔
      ∃ p : Site d, P (A.run (A.init x) t p) = true := by
  obtain ⟨ha, hb⟩ := A.cyclic_exact x G N hN t ht
  constructor
  · rintro (h | ⟨z, hz⟩)
    · refine ⟨(-(t : ℤ) - 1, fun _ => 0), ?_⟩
      rw [A.run_blank_outside x t _ (fun h => by have := h.1; omega)]
      exact h
    · by_cases hc : ∃ p : Site d, InCone x t p ∧ ((flat (base x G) p : ℤ) : ZMod N) = z
      · obtain ⟨p, hp, rfl⟩ := hc
        exact ⟨p, by rw [← ha p (inCone_mono x (by omega) p hp)]; exact hz⟩
      · push_neg at hc
        refine ⟨(-(t : ℤ) - 1, fun _ => 0), ?_⟩
        rw [A.run_blank_outside x t _ (fun h => by have := h.1; omega)]
        rw [hb z hc] at hz
        exact hz
  · rintro ⟨p, hp⟩
    by_cases hc : InCone x t p
    · right
      exact ⟨_, by rw [ha p (inCone_mono x (by omega) p hc)]; exact hp⟩
    · left
      rw [A.run_blank_outside x t p hc] at hp
      exact hp

end PVNP.Discrete.WCCD
