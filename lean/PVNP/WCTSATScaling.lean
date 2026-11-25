import PVNP.WCTSATDevice
import PVNP.SATTarget
import PVNP.CookLevinUniform

/-!
# Superpolynomial physical resources for SAT: what a proof would prove

**Question.** Can interwoven SAT constraints force superpolynomial physical resources across
every admissible, uniformly encoded frozen-WCT solver? In quantifier form, for a device class
`𝓜` with charged resource `𝓡`:

  `∀ M ∈ 𝓜 deciding SAT, ∀ k, for infinitely many n, ∃ F of length ≥ n, 𝓡_M(F) > n^k`

(`SuperpolyResources`, with "infinitely many lengths" written as "beyond every `N`").

**The charged zero-mode class** (`ZeroDev`). A device is a Turing machine `M` with polynomial
time bound `p` deciding an amplitude-bit language `A`. The input `x` is prepared as the exact
zero-mode state of amplitude `2` (if `x ∈ A`) or `1` on the torus of side `L`, evolved by the
frozen equation, and read at time `1` by the fixed real detector of `WCTSATDevice` with the
fixed threshold `5/(2L)`. Its charged resource (`ZeroDev.res`) adds the machine's time bound,
the evolution time, the curvature budget `∫₀¹ ‖Δψ‖²`, the prepared mass and the inverse margin.

**Results.**

* `zdecides_iff`: a zero-mode device decides exactly its amplitude-bit language.
* `ZeroDev.res_le`: its charged resource is bounded by a polynomial in the input length.
* `zeroSuperpoly_iff`: in the zero-mode class, `SuperpolyResources Lang ↔ Lang ∉ P_TM`, for every
  language.
* `zeroSuperpoly_SAT_iff`: for dense SAT, `SuperpolyResources ↔ P_TM ≠ NP_TM`.
* `superpoly_SAT_implies_P_ne_NP`: in **every** device class that contains, for each language of
  `P_TM`, a device with polynomially bounded resource, `SuperpolyResources SAT_dense` implies
  `P_TM ≠ NP_TM`. `torus_superpoly_implies_P_ne_NP` is the special case of a class into which the
  zero-mode devices embed with polynomially bounded resources.

**Reading.** A superpolynomial physical lower bound for SAT over any admissible class that
contains the charged zero-mode devices is at least as hard as `P_TM ≠ NP_TM`, and for the
zero-mode class it is equivalent to it. The transfer from such a physical lower bound to the
classical one needs no simulation theorem: the classical polynomial-time deciders are inside the
physical class. The converse transfer, from a classical lower bound to a physical one for a
larger class, would need a resource-preserving simulation of the PDE devices by Turing machines
(manuscript claim I-11), which is not available.

None of this uses the internal structure of SAT. In particular an exponential number of
configurations of the interwoven field `Ψ ∈ {±1}ⁿ` is not a resource lower bound: every language
of `P_TM`, however large its configuration space, has a zero-mode device with polynomial
resources (`zero_charges_P`).
-/

namespace PVNP.WCTSATScaling

open PVNP.Torus PVNP.WCTSATDevice PVNP.Discrete PVNP.Discrete.SATV

/-! ### The target statement and the barrier for every class -/

/-- **The superpolynomial-resource statement** for a device class: every device that decides
`Lang` exceeds `n^k`, for every `k`, on inputs of arbitrarily large length. -/
def SuperpolyResources {Dev : Type*} (Decides : Dev → Set (List Bool) → Prop)
    (R : Dev → List Bool → ℝ) (Lang : Set (List Bool)) : Prop :=
  ∀ D, Decides D Lang → ∀ k N : ℕ, ∃ x : List Bool, N ≤ x.length ∧ (x.length : ℝ) ^ k < R D x

/-- A class charges `P_TM` polynomially if every language of `P_TM` has a device of the class
whose resource is bounded by a polynomial in the input length. -/
def ChargesPPoly {Dev : Type*} (Decides : Dev → Set (List Bool) → Prop)
    (R : Dev → List Bool → ℝ) : Prop :=
  ∀ Lang ∈ P_TM, ∃ D, Decides D Lang ∧ ∃ q : Polynomial ℕ, ∀ x, R D x ≤ ((q.eval x.length : ℕ) : ℝ)

/-- A polynomially bounded resource is not superpolynomial. -/
theorem not_superpoly_of_poly {f : List Bool → ℝ} {q : Polynomial ℕ}
    (hq : ∀ x, f x ≤ ((q.eval x.length : ℕ) : ℝ)) :
    ¬ ∀ k N : ℕ, ∃ x : List Bool, N ≤ x.length ∧ (x.length : ℝ) ^ k < f x := by
  intro h
  obtain ⟨x, hx, hlt⟩ := h (q.natDegree + 1) (q.eval 1 + 1)
  have hle : q.eval x.length ≤ x.length ^ (q.natDegree + 1) :=
    PVNP.SATTarget.eval_le_pow_succ q hx
  have hle' : ((q.eval x.length : ℕ) : ℝ) ≤ (x.length : ℝ) ^ (q.natDegree + 1) := by
    exact_mod_cast hle
  linarith [hq x]

/-- In a class that charges `P_TM` polynomially, a superpolynomial lower bound for `Lang`
excludes `Lang` from `P_TM`. -/
theorem superpoly_implies_not_mem_P {Dev : Type*} {Decides : Dev → Set (List Bool) → Prop}
    {R : Dev → List Bool → ℝ} (hP : ChargesPPoly Decides R) {Lang : Set (List Bool)}
    (h : SuperpolyResources Decides R Lang) : Lang ∉ P_TM := by
  intro hL
  obtain ⟨D, hD, q, hq⟩ := hP Lang hL
  exact not_superpoly_of_poly hq (h D hD)

/-- **Barrier.** In every device class that charges `P_TM` polynomially, a superpolynomial
resource lower bound for dense SAT proves `P_TM ≠ NP_TM`. -/
theorem superpoly_SAT_implies_P_ne_NP {Dev : Type*} {Decides : Dev → Set (List Bool) → Prop}
    {R : Dev → List Bool → ℝ} (hP : ChargesPPoly Decides R)
    (h : SuperpolyResources Decides R SAT_dense) : P_TM ≠ NP_TM := by
  rw [← CookLevin.Gen.satLowerBound_iff_P_ne_NP]
  exact superpoly_implies_not_mem_P hP h

/-! ### The charged zero-mode torus devices -/

/-- A charged zero-mode device: a machine with a polynomial time bound deciding the
amplitude-bit language `A`. -/
structure ZeroDev where
  /-- The encoder's machine. -/
  M : TM
  /-- Its time bound. -/
  p : Polynomial ℕ
  /-- The amplitude-bit language it decides. -/
  A : Set (List Bool)
  hM : M.Decides A (fun n => p.eval n)

open Classical in
/-- The prepared amplitude: `2` on the amplitude-bit language, `1` off it. -/
noncomputable def ZeroDev.amp (D : ZeroDev) (x : List Bool) : ℂ := if x ∈ D.A then 2 else 1

/-- The exact frozen trajectory of input `x`. -/
noncomputable def ZeroDev.run (L κ β γ : ℝ) (D : ZeroDev) (x : List Bool) : ℝ → ℓ2 :=
  zeroMode L κ β γ (D.amp x)

/-- The device decides `Lang` with margin `3/(2L)` around the threshold `5/(2L)` at time `1`. -/
def ZDecides (L κ β γ : ℝ) (D : ZeroDev) (Lang : Set (List Bool)) : Prop :=
  ∀ x, (x ∈ Lang → 5 / (2 * L) + 3 / (2 * L) ≤ Jdet L (detector L) (D.run L κ β γ x 1)) ∧
    (x ∉ Lang → Jdet L (detector L) (D.run L κ β γ x 1) ≤ 5 / (2 * L) - 3 / (2 * L))

/-- The charged resource: machine time bound, evolution time, curvature budget, prepared mass
and inverse margin. -/
noncomputable def ZeroDev.res (L κ β γ : ℝ) (D : ZeroDev) (x : List Bool) : ℝ :=
  ((D.p.eval x.length : ℕ) : ℝ) + 1 + (∫ t in (0 : ℝ)..1, ‖Dc L (D.run L κ β γ x t)‖ ^ 2) +
    mass L (D.run L κ β γ x 0) + (3 / (2 * L))⁻¹

variable {L κ β γ : ℝ}

theorem ZeroDev.isSolution (hL : 0 < L) (D : ZeroDev) (x : List Bool) :
    IsSolution L κ β γ (D.run L κ β γ x) :=
  zeroMode_isSolution hL _

open Classical in
theorem ZeroDev.Jdet_run (hL : 0 < L) (D : ZeroDev) (x : List Bool) (t : ℝ) :
    Jdet L (detector L) (D.run L κ β γ x t) = if x ∈ D.A then 4 / L else 1 / L := by
  classical
  rw [ZeroDev.run, Jdet_zeroMode_detector hL, ZeroDev.amp]
  split_ifs <;> norm_num

/-- **A zero-mode device decides exactly its amplitude-bit language.** -/
theorem zdecides_iff (hL : 0 < L) (D : ZeroDev) (Lang : Set (List Bool)) :
    ZDecides L κ β γ D Lang ↔ D.A = Lang := by
  have e1 : 5 / (2 * L) + 3 / (2 * L) = 4 / L := by field_simp; ring
  have e2 : 5 / (2 * L) - 3 / (2 * L) = 1 / L := by field_simp; ring
  have hlt : 1 / L < 4 / L := by gcongr; norm_num
  constructor
  · intro h
    ext x
    have hx := h x
    rw [D.Jdet_run hL, e1, e2] at hx
    by_cases hA : x ∈ D.A
    · rw [if_pos hA] at hx
      refine ⟨fun _ => ?_, fun _ => hA⟩
      by_contra hn
      have := hx.2 hn
      linarith
    · rw [if_neg hA] at hx
      refine ⟨fun h' => absurd h' hA, fun hLang => ?_⟩
      exact absurd (hx.1 hLang) (not_le.mpr hlt)
  · rintro rfl x
    rw [D.Jdet_run hL, e1, e2]
    exact ⟨fun hx => by simp [hx], fun hx => by simp [hx]⟩

/-- **The charged resource of a zero-mode device is polynomial.** -/
theorem ZeroDev.res_le (hL : 0 < L) (D : ZeroDev) (x : List Bool) :
    D.res L κ β γ x ≤ (((D.p + Polynomial.C (⌈2 * L / 3⌉₊ + 5)).eval x.length : ℕ) : ℝ) := by
  classical
  have hB : (∫ t in (0 : ℝ)..1, ‖Dc L (D.run L κ β γ x t)‖ ^ 2) = 0 :=
    budget_zeroMode L κ β γ _ 1
  have hM : mass L (D.run L κ β γ x 0) ≤ 4 := by
    rw [ZeroDev.run, mass_zeroMode, ZeroDev.amp]
    split_ifs <;> norm_num
  have hm : (3 / (2 * L))⁻¹ = 2 * L / 3 := by field_simp
  have hc : 2 * L / 3 ≤ (⌈2 * L / 3⌉₊ : ℝ) := Nat.le_ceil _
  unfold ZeroDev.res
  rw [hB, hm]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Nat.cast_add]
  push_cast
  linarith

/-- **The zero-mode class charges `P_TM` polynomially**: every language of `P_TM`, however
large its configuration space, has a zero-mode device with polynomial resources. -/
theorem zero_charges_P (hL : 0 < L) : ChargesPPoly (ZDecides L κ β γ) (ZeroDev.res L κ β γ) := by
  rintro Lang ⟨M, p, hM⟩
  exact ⟨⟨M, p, Lang, hM⟩, (zdecides_iff hL _ _).2 rfl, _, (ZeroDev.res_le hL _)⟩

/-- Every language decided by a zero-mode device is in `P_TM`. -/
theorem zdecides_mem_P (hL : 0 < L) {D : ZeroDev} {Lang : Set (List Bool)}
    (h : ZDecides L κ β γ D Lang) : Lang ∈ P_TM := by
  rw [← (zdecides_iff hL D Lang).1 h]
  exact ⟨D.M, D.p, D.hM⟩

/-- **In the zero-mode class the superpolynomial statement for `Lang` is exactly
`Lang ∉ P_TM`.** -/
theorem zeroSuperpoly_iff (hL : 0 < L) (Lang : Set (List Bool)) :
    SuperpolyResources (ZDecides L κ β γ) (ZeroDev.res L κ β γ) Lang ↔ Lang ∉ P_TM := by
  constructor
  · exact superpoly_implies_not_mem_P (zero_charges_P hL)
  · intro hP D hD
    exact absurd (zdecides_mem_P hL hD) hP

/-- **For dense SAT, the superpolynomial statement in the zero-mode class is equivalent to
`P_TM ≠ NP_TM`.** -/
theorem zeroSuperpoly_SAT_iff (hL : 0 < L) :
    SuperpolyResources (ZDecides L κ β γ) (ZeroDev.res L κ β γ) SAT_dense ↔ P_TM ≠ NP_TM :=
  (zeroSuperpoly_iff hL _).trans CookLevin.Gen.satLowerBound_iff_P_ne_NP

/-- **Every admissible torus class containing the zero-mode devices.** If the zero-mode devices
embed into a device class (`ι`) preserving what they decide, with resources still bounded by a
polynomial, then a superpolynomial resource lower bound for dense SAT over that class proves
`P_TM ≠ NP_TM`. -/
theorem torus_superpoly_implies_P_ne_NP (hL : 0 < L) {Dev : Type*}
    {Decides : Dev → Set (List Bool) → Prop} {R : Dev → List Bool → ℝ} (ι : ZeroDev → Dev)
    (hdec : ∀ D Lang, ZDecides L κ β γ D Lang → Decides (ι D) Lang)
    (hres : ∀ D : ZeroDev, ∃ q : Polynomial ℕ, ∀ x, R (ι D) x ≤ ((q.eval x.length : ℕ) : ℝ))
    (h : SuperpolyResources Decides R SAT_dense) : P_TM ≠ NP_TM := by
  refine superpoly_SAT_implies_P_ne_NP (Decides := Decides) (R := R) ?_ h
  intro Lang hLang
  obtain ⟨D, hD, -⟩ := zero_charges_P (κ := κ) (β := β) (γ := γ) hL Lang hLang
  exact ⟨ι D, hdec D Lang hD, hres D⟩

end PVNP.WCTSATScaling
