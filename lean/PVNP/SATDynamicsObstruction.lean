import PVNP.SATFalseWell
import PVNP.CookLevinUniform

/-!
# I-3: what a physical SAT evolution can and cannot do

The static criterion is proved: with the sign-blind interwoven energy `E^{sb}_F`, a formula is
satisfiable iff the ground energy is `0`, unsatisfiable iff it is at least `1/8`, and the sign
readout of any unit field below `1/8` is a satisfying assignment (`InterwovenSAT`). I-3 asks for
the missing dynamic link: a physical evolution from a prepared state to the readout region.

**1. Energy-descent dynamics are trapped** (`energy_monotone_trapped`). `SATFalseWell` gives a
satisfiable formula `trapFormula` whose energy is at least `1 + (s₀ + s₁ + s₂)/2` on the box of
unit fields with all three positive-literal scores `sᵢ ≤ 1/8`. Hence **every** continuous evolution
of unit fields along which `E^{sb}` does not increase, started in that box below energy `17/16`,
stays in the box forever with energy `≥ 1`: to leave the box it must cross a point where the
largest score equals `1/8`, where the energy is at least `17/16`. This covers every gradient flow
of `E^{sb}`, every damped or dissipative evolution with Lyapunov function `E^{sb}`, at any speed.
The readout `E^{sb} < 1/8` never fires although the formula is satisfiable.

**2. Every formula-independent corner preparation fails** (`corner_trapped`,
`no_corner_preparation_decides`). Flipping the polarity of a variable's literals and the sign of
its field component preserves the energy (`energySB_flip`) and satisfiability (`sat_flipF`).
So for every binary corner `a` there is a satisfiable formula (`flipF a trapFormula`) whose false
well sits at the corner field `fieldOf a`: an energy-nonincreasing evolution prepared at `fieldOf a`
never reaches the readout region.

**3. A correct end-to-end device exists, at exponential cost** (`sat_iff_corner_sweep`,
`corner_sweep_card`). Preparing each of the `2^n` corner fields over the `n = nvar F` variables of
`F` and reading `E^{sb} < 1/8` decides SAT for every formula. The encoder
reads `F` but presupposes nothing about its satisfiability.

**4. The efficiency question is classical** (`efficient_device_and_simulation_imply_P_eq_NP`).
A physical SAT decider with polynomially bounded resources, together with a resource-preserving
Turing simulation of the device class (claim I-11), would give `P_TM = NP_TM`.

No statement here is a lower bound for all physical or classical SAT algorithms.
-/

open Filter Topology

namespace PVNP.SATDynamics

open PVNP.PartIPsiSat PVNP.InterwovenSAT PVNP.SATFalseWell PVNP.Discrete

/-! ### 1. The trapping theorem -/

/-- For a unit field the positive-literal score is `(1 + Re ψᵢ)/2`. -/
theorem sPos_eq {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (i : ℕ) :
    sPos (phases Ψ) i = (1 + (Ψ i).re) / 2 := by
  unfold sPos
  rw [cos_phase hΨ i]

/-- The trap box: all three positive-literal scores at most `1/8`. -/
def InBox (Ψ : ℕ → ℂ) : Prop :=
  sPos (phases Ψ) 0 ≤ 1 / 8 ∧ sPos (phases Ψ) 1 ≤ 1 / 8 ∧ sPos (phases Ψ) 2 ≤ 1 / 8

theorem energy_lower_in_box {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) {Ψ : ℕ → ℂ}
    (hΨ : Admissible Ψ) (hb : InBox Ψ) :
    1 + (sPos (phases Ψ) 0 + sPos (phases Ψ) 1 + sPos (phases Ψ) 2) / 2 ≤
      energySB trapFormula lam mu Ψ := by
  have h := trapEnergy_local_lower (sPos_nonneg _ 0) (sPos_nonneg _ 1) (sPos_nonneg _ 2)
    hb.1 hb.2.1 hb.2.2
  rw [← Elogic_trapFormula] at h
  have h2 := energySB_ge_Elog trapFormula hlam hmu hΨ
  unfold Elog at h2
  linarith

/-- **Energy-descent evolutions are trapped by the false well.** Let `Ψ(t)` be any evolution of
unit fields whose first three components depend continuously on `t` and along which the
sign-blind energy of `trapFormula` does not increase for `t ≥ 0`. If `Ψ(0)` lies in the trap box
with energy below `17/16`, then for every `t ≥ 0` the field stays in the box and its energy is at
least `1`; in particular it never reaches the readout region `E^{sb} < 1/8`, although
`trapFormula` is satisfiable. -/
theorem energy_monotone_trapped {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t)) (hc0 : Continuous fun t => Ψ t 0)
    (hc1 : Continuous fun t => Ψ t 1) (hc2 : Continuous fun t => Ψ t 2)
    (hmono : AntitoneOn (fun t => energySB trapFormula lam mu (Ψ t)) (Set.Ici 0))
    (hb0 : InBox (Ψ 0)) (hE0 : energySB trapFormula lam mu (Ψ 0) < 17 / 16) :
    ∀ t, 0 ≤ t → InBox (Ψ t) ∧ 1 ≤ energySB trapFormula lam mu (Ψ t) := by
  set s : ℕ → ℝ → ℝ := fun i t => (1 + (Ψ t i).re) / 2 with hs_def
  have hs : ∀ i t, sPos (phases (Ψ t)) i = s i t := fun i t => sPos_eq (hadm t) i
  have hsnn : ∀ i t, 0 ≤ s i t := fun i t => by rw [← hs]; exact sPos_nonneg _ i
  set m : ℝ → ℝ := fun t => max (max (s 0 t) (s 1 t)) (s 2 t) with hm_def
  have hcs : ∀ i, Continuous (fun t => Ψ t i) → Continuous (s i) := fun i h =>
    (continuous_const.add (Complex.continuous_re.comp h)).div_const 2
  have hmc : Continuous m := ((hcs 0 hc0).max (hcs 1 hc1)).max (hcs 2 hc2)
  have hbox_iff : ∀ t, InBox (Ψ t) ↔ m t ≤ 1 / 8 := fun t => by
    simp only [InBox, hs, hm_def, max_le_iff, and_assoc]
  have hlow : ∀ t, InBox (Ψ t) →
      1 + (s 0 t + s 1 t + s 2 t) / 2 ≤ energySB trapFormula lam mu (Ψ t) := fun t hb => by
    have h := energy_lower_in_box hlam hmu (hadm t) hb
    rwa [hs, hs, hs] at h
  have hm0 : m 0 < 1 / 8 := by
    have h := hlow 0 hb0
    have h0 := hsnn 0 0
    have h1 := hsnn 1 0
    have h2 := hsnn 2 0
    simp only [hm_def, max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
  intro t ht
  have hmt : m t ≤ 1 / 8 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨τ, hτ, hmτ⟩ := intermediate_value_Icc ht hmc.continuousOn ⟨hm0.le, hgt.le⟩
    have hbτ : InBox (Ψ τ) := (hbox_iff τ).2 hmτ.le
    have hl := hlow τ hbτ
    have hsum : 1 / 8 ≤ s 0 τ + s 1 τ + s 2 τ := by
      rw [← hmτ]
      have h0 := hsnn 0 τ
      have h1 := hsnn 1 τ
      have h2 := hsnn 2 τ
      exact max_le (max_le (by linarith) (by linarith)) (by linarith)
    have hEτ : energySB trapFormula lam mu (Ψ τ) ≤ energySB trapFormula lam mu (Ψ 0) :=
      hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ.1) hτ.1
    linarith
  have hb := (hbox_iff t).2 hmt
  refine ⟨hb, ?_⟩
  have := hlow t hb
  have h0 := hsnn 0 t
  have h1 := hsnn 1 t
  have h2 := hsnn 2 t
  linarith

/-- The all-false corner lies in the trap box with energy `1`. -/
theorem false_corner_in_box : InBox (fieldOf fun _ => false) := by
  have h : ∀ i, sPos (phases (fieldOf fun _ => false)) i = 0 := fun i => by
    rw [sPos_eq (fieldOf_admissible _) i]
    simp [fieldOf]
  refine ⟨?_, ?_, ?_⟩ <;> rw [h] <;> norm_num

theorem false_corner_energy {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    energySB trapFormula lam mu (fieldOf fun _ => false) = 1 :=
  (signblind_false_local_well hlam hmu).2.1

/-! ### 2. Sign-flip symmetry and corner preparations -/

/-- Flip the polarity of the literals of the variables with `a v = true`. -/
def flipLit (a : ℕ → Bool) (l : Lit) : Lit := ⟨l.v, xor l.pos (a l.v)⟩

/-- Flip a formula. -/
def flipF (a : ℕ → Bool) (F : CNF3) : CNF3 := F.map fun c => fun k => flipLit a (c k)

/-- Flip the sign of the field components of the variables with `a i = true`. -/
noncomputable def flipField (a : ℕ → Bool) (Ψ : ℕ → ℂ) : ℕ → ℂ :=
  fun i => if a i then -Ψ i else Ψ i

theorem flipLit_flipLit (a : ℕ → Bool) (l : Lit) : flipLit a (flipLit a l) = l := by
  cases l with
  | mk v pos => simp [flipLit]

theorem flipF_flipF (a : ℕ → Bool) (F : CNF3) : flipF a (flipF a F) = F := by
  unfold flipF
  rw [List.map_map]
  conv_rhs => rw [← List.map_id F]
  refine List.map_congr_left fun c _ => ?_
  funext k
  simp [flipLit_flipLit]

theorem flipField_flipField (a : ℕ → Bool) (Ψ : ℕ → ℂ) : flipField a (flipField a Ψ) = Ψ := by
  funext i
  unfold flipField
  split_ifs <;> simp

theorem admissible_flipField {a : ℕ → Bool} {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) :
    Admissible (flipField a Ψ) := fun i => by
  unfold flipField
  split_ifs
  · rw [norm_neg]; exact hΨ i
  · exact hΨ i

theorem sq_flipField (a : ℕ → Bool) (Ψ : ℕ → ℂ) :
    InterwovenSAT.sq (flipField a Ψ) = InterwovenSAT.sq Ψ := by
  funext i
  unfold InterwovenSAT.sq flipField
  split_ifs <;> ring

theorem score_flip {a : ℕ → Bool} {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (l : Lit) :
    score (phases (flipField a Ψ)) (flipLit a l) = score (phases Ψ) l := by
  unfold score
  have h1 := cos_phase (admissible_flipField (a := a) hΨ) l.v
  have h2 := cos_phase hΨ l.v
  simp only [flipLit] at h1 ⊢
  rw [h1, h2]
  unfold flipField eta
  cases hp : l.pos <;> cases ha : a l.v <;> simp

theorem clausePen_flip {a : ℕ → Bool} {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (c : Clause3) :
    clausePen (phases (flipField a Ψ)) (fun k => flipLit a (c k)) = clausePen (phases Ψ) c := by
  unfold clausePen
  exact Finset.prod_congr rfl fun k _ => by rw [score_flip hΨ]

theorem Elog_flip {a : ℕ → Bool} {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (F : CNF3) :
    Elog (flipF a F) (flipField a Ψ) = Elog F Ψ := by
  unfold Elog Elogic flipF
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => clausePen_flip hΨ c

theorem edges_flipF (a : ℕ → Bool) (F : CNF3) : edges (flipF a F) = edges F := by
  unfold edges flipF
  rw [List.flatMap_map]
  rfl

theorem hyperedges_flipF (a : ℕ → Bool) (F : CNF3) : hyperedges (flipF a F) = hyperedges F := by
  unfold hyperedges flipF
  rw [List.map_map]
  rfl

theorem vars_flipF (a : ℕ → Bool) (F : CNF3) : vars (flipF a F) = vars F := by
  unfold vars
  rw [hyperedges_flipF]

theorem glap_flipF (a : ℕ → Bool) (F : CNF3) (Ψ : ℕ → ℂ) (v : ℕ) :
    glap (flipF a F) Ψ v = glap F Ψ v := by
  unfold glap
  rw [edges_flipF]

/-- **Sign-flip symmetry of the sign-blind energy.** -/
theorem energySB_flip {a : ℕ → Bool} {Ψ : ℕ → ℂ} (hΨ : Admissible Ψ) (F : CNF3) (lam mu : ℝ) :
    energySB (flipF a F) lam mu (flipField a Ψ) = energySB F lam mu Ψ := by
  unfold energySB
  rw [Elog_flip hΨ, sq_flipField]
  unfold Ecoup Ecurv
  rw [edges_flipF, vars_flipF]
  simp only [glap_flipF]

theorem litVal_flip (a b : ℕ → Bool) (l : Lit) :
    litVal (fun v => xor (b v) (a v)) (flipLit a l) = litVal b l := by
  cases l with
  | mk v pos => cases pos <;> cases hb : b v <;> cases ha : a v <;> simp [litVal, flipLit, hb, ha]

/-- Flipping preserves satisfiability. -/
theorem sat_flipF (a : ℕ → Bool) (F : CNF3) : Sat (flipF a F) ↔ Sat F := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun v => xor (b v) (a v), fun c hc => ?_⟩
    have h := hb (fun k => flipLit a (c k)) (List.mem_map.2 ⟨c, hc, rfl⟩)
    have e : ∀ k, litVal (fun v => xor (b v) (a v)) (c k) = litVal b (flipLit a (c k)) :=
      fun k => by
        have := litVal_flip a b (flipLit a (c k))
        rwa [flipLit_flipLit] at this
    simp only [clauseVal] at h ⊢
    rw [e, e, e]
    exact h
  · rintro ⟨b, hb⟩
    refine ⟨fun v => xor (b v) (a v), fun c' hc' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    have h := hb c hc
    simp only [clauseVal] at h ⊢
    rw [litVal_flip, litVal_flip, litVal_flip]
    exact h

theorem flipField_false_corner (a : ℕ → Bool) :
    flipField a (fieldOf fun _ => false) = fieldOf a := by
  funext i
  unfold flipField fieldOf
  cases a i <;> simp

/-- **Every corner preparation is trapped on some satisfiable formula.** For a binary corner `a`,
the formula `flipF a trapFormula` is satisfiable, and every evolution of unit fields prepared at
`fieldOf a`, continuous in its first three components and with nonincreasing sign-blind energy,
keeps energy at least `1` for all `t ≥ 0`. -/
theorem corner_trapped (a : ℕ → Bool) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {Ψ : ℝ → ℕ → ℂ} (hadm : ∀ t, Admissible (Ψ t)) (hc : ∀ i, Continuous fun t => Ψ t i)
    (hmono : AntitoneOn (fun t => energySB (flipF a trapFormula) lam mu (Ψ t)) (Set.Ici 0))
    (h0 : Ψ 0 = fieldOf a) :
    Sat (flipF a trapFormula) ∧ ∀ t, 0 ≤ t → 1 ≤ energySB (flipF a trapFormula) lam mu (Ψ t) := by
  refine ⟨(sat_flipF a _).2 trapFormula_sat, fun t ht => ?_⟩
  set Φ : ℝ → ℕ → ℂ := fun t => flipField a (Ψ t) with hΦ
  have hE : ∀ t, energySB trapFormula lam mu (Φ t) = energySB (flipF a trapFormula) lam mu (Ψ t) :=
    fun t => by
      have := energySB_flip (a := a) (admissible_flipField (a := a) (hadm t)) trapFormula lam mu
      rw [flipField_flipField] at this
      exact this.symm
  have hΦc : ∀ i, Continuous fun t => Φ t i := fun i => by
    simp only [hΦ, flipField]
    split_ifs
    · exact (hc i).neg
    · exact hc i
  have hΦ0 : flipField a (Ψ 0) = fieldOf fun _ => false := by
    rw [h0, ← flipField_false_corner a, flipField_flipField]
  have hmono' : AntitoneOn (fun t => energySB trapFormula lam mu (Φ t)) (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [hE]
    exact hmono hx hy hxy
  have htrap := energy_monotone_trapped hlam hmu (fun t => admissible_flipField (hadm t))
    (hΦc 0) (hΦc 1) (hΦc 2) hmono' (by rw [hΦ0]; exact false_corner_in_box)
    (by rw [hΦ0, false_corner_energy hlam hmu]; norm_num) t ht
  rw [← hE]
  exact htrap.2

/-- **No formula-independent corner preparation yields a SAT decider by energy descent.** For
every corner `a` there is a satisfiable formula on which every energy-nonincreasing evolution
prepared at `fieldOf a` never enters the readout region `E^{sb} < 1/8`. -/
theorem no_corner_preparation_decides (a : ℕ → Bool) {lam mu : ℝ} (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu) :
    ∃ F, Sat F ∧ ∀ Ψ : ℝ → ℕ → ℂ, (∀ t, Admissible (Ψ t)) → (∀ i, Continuous fun t => Ψ t i) →
      AntitoneOn (fun t => energySB F lam mu (Ψ t)) (Set.Ici 0) → Ψ 0 = fieldOf a →
      ∀ t, 0 ≤ t → ¬ energySB F lam mu (Ψ t) < 1 / 8 := by
  refine ⟨flipF a trapFormula, (sat_flipF a _).2 trapFormula_sat, fun Ψ hadm hc hmono h0 t ht => ?_⟩
  have := (corner_trapped a hlam hmu hadm hc hmono h0).2 t ht
  linarith

/-! ### 3. A correct end-to-end device at exponential cost -/

/-- One more than the largest variable index of `F`. -/
def nvar (F : CNF3) : ℕ := ((F.flatMap fun c => [(c 0).v, (c 1).v, (c 2).v]).foldr max 0) + 1

theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem var_lt_nvar {F : CNF3} {c : Clause3} (hc : c ∈ F) (k : Fin 3) : (c k).v < nvar F := by
  unfold nvar
  have hmem : (c k).v ∈ F.flatMap fun c => [(c 0).v, (c 1).v, (c 2).v] := by
    refine List.mem_flatMap.2 ⟨c, hc, ?_⟩
    fin_cases k <;> simp
  exact Nat.lt_succ_of_le (le_foldr_max hmem)

/-- Extend an assignment of the first `n` variables by `false`. -/
def ext {n : ℕ} (a : Fin n → Bool) : ℕ → Bool := fun i => if h : i < n then a ⟨i, h⟩ else false

/-- **The corner sweep decides SAT.** For every formula and all `λ, μ ≥ 0`, `F` is satisfiable
iff one of the `2^{nvar F}` corner fields over its variables reads `E^{sb} < 1/8`. -/
theorem sat_iff_corner_sweep (F : CNF3) {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    Sat F ↔ ∃ a : Fin (nvar F) → Bool, energySB F lam mu (fieldOf (ext a)) < 1 / 8 := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun i => b i, ?_⟩
    rw [energySB_fieldOf, (Elogic_phaseOf_eq_zero_iff _ F).2]
    · norm_num
    · intro c hc
      have h := hb c hc
      have e : ∀ k, litVal (ext fun i : Fin (nvar F) => b i) (c k) = litVal b (c k) := fun k => by
        unfold litVal ext
        rw [dif_pos (var_lt_nvar hc k)]
      simp only [clauseVal] at h ⊢
      rw [e, e, e]
      exact h
  · rintro ⟨a, ha⟩
    exact (sat_iff_energySB_lt_eighth F hlam hmu).2 ⟨_, fieldOf_admissible _, ha⟩

/-- The sweep prepares `2^{nvar F}` corner fields. -/
theorem corner_sweep_card (F : CNF3) : Fintype.card (Fin (nvar F) → Bool) = 2 ^ nvar F := by
  simp

/-! ### 4. The efficiency question is classical -/

/-- **An efficient physical SAT decider plus a resource-preserving simulation would give
`P_TM = NP_TM`.** `Decides D L` and the resource `R D x` describe any device class; `hsim` is the
missing simulation theorem of I-11 for that class. -/
theorem efficient_device_and_simulation_imply_P_eq_NP {Dev : Type*}
    (Decides : Dev → Set (List Bool) → Prop) (R : Dev → List Bool → ℝ)
    (hsim : ∀ D Lang, Decides D Lang →
      (∃ q : Polynomial ℕ, ∀ x, R D x ≤ ((q.eval x.length : ℕ) : ℝ)) → Lang ∈ P_TM)
    (hdev : ∃ D, Decides D SATV.SAT_dense ∧
      ∃ q : Polynomial ℕ, ∀ x, R D x ≤ ((q.eval x.length : ℕ) : ℝ)) :
    P_TM = NP_TM := by
  obtain ⟨D, hD, hq⟩ := hdev
  exact CookLevin.Gen.SAT_mem_P_TM_iff.1 (hsim D _ hD hq)

end PVNP.SATDynamics
