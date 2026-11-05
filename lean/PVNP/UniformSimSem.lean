import PVNP.UniformSimProg

/-!
# Milestone 5, part 3: semantics of the simulator — basics, initialization, machine loops

* `trip_def`, `stepP_inl_of`, `stepP_inr_of`: unfolding one round trip of `prog σ`.
* `Agree L d l l'`: `l'` extends `l` and differs from it only on the track `L`.
* `init_trip`: the initialization trip writes the input on the lattice and encoder tracks with the
  heads on cell `0`, and evaluates the optional pair-format guard.
* `sim_loop`: a machine simulated on a folded track runs to its first halting time `t`, one round
  trip per step, changing only its track and adding at most `t` cells.
-/

namespace PVNP.UniformSim

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.PartIITuring PVNP.PartIIUniform

namespace Spec

variable (σ : Spec)

/-! ### One round trip -/

theorem trip_def (i : Ins σ) (l : List (Cell σ)) :
    σ.prog.trip i l = bscan (σ.bwd i) (fscan (σ.fwd i) σ.buf0 l).2
      ((fscan (σ.fwd i) σ.buf0 l).1 ++ (σ.ext i (fscan (σ.fwd i) σ.buf0 l).2).toList) := rfl

theorem stepP_inl_of {i i' : Ins σ} {l : List (Cell σ)}
    (h : σ.next i (σ.prog.trip i l).2 = .inl i') :
    σ.prog.stepP (i, l) = .inl (i', (σ.prog.trip i l).1) := by
  simp only [Prog.stepP, h]

theorem stepP_inr_of {i : Ins σ} {a : Bool} {l : List (Cell σ)}
    (h : σ.next i (σ.prog.trip i l).2 = .inr a) :
    σ.prog.stepP (i, l) = .inr (a, (σ.prog.trip i l).1) := by
  simp only [Prog.stepP, h]

/-- A round trip whose backward pass is the identity and which never extends. -/
theorem trip_fwd (i : Ins σ) (hb : ∀ b a, σ.bwd i b a = (a, b)) (he : ∀ b, σ.ext i b = none)
    (l : List (Cell σ)) :
    σ.prog.trip i l = fscan (σ.fwd i) σ.buf0 l := by
  rw [trip_def, he]
  simp only [Option.toList_none, List.append_nil]
  have : ∀ (b : Buf σ) (l' : List (Cell σ)), bscan (σ.bwd i) b l' = (l', b) := by
    intro b l'
    induction l' generalizing b with
    | nil => rfl
    | cons a l' ih => simp only [bscan, ih, hb]
  rw [this]

end Spec

/-! ### Agreement off a track -/

/-- `l'` extends `l` and differs from it (and, beyond its end, from `d`) only on the track `L`. -/
def Agree {C T : Type} (L : Lens C T) (d : C) (l l' : List C) : Prop :=
  l.length ≤ l'.length ∧ ∀ (j : ℕ) (hj : j < l'.length), l'[j] = L.set (L.get l'[j]) (l.getD j d)

theorem Agree.refl {C T : Type} (L : Lens C T) (d : C) (l : List C) : Agree L d l l := by
  refine ⟨le_rfl, fun j hj => ?_⟩
  rw [List.getD_eq_getElem _ _ hj, L.set_get]

theorem Agree.trans {C T : Type} {L : Lens C T} {d : C} {l l' l'' : List C}
    (h : Agree L d l l') (h' : Agree L d l' l'') : Agree L d l l'' := by
  have h1 := h.1
  refine ⟨h1.trans h'.1, fun j hj => ?_⟩
  have e := h'.2 j hj
  by_cases hj' : j < l'.length
  · rw [List.getD_eq_getElem _ _ hj', h.2 j hj', L.set_set] at e
    exact e
  · rw [List.getD_eq_default _ _ (by omega)] at e
    rw [List.getD_eq_default _ _ (by omega)]
    exact e

namespace Spec

variable (σ : Spec)

/-! ### Initialization -/

/-- The cells written by the initialization trip. -/
def initCell (x : List Bool) (j : ℕ) : Cell σ :=
  {σ.dflt with
    inp := x[j]?
    fst := decide (j = 0)
    lat := ⟨inSym σ.ML x[j]?, σ.ML.blank, if j = 0 then some true else none, none⟩
    enc := ⟨inSym σ.ME x[j]?, σ.ME.blank, if j = 0 then some true else none, none⟩}

theorem init_fbuf (x : List Bool) :
    ∀ j ≤ x.length, (fscan (σ.fwd .init) σ.buf0 ((x.map σ.lift).take j)).2 =
      {σ.buf0 with f1 := decide (0 < j), g := PS.run .tag (x.take j)} := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [fscan_take_succ _ _ _ j (by simp; omega), ih (by omega)]
    have hx : (x.map σ.lift)[j]'(by simp; omega) = σ.lift (x[j]'(by omega)) := by simp
    rw [hx]
    simp only [fwd, lift, gStep]
    rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some, PS.run_append]
    simp [PS.run]

theorem init_trip (x : List Bool) :
    (σ.prog.trip .init (x.map σ.lift)).1 = (List.range (max x.length 1)).map (σ.initCell x) ∧
      (σ.prog.trip .init (x.map σ.lift)).2.g = PS.run .tag x := by
  have hb : ∀ b a, σ.bwd .init b a = (a, b) := fun _ _ => rfl
  rw [trip_def]
  have hfin : (fscan (σ.fwd .init) σ.buf0 (x.map σ.lift)).2 =
      {σ.buf0 with f1 := decide (0 < x.length), g := PS.run .tag x} := by
    rw [fscan_snd_eq_take, init_fbuf σ x (x.map σ.lift).length (by simp)]
    simp
  have hbs : ∀ (b : Buf σ) (l' : List (Cell σ)), bscan (σ.bwd .init) b l' = (l', b) := by
    intro b l'
    induction l' generalizing b with
    | nil => rfl
    | cons a l' ih => simp only [bscan, ih, hb]
  rw [hbs, hfin]
  refine ⟨?_, rfl⟩
  cases x with
  | nil =>
    simp [fscan, ext, initCell, inSym]
    rfl
  | cons a x' =>
    have hne : ∀ g : PS, σ.ext .init {σ.buf0 with f1 := decide (0 < (a :: x').length), g := g} =
        none := fun g => by simp [ext]
    rw [hne, Option.toList_none, List.append_nil]
    apply List.ext_getElem
    · simp [fscan_length]
    · intro j h1 h2
      simp only [List.length_map, List.length_range] at h2
      have hj : j < (a :: x').length := by simp at h2 ⊢; omega
      rw [List.getElem_map, List.getElem_range]
      rw [fscan_getElem _ _ _ j (by simpa using hj), init_fbuf σ (a :: x') j hj.le]
      simp only [List.getElem_map, fwd, lift, initCell, List.getElem?_eq_getElem hj]
      by_cases hj0 : j = 0
      · subst hj0; simp
      · simp [hj0, Nat.pos_of_ne_zero hj0]

/-! ### Simulated machines -/

theorem haltingQ_iff (M : MTM) (q : M.Q) : haltingQ M q = true ↔ M.Halting q := by
  simp [haltingQ, MTM.Halting]

theorem run_step_comm (M : MTM) (c : M.Cfg) (s : ℕ) : M.run (M.step c) s = M.run c (s + 1) := by
  rw [show s + 1 = 1 + s by ring, MTM.run_add]; rfl

/-- **The simulated machine runs to its first halting time.** -/
theorem sim_loop (M : MTM) (L : Lens (Cell σ) (FCell M.Γ)) (LB : Lens (Buf σ) (SimBuf M.Q))
    (simI : M.Q → Ins σ) (exitI : Ins σ)
    (hfwd : ∀ q, σ.fwd (simI q) = gF M L LB q)
    (hbwd : ∀ q, σ.bwd (simI q) = gB M L LB)
    (hext : ∀ q, σ.ext (simI q) = gE M L LB σ.dflt)
    (hb0 : LB.get σ.buf0 = SimBuf.start M.Q)
    (hnext : ∀ q b, σ.next (simI q) b =
      match (LB.get b).nq with
      | some q' => if haltingQ M q' then .inl exitI else .inl (simI q')
      | none => .inl exitI) :
    ∀ (t : ℕ) (c : M.Cfg) (l : List (Cell σ)), FRep L.get M.blank l c.tape c.head →
      (∀ s < t, haltingQ M (M.run c s).q = false) → haltingQ M (M.run c t).q = true → 0 < t →
      ∃ l', RN σ.prog (simI c.q, l) (exitI, l') t ∧
        FRep L.get M.blank l' (M.run c t).tape (M.run c t).head ∧ Agree L σ.dflt l l' ∧
        l'.length ≤ l.length + t := by
  intro t
  induction t with
  | zero => intro c l _ _ _ h; omega
  | succ t ih =>
    intro c l hrep hnh hh _
    have htrip : σ.prog.trip (simI c.q) l = simTrip M L LB σ.dflt c.q σ.buf0 l := by
      rw [trip_def, hfwd, hbwd, hext]; rfl
    obtain ⟨hrep1, hnq, hlo, hhi, hcells⟩ := simTrip_spec M L LB σ.dflt c.q σ.buf0 hb0 l
      c.tape c.head hrep
    have hc : (⟨c.tape, c.head, c.q⟩ : M.Cfg) = c := rfl
    rw [hc] at hrep1 hnq
    set l1 := (simTrip M L LB σ.dflt c.q σ.buf0 l).1 with hl1
    have hag1 : Agree L σ.dflt l l1 := ⟨hlo, hcells⟩
    have hrun1 : M.run c 1 = M.step c := rfl
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · subst ht0
      have hn : σ.next (simI c.q) (σ.prog.trip (simI c.q) l).2 = .inl exitI := by
        rw [hnext, htrip, hnq]
        simp only
        rw [← hrun1, if_pos hh]
      refine ⟨l1, ?_, ?_, hag1, hhi⟩
      · have := RN.single (σ.stepP_inl_of hn)
        rwa [htrip] at this
      · rw [hrun1]; exact hrep1
    · have hnh1 : haltingQ M (M.step c).q = false := by rw [← hrun1]; exact hnh 1 (by omega)
      have hn : σ.next (simI c.q) (σ.prog.trip (simI c.q) l).2 = .inl (simI (M.step c).q) := by
        rw [hnext, htrip, hnq]
        simp only
        rw [hnh1]; rfl
      obtain ⟨l', hrn, hrep', hag', hlen'⟩ := ih (M.step c) l1 hrep1
        (fun s hs => by rw [run_step_comm]; exact hnh (s + 1) (by omega))
        (by rw [run_step_comm]; exact hh) ht0
      refine ⟨l', ?_, ?_, hag1.trans hag', by omega⟩
      · have h1 := σ.stepP_inl_of hn
        rw [htrip] at h1
        exact RN.step h1 hrn
      · rw [run_step_comm] at hrep'; exact hrep'

end Spec

end PVNP.UniformSim
