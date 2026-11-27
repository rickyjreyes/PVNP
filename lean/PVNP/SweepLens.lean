import PVNP.SweepCompose

/-!
# Track lenses: verified alphabet translations for sweep programs

The verified primitives use different cell alphabets. A **track lens** `ℓ : TrackLens E D` views
a multi-track alphabet `E` through the tracks of `D`. It has `get : E → D` and
`put : E → D → E` with `get (put x d) = d`. Lifting a program `A` over `D` along `ℓ`,
`viaLens A ℓ z lift`, runs `A` on the viewed tracks and leaves every other track as it was.

* `fscan_lens`, `bscan_lens`: the lifted scans are the original scans on the viewed tracks,
  written back with `put`.
* `trip_lens_view`, `trip_lens_buf`, `tripCost_lens`: the lifted trip has the original trip's
  view, buffer and exact cost.
* `stepP_lens`: the lifted step is the original step on the view.
* `reachFirst_lens`, **transport**: a first arrival of `A` from the view `l.map get` lifts to a
  first arrival of the lifted program from `l`. The cost is the same and the output view is the
  same.
* `frame_trip`, `reachFirst_lens_frame`, **frame preservation**: suppose `A` never extends the
  tape and a second lens `ℓ₂` is independent of `ℓ`, meaning `ℓ₂.get (ℓ.put x d) = ℓ₂.get x`.
  Then the lifted program leaves the `ℓ₂`-tracks unchanged.

Programs over different alphabets can therefore run on a common track alphabet and be composed
with `ProgOn.seq_reach`. A later stage reads earlier outputs directly from shared tracks, with no
copying program.
-/

namespace PVNP.Discrete.Sweep

/-- A track view of the alphabet `E` through `D`. -/
structure TrackLens (E D : Type) where
  get : E → D
  put : E → D → E
  get_put : ∀ x d, get (put x d) = d

namespace TrackLens

variable {E D : Type} (ℓ : TrackLens E D)

theorem map_get_zipWith : ∀ (l : List E) (m : List D), m.length = l.length →
    (List.zipWith ℓ.put l m).map ℓ.get = m
  | [], [], _ => rfl
  | x :: l, d :: m, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, ℓ.get_put,
      map_get_zipWith l m (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem length_zipWith (l : List E) (m : List D) (h : m.length = l.length) :
    (List.zipWith ℓ.put l m).length = l.length := by
  rw [List.length_zipWith, h, min_self]

/-- `ℓ₂` reads tracks that `ℓ` does not write. -/
def Indep {D₂ : Type} (ℓ₂ : TrackLens E D₂) : Prop := ∀ x d, ℓ₂.get (ℓ.put x d) = ℓ₂.get x

theorem frame_zipWith {D₂ : Type} {ℓ₂ : TrackLens E D₂} (hi : ℓ.Indep ℓ₂) :
    ∀ (l : List E) (m : List D), m.length = l.length →
      (List.zipWith ℓ.put l m).map ℓ₂.get = l.map ℓ₂.get
  | [], [], _ => rfl
  | x :: l, d :: m, h => by
    simp only [List.zipWith_cons_cons, List.map_cons, hi x d,
      frame_zipWith hi l m (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

end TrackLens

namespace ProgOn

variable {D E : Type} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

/-- Lift a program along a track lens. Right-end extensions are written into the cell `z`. -/
def viaLens (A : ProgOn D) (ℓ : TrackLens E D) (z : E) (lift' : Bool → E) : ProgOn E where
  I := A.I
  B := A.B
  lift := lift'
  start := A.start
  init := A.init
  fwd i b x := (ℓ.put x (A.fwd i b (ℓ.get x)).1, (A.fwd i b (ℓ.get x)).2)
  ext i b := (A.ext i b).map (ℓ.put z)
  bwd i b x := (ℓ.put x (A.bwd i b (ℓ.get x)).1, (A.bwd i b (ℓ.get x)).2)
  next := A.next

variable (A : ProgOn D) (ℓ : TrackLens E D) (z : E) (lift' : Bool → E)

theorem fscan_lens (i : A.I) : ∀ (b : A.B) (l : List E),
    fscan ((viaLens A ℓ z lift').fwd i) b l =
      (List.zipWith ℓ.put l (fscan (A.fwd i) b (l.map ℓ.get)).1,
        (fscan (A.fwd i) b (l.map ℓ.get)).2)
  | _, [] => rfl
  | b, x :: l => by
    have ih := fscan_lens i (A.fwd i b (ℓ.get x)).2 l
    simp only [fscan, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [show (viaLens A ℓ z lift').fwd i b x =
      (ℓ.put x (A.fwd i b (ℓ.get x)).1, (A.fwd i b (ℓ.get x)).2) from rfl, ih]

theorem bscan_lens (i : A.I) (b : A.B) : ∀ l : List E,
    bscan ((viaLens A ℓ z lift').bwd i) b l =
      (List.zipWith ℓ.put l (bscan (A.bwd i) b (l.map ℓ.get)).1,
        (bscan (A.bwd i) b (l.map ℓ.get)).2)
  | [] => rfl
  | x :: l => by
    have ih := bscan_lens i b l
    simp only [bscan, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    rfl

theorem fpass_lens (i : A.I) (l : List E) :
    (viaLens A ℓ z lift').toProg.fpass i l =
      (List.zipWith ℓ.put l (A.toProg.fpass i (l.map ℓ.get)).1,
        (A.toProg.fpass i (l.map ℓ.get)).2) :=
  fscan_lens A ℓ z lift' i (A.init i) l

theorem mid_lens_view (i : A.I) (l : List E) :
    ((viaLens A ℓ z lift').toProg.mid i l).map ℓ.get = A.toProg.mid i (l.map ℓ.get) := by
  unfold Prog.mid
  rw [fpass_lens, List.map_append]
  have hlen : (A.toProg.fpass i (l.map ℓ.get)).1.length = l.length := by
    unfold Prog.fpass; rw [fscan_length, List.length_map]
  rw [ℓ.map_get_zipWith _ _ hlen]
  congr 1
  show ((A.ext i (A.toProg.fpass i (l.map ℓ.get)).2).map (ℓ.put z)).toList.map ℓ.get =
    (A.ext i (A.toProg.fpass i (l.map ℓ.get)).2).toList
  cases A.ext i (A.toProg.fpass i (l.map ℓ.get)).2 <;> simp [ℓ.get_put]

theorem trip_lens (i : A.I) (l : List E) :
    (viaLens A ℓ z lift').toProg.trip i l =
      (List.zipWith ℓ.put ((viaLens A ℓ z lift').toProg.mid i l)
          (A.toProg.trip i (l.map ℓ.get)).1, (A.toProg.trip i (l.map ℓ.get)).2) := by
  have hb : ((viaLens A ℓ z lift').toProg.fpass i l).2 = (A.toProg.fpass i (l.map ℓ.get)).2 := by
    rw [fpass_lens]
  have h := bscan_lens A ℓ z lift' i (A.toProg.fpass i (l.map ℓ.get)).2
    ((viaLens A ℓ z lift').toProg.mid i l)
  rw [mid_lens_view] at h
  show bscan ((viaLens A ℓ z lift').bwd i) ((viaLens A ℓ z lift').toProg.fpass i l).2
    ((viaLens A ℓ z lift').toProg.mid i l) = _
  rw [hb]
  exact h

theorem trip_lens_buf (i : A.I) (l : List E) :
    ((viaLens A ℓ z lift').toProg.trip i l).2 = (A.toProg.trip i (l.map ℓ.get)).2 := by
  rw [trip_lens]

theorem trip_lens_view (i : A.I) (l : List E) :
    ((viaLens A ℓ z lift').toProg.trip i l).1.map ℓ.get = (A.toProg.trip i (l.map ℓ.get)).1 := by
  rw [trip_lens]
  apply ℓ.map_get_zipWith
  have h1 := bscan_length (A.bwd i) (A.toProg.fpass i (l.map ℓ.get)).2
    (A.toProg.mid i (l.map ℓ.get))
  have h2 := congrArg List.length (mid_lens_view A ℓ z lift' i l)
  rw [List.length_map] at h2
  show (bscan (A.bwd i) _ _).1.length = _
  rw [h1, h2]

theorem tripCost_lens (i : A.I) (l : List E) :
    (viaLens A ℓ z lift').toProg.tripCost i l = A.toProg.tripCost i (l.map ℓ.get) := by
  unfold Prog.tripCost
  rw [fpass_lens, List.length_map]
  show 2 * l.length + 2 +
      ((A.ext i (A.toProg.fpass i (l.map ℓ.get)).2).map (ℓ.put z)).toList.length =
    2 * l.length + 2 + (A.ext i (A.toProg.fpass i (l.map ℓ.get)).2).toList.length
  cases A.ext i (A.toProg.fpass i (l.map ℓ.get)).2 <;> rfl

theorem stepP_lens {i j : A.I} {l : List E} {m : List D}
    (h : A.toProg.stepP (i, l.map ℓ.get) = .inl (j, m)) :
    ∃ l', (viaLens A ℓ z lift').toProg.stepP (i, l) = .inl (j, l') ∧ l'.map ℓ.get = m ∧
      l' = ((viaLens A ℓ z lift').toProg.trip i l).1 := by
  obtain ⟨k1, k2⟩ := next_of_stepP h
  refine ⟨((viaLens A ℓ z lift').toProg.trip i l).1, ?_, ?_, rfl⟩
  · have hn : (viaLens A ℓ z lift').toProg.next i ((viaLens A ℓ z lift').toProg.trip i l).2 =
        .inl j := by
      rw [trip_lens_buf]; exact k1
    simp only [Prog.stepP]
    rw [hn]
  · rw [trip_lens_view, k2]

/-- **Transport of first arrivals along a track lens.** -/
theorem reachFirst_lens {e : A.I} {s : A.toProg.I × List A.toProg.D} {m : List A.toProg.D}
    {c : ℕ} (h : ReachFirst A.toProg e s m c) :
    ∀ l : List E, s.2 = l.map ℓ.get →
      ∃ l', ReachFirst (viaLens A ℓ z lift').toProg e (s.1, l) l' c ∧ l'.map ℓ.get = m := by
  induction h with
  | @last s m hs =>
    intro l hl
    obtain ⟨i, l0⟩ := s
    simp only at hl
    subst hl
    obtain ⟨l', h1, h2, _⟩ := stepP_lens A ℓ z lift' hs
    refine ⟨l', ?_, h2⟩
    have h3 := ReachFirst.last (P := (viaLens A ℓ z lift').toProg) (e := e) h1
    rwa [tripCost_lens] at h3
  | @step s j l₁ m c hs hne _ ih =>
    intro l hl
    obtain ⟨i, l0⟩ := s
    simp only at hl
    subst hl
    obtain ⟨l', h1, h2, _⟩ := stepP_lens A ℓ z lift' hs
    obtain ⟨l'', h4, h5⟩ := ih l' h2.symm
    refine ⟨l'', ?_, h5⟩
    have h3 := ReachFirst.step (P := (viaLens A ℓ z lift').toProg) (e := e) h1 hne h4
    rwa [tripCost_lens] at h3

/-- **Frame preservation for one trip**: without extensions, an independent lens sees no change. -/
theorem frame_trip (hext : ∀ i b, A.ext i b = none) {D₂ : Type} {ℓ₂ : TrackLens E D₂}
    (hi : ℓ.Indep ℓ₂) (i : A.I) (l : List E) :
    ((viaLens A ℓ z lift').toProg.trip i l).1.map ℓ₂.get = l.map ℓ₂.get := by
  have hmid : (viaLens A ℓ z lift').toProg.mid i l =
      List.zipWith ℓ.put l (A.toProg.fpass i (l.map ℓ.get)).1 := by
    unfold Prog.mid
    rw [fpass_lens]
    show _ ++ ((A.ext i _).map (ℓ.put z)).toList = _
    rw [hext]
    simp
  have hlenF : (A.toProg.fpass i (l.map ℓ.get)).1.length = l.length := by
    unfold Prog.fpass; rw [fscan_length, List.length_map]
  rw [trip_lens, ℓ.frame_zipWith hi, hmid, ℓ.frame_zipWith hi _ _ hlenF]
  have h1 := bscan_length (A.bwd i) (A.toProg.fpass i (l.map ℓ.get)).2
    (A.toProg.mid i (l.map ℓ.get))
  have h2 := congrArg List.length (mid_lens_view A ℓ z lift' i l)
  rw [List.length_map] at h2
  show (bscan (A.bwd i) _ _).1.length = _
  rw [h1, h2]

/-- **Frame preservation for a first arrival.** -/
theorem reachFirst_lens_frame (hext : ∀ i b, A.ext i b = none) {D₂ : Type}
    {ℓ₂ : TrackLens E D₂} (hi : ℓ.Indep ℓ₂) {e : A.I}
    {s : (viaLens A ℓ z lift').toProg.I × List (viaLens A ℓ z lift').toProg.D}
    {l' : List (viaLens A ℓ z lift').toProg.D} {c : ℕ}
    (h : ReachFirst (viaLens A ℓ z lift').toProg e s l' c) :
    l'.map ℓ₂.get = s.2.map ℓ₂.get := by
  induction h with
  | @last s l hs =>
    obtain ⟨k1, k2⟩ := next_of_stepP (P := (viaLens A ℓ z lift').toProg) (i := s.1)
      (l := s.2) hs
    rw [← k2]
    exact frame_trip A ℓ z lift' hext hi s.1 s.2
  | @step s j l₁ l c hs _ _ ih =>
    obtain ⟨k1, k2⟩ := next_of_stepP (P := (viaLens A ℓ z lift').toProg) (i := s.1)
      (l := s.2) hs
    rw [ih, ← k2]
    exact frame_trip A ℓ z lift' hext hi s.1 s.2

end ProgOn

end PVNP.Discrete.Sweep
