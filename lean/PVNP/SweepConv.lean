import PVNP.SweepPoly

/-!
# Finite Fourier convolution on the Turing machine, by Kronecker substitution

The convolution `c_k = Σ_{i+j=k} a_i b_j` of two coefficient vectors is computed by one
multiplication of two integers. Evaluated at `2^L`, the coefficient polynomials of `a` and `b`
multiply to the coefficient polynomial of `c` (`kron_mul`). When every coefficient of `c` lies in
the `L`-bit range, the `L`-bit words of the product are its coefficients, read in excess
`2^{L−1}`.

The machine works on the excess-packed format of `SweepPoly`: `L`-bit words `a_i + 2^{L−1}` on one
track. On the common alphabet `KCell` it has three verified stages:

1. the subtractor removes the packed excess constant of `a`, leaving `Σ_i a_i 2^{iL}` in two's
   complement;
2. the subtractor does the same for `b`;
3. the verified multiplier adds the product to the accumulator, which holds the packed excess
   constant of the output.

So the accumulator becomes the packed excess codes of `c`, in exactly
`(trips + 3)(2N + 2) ≤ (N + 3)(2N + 2)` transitions.

* `kron_mul`: **Kronecker substitution**, `kron L a · kron L b = kron L (a ∗ b)`.
* `pack_excess`: the packed excess codes are the Kronecker value plus a packed constant.
* `conv_run`, `conv_tm`: the convolution machine on any tape and on the compiled TM.
* `convAt_box`, `conv2_tm`: **Fourier convolution on a box of modes.** Modes `p ∈ [−R, R]²` are
  packed at `ι(p) = (p₁ + R) + (4R + 1)(p₂ + R)`. Indices add exactly when modes add, because
  there is no carry between the two digits. So the packed convolution at `κ(k)` is the Fourier
  convolution `(a ⋆ b)(k) = Σ_j a(k − j) b(j)` for every `k ∈ [−2R, 2R]²`.
* `cconv_run`, `cconv_tm`, `cconv2_tm`: **complex coefficients**, by four lifted real
  convolutions on the common alphabet `CKCell`. They accumulate `Re = A_R B_R − A_I B_I` and
  `Im = A_R B_I + A_I B_R`. The second stage swaps the roles of the vector and the constant,
  which negates `A_I`.
-/


namespace PVNP.Discrete.SweepArith

open PVNP.Discrete PVNP.Discrete.Sweep Polynomial

/-! ### Kronecker substitution -/

/-- The value of a coefficient list at `2^L`: `kron L a = Σ_i a_i 2^{iL}`. -/
def kron (L : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: as => a + 2 ^ L * kron L as

/-- The coefficient polynomial of a list: `Σ_i a_i Xⁱ`. -/
noncomputable def cpoly : List ℤ → ℤ[X]
  | [] => 0
  | a :: as => C a + X * cpoly as

theorem cpoly_coeff : ∀ (a : List ℤ) (i : ℕ), (cpoly a).coeff i = a.getD i 0
  | [], i => by simp [cpoly]
  | a :: as, 0 => by simp [cpoly]
  | a :: as, i + 1 => by
    rw [cpoly, coeff_add, coeff_C, coeff_X_mul, cpoly_coeff as i]
    simp

theorem cpoly_eval (L : ℕ) : ∀ a : List ℤ, (cpoly a).eval (2 ^ L) = kron L a
  | [] => by simp [cpoly, kron]
  | a :: as => by simp [cpoly, kron, cpoly_eval L as]

/-- The convolution coefficient `Σ_{i+j=k} a_i b_j`. -/
def convAt (a b : List ℤ) (k : ℕ) : ℤ :=
  ∑ p ∈ Finset.antidiagonal k, a.getD p.1 0 * b.getD p.2 0

/-- The convolution of two coefficient lists, of length `|a| + |b| − 1`. -/
def conv (a b : List ℤ) : List ℤ := (List.range (a.length + b.length - 1)).map (convAt a b)

theorem convAt_eq_zero (a b : List ℤ) (k : ℕ) (hk : a.length + b.length - 1 ≤ k) :
    convAt a b k = 0 := by
  unfold convAt
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  by_cases h1 : a.length ≤ p.1
  · rw [List.getD_eq_default _ _ h1, zero_mul]
  · have h2 : b.length ≤ p.2 := by omega
    rw [List.getD_eq_default _ _ h2, mul_zero]

theorem conv_getD (a b : List ℤ) (k : ℕ) : (conv a b).getD k 0 = convAt a b k := by
  by_cases hk : k < a.length + b.length - 1
  · have hk' : k < (conv a b).length := by simp [conv, hk]
    rw [List.getD_eq_getElem _ _ hk']
    simp [conv]
  · rw [List.getD_eq_default _ _ (by simp [conv]; omega),
      convAt_eq_zero a b k (by omega)]

theorem cpoly_conv (a b : List ℤ) : cpoly (conv a b) = cpoly a * cpoly b := by
  ext k
  rw [cpoly_coeff, conv_getD, coeff_mul]
  simp only [convAt, cpoly_coeff]

/-- **Kronecker substitution**: the product of the values at `2^L` is the value of the
convolution. -/
theorem kron_mul (L : ℕ) (a b : List ℤ) : kron L a * kron L b = kron L (conv a b) := by
  rw [← cpoly_eval, ← cpoly_eval, ← cpoly_eval, cpoly_conv, eval_mul]

theorem conv_length (a b : List ℤ) : (conv a b).length = a.length + b.length - 1 := by
  simp [conv]

/-! ### The excess format -/

theorem excess_lt {L : ℕ} (hL : 0 < L) {c : ℤ} (h1 : -(2 : ℤ) ^ (L - 1) ≤ c)
    (h2 : c < 2 ^ (L - 1)) : (c + 2 ^ (L - 1)).toNat < 2 ^ L := by
  have e : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : ((c + 2 ^ (L - 1)).toNat : ℤ) < ((2 ^ L : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by linarith)]; push_cast; linarith
  exact_mod_cast h3

/-- The packed excess codes are the Kronecker value plus the packed excess constant. -/
theorem pack_excess (L : ℕ) : ∀ c : List ℤ, (∀ x ∈ c, -(2 : ℤ) ^ (L - 1) ≤ x) →
    ((pack L (excessCodes L c) : ℕ) : ℤ) =
      kron L c + ((pack L (List.replicate c.length (2 ^ (L - 1))) : ℕ) : ℤ)
  | [], _ => by simp [pack, excessCodes, kron]
  | c :: cs, h => by
    have h0 : 0 ≤ c + 2 ^ (L - 1) := by linarith [h c (by simp)]
    have ih := pack_excess L cs (fun x hx => h x (by simp [hx]))
    simp only [excessCodes] at ih
    simp only [excessCodes, List.map_cons, pack, List.length_cons, List.replicate_succ, kron]
    push_cast
    rw [ih, Int.toNat_of_nonneg h0]
    ring

theorem pack_lt (L : ℕ) : ∀ ws : List ℕ, (∀ w ∈ ws, w < 2 ^ L) → pack L ws < 2 ^ (L * ws.length)
  | [], _ => by simp [pack]
  | w :: ws, h => by
    have ih := pack_lt L ws (fun x hx => h x (by simp [hx]))
    have hw := h w (by simp)
    rw [pack, List.length_cons, Nat.mul_succ, pow_add]
    have : 2 ^ L * pack L ws + 2 ^ L ≤ 2 ^ L * 2 ^ (L * ws.length) := by
      have := Nat.mul_le_mul_left (2 ^ L) ih
      rw [Nat.mul_succ] at this
      linarith
    nlinarith

theorem excessCodes_lt {L : ℕ} (hL : 0 < L) (c : List ℤ)
    (h : ∀ x ∈ c, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1)) :
    ∀ w ∈ excessCodes L c, w < 2 ^ L := by
  intro w hw
  simp only [excessCodes, List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  exact excess_lt hL (h x hx).1 (h x hx).2


/-! ### The common alphabet -/

/-- Cells for convolution: the multiplier tracks `x, y, acc`, the packed inputs `va, vb` and their
packed excess constants `ea, eb`. -/
structure KCell where
  m : MCell
  va : Bool
  vb : Bool
  ea : Bool
  eb : Bool
  deriving DecidableEq

instance : Fintype KCell :=
  Fintype.ofEquiv (MCell × Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩
      invFun := fun x => ⟨x.m, x.va, x.vb, x.ea, x.eb⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The value of one track. -/
def kv (f : KCell → Bool) (l : List KCell) : ℕ := val (l.map f)

/-- The first input conversion: `x := va − ea`. -/
def lensKa : TrackLens KCell Cell :=
  ⟨fun x => ⟨x.va, x.ea, x.m.x⟩, fun x c => ⟨⟨c.r, x.m.y, x.m.acc⟩, c.a, x.vb, c.b, x.eb⟩,
    fun _ _ => rfl⟩
/-- The second input conversion: `y := vb − eb`. -/
def lensKb : TrackLens KCell Cell :=
  ⟨fun x => ⟨x.vb, x.eb, x.m.y⟩, fun x c => ⟨⟨x.m.x, c.r, x.m.acc⟩, x.va, c.a, x.ea, c.b⟩,
    fun _ _ => rfl⟩
/-- The multiplier: `acc := acc + x·y`. -/
def lensKm : TrackLens KCell MCell :=
  ⟨KCell.m, fun x m => ⟨m, x.va, x.vb, x.ea, x.eb⟩, fun _ _ => rfl⟩

/-- The tracks the first conversion does not touch. -/
def lensRa : TrackLens KCell (Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.m.y, x.m.acc, x.vb, x.eb),
    fun x k => ⟨⟨x.m.x, k.1, k.2.1⟩, x.va, k.2.2.1, x.ea, k.2.2.2⟩, fun _ _ => rfl⟩
/-- The tracks the second conversion does not touch. -/
def lensRb : TrackLens KCell (Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.m.x, x.m.acc, x.va, x.ea),
    fun x k => ⟨⟨k.1, x.m.y, k.2.1⟩, k.2.2.1, x.vb, k.2.2.2, x.eb⟩, fun _ _ => rfl⟩

/-- The tracks the multiplier does not touch. -/
def lensRm : TrackLens KCell (Bool × Bool × Bool × Bool) :=
  ⟨fun x => (x.va, x.vb, x.ea, x.eb), fun x k => ⟨x.m, k.1, k.2.1, k.2.2.1, k.2.2.2⟩,
    fun _ _ => rfl⟩

def kz0 : KCell := ⟨⟨false, false, false⟩, false, false, false, false⟩
def kbit (b : Bool) : KCell := ⟨⟨b, false, false⟩, false, false, false, false⟩

def SUBA : ProgOn KCell := (ProgOn.ofProg subProg).viaLens lensKa kz0 kbit
def SUBB : ProgOn KCell := (ProgOn.ofProg subProg).viaLens lensKb kz0 kbit
def MULK : ProgOn KCell := (ProgOn.ofProg mulProg).viaLens lensKm kz0 kbit
def K1 : ProgOn KCell := ProgOn.seq SUBA SUBB AddI.done

/-- **The convolution machine**: `x := va − ea`, then `y := vb − eb`, then `acc := acc + x·y`. -/
def convProg : ProgOn KCell := ProgOn.seq K1 MULK (Sum.inr AddI.done)

/-- A subtractor stage along a lens, with its frame. -/
theorem stk_sub (ℓ : TrackLens KCell Cell) (l : List KCell) :
    ∃ l', ReachFirst ((ProgOn.ofProg subProg).viaLens ℓ kz0 kbit).toProg AddI.done (AddI.go, l) l'
        (2 * l.length + 2) ∧
      l'.map ℓ.get = (fscan fsub false (l.map ℓ.get)).1 ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens KCell D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  have hr := sub_first (l.map ℓ.get)
  rw [List.length_map] at hr
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg subProg) ℓ kz0 kbit hr l rfl
  refine ⟨l', hr', hv, fun ℓ₂ hi => ?_⟩
  exact ProgOn.reachFirst_lens_frame (ProgOn.ofProg subProg) ℓ kz0 kbit (fun _ _ => rfl) hi hr'

/-- The multiplier stage, with its frame. -/
theorem stk_mul (l : List KCell) (hl : l ≠ []) :
    ∃ l', ReachFirst MULK.toProg MulI.done (MulI.prep, l) l'
        ((trips (kv (fun x => x.m.y) l) + 1) * (2 * l.length + 2)) ∧
      kv (fun x => x.m.acc) l' =
        (kv (fun x => x.m.acc) l + kv (fun x => x.m.x) l * kv (fun x => x.m.y) l) % 2 ^ l.length ∧
      l'.length = l.length ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens KCell D₂), lensKm.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  obtain ⟨m, hr, hlen, _, hv⟩ := mul_first (l.map lensKm.get) (by simpa using hl)
  have ey : vY (l.map lensKm.get) = kv (fun x => x.m.y) l := by
    unfold vY kv; rw [List.map_map]; rfl
  have ex : vX (l.map lensKm.get) = kv (fun x => x.m.x) l := by
    unfold vX kv; rw [List.map_map]; rfl
  have ea : vA (l.map lensKm.get) = kv (fun x => x.m.acc) l := by
    unfold vA kv; rw [List.map_map]; rfl
  rw [ey, List.length_map] at hr
  rw [List.length_map] at hv hlen
  obtain ⟨l', hr', hv'⟩ := ProgOn.reachFirst_lens (ProgOn.ofProg mulProg) lensKm kz0 kbit hr l rfl
  have hfr : ∀ {D₂ : Type} (ℓ₂ : TrackLens KCell D₂), lensKm.Indep ℓ₂ →
      l'.map ℓ₂.get = l.map ℓ₂.get := fun ℓ₂ hi =>
    ProgOn.reachFirst_lens_frame (ProgOn.ofProg mulProg) lensKm kz0 kbit (fun _ _ => rfl) hi hr'
  have hl' : l'.length = l.length := by
    have := congrArg List.length hv'
    rw [List.length_map, hlen] at this
    exact this
  refine ⟨l', hr', ?_, hl', hfr⟩
  have hlt : vA m < 2 ^ l.length := by
    have := val_lt (m.map MCell.acc)
    rw [List.length_map, hlen] at this
    exact this
  have e : kv (fun x => x.m.acc) l' = vA m := by
    rw [← hv']; unfold kv vA; rw [List.map_map]; rfl
  rw [e, ← Nat.mod_eq_of_lt hlt, hv, ea, ex, ey]

theorem kv_congr {f : KCell → Bool} {l l' : List KCell} (h : l'.map f = l.map f) :
    kv f l' = kv f l := by
  unfold kv; rw [h]

theorem kmap_proj {β γ : Type} {l l' : List KCell} {g : KCell → β} (h : l'.map g = l.map g)
    (π : β → γ) : l'.map (fun x => π (g x)) = l.map (fun x => π (g x)) := by
  have := congrArg (List.map π) h
  simpa [List.map_map, Function.comp_def] using this

/-- `C + x·y` on codes is the code of `C + XY`. -/
theorem tc_fma (N C : ℕ) (X Y : ℤ) : (C + tc N X * tc N Y) % 2 ^ N = tc N ((C : ℤ) + X * Y) := by
  have h : (((C + tc N X * tc N Y) % 2 ^ N : ℕ) : ℤ) = ((tc N ((C : ℤ) + X * Y) : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, tc_cast]
    have hm : X % 2 ^ N * (Y % 2 ^ N) ≡ X * Y [ZMOD 2 ^ N] :=
      (Int.mod_modEq X _).mul (Int.mod_modEq Y _)
    exact hm.add_left (C : ℤ)
  exact_mod_cast h

/-- **The convolution machine on any tape.** With `PA, QA, PB, QB` on the tracks `va, ea, vb, eb`
and `C` on the accumulator, all below `2^N`, it first-arrives at its exit in exactly
`(trips (tc_N (PB − QB)) + 3)(2N + 2)` transitions, with `acc = tc_N(C + (PA − QA)(PB − QB))`. -/
theorem conv_run (l : List KCell) {N : ℕ} (hl : l.length = N) (hN : 0 < N)
    {PA QA PB QB C : ℕ} (hPA : kv KCell.va l = PA) (hQA : kv KCell.ea l = QA)
    (hPB : kv KCell.vb l = PB) (hQB : kv KCell.eb l = QB) (hC : kv (fun x => x.m.acc) l = C)
    (hPA' : PA < 2 ^ N) (hQA' : QA < 2 ^ N) (hPB' : PB < 2 ^ N) (hQB' : QB < 2 ^ N) :
    ∃ l', ReachFirst convProg.toProg (Sum.inr MulI.done) (Sum.inl (Sum.inl AddI.go), l) l'
        ((trips (tc N ((PB : ℤ) - QB)) + 3) * (2 * N + 2)) ∧
      kv (fun x => x.m.acc) l' = tc N ((C : ℤ) + ((PA : ℤ) - QA) * ((PB : ℤ) - QB)) ∧
      l'.length = N ∧ l'.map KCell.va = l.map KCell.va ∧ l'.map KCell.vb = l.map KCell.vb ∧
      l'.map KCell.ea = l.map KCell.ea ∧ l'.map KCell.eb = l.map KCell.eb := by
  -- stage 1: x := va − ea
  obtain ⟨l1, r1, v1, f1⟩ := stk_sub lensKa l
  have ha1 : val ((l.map lensKa.get).map Cell.a) = tc N (PA : ℤ) := by
    rw [List.map_map, tc_natCast hPA']; exact hPA
  have hb1 : val ((l.map lensKa.get).map Cell.b) = tc N (QA : ℤ) := by
    rw [List.map_map, tc_natCast hQA']; exact hQA
  have hsub1 := sub_tc_value (l.map lensKa.get) N (by rw [List.length_map, hl]) _ _ ha1 hb1
  have len1 : l1.length = N := by
    have := congrArg List.length v1
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, hl]
  have hx1 : kv (fun x => x.m.x) l1 = tc N ((PA : ℤ) - QA) := by
    have e : kv (fun x => x.m.x) l1 = val ((l1.map lensKa.get).map Cell.r) := by
      unfold kv; rw [List.map_map]; rfl
    rw [e, v1]; exact hsub1
  have g1 : l1.map lensRa.get = l.map lensRa.get := f1 lensRa (fun _ _ => rfl)
  -- stage 2: y := vb − eb
  obtain ⟨l2, r2, v2, f2⟩ := stk_sub lensKb l1
  have vb1 : l1.map KCell.vb = l.map KCell.vb := kmap_proj g1 (fun k => k.2.2.1)
  have eb1 : l1.map KCell.eb = l.map KCell.eb := kmap_proj g1 (fun k => k.2.2.2)
  have ha2 : val ((l1.map lensKb.get).map Cell.a) = tc N (PB : ℤ) := by
    rw [List.map_map, tc_natCast hPB']; exact (congrArg val vb1).trans hPB
  have hb2 : val ((l1.map lensKb.get).map Cell.b) = tc N (QB : ℤ) := by
    rw [List.map_map, tc_natCast hQB']; exact (congrArg val eb1).trans hQB
  have hsub2 := sub_tc_value (l1.map lensKb.get) N (by rw [List.length_map, len1]) _ _ ha2 hb2
  have len2 : l2.length = N := by
    have := congrArg List.length v2
    rw [List.length_map, fscan_length, List.length_map] at this
    rw [this, len1]
  have hy2 : kv (fun x => x.m.y) l2 = tc N ((PB : ℤ) - QB) := by
    have e : kv (fun x => x.m.y) l2 = val ((l2.map lensKb.get).map Cell.r) := by
      unfold kv; rw [List.map_map]; rfl
    rw [e, v2]; exact hsub2
  have g2 : l2.map lensRb.get = l1.map lensRb.get := f2 lensRb (fun _ _ => rfl)
  have hx2 : kv (fun x => x.m.x) l2 = tc N ((PA : ℤ) - QA) :=
    (kv_congr (kmap_proj g2 (fun k => k.1))).trans hx1
  have hc2 : kv (fun x => x.m.acc) l2 = C := by
    have e2 : l2.map (fun x => x.m.acc) = l1.map (fun x => x.m.acc) :=
      kmap_proj g2 (fun k => k.2.1)
    have e1 : l1.map (fun x => x.m.acc) = l.map (fun x => x.m.acc) :=
      kmap_proj g1 (fun k => k.2.1)
    exact (kv_congr (e2.trans e1)).trans hC
  -- stage 3: acc := acc + x·y
  have hne : l2 ≠ [] := by
    intro e; rw [e, List.length_nil] at len2; omega
  obtain ⟨l3, r3, v3, len3, f3⟩ := stk_mul l2 hne
  rw [hy2, len2] at r3
  rw [hc2, hx2, hy2, len2, tc_fma] at v3
  have hK1 := ProgOn.seq_reachFirst (A := SUBA) (B := SUBB) (e := AddI.done)
    (show SUBB.start ≠ AddI.done by decide) r1 r2
  have hall := ProgOn.seq_reachFirst (A := K1) (B := MULK) (e := Sum.inr AddI.done)
    (show MULK.start ≠ MulI.done by decide) hK1 r3
  -- the input tracks are unchanged
  obtain ⟨sa1, sb1⟩ := fscan_sub_ab false (l.map lensKa.get)
  obtain ⟨sa2, sb2⟩ := fscan_sub_ab false (l1.map lensKb.get)
  have va1 : l1.map KCell.va = l.map KCell.va := by
    have := congrArg (List.map Cell.a) v1
    rw [sa1, List.map_map, List.map_map] at this
    exact this
  have ea1 : l1.map KCell.ea = l.map KCell.ea := by
    have := congrArg (List.map Cell.b) v1
    rw [sb1, List.map_map, List.map_map] at this
    exact this
  have vb2 : l2.map KCell.vb = l1.map KCell.vb := by
    have := congrArg (List.map Cell.a) v2
    rw [sa2, List.map_map, List.map_map] at this
    exact this
  have eb2 : l2.map KCell.eb = l1.map KCell.eb := by
    have := congrArg (List.map Cell.b) v2
    rw [sb2, List.map_map, List.map_map] at this
    exact this
  have va2 : l2.map KCell.va = l1.map KCell.va := kmap_proj g2 (fun k => k.2.2.1)
  have ea2 : l2.map KCell.ea = l1.map KCell.ea := kmap_proj g2 (fun k => k.2.2.2)
  have g3 : l3.map lensRm.get = l2.map lensRm.get := f3 lensRm (fun _ _ => rfl)
  have va3 : l3.map KCell.va = l2.map KCell.va := kmap_proj g3 (fun k => k.1)
  have vb3 : l3.map KCell.vb = l2.map KCell.vb := kmap_proj g3 (fun k => k.2.1)
  have ea3 : l3.map KCell.ea = l2.map KCell.ea := kmap_proj g3 (fun k => k.2.2.1)
  have eb3 : l3.map KCell.eb = l2.map KCell.eb := kmap_proj g3 (fun k => k.2.2.2)
  refine ⟨l3, ?_, v3, by rw [len3, len2], va3.trans (va2.trans va1),
    vb3.trans (vb2.trans vb1), ea3.trans (ea2.trans ea1), eb3.trans (eb2.trans eb1)⟩
  rw [hl, len1] at hall
  convert hall using 1
  ring

/-! ### The layout and the compiled machine -/

/-- Five tracks zipped into convolution cells; the multiplier's `x, y` start at zero. -/
def mkK : List Bool → List Bool → List Bool → List Bool → List Bool → List KCell
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es =>
      ⟨⟨false, false, e⟩, a, b, c, d⟩ :: mkK as bs cs ds es
  | _, _, _, _, _ => []

theorem mkK_spec : ∀ (as bs cs ds es : List Bool), bs.length = as.length →
    cs.length = as.length → ds.length = as.length → es.length = as.length →
    (mkK as bs cs ds es).map KCell.va = as ∧ (mkK as bs cs ds es).map KCell.vb = bs ∧
      (mkK as bs cs ds es).map KCell.ea = cs ∧ (mkK as bs cs ds es).map KCell.eb = ds ∧
      (mkK as bs cs ds es).map (fun x => x.m.acc) = es ∧
      (mkK as bs cs ds es).length = as.length
  | [], bs, cs, ds, es, h1, h2, h3, h4 => by
    rw [List.length_nil, List.length_eq_zero_iff] at h1 h2 h3 h4
    subst h1 h2 h3 h4
    simp [mkK]
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es, h1, h2, h3, h4 => by
    simp only [List.length_cons, add_left_inj] at h1 h2 h3 h4
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mkK_spec as bs cs ds es h1 h2 h3 h4
    simp [mkK, e1, e2, e3, e4, e5, e6]
  | _ :: _, [], _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3, _ => by simp at h3
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, h4 => by simp at h4

/-- The packed excess constant of `n` words: `Σ_{i<n} 2^{L−1} 2^{iL}`. -/
def excessConst (L n : ℕ) : ℕ := pack L (List.replicate n (2 ^ (L - 1)))

/-- The convolution layout on `N` cells: the packed excess codes of `a` and `b`, their excess
constants, and the excess constant of the output on the accumulator. -/
def convInput (N L : ℕ) (a b : List ℤ) : List KCell :=
  mkK (bitsOf N (pack L (excessCodes L a))) (bitsOf N (pack L (excessCodes L b)))
    (bitsOf N (excessConst L a.length)) (bitsOf N (excessConst L b.length))
    (bitsOf N (excessConst L (a.length + b.length - 1)))

theorem excessConst_lt {L : ℕ} (hL : 0 < L) (n : ℕ) : excessConst L n < 2 ^ (L * n) := by
  have h := pack_lt L (List.replicate n (2 ^ (L - 1))) (by
    intro w hw
    rw [List.eq_of_mem_replicate hw]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [List.length_replicate] at h
  exact h

/-- **Convolution on the compiled Turing machine.** Let `a, b` be nonempty lists of integers in
the `L`-bit range whose convolution `c = a ∗ b`, `c_k = Σ_{i+j=k} a_i b_j`, also lies in the
`L`-bit range, and let `(|a| + |b| − 1)L ≤ N`. From the layout `convInput N L a b`, the compiled
single-tape TM runs exactly `(trips (tc_N (kron L b)) + 3)(2N + 2) ≤ (N + 3)(2N + 2)`
transitions. Its accumulator then holds the packed excess codes of `c`: its `k`-th `L`-bit word is
`c_k + 2^{L−1}`. -/
theorem conv_tm {N L : ℕ} (hL : 0 < L) {a b : List ℤ} (ha0 : a ≠ []) (hb0 : b ≠ [])
    (ha : ∀ x ∈ a, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hb : ∀ x ∈ b, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hc : ∀ x ∈ conv a b, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hKN : (a.length + b.length - 1) * L ≤ N)
    (T : ℤ → Sym KCell) (hT : convProg.toProg.Repr T (convInput N L a b)) :
    ∃ l' T', convProg.toProg.Repr T' l' ∧
      kv (fun x => x.m.acc) l' = pack L (excessCodes L (conv a b)) ∧
      (∀ k < a.length + b.length - 1,
        kv (fun x => x.m.acc) l' / 2 ^ (k * L) % 2 ^ L = (convAt a b k + 2 ^ (L - 1)).toNat) ∧
      convProg.toProg.toTM.run
          ⟨.fwd convProg.start (convProg.toProg.init convProg.start), T, 0⟩
          ((trips (tc N (kron L b)) + 3) * (2 * N + 2)) =
        ⟨.fwd (Sum.inr MulI.done) (convProg.toProg.init (Sum.inr MulI.done)), T', 0⟩ ∧
      (trips (tc N (kron L b)) + 3) * (2 * N + 2) ≤ (N + 3) * (2 * N + 2) := by
  have hapos : 0 < a.length := List.length_pos_of_ne_nil ha0
  have hbpos : 0 < b.length := List.length_pos_of_ne_nil hb0
  have hN : 0 < N := by
    have : 1 * 1 ≤ (a.length + b.length - 1) * L := Nat.mul_le_mul (by omega) hL
    omega
  have hpow : ∀ n, n ≤ a.length + b.length - 1 → 2 ^ (L * n) ≤ 2 ^ N := fun n hn =>
    Nat.pow_le_pow_right (by norm_num)
      (le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right L hn) hKN)
  have hlenA : (excessCodes L a).length = a.length := by simp [excessCodes]
  have hlenB : (excessCodes L b).length = b.length := by simp [excessCodes]
  have hPA : pack L (excessCodes L a) < 2 ^ N := by
    have := pack_lt L _ (excessCodes_lt hL a ha)
    rw [hlenA] at this
    exact lt_of_lt_of_le this (hpow _ (by omega))
  have hPB : pack L (excessCodes L b) < 2 ^ N := by
    have := pack_lt L _ (excessCodes_lt hL b hb)
    rw [hlenB] at this
    exact lt_of_lt_of_le this (hpow _ (by omega))
  have hQA : excessConst L a.length < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ (by omega))
  have hQB : excessConst L b.length < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ (by omega))
  have hQC : excessConst L (a.length + b.length - 1) < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ le_rfl)
  have hlenC : (excessCodes L (conv a b)).length = a.length + b.length - 1 := by
    simp [excessCodes, conv_length]
  have hPC : pack L (excessCodes L (conv a b)) < 2 ^ N := by
    have := pack_lt L _ (excessCodes_lt hL _ hc)
    rw [hlenC] at this
    exact lt_of_lt_of_le this (hpow _ le_rfl)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mkK_spec (bitsOf N (pack L (excessCodes L a)))
    (bitsOf N (pack L (excessCodes L b))) (bitsOf N (excessConst L a.length))
    (bitsOf N (excessConst L b.length)) (bitsOf N (excessConst L (a.length + b.length - 1)))
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
    (by simp [bitsOf_length])
  rw [bitsOf_length] at e6
  have kPA : kv KCell.va (convInput N L a b) = pack L (excessCodes L a) := by
    unfold kv convInput; rw [e1, val_bitsOf, Nat.mod_eq_of_lt hPA]
  have kPB : kv KCell.vb (convInput N L a b) = pack L (excessCodes L b) := by
    unfold kv convInput; rw [e2, val_bitsOf, Nat.mod_eq_of_lt hPB]
  have kQA : kv KCell.ea (convInput N L a b) = excessConst L a.length := by
    unfold kv convInput; rw [e3, val_bitsOf, Nat.mod_eq_of_lt hQA]
  have kQB : kv KCell.eb (convInput N L a b) = excessConst L b.length := by
    unfold kv convInput; rw [e4, val_bitsOf, Nat.mod_eq_of_lt hQB]
  have kC : kv (fun x => x.m.acc) (convInput N L a b) =
      excessConst L (a.length + b.length - 1) := by
    unfold kv convInput; rw [e5, val_bitsOf, Nat.mod_eq_of_lt hQC]
  obtain ⟨l', hr, hacc, -⟩ := conv_run (convInput N L a b) e6 hN kPA kQA kPB kQB kC hPA hQA hPB hQB
  have hA : ((pack L (excessCodes L a) : ℕ) : ℤ) - (excessConst L a.length : ℕ) = kron L a := by
    rw [pack_excess L a (fun x hx => (ha x hx).1)]; unfold excessConst; ring
  have hB : ((pack L (excessCodes L b) : ℕ) : ℤ) - (excessConst L b.length : ℕ) = kron L b := by
    rw [pack_excess L b (fun x hx => (hb x hx).1)]; unfold excessConst; ring
  have hC : ((excessConst L (a.length + b.length - 1) : ℕ) : ℤ) + kron L a * kron L b =
      ((pack L (excessCodes L (conv a b)) : ℕ) : ℤ) := by
    rw [kron_mul, pack_excess L (conv a b) (fun x hx => (hc x hx).1), conv_length]
    unfold excessConst; ring
  rw [hA, hB, hC, tc_natCast hPC] at hacc
  rw [hB] at hr
  obtain ⟨T', hT', hrun⟩ := convProg.toProg.reach_run hr.reach T hT
  refine ⟨l', T', hT', hacc, ?_, hrun, ?_⟩
  · intro k hk
    rw [hacc, pack_word L _ k (by rw [hlenC]; exact hk) (excessCodes_lt hL _ hc)]
    simp [excessCodes, conv]
  · have := trips_le N (tc N (kron L b)) (tc_lt _ _)
    exact Nat.mul_le_mul_right _ (by omega)

/-! ### Fourier convolution on a modeBox of modes -/

/-- The modeBox `[−R, R]²` of Fourier modes. -/
def modeBox (R : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R

/-- The packed index of a mode `p ∈ [−R, R]²`, in rows of width `W = 4R + 1`:
`ι(p) = (p₁ + R) + W(p₂ + R)`. -/
def bidx (R : ℕ) (p : ℤ × ℤ) : ℕ := (p.1 + R).toNat + (4 * R + 1) * (p.2 + R).toNat

/-- The packed index of a mode `k ∈ [−2R, 2R]²`: `κ(k) = (k₁ + 2R) + W(k₂ + 2R)`. -/
def bidx2 (R : ℕ) (k : ℤ × ℤ) : ℕ :=
  (k.1 + 2 * R).toNat + (4 * R + 1) * (k.2 + 2 * R).toNat

/-- The number of packed words of a function on `[−R, R]²`. -/
def blen (R : ℕ) : ℕ := 2 * R + 1 + (4 * R + 1) * (2 * R)

/-- The packed coefficient list of a function on the modeBox, zero at the padding positions. -/
def boxList (R : ℕ) (f : ℤ × ℤ → ℤ) : List ℤ :=
  (List.range (blen R)).map fun i =>
    if i % (4 * R + 1) ≤ 2 * R then
      f (((i % (4 * R + 1) : ℕ) : ℤ) - R, ((i / (4 * R + 1) : ℕ) : ℤ) - R)
    else 0

/-- **The Fourier convolution** on the modeBox: `(a ⋆ b)(k) = Σ_{j ∈ [−R, R]²} a(k − j) b(j)`. -/
def bconv (R : ℕ) (a b : ℤ × ℤ → ℤ) (k : ℤ × ℤ) : ℤ := ∑ j ∈ modeBox R, a (k - j) * b j

theorem mem_modeBox {R : ℕ} {p : ℤ × ℤ} :
    p ∈ modeBox R ↔ -(R : ℤ) ≤ p.1 ∧ p.1 ≤ R ∧ -(R : ℤ) ≤ p.2 ∧ p.2 ≤ R := by
  simp [modeBox, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- Uniqueness of division with remainder. -/
theorem digits_eq {W r q r' q' : ℕ} (hr : r < W) (hr' : r' < W) (h : r + W * q = r' + W * q') :
    r = r' ∧ q = q' := by
  have hW : 0 < W := by omega
  have h1 : (r + W * q) % W = r := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have h2 : (r' + W * q') % W = r' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
  have h3 : (r + W * q) / W = q := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, zero_add]
  have h4 : (r' + W * q') / W = q' := by
    rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr', zero_add]
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

theorem bidx_inj {R : ℕ} {p q : ℤ × ℤ} (hp : p ∈ modeBox R) (hq : q ∈ modeBox R)
    (h : bidx R p = bidx R q) : p = q := by
  rw [mem_modeBox] at hp hq
  unfold bidx at h
  obtain ⟨d1, d2⟩ := digits_eq (W := 4 * R + 1) (by omega) (by omega) h
  exact Prod.ext (by omega) (by omega)

theorem bidx_bound {R : ℕ} {p : ℤ × ℤ} (hp : p ∈ modeBox R) :
    bidx R p < blen R ∧ bidx R p % (4 * R + 1) ≤ 2 * R := by
  rw [mem_modeBox] at hp
  unfold bidx blen
  have h2 : (4 * R + 1) * (p.2 + R).toNat ≤ (4 * R + 1) * (2 * R) :=
    Nat.mul_le_mul_left _ (by omega)
  refine ⟨by omega, ?_⟩
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Every packed position with a small first digit is the index of a mode of the modeBox. -/
theorem bidx_decode {R i : ℕ} (hi : i < blen R) (hd : i % (4 * R + 1) ≤ 2 * R) :
    ((((i % (4 * R + 1) : ℕ) : ℤ) - R, ((i / (4 * R + 1) : ℕ) : ℤ) - R) : ℤ × ℤ) ∈ modeBox R ∧
      bidx R (((i % (4 * R + 1) : ℕ) : ℤ) - R, ((i / (4 * R + 1) : ℕ) : ℤ) - R) = i := by
  have hq : i / (4 * R + 1) ≤ 2 * R := by
    have h1 : i < (2 * R + 1) * (4 * R + 1) := by unfold blen at hi; nlinarith
    have h2 : i / (4 * R + 1) < 2 * R + 1 := (Nat.div_lt_iff_lt_mul (by omega)).2 h1
    omega
  have hmem : ∀ r q : ℕ, r ≤ 2 * R → q ≤ 2 * R →
      (((r : ℤ) - R, (q : ℤ) - R) : ℤ × ℤ) ∈ modeBox R := fun r q hr hq =>
    mem_modeBox.2 ⟨by omega, by omega, by omega, by omega⟩
  refine ⟨hmem _ _ hd hq, ?_⟩
  unfold bidx
  simp only [sub_add_cancel, Int.toNat_natCast]
  exact Nat.mod_add_div i (4 * R + 1)

theorem boxList_getD (R : ℕ) (f : ℤ × ℤ → ℤ) (i : ℕ) :
    (boxList R f).getD i 0 =
      if i < blen R ∧ i % (4 * R + 1) ≤ 2 * R then
        f (((i % (4 * R + 1) : ℕ) : ℤ) - R, ((i / (4 * R + 1) : ℕ) : ℤ) - R)
      else 0 := by
  by_cases hi : i < blen R
  · rw [List.getD_eq_getElem _ _ (by simp [boxList, hi])]
    simp [boxList, hi]
  · rw [List.getD_eq_default _ _ (by simp [boxList]; omega)]
    simp [hi]

theorem boxList_length (R : ℕ) (f : ℤ × ℤ → ℤ) : (boxList R f).length = blen R := by
  simp [boxList]

/-- The coefficient polynomial of the packed list places `f(p)` at `X^{ι(p)}`. -/
theorem cpoly_boxList (R : ℕ) (f : ℤ × ℤ → ℤ) :
    cpoly (boxList R f) = ∑ p ∈ modeBox R, C (f p) * X ^ bidx R p := by
  ext i
  rw [cpoly_coeff, finset_sum_coeff, boxList_getD]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · obtain ⟨hp0, hb0⟩ := bidx_decode h.1 h.2
    rw [Finset.sum_eq_single _ (fun p hp hne => ?_) (fun h' => absurd hp0 h')]
    · rw [if_pos hb0.symm]
    · rw [if_neg]
      intro hi
      exact hne (bidx_inj hp hp0 (hi.symm.trans hb0.symm))
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro hi
    exact h (hi ▸ bidx_bound hp)

/-- Indices add exactly when modes add: no carry between the two digits. -/
theorem bidx_add {R : ℕ} {p q k : ℤ × ℤ} (hp : p ∈ modeBox R) (hq : q ∈ modeBox R)
    (hk : k ∈ modeBox (2 * R)) : bidx R p + bidx R q = bidx2 R k ↔ p + q = k := by
  rw [mem_modeBox] at hp hq hk
  push_cast at hk
  unfold bidx bidx2
  constructor
  · intro h
    have h' : ((p.1 + R).toNat + (q.1 + R).toNat) +
        (4 * R + 1) * ((p.2 + R).toNat + (q.2 + R).toNat) =
        (k.1 + 2 * R).toNat + (4 * R + 1) * (k.2 + 2 * R).toNat := by rw [← h]; ring
    obtain ⟨d1, d2⟩ := digits_eq (W := 4 * R + 1) (by omega) (by omega) h'
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add]; omega)
  · intro h
    have h1 : k.1 = p.1 + q.1 := by rw [← h]; rfl
    have h2 : k.2 = p.2 + q.2 := by rw [← h]; rfl
    have d1 : (k.1 + 2 * R).toNat = (p.1 + R).toNat + (q.1 + R).toNat := by omega
    have d2 : (k.2 + 2 * R).toNat = (p.2 + R).toNat + (q.2 + R).toNat := by omega
    rw [d1, d2]; ring

theorem cpoly_mul_coeff (a b : List ℤ) (k : ℕ) :
    (cpoly a * cpoly b).coeff k = convAt a b k := by
  rw [coeff_mul]; simp only [convAt, cpoly_coeff]

/-- **The packed convolution is the Fourier convolution**: for `a` supported on the modeBox and every
mode `k ∈ [−2R, 2R]²`, the coefficient of the packed convolution at `κ(k)` is `(a ⋆ b)(k)`. -/
theorem convAt_box (R : ℕ) (a b : ℤ × ℤ → ℤ) (ha : ∀ p ∉ modeBox R, a p = 0) {k : ℤ × ℤ}
    (hk : k ∈ modeBox (2 * R)) :
    convAt (boxList R a) (boxList R b) (bidx2 R k) = bconv R a b k := by
  rw [← cpoly_mul_coeff, cpoly_boxList, cpoly_boxList, Finset.sum_mul_sum]
  simp_rw [finset_sum_coeff]
  unfold bconv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have e : ∀ p, C (a p) * X ^ bidx R p * (C (b q) * X ^ bidx R q) =
      C (a p * b q) * X ^ (bidx R p + bidx R q) := by
    intro p; rw [C_mul, pow_add]; ring
  simp_rw [e, coeff_C_mul_X_pow]
  by_cases hkq : k - q ∈ modeBox R
  · rw [Finset.sum_eq_single (k - q) (fun p hp hne => ?_) (fun h => absurd hkq h)]
    · rw [if_pos ((bidx_add hkq hq hk).2 (by abel)).symm]
    · rw [if_neg]
      intro h
      have := (bidx_add hp hq hk).1 h.symm
      exact hne (by rw [← this]; abel)
  · rw [ha _ hkq, zero_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    have := (bidx_add hp hq hk).1 h.symm
    exact hkq (by rw [← this, add_sub_cancel_right]; exact hp)

theorem blen_conv (R : ℕ) : blen R + blen R - 1 = (4 * R + 1) ^ 2 := by
  unfold blen
  have : 2 * R + 1 + (4 * R + 1) * (2 * R) + (2 * R + 1 + (4 * R + 1) * (2 * R)) =
      (4 * R + 1) ^ 2 + 1 := by ring
  omega

/-- Every index of the packed product is the index of a mode of the product modeBox. -/
theorem bidx2_decode {R n : ℕ} (hn : n < (4 * R + 1) ^ 2) :
    ((((n % (4 * R + 1) : ℕ) : ℤ) - 2 * R, ((n / (4 * R + 1) : ℕ) : ℤ) - 2 * R) : ℤ × ℤ) ∈
        modeBox (2 * R) ∧
      bidx2 R (((n % (4 * R + 1) : ℕ) : ℤ) - 2 * R, ((n / (4 * R + 1) : ℕ) : ℤ) - 2 * R) = n := by
  have hW : 0 < 4 * R + 1 := by omega
  have hq : n / (4 * R + 1) < 4 * R + 1 := (Nat.div_lt_iff_lt_mul hW).2 (by rw [sq] at hn; exact hn)
  have hr : n % (4 * R + 1) < 4 * R + 1 := Nat.mod_lt _ hW
  have hmem : ∀ r q : ℕ, r < 4 * R + 1 → q < 4 * R + 1 →
      (((r : ℤ) - 2 * R, (q : ℤ) - 2 * R) : ℤ × ℤ) ∈ modeBox (2 * R) := fun r q hr hq =>
    mem_modeBox.2 ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega, by push_cast; omega⟩
  refine ⟨hmem _ _ hr hq, ?_⟩
  unfold bidx2
  simp only [sub_add_cancel, Int.toNat_natCast]
  exact Nat.mod_add_div n (4 * R + 1)

theorem bidx2_lt {R : ℕ} {k : ℤ × ℤ} (hk : k ∈ modeBox (2 * R)) : bidx2 R k < (4 * R + 1) ^ 2 := by
  rw [mem_modeBox] at hk
  push_cast at hk
  unfold bidx2
  have h2 : (4 * R + 1) * (k.2 + 2 * R).toNat ≤ (4 * R + 1) * (4 * R) :=
    Nat.mul_le_mul_left _ (by omega)
  have : (4 * R + 1) ^ 2 = (4 * R + 1) * (4 * R) + (4 * R + 1) := by ring
  omega

theorem boxList_ne_nil (R : ℕ) (f : ℤ × ℤ → ℤ) : boxList R f ≠ [] := by
  intro h
  have := boxList_length R f
  rw [h, List.length_nil] at this
  unfold blen at this
  omega

theorem boxList_range {L R : ℕ} (f : ℤ × ℤ → ℤ)
    (hf : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ f p ∧ f p < 2 ^ (L - 1)) :
    ∀ x ∈ boxList R f, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1) := by
  intro x hx
  simp only [boxList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  split_ifs
  · exact hf _
  · exact ⟨neg_nonpos.2 (by positivity), by positivity⟩

/-- The entries of the packed convolution are the values of the Fourier convolution. -/
theorem conv_boxList_range {L R : ℕ} (a b : ℤ × ℤ → ℤ) (ha0 : ∀ p ∉ modeBox R, a p = 0)
    (hc : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R a b k ∧ bconv R a b k < 2 ^ (L - 1)) :
    ∀ x ∈ conv (boxList R a) (boxList R b), -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1) := by
  intro x hx
  simp only [conv, List.mem_map, List.mem_range] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  rw [boxList_length, boxList_length, blen_conv] at hn
  obtain ⟨hk, hidx⟩ := bidx2_decode hn
  have e := convAt_box R a b ha0 hk
  rw [hidx] at e
  rw [e]
  exact hc _ hk

/-- **Fourier convolution on the compiled Turing machine.** Let `a, b : ℤ² → ℤ` be supported on
the modeBox `[−R, R]²` with values in the `L`-bit range, and let their Fourier convolution `a ⋆ b`
lie in the `L`-bit range on `[−2R, 2R]²`. With `(4R + 1)² L ≤ N`, from the packed layout
`convInput N L (boxList R a) (boxList R b)` the compiled single-tape TM runs exactly
`(trips (tc_N (kron L (boxList R b))) + 3)(2N + 2) ≤ (N + 3)(2N + 2)` transitions. For every
mode `k ∈ [−2R, 2R]²`, the accumulator's `L`-bit word at the index `κ(k)` is then
`(a ⋆ b)(k) + 2^{L−1}`. -/
theorem conv2_tm {N L R : ℕ} (hL : 0 < L) {a b : ℤ × ℤ → ℤ} (ha0 : ∀ p ∉ modeBox R, a p = 0)
    (ha : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ a p ∧ a p < 2 ^ (L - 1))
    (hb : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ b p ∧ b p < 2 ^ (L - 1))
    (hc : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R a b k ∧ bconv R a b k < 2 ^ (L - 1))
    (hKN : (4 * R + 1) ^ 2 * L ≤ N) (T : ℤ → Sym KCell)
    (hT : convProg.toProg.Repr T (convInput N L (boxList R a) (boxList R b))) :
    ∃ l' T', convProg.toProg.Repr T' l' ∧
      (∀ k ∈ modeBox (2 * R), kv (fun x => x.m.acc) l' / 2 ^ (bidx2 R k * L) % 2 ^ L =
        (bconv R a b k + 2 ^ (L - 1)).toNat) ∧
      convProg.toProg.toTM.run
          ⟨.fwd convProg.start (convProg.toProg.init convProg.start), T, 0⟩
          ((trips (tc N (kron L (boxList R b))) + 3) * (2 * N + 2)) =
        ⟨.fwd (Sum.inr MulI.done) (convProg.toProg.init (Sum.inr MulI.done)), T', 0⟩ ∧
      (trips (tc N (kron L (boxList R b))) + 3) * (2 * N + 2) ≤ (N + 3) * (2 * N + 2) := by
  have hlen : (boxList R a).length + (boxList R b).length - 1 = (4 * R + 1) ^ 2 := by
    rw [boxList_length, boxList_length, blen_conv]
  obtain ⟨l', T', hT', -, hw, hrun, hcost⟩ := conv_tm hL (boxList_ne_nil R a) (boxList_ne_nil R b)
    (boxList_range a ha) (boxList_range b hb) (conv_boxList_range a b ha0 hc)
    (by rw [hlen]; exact hKN) T hT
  refine ⟨l', T', hT', fun k hk => ?_, hrun, hcost⟩
  rw [hw _ (by rw [hlen]; exact bidx2_lt hk), convAt_box R a b ha0 hk]

/-! ### Complex convolution: four lifted real convolutions -/

theorem convProg_ext : ∀ i b, convProg.ext i b = none :=
  ProgOn.seq_ext_none _ _ _
    (ProgOn.seq_ext_none _ _ _ (ProgOn.viaLens_ext_none _ _ _ _ (fun _ _ => rfl))
      (ProgOn.viaLens_ext_none _ _ _ _ (fun _ _ => rfl)))
    (ProgOn.viaLens_ext_none _ _ _ _ (fun _ _ => rfl))

/-- **A lifted convolution stage**: the convolution machine run through a lens, with the input
tracks of its view unchanged and its frame. -/
theorem conv_lens {E : Type} [Fintype E] [DecidableEq E] (ℓ : TrackLens E KCell) (z : E)
    (lift' : Bool → E) (l : List E) {N : ℕ} (hl : l.length = N) (hN : 0 < N)
    {PA QA PB QB C : ℕ} (hPA : kv KCell.va (l.map ℓ.get) = PA)
    (hQA : kv KCell.ea (l.map ℓ.get) = QA) (hPB : kv KCell.vb (l.map ℓ.get) = PB)
    (hQB : kv KCell.eb (l.map ℓ.get) = QB) (hC : kv (fun x => x.m.acc) (l.map ℓ.get) = C)
    (hPA' : PA < 2 ^ N) (hQA' : QA < 2 ^ N) (hPB' : PB < 2 ^ N) (hQB' : QB < 2 ^ N) :
    ∃ l', ReachFirst (convProg.viaLens ℓ z lift').toProg (Sum.inr MulI.done)
        (Sum.inl (Sum.inl AddI.go), l) l' ((trips (tc N ((PB : ℤ) - QB)) + 3) * (2 * N + 2)) ∧
      kv (fun x => x.m.acc) (l'.map ℓ.get) = tc N ((C : ℤ) + ((PA : ℤ) - QA) * ((PB : ℤ) - QB)) ∧
      l'.length = N ∧
      (l'.map ℓ.get).map KCell.va = (l.map ℓ.get).map KCell.va ∧
      (l'.map ℓ.get).map KCell.vb = (l.map ℓ.get).map KCell.vb ∧
      (l'.map ℓ.get).map KCell.ea = (l.map ℓ.get).map KCell.ea ∧
      (l'.map ℓ.get).map KCell.eb = (l.map ℓ.get).map KCell.eb ∧
      ∀ {D₂ : Type} (ℓ₂ : TrackLens E D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get := by
  obtain ⟨m, hr, hacc, hlen, hva, hvb, hea, heb⟩ :=
    conv_run (l.map ℓ.get) (by rw [List.length_map, hl]) hN hPA hQA hPB hQB hC hPA' hQA' hPB' hQB'
  obtain ⟨l', hr', hv⟩ := ProgOn.reachFirst_lens convProg ℓ z lift' hr l rfl
  have hfr : ∀ {D₂ : Type} (ℓ₂ : TrackLens E D₂), ℓ.Indep ℓ₂ → l'.map ℓ₂.get = l.map ℓ₂.get :=
    fun ℓ₂ hi => ProgOn.reachFirst_lens_frame convProg ℓ z lift' convProg_ext hi hr'
  have hl' : l'.length = N := by
    have := congrArg List.length hv
    rw [List.length_map, hlen] at this
    exact this
  exact ⟨l', hr', (congrArg (kv (fun x => x.m.acc)) hv).trans hacc, hl',
    (congrArg (List.map KCell.va) hv).trans hva, (congrArg (List.map KCell.vb) hv).trans hvb,
    (congrArg (List.map KCell.ea) hv).trans hea, (congrArg (List.map KCell.eb) hv).trans heb, hfr⟩

/-- Cells for complex convolution: the multiplier's `x, y`, the accumulators `accR, accI`, the
packed real and imaginary parts of both inputs, and the two excess constants. -/
structure CKCell where
  x : Bool
  y : Bool
  accR : Bool
  accI : Bool
  vaR : Bool
  vaI : Bool
  vbR : Bool
  vbI : Bool
  ea : Bool
  eb : Bool
  deriving DecidableEq

instance : Fintype CKCell :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool)
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j⟩ => ⟨a, b, c, d, e, f, g, h, i, j⟩
      invFun := fun x => ⟨x.x, x.y, x.accR, x.accI, x.vaR, x.vaI, x.vbR, x.vbI, x.ea, x.eb⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The value of one track. -/
def cv (f : CKCell → Bool) (l : List CKCell) : ℕ := val (l.map f)

/-- Stage 1, `accR += (vaR − ea)(vbR − eb)`. -/
def lensC1 : TrackLens CKCell KCell :=
  ⟨fun c => ⟨⟨c.x, c.y, c.accR⟩, c.vaR, c.vbR, c.ea, c.eb⟩,
    fun c k => ⟨k.m.x, k.m.y, k.m.acc, c.accI, k.va, c.vaI, k.vb, c.vbI, k.ea, k.eb⟩,
    fun _ _ => rfl⟩
/-- Stage 2, `accR += (ea − vaI)(vbI − eb)`: the roles of the vector and the constant are
swapped, which negates the imaginary part. -/
def lensC2 : TrackLens CKCell KCell :=
  ⟨fun c => ⟨⟨c.x, c.y, c.accR⟩, c.ea, c.vbI, c.vaI, c.eb⟩,
    fun c k => ⟨k.m.x, k.m.y, k.m.acc, c.accI, c.vaR, k.ea, c.vbR, k.vb, k.va, k.eb⟩,
    fun _ _ => rfl⟩
/-- Stage 3, `accI += (vaR − ea)(vbI − eb)`. -/
def lensC3 : TrackLens CKCell KCell :=
  ⟨fun c => ⟨⟨c.x, c.y, c.accI⟩, c.vaR, c.vbI, c.ea, c.eb⟩,
    fun c k => ⟨k.m.x, k.m.y, c.accR, k.m.acc, k.va, c.vaI, c.vbR, k.vb, k.ea, k.eb⟩,
    fun _ _ => rfl⟩
/-- Stage 4, `accI += (vaI − ea)(vbR − eb)`. -/
def lensC4 : TrackLens CKCell KCell :=
  ⟨fun c => ⟨⟨c.x, c.y, c.accI⟩, c.vaI, c.vbR, c.ea, c.eb⟩,
    fun c k => ⟨k.m.x, k.m.y, c.accR, k.m.acc, c.vaR, k.va, k.vb, c.vbI, k.ea, k.eb⟩,
    fun _ _ => rfl⟩

/-- The tracks each stage does not touch. -/
def lensQ1 : TrackLens CKCell (Bool × Bool × Bool) :=
  ⟨fun c => (c.accI, c.vaI, c.vbI),
    fun c t => ⟨c.x, c.y, c.accR, t.1, c.vaR, t.2.1, c.vbR, t.2.2, c.ea, c.eb⟩, fun _ _ => rfl⟩
def lensQ2 : TrackLens CKCell (Bool × Bool × Bool) :=
  ⟨fun c => (c.accI, c.vaR, c.vbR),
    fun c t => ⟨c.x, c.y, c.accR, t.1, t.2.1, c.vaI, t.2.2, c.vbI, c.ea, c.eb⟩, fun _ _ => rfl⟩
def lensQ3 : TrackLens CKCell (Bool × Bool × Bool) :=
  ⟨fun c => (c.accR, c.vaI, c.vbR),
    fun c t => ⟨c.x, c.y, t.1, c.accI, c.vaR, t.2.1, t.2.2, c.vbI, c.ea, c.eb⟩, fun _ _ => rfl⟩
def lensQ4 : TrackLens CKCell (Bool × Bool × Bool) :=
  ⟨fun c => (c.accR, c.vaR, c.vbI),
    fun c t => ⟨c.x, c.y, t.1, c.accI, t.2.1, c.vaI, c.vbR, t.2.2, c.ea, c.eb⟩, fun _ _ => rfl⟩

def ckz0 : CKCell := ⟨false, false, false, false, false, false, false, false, false, false⟩
def ckbit (b : Bool) : CKCell := ⟨b, false, false, false, false, false, false, false, false, false⟩

def CS1 : ProgOn CKCell := convProg.viaLens lensC1 ckz0 ckbit
def CS2 : ProgOn CKCell := convProg.viaLens lensC2 ckz0 ckbit
def CS3 : ProgOn CKCell := convProg.viaLens lensC3 ckz0 ckbit
def CS4 : ProgOn CKCell := convProg.viaLens lensC4 ckz0 ckbit
def CC1 : ProgOn CKCell := ProgOn.seq CS1 CS2 (Sum.inr MulI.done)
def CC2 : ProgOn CKCell := ProgOn.seq CC1 CS3 (Sum.inr (Sum.inr MulI.done))

/-- **The complex convolution machine**: four lifted real convolutions, accumulating
`accR += A_R B_R − A_I B_I` and `accI += A_R B_I + A_I B_R`. -/
def cconvProg : ProgOn CKCell := ProgOn.seq CC2 CS4 (Sum.inr (Sum.inr MulI.done))

theorem cv_congr {f : CKCell → Bool} {l l' : List CKCell} (h : l'.map f = l.map f) :
    cv f l' = cv f l := by
  unfold cv; rw [h]

theorem cmap_proj {β γ : Type} {l l' : List CKCell} {g : CKCell → β} (h : l'.map g = l.map g)
    (π : β → γ) : l'.map (fun x => π (g x)) = l.map (fun x => π (g x)) := by
  have := congrArg (List.map π) h
  simpa [List.map_map, Function.comp_def] using this

theorem tc_tc_add (N : ℕ) (X Y : ℤ) : tc N (((tc N X : ℕ) : ℤ) + Y) = tc N (X + Y) := by
  have h : ((tc N (((tc N X : ℕ) : ℤ) + Y) : ℕ) : ℤ) = ((tc N (X + Y) : ℕ) : ℤ) := by
    rw [tc_cast, tc_cast, tc_cast]
    exact (Int.mod_modEq X _).add_right Y
  exact_mod_cast h

/-- **The complex convolution machine on any tape.** With the real and imaginary parts
`PAR, PAI, PBR, PBI`, the constants `QA, QB` and the accumulators `CR, CI`, the inputs below
`2^N`, it first-arrives at its exit with
`accR = tc_N(CR + A_R B_R − A_I B_I)` and `accI = tc_N(CI + A_R B_I + A_I B_R)`, where
`A_R = PAR − QA`, `A_I = PAI − QA`, `B_R = PBR − QB`, `B_I = PBI − QB`. It takes exactly
`(2(t_R + t_I) + 12)(2N + 2)` transitions, with `t_R, t_I` the bit lengths of the codes of
`B_R, B_I`. -/
theorem cconv_run (l : List CKCell) {N : ℕ} (hl : l.length = N) (hN : 0 < N)
    {PAR PAI PBR PBI QA QB CR CI : ℕ}
    (h1 : cv CKCell.vaR l = PAR) (h2 : cv CKCell.vaI l = PAI) (h3 : cv CKCell.vbR l = PBR)
    (h4 : cv CKCell.vbI l = PBI) (h5 : cv CKCell.ea l = QA) (h6 : cv CKCell.eb l = QB)
    (h7 : cv CKCell.accR l = CR) (h8 : cv CKCell.accI l = CI)
    (b1 : PAR < 2 ^ N) (b2 : PAI < 2 ^ N) (b3 : PBR < 2 ^ N) (b4 : PBI < 2 ^ N)
    (b5 : QA < 2 ^ N) (b6 : QB < 2 ^ N) :
    ∃ l', ReachFirst cconvProg.toProg (Sum.inr (Sum.inr MulI.done))
        (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl AddI.go)))), l) l'
        ((2 * (trips (tc N ((PBR : ℤ) - QB)) + trips (tc N ((PBI : ℤ) - QB))) + 12) *
          (2 * N + 2)) ∧
      cv CKCell.accR l' = tc N ((CR : ℤ) + ((PAR : ℤ) - QA) * ((PBR : ℤ) - QB) -
        ((PAI : ℤ) - QA) * ((PBI : ℤ) - QB)) ∧
      cv CKCell.accI l' = tc N ((CI : ℤ) + ((PAR : ℤ) - QA) * ((PBI : ℤ) - QB) +
        ((PAI : ℤ) - QA) * ((PBR : ℤ) - QB)) := by
  -- stage 1
  obtain ⟨l1, r1, a1, len1, va1, vb1, ea1, eb1, f1⟩ := conv_lens lensC1 ckz0 ckbit l hl hN
    (PA := PAR) (QA := QA) (PB := PBR) (QB := QB) (C := CR)
    (by unfold kv; rw [List.map_map]; exact h1) (by unfold kv; rw [List.map_map]; exact h5)
    (by unfold kv; rw [List.map_map]; exact h3) (by unfold kv; rw [List.map_map]; exact h6)
    (by unfold kv; rw [List.map_map]; exact h7) b1 b5 b3 b6
  have q1 : l1.map lensQ1.get = l.map lensQ1.get := f1 lensQ1 (fun _ _ => rfl)
  have s1ea : l1.map CKCell.ea = l.map CKCell.ea := by
    have := ea1; rw [List.map_map, List.map_map] at this; exact this
  have s1eb : l1.map CKCell.eb = l.map CKCell.eb := by
    have := eb1; rw [List.map_map, List.map_map] at this; exact this
  have s1vaR : l1.map CKCell.vaR = l.map CKCell.vaR := by
    have := va1; rw [List.map_map, List.map_map] at this; exact this
  have s1vbR : l1.map CKCell.vbR = l.map CKCell.vbR := by
    have := vb1; rw [List.map_map, List.map_map] at this; exact this
  have s1accI : l1.map CKCell.accI = l.map CKCell.accI := cmap_proj q1 (fun t => t.1)
  have s1vaI : l1.map CKCell.vaI = l.map CKCell.vaI := cmap_proj q1 (fun t => t.2.1)
  have s1vbI : l1.map CKCell.vbI = l.map CKCell.vbI := cmap_proj q1 (fun t => t.2.2)
  have c1R : cv CKCell.accR l1 = tc N ((CR : ℤ) + ((PAR : ℤ) - QA) * ((PBR : ℤ) - QB)) := by
    have := a1; unfold kv at this; rw [List.map_map] at this; exact this
  -- stage 2
  obtain ⟨l2, r2, a2, len2, va2, vb2, ea2, eb2, f2⟩ := conv_lens lensC2 ckz0 ckbit l1 len1 hN
    (PA := QA) (QA := PAI) (PB := PBI) (QB := QB)
    (C := tc N ((CR : ℤ) + ((PAR : ℤ) - QA) * ((PBR : ℤ) - QB)))
    (by unfold kv; rw [List.map_map]; exact (cv_congr s1ea).trans h5)
    (by unfold kv; rw [List.map_map]; exact (cv_congr s1vaI).trans h2)
    (by unfold kv; rw [List.map_map]; exact (cv_congr s1vbI).trans h4)
    (by unfold kv; rw [List.map_map]; exact (cv_congr s1eb).trans h6)
    (by unfold kv; rw [List.map_map]; exact c1R) b5 b2 b4 b6
  have q2 : l2.map lensQ2.get = l1.map lensQ2.get := f2 lensQ2 (fun _ _ => rfl)
  have s2ea : l2.map CKCell.ea = l1.map CKCell.ea := by
    have := va2; rw [List.map_map, List.map_map] at this; exact this
  have s2vaI : l2.map CKCell.vaI = l1.map CKCell.vaI := by
    have := ea2; rw [List.map_map, List.map_map] at this; exact this
  have s2vbI : l2.map CKCell.vbI = l1.map CKCell.vbI := by
    have := vb2; rw [List.map_map, List.map_map] at this; exact this
  have s2eb : l2.map CKCell.eb = l1.map CKCell.eb := by
    have := eb2; rw [List.map_map, List.map_map] at this; exact this
  have s2accI : l2.map CKCell.accI = l1.map CKCell.accI := cmap_proj q2 (fun t => t.1)
  have s2vaR : l2.map CKCell.vaR = l1.map CKCell.vaR := cmap_proj q2 (fun t => t.2.1)
  have s2vbR : l2.map CKCell.vbR = l1.map CKCell.vbR := cmap_proj q2 (fun t => t.2.2)
  have c2R : cv CKCell.accR l2 = tc N ((CR : ℤ) + ((PAR : ℤ) - QA) * ((PBR : ℤ) - QB) -
      ((PAI : ℤ) - QA) * ((PBI : ℤ) - QB)) := by
    have := a2; unfold kv at this; rw [List.map_map] at this
    rw [show cv CKCell.accR l2 = _ from this, tc_tc_add]
    congr 1; ring
  -- stage 3
  obtain ⟨l3, r3, a3, len3, va3, vb3, ea3, eb3, f3⟩ := conv_lens lensC3 ckz0 ckbit l2 len2 hN
    (PA := PAR) (QA := QA) (PB := PBI) (QB := QB) (C := CI)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s2vaR.trans s1vaR)).trans h1)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s2ea.trans s1ea)).trans h5)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s2vbI.trans s1vbI)).trans h4)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s2eb.trans s1eb)).trans h6)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s2accI.trans s1accI)).trans h8)
    b1 b5 b4 b6
  have q3 : l3.map lensQ3.get = l2.map lensQ3.get := f3 lensQ3 (fun _ _ => rfl)
  have s3vaR : l3.map CKCell.vaR = l2.map CKCell.vaR := by
    have := va3; rw [List.map_map, List.map_map] at this; exact this
  have s3ea : l3.map CKCell.ea = l2.map CKCell.ea := by
    have := ea3; rw [List.map_map, List.map_map] at this; exact this
  have s3eb : l3.map CKCell.eb = l2.map CKCell.eb := by
    have := eb3; rw [List.map_map, List.map_map] at this; exact this
  have s3accR : l3.map CKCell.accR = l2.map CKCell.accR := cmap_proj q3 (fun t => t.1)
  have s3vaI : l3.map CKCell.vaI = l2.map CKCell.vaI := cmap_proj q3 (fun t => t.2.1)
  have s3vbR : l3.map CKCell.vbR = l2.map CKCell.vbR := cmap_proj q3 (fun t => t.2.2)
  have c3I : cv CKCell.accI l3 = tc N ((CI : ℤ) + ((PAR : ℤ) - QA) * ((PBI : ℤ) - QB)) := by
    have := a3; unfold kv at this; rw [List.map_map] at this; exact this
  -- stage 4
  obtain ⟨l4, r4, a4, -, -, -, -, -, f4⟩ := conv_lens lensC4 ckz0 ckbit l3 len3 hN
    (PA := PAI) (QA := QA) (PB := PBR) (QB := QB)
    (C := tc N ((CI : ℤ) + ((PAR : ℤ) - QA) * ((PBI : ℤ) - QB)))
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s3vaI.trans (s2vaI.trans s1vaI))).trans h2)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s3ea.trans (s2ea.trans s1ea))).trans h5)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s3vbR.trans (s2vbR.trans s1vbR))).trans h3)
    (by unfold kv; rw [List.map_map]; exact (cv_congr (s3eb.trans (s2eb.trans s1eb))).trans h6)
    (by unfold kv; rw [List.map_map]; exact c3I) b2 b5 b3 b6
  have q4 : l4.map lensQ4.get = l3.map lensQ4.get := f4 lensQ4 (fun _ _ => rfl)
  have s4accR : l4.map CKCell.accR = l3.map CKCell.accR := cmap_proj q4 (fun t => t.1)
  have c4I : cv CKCell.accI l4 = tc N ((CI : ℤ) + ((PAR : ℤ) - QA) * ((PBI : ℤ) - QB) +
      ((PAI : ℤ) - QA) * ((PBR : ℤ) - QB)) := by
    have := a4; unfold kv at this; rw [List.map_map] at this
    rw [show cv CKCell.accI l4 = _ from this, tc_tc_add]
  -- composition
  have hC1 := ProgOn.seq_reachFirst (A := CS1) (B := CS2) (e := Sum.inr MulI.done)
    (show CS2.start ≠ Sum.inr MulI.done by decide) r1 r2
  have hC2 := ProgOn.seq_reachFirst (A := CC1) (B := CS3) (e := Sum.inr (Sum.inr MulI.done))
    (show CS3.start ≠ Sum.inr MulI.done by decide) hC1 r3
  have hall := ProgOn.seq_reachFirst (A := CC2) (B := CS4) (e := Sum.inr (Sum.inr MulI.done))
    (show CS4.start ≠ Sum.inr MulI.done by decide) hC2 r4
  refine ⟨l4, ?_, (cv_congr (s4accR.trans s3accR)).trans c2R, c4I⟩
  convert hall using 1
  ring

/-! ### Complex convolution: the Kronecker identities, the layout and the compiled machine -/

/-- The real part of the complex convolution of `a = ar + i·ai` and `b = br + i·bi`. -/
def cconvR (ar ai br bi : List ℤ) : List ℤ :=
  (List.range (ar.length + br.length - 1)).map fun k => convAt ar br k - convAt ai bi k

/-- The imaginary part of the complex convolution. -/
def cconvI (ar ai br bi : List ℤ) : List ℤ :=
  (List.range (ar.length + br.length - 1)).map fun k => convAt ar bi k + convAt ai br k

theorem kron_cconvR (L : ℕ) {ar ai br bi : List ℤ} (hai : ai.length = ar.length)
    (hbi : bi.length = br.length) :
    kron L ar * kron L br - kron L ai * kron L bi = kron L (cconvR ar ai br bi) := by
  rw [← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← eval_mul,
    ← eval_mul, ← eval_sub]
  congr 1
  ext k
  rw [coeff_sub, cpoly_mul_coeff, cpoly_mul_coeff, cpoly_coeff]
  by_cases hk : k < ar.length + br.length - 1
  · rw [List.getD_eq_getElem _ _ (by simp [cconvR, hk])]
    simp [cconvR]
  · rw [List.getD_eq_default _ _ (by simp [cconvR]; omega), convAt_eq_zero ar br k (by omega),
      convAt_eq_zero ai bi k (by rw [hai, hbi]; omega)]
    ring

theorem kron_cconvI (L : ℕ) {ar ai br bi : List ℤ} (hai : ai.length = ar.length)
    (hbi : bi.length = br.length) :
    kron L ar * kron L bi + kron L ai * kron L br = kron L (cconvI ar ai br bi) := by
  rw [← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← cpoly_eval, ← eval_mul,
    ← eval_mul, ← eval_add]
  congr 1
  ext k
  rw [coeff_add, cpoly_mul_coeff, cpoly_mul_coeff, cpoly_coeff]
  by_cases hk : k < ar.length + br.length - 1
  · rw [List.getD_eq_getElem _ _ (by simp [cconvI, hk])]
    simp [cconvI]
  · rw [List.getD_eq_default _ _ (by simp [cconvI]; omega),
      convAt_eq_zero ar bi k (by rw [hbi]; omega), convAt_eq_zero ai br k (by rw [hai]; omega)]
    ring

theorem cconvR_length (ar ai br bi : List ℤ) :
    (cconvR ar ai br bi).length = ar.length + br.length - 1 := by simp [cconvR]

theorem cconvI_length (ar ai br bi : List ℤ) :
    (cconvI ar ai br bi).length = ar.length + br.length - 1 := by simp [cconvI]

theorem map_range_getD (l : List Bool) (n : ℕ) (h : l.length = n) :
    (List.range n).map (fun i => l.getD i false) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

/-- Eight tracks zipped into complex convolution cells, cell by cell; the multiplier's `x, y`
start at zero. -/
def mkCK (as bs cs ds es fs gs hs : List Bool) : List CKCell :=
  (List.range as.length).map fun i =>
    ⟨false, false, gs.getD i false, hs.getD i false, as.getD i false, bs.getD i false,
      cs.getD i false, ds.getD i false, es.getD i false, fs.getD i false⟩

theorem mkCK_spec (as bs cs ds es fs gs hs : List Bool) (h1 : bs.length = as.length)
    (h2 : cs.length = as.length) (h3 : ds.length = as.length) (h4 : es.length = as.length)
    (h5 : fs.length = as.length) (h6 : gs.length = as.length) (h7 : hs.length = as.length) :
    (mkCK as bs cs ds es fs gs hs).map CKCell.vaR = as ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.vaI = bs ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.vbR = cs ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.vbI = ds ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.ea = es ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.eb = fs ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.accR = gs ∧
      (mkCK as bs cs ds es fs gs hs).map CKCell.accI = hs ∧
      (mkCK as bs cs ds es fs gs hs).length = as.length := by
  unfold mkCK
  simp only [List.map_map, Function.comp_def, List.length_map, List.length_range]
  exact ⟨map_range_getD as _ rfl, map_range_getD bs _ h1, map_range_getD cs _ h2,
    map_range_getD ds _ h3, map_range_getD es _ h4, map_range_getD fs _ h5,
    map_range_getD gs _ h6, map_range_getD hs _ h7, trivial⟩

/-- The complex convolution layout on `N` cells: the packed excess codes of the four parts, the
two input excess constants, and the output excess constant on both accumulators. -/
def cconvInput (N L : ℕ) (ar ai br bi : List ℤ) : List CKCell :=
  mkCK (bitsOf N (pack L (excessCodes L ar))) (bitsOf N (pack L (excessCodes L ai)))
    (bitsOf N (pack L (excessCodes L br))) (bitsOf N (pack L (excessCodes L bi)))
    (bitsOf N (excessConst L ar.length)) (bitsOf N (excessConst L br.length))
    (bitsOf N (excessConst L (ar.length + br.length - 1)))
    (bitsOf N (excessConst L (ar.length + br.length - 1)))

/-- **Complex convolution on the compiled Turing machine.** Let `a = ar + i·ai` and
`b = br + i·bi` be nonempty coefficient vectors (`|ai| = |ar|`, `|bi| = |br|`) with parts in the
`L`-bit range, whose complex convolution `c = a ∗ b` has real and imaginary parts in the `L`-bit
range, and let `(|ar| + |br| − 1)L ≤ N`. From the layout `cconvInput N L ar ai br bi` the compiled
single-tape TM runs exactly `(2(t_R + t_I) + 12)(2N + 2) ≤ (4N + 12)(2N + 2)` transitions, where
`t_R, t_I` are the bit lengths of the codes of `kron L br` and `kron L bi`. Its accumulators then
hold the packed excess codes of `Re c` and `Im c`: the `k`-th `L`-bit words are
`Σ_{i+j=k} (ar_i br_j − ai_i bi_j) + 2^{L−1}` and `Σ_{i+j=k} (ar_i bi_j + ai_i br_j) + 2^{L−1}`. -/
theorem cconv_tm {N L : ℕ} (hL : 0 < L) {ar ai br bi : List ℤ} (ha0 : ar ≠ []) (hb0 : br ≠ [])
    (hai : ai.length = ar.length) (hbi : bi.length = br.length)
    (h1 : ∀ x ∈ ar, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (h2 : ∀ x ∈ ai, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (h3 : ∀ x ∈ br, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (h4 : ∀ x ∈ bi, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hcR : ∀ x ∈ cconvR ar ai br bi, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hcI : ∀ x ∈ cconvI ar ai br bi, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1))
    (hKN : (ar.length + br.length - 1) * L ≤ N)
    (T : ℤ → Sym CKCell) (hT : cconvProg.toProg.Repr T (cconvInput N L ar ai br bi)) :
    ∃ l' T', cconvProg.toProg.Repr T' l' ∧
      cv CKCell.accR l' = pack L (excessCodes L (cconvR ar ai br bi)) ∧
      cv CKCell.accI l' = pack L (excessCodes L (cconvI ar ai br bi)) ∧
      (∀ k < ar.length + br.length - 1,
        cv CKCell.accR l' / 2 ^ (k * L) % 2 ^ L =
            (convAt ar br k - convAt ai bi k + 2 ^ (L - 1)).toNat ∧
          cv CKCell.accI l' / 2 ^ (k * L) % 2 ^ L =
            (convAt ar bi k + convAt ai br k + 2 ^ (L - 1)).toNat) ∧
      cconvProg.toProg.toTM.run
          ⟨.fwd cconvProg.start (cconvProg.toProg.init cconvProg.start), T, 0⟩
          ((2 * (trips (tc N (kron L br)) + trips (tc N (kron L bi))) + 12) * (2 * N + 2)) =
        ⟨.fwd (Sum.inr (Sum.inr MulI.done))
          (cconvProg.toProg.init (Sum.inr (Sum.inr MulI.done))), T', 0⟩ ∧
      (2 * (trips (tc N (kron L br)) + trips (tc N (kron L bi))) + 12) * (2 * N + 2) ≤
        (4 * N + 12) * (2 * N + 2) := by
  have hapos : 0 < ar.length := List.length_pos_of_ne_nil ha0
  have hbpos : 0 < br.length := List.length_pos_of_ne_nil hb0
  have hN : 0 < N := by
    have : 1 * 1 ≤ (ar.length + br.length - 1) * L := Nat.mul_le_mul (by omega) hL
    omega
  have hpow : ∀ n, n ≤ ar.length + br.length - 1 → 2 ^ (L * n) ≤ 2 ^ N := fun n hn =>
    Nat.pow_le_pow_right (by norm_num)
      (le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right L hn) hKN)
  have hP : ∀ c : List ℤ, (∀ x ∈ c, -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1)) →
      c.length ≤ ar.length + br.length - 1 → pack L (excessCodes L c) < 2 ^ N := by
    intro c hc hlen
    have := pack_lt L _ (excessCodes_lt hL c hc)
    rw [show (excessCodes L c).length = c.length by simp [excessCodes]] at this
    exact lt_of_lt_of_le this (hpow _ hlen)
  have b1 := hP ar h1 (by omega)
  have b2 := hP ai h2 (by omega)
  have b3 := hP br h3 (by omega)
  have b4 := hP bi h4 (by omega)
  have bR := hP _ hcR (by rw [cconvR_length])
  have bI := hP _ hcI (by rw [cconvI_length])
  have b5 : excessConst L ar.length < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ (by omega))
  have b6 : excessConst L br.length < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ (by omega))
  have b7 : excessConst L (ar.length + br.length - 1) < 2 ^ N :=
    lt_of_lt_of_le (excessConst_lt hL _) (hpow _ le_rfl)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := mkCK_spec (bitsOf N (pack L (excessCodes L ar)))
    (bitsOf N (pack L (excessCodes L ai))) (bitsOf N (pack L (excessCodes L br)))
    (bitsOf N (pack L (excessCodes L bi))) (bitsOf N (excessConst L ar.length))
    (bitsOf N (excessConst L br.length)) (bitsOf N (excessConst L (ar.length + br.length - 1)))
    (bitsOf N (excessConst L (ar.length + br.length - 1)))
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
    (by simp [bitsOf_length]) (by simp [bitsOf_length]) (by simp [bitsOf_length])
    (by simp [bitsOf_length])
  rw [bitsOf_length] at e9
  have k1 : cv CKCell.vaR (cconvInput N L ar ai br bi) = pack L (excessCodes L ar) := by
    unfold cv cconvInput; rw [e1, val_bitsOf, Nat.mod_eq_of_lt b1]
  have k2 : cv CKCell.vaI (cconvInput N L ar ai br bi) = pack L (excessCodes L ai) := by
    unfold cv cconvInput; rw [e2, val_bitsOf, Nat.mod_eq_of_lt b2]
  have k3 : cv CKCell.vbR (cconvInput N L ar ai br bi) = pack L (excessCodes L br) := by
    unfold cv cconvInput; rw [e3, val_bitsOf, Nat.mod_eq_of_lt b3]
  have k4 : cv CKCell.vbI (cconvInput N L ar ai br bi) = pack L (excessCodes L bi) := by
    unfold cv cconvInput; rw [e4, val_bitsOf, Nat.mod_eq_of_lt b4]
  have k5 : cv CKCell.ea (cconvInput N L ar ai br bi) = excessConst L ar.length := by
    unfold cv cconvInput; rw [e5, val_bitsOf, Nat.mod_eq_of_lt b5]
  have k6 : cv CKCell.eb (cconvInput N L ar ai br bi) = excessConst L br.length := by
    unfold cv cconvInput; rw [e6, val_bitsOf, Nat.mod_eq_of_lt b6]
  have k7 : cv CKCell.accR (cconvInput N L ar ai br bi) =
      excessConst L (ar.length + br.length - 1) := by
    unfold cv cconvInput; rw [e7, val_bitsOf, Nat.mod_eq_of_lt b7]
  have k8 : cv CKCell.accI (cconvInput N L ar ai br bi) =
      excessConst L (ar.length + br.length - 1) := by
    unfold cv cconvInput; rw [e8, val_bitsOf, Nat.mod_eq_of_lt b7]
  obtain ⟨l', hr, haR, haI⟩ := cconv_run (cconvInput N L ar ai br bi) e9 hN k1 k2 k3 k4 k5 k6 k7 k8
    b1 b2 b3 b4 b5 b6
  have hAR : ((pack L (excessCodes L ar) : ℕ) : ℤ) - (excessConst L ar.length : ℕ) = kron L ar := by
    rw [pack_excess L ar (fun x hx => (h1 x hx).1)]; unfold excessConst; ring
  have hAI : ((pack L (excessCodes L ai) : ℕ) : ℤ) - (excessConst L ar.length : ℕ) = kron L ai := by
    rw [pack_excess L ai (fun x hx => (h2 x hx).1), hai]; unfold excessConst; ring
  have hBR : ((pack L (excessCodes L br) : ℕ) : ℤ) - (excessConst L br.length : ℕ) = kron L br := by
    rw [pack_excess L br (fun x hx => (h3 x hx).1)]; unfold excessConst; ring
  have hBI : ((pack L (excessCodes L bi) : ℕ) : ℤ) - (excessConst L br.length : ℕ) = kron L bi := by
    rw [pack_excess L bi (fun x hx => (h4 x hx).1), hbi]; unfold excessConst; ring
  have hCR : ((excessConst L (ar.length + br.length - 1) : ℕ) : ℤ) + kron L ar * kron L br -
      kron L ai * kron L bi = ((pack L (excessCodes L (cconvR ar ai br bi)) : ℕ) : ℤ) := by
    rw [add_sub_assoc, kron_cconvR L hai hbi,
      pack_excess L _ (fun x hx => (hcR x hx).1), cconvR_length]
    unfold excessConst; ring
  have hCI : ((excessConst L (ar.length + br.length - 1) : ℕ) : ℤ) + kron L ar * kron L bi +
      kron L ai * kron L br = ((pack L (excessCodes L (cconvI ar ai br bi)) : ℕ) : ℤ) := by
    rw [add_assoc, kron_cconvI L hai hbi,
      pack_excess L _ (fun x hx => (hcI x hx).1), cconvI_length]
    unfold excessConst; ring
  rw [hAR, hAI, hBR, hBI, hCR, tc_natCast bR] at haR
  rw [hAR, hAI, hBR, hBI, hCI, tc_natCast bI] at haI
  rw [hBR, hBI] at hr
  obtain ⟨T', hT', hrun⟩ := cconvProg.toProg.reach_run hr.reach T hT
  refine ⟨l', T', hT', haR, haI, fun k hk => ⟨?_, ?_⟩, hrun, ?_⟩
  · rw [haR, pack_word L _ k (by simp [excessCodes, cconvR_length]; exact hk)
      (excessCodes_lt hL _ hcR)]
    simp [excessCodes, cconvR]
  · rw [haI, pack_word L _ k (by simp [excessCodes, cconvI_length]; exact hk)
      (excessCodes_lt hL _ hcI)]
    simp [excessCodes, cconvI]
  · have t1 := trips_le N (tc N (kron L br)) (tc_lt _ _)
    have t2 := trips_le N (tc N (kron L bi)) (tc_lt _ _)
    exact Nat.mul_le_mul_right _ (by omega)

/-- The parts of the packed complex convolution are the parts of the Fourier convolution. -/
theorem cconv_boxList_range {L R : ℕ} (ar ai br bi : ℤ × ℤ → ℤ)
    (har : ∀ p ∉ modeBox R, ar p = 0) (hai : ∀ p ∉ modeBox R, ai p = 0)
    (hcR : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R ar br k - bconv R ai bi k ∧
      bconv R ar br k - bconv R ai bi k < 2 ^ (L - 1))
    (hcI : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R ar bi k + bconv R ai br k ∧
      bconv R ar bi k + bconv R ai br k < 2 ^ (L - 1)) :
    (∀ x ∈ cconvR (boxList R ar) (boxList R ai) (boxList R br) (boxList R bi),
        -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1)) ∧
      (∀ x ∈ cconvI (boxList R ar) (boxList R ai) (boxList R br) (boxList R bi),
        -(2 : ℤ) ^ (L - 1) ≤ x ∧ x < 2 ^ (L - 1)) := by
  constructor
  · intro x hx
    simp only [cconvR, List.mem_map, List.mem_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [boxList_length, boxList_length, blen_conv] at hn
    obtain ⟨hk, hidx⟩ := bidx2_decode hn
    have e1 := convAt_box R ar br har hk
    have e2 := convAt_box R ai bi hai hk
    rw [hidx] at e1 e2
    rw [e1, e2]
    exact hcR _ hk
  · intro x hx
    simp only [cconvI, List.mem_map, List.mem_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    rw [boxList_length, boxList_length, blen_conv] at hn
    obtain ⟨hk, hidx⟩ := bidx2_decode hn
    have e1 := convAt_box R ar bi har hk
    have e2 := convAt_box R ai br hai hk
    rw [hidx] at e1 e2
    rw [e1, e2]
    exact hcI _ hk

/-- **Complex Fourier convolution on the compiled Turing machine.** Let `a = ar + i·ai` and
`b = br + i·bi` have parts `ℤ² → ℤ` in the `L`-bit range, with `ar, ai` supported on the box
`[−R, R]²`, and let the real and imaginary parts of the Fourier convolution `a ⋆ b` lie in the
`L`-bit range on `[−2R, 2R]²`. With `(4R + 1)² L ≤ N`, from the packed layout the compiled
single-tape TM runs at most `(4N + 12)(2N + 2)` transitions, and for every mode
`k ∈ [−2R, 2R]²` the accumulators' words at `κ(k)` are `Re (a ⋆ b)(k) + 2^{L−1}` and
`Im (a ⋆ b)(k) + 2^{L−1}`. -/
theorem cconv2_tm {N L R : ℕ} (hL : 0 < L) {ar ai br bi : ℤ × ℤ → ℤ}
    (har : ∀ p ∉ modeBox R, ar p = 0) (hai : ∀ p ∉ modeBox R, ai p = 0)
    (h1 : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ ar p ∧ ar p < 2 ^ (L - 1))
    (h2 : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ ai p ∧ ai p < 2 ^ (L - 1))
    (h3 : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ br p ∧ br p < 2 ^ (L - 1))
    (h4 : ∀ p, -(2 : ℤ) ^ (L - 1) ≤ bi p ∧ bi p < 2 ^ (L - 1))
    (hcR : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R ar br k - bconv R ai bi k ∧
      bconv R ar br k - bconv R ai bi k < 2 ^ (L - 1))
    (hcI : ∀ k ∈ modeBox (2 * R), -(2 : ℤ) ^ (L - 1) ≤ bconv R ar bi k + bconv R ai br k ∧
      bconv R ar bi k + bconv R ai br k < 2 ^ (L - 1))
    (hKN : (4 * R + 1) ^ 2 * L ≤ N) (T : ℤ → Sym CKCell)
    (hT : cconvProg.toProg.Repr T
      (cconvInput N L (boxList R ar) (boxList R ai) (boxList R br) (boxList R bi))) :
    ∃ l' T' c, cconvProg.toProg.Repr T' l' ∧
      (∀ k ∈ modeBox (2 * R),
        cv CKCell.accR l' / 2 ^ (bidx2 R k * L) % 2 ^ L =
            (bconv R ar br k - bconv R ai bi k + 2 ^ (L - 1)).toNat ∧
          cv CKCell.accI l' / 2 ^ (bidx2 R k * L) % 2 ^ L =
            (bconv R ar bi k + bconv R ai br k + 2 ^ (L - 1)).toNat) ∧
      cconvProg.toProg.toTM.run
          ⟨.fwd cconvProg.start (cconvProg.toProg.init cconvProg.start), T, 0⟩ c =
        ⟨.fwd (Sum.inr (Sum.inr MulI.done))
          (cconvProg.toProg.init (Sum.inr (Sum.inr MulI.done))), T', 0⟩ ∧
      c ≤ (4 * N + 12) * (2 * N + 2) := by
  have hlen : (boxList R ar).length + (boxList R br).length - 1 = (4 * R + 1) ^ 2 := by
    rw [boxList_length, boxList_length, blen_conv]
  obtain ⟨hR, hI⟩ := cconv_boxList_range ar ai br bi har hai hcR hcI
  obtain ⟨l', T', hT', -, -, hw, hrun, hcost⟩ := cconv_tm hL (boxList_ne_nil R ar)
    (boxList_ne_nil R br) (by rw [boxList_length, boxList_length])
    (by rw [boxList_length, boxList_length]) (boxList_range ar h1) (boxList_range ai h2)
    (boxList_range br h3) (boxList_range bi h4) hR hI (by rw [hlen]; exact hKN) T hT
  refine ⟨l', T', _, hT', fun k hk => ?_, hrun, hcost⟩
  obtain ⟨w1, w2⟩ := hw _ (by rw [hlen]; exact bidx2_lt hk)
  rw [w1, w2, convAt_box R ar br har hk, convAt_box R ai bi hai hk, convAt_box R ar bi har hk,
    convAt_box R ai br hai hk]
  exact ⟨rfl, rfl⟩

end PVNP.Discrete.SweepArith
