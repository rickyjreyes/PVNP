import PVNP.SweepReg

/-!
# A library of register programs with verified values and costs

Programs of the register machine (`SweepReg`) for the arithmetic of the continuum evaluator,
each proved at the level of register values with an explicit cost bound. Every program here
compiles to a single-tape Turing machine with the same cost (`compile_first`).

* **Bits** (`testBit_val`, `val_ofFn_testBit`, `bitv`, `val_map_bit`): the bitwise map of two
  registers is a function of their values.
* **Functional semantics** (`Prim.sem`, `Prim.rv_apply`): the register values after any
  instruction are a function of the values before it and of the tape length.
* **Loops with a variant** (`run_loop`): if at most `k` iterations remain and each body run costs
  at most `B`, the loop costs at most `k (2N + 2 + B) + 2N + 2`.
* **Copying and clearing** (`run_mov`, `run_clr`).
* **Shifts by a register amount** (`run_shlBy`, `run_shrBy`): `x := x · 2^c mod 2^N` and
  `x := ⌊x / 2^c⌋`.
* **Multiplication** (`run_mulP`): `p := a · b mod 2^N`, by shift and add, in at most
  `(N + 4) · 6 (2N + 2)` transitions.
* **Division** (`run_divP`): `q := ⌊a/d⌋` and `r := a mod d` for `d ≥ 1` and `2a < 2^N`, by
  doubling the divisor and then restoring, in at most `16 (N + 1)(2N + 2)` transitions.
* **Tape extension and the input length** (`run_extendBy`, `run_bitLen`): the tape grows by the
  value of a register, and the bit length of the input marker `2^n − 1` is `n`.

Signed arithmetic is two's complement modulo `2^N` (`tc`); `sub` is exact in that sense.
-/

namespace PVNP.Discrete.SweepReg

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.SweepArith

variable {K : ℕ}

/-! ### Bits of register values -/

theorem testBit_val : ∀ (m : List Bool) (t : ℕ), (val m).testBit t = m.getD t false
  | [], t => by simp [val]
  | b :: m, 0 => by
    simp only [val, List.getD_cons_zero]
    rw [Nat.testBit_zero]
    cases b <;> simp [Nat.add_mul_mod_self_left]
  | b :: m, t + 1 => by
    simp only [val, List.getD_cons_succ]
    rw [Nat.testBit_succ, ← testBit_val m t]
    congr 1
    rcases b with _ | _ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem val_ofFn_testBit (a : ℕ) : ∀ N : ℕ, val (List.ofFn fun t : Fin N => a.testBit t) = a % 2 ^ N
  | 0 => by simp [val, Nat.mod_one]
  | N + 1 => by
    rw [List.ofFn_succ, val]
    simp only [Fin.val_zero, Fin.val_succ]
    have ih := val_ofFn_testBit (a / 2) N
    have e : (fun i : Fin N => a.testBit (i + 1)) = fun i : Fin N => (a / 2).testBit i := by
      funext i; rw [Nat.testBit_succ]
    rw [e, ih, Nat.testBit_zero, pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]

/-- The bitwise map of two numbers on `N` bits. -/
def bitv (op : Bool → Bool → Bool) (N a b : ℕ) : ℕ :=
  val (List.ofFn fun t : Fin N => op (a.testBit t) (b.testBit t))

theorem rv_testBit (l : List (RC K)) (i : Fin K) (t : ℕ) (ht : t < l.length) :
    (rv l i).testBit t = l[t] i := by
  rw [rv, testBit_val, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]

theorem val_map_bit (l : List (RC K)) (op : Bool → Bool → Bool) (j k : Fin K) :
    val (l.map fun x => op (x j) (x k)) = bitv op l.length (rv l j) (rv l k) := by
  unfold bitv
  congr 1
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [rv_testBit l j t (by simpa using h1), rv_testBit l k t (by simpa using h1)]

theorem bitv_false (N a b : ℕ) : bitv (fun _ _ => false) N a b = 0 := by
  unfold bitv
  have : (List.ofFn fun _ : Fin N => false) = List.replicate N false := by
    rw [List.eq_replicate_iff]; simp
  rw [this, val_replicate]; simp

theorem bitv_fst (N a b : ℕ) : bitv (fun x _ => x) N a b = a % 2 ^ N := by
  unfold bitv; exact val_ofFn_testBit a N

theorem bitv_and_ones (N a : ℕ) : bitv (· && ·) N a (2 ^ N - 1) = a % 2 ^ N := by
  unfold bitv
  rw [← val_ofFn_testBit a N]
  congr 1
  apply List.ext_getElem
  · simp
  · intro t h1 _
    simp only [List.getElem_ofFn, Nat.testBit_two_pow_sub_one]
    have : t < N := by simpa using h1
    simp [this]

theorem bitv_and_zero (N a : ℕ) : bitv (· && ·) N a 0 = 0 := by
  unfold bitv
  have : (List.ofFn fun t : Fin N => (a.testBit t && (0 : ℕ).testBit t)) =
      List.replicate N false := by
    rw [List.eq_replicate_iff]; simp
  rw [this, val_replicate]; simp

/-! ### The functional semantics of the instructions -/

namespace Prim

/-- The effect of an instruction on the register values, on a tape of length `N`. -/
def sem : Prim K → ℕ → (Fin K → ℕ) → Fin K → ℕ
  | sub i j k, N, σ => Function.update σ i (tc N ((σ j : ℤ) - σ k))
  | add i j k, N, σ => Function.update σ i ((σ j + σ k) % 2 ^ N)
  | shl i j, N, σ => Function.update σ i (2 * σ j % 2 ^ N)
  | shr i j, _, σ => Function.update σ i (σ j / 2)
  | bit i j k op, N, σ => Function.update σ i (bitv op N (σ j) (σ k))
  | spread i j, N, σ => Function.update σ i (if σ j % 2 = 1 then 2 ^ N - 1 else 0)
  | lt i j k, N, σ => Function.update σ i (if σ j < σ k then 2 ^ N - 1 else 0)
  | one i, N, σ => Function.update σ i (1 % 2 ^ N)
  | extend, _, σ => σ

/-- **The register values after an instruction.** -/
theorem rv_apply (p : Prim K) (l : List (RC K)) : rv (p.apply l) = p.sem l.length (rv l) := by
  cases p with
  | sub i j k => exact sub_rv i j k l
  | add i j k => exact add_rv i j k l
  | shl i j => exact shl_rv i j l
  | shr i j => exact shr_rv i j l
  | bit i j k op => rw [bit_rv, val_map_bit]; rfl
  | spread i j => exact spread_rv i j l
  | lt i j k => exact lt_rv i j k l
  | one i => exact one_rv i l
  | extend => exact extend_rv l

end Prim

/-! ### Programs over a fixed tape length -/

/-- A primitive instruction other than the extension keeps the tape length and costs `2N + 2`. -/
theorem run_prim {p : Prim K} (hp : p ≠ Prim.extend) (l : List (RC K)) :
    Run (.prim p) l (p.apply l) (2 * l.length + 2) ∧ (p.apply l).length = l.length ∧
      rv (p.apply l) = p.sem l.length (rv l) := by
  refine ⟨?_, Prim.apply_length_of p hp l, Prim.rv_apply p l⟩
  have h := Run.prim p l
  rwa [Prim.cost_of p hp] at h

/-- **Loops with a variant.** `I k l`: at most `k` iterations remain. -/
theorem run_loop {j : Fin K} {P : RProg K} (N B : ℕ) (I : ℕ → List (RC K) → Prop)
    (Q : List (RC K) → Prop)
    (hlen : ∀ k l, I k l → l.length = N)
    (h0 : ∀ l, I 0 l → rv l j = 0)
    (hQ : ∀ k l, I k l → rv l j = 0 → Q l)
    (hs : ∀ k l, I (k + 1) l → rv l j ≠ 0 → ∃ l' c, Run P l l' c ∧ c ≤ B ∧ I k l') :
    ∀ k l, I k l → ∃ l' c, Run (.loop j P) l l' c ∧ Q l' ∧
      c ≤ k * (2 * N + 2 + B) + (2 * N + 2) := by
  intro k
  induction k with
  | zero =>
    intro l hI
    have hz := h0 l hI
    refine ⟨l, _, Run.stop hz, hQ 0 l hI hz, ?_⟩
    rw [hlen 0 l hI]; omega
  | succ k ih =>
    intro l hI
    have e : (k + 1) * (2 * N + 2 + B) = k * (2 * N + 2 + B) + (2 * N + 2 + B) := Nat.succ_mul _ _
    by_cases hz : rv l j = 0
    · refine ⟨l, _, Run.stop hz, hQ _ l hI hz, ?_⟩
      rw [hlen _ l hI]; omega
    · obtain ⟨l₁, c₁, hr₁, hc₁, hI₁⟩ := hs k l hI hz
      obtain ⟨l₂, c₂, hr₂, hQ₂, hc₂⟩ := ih l₁ hI₁
      refine ⟨l₂, _, Run.iter hz hr₁ hr₂, hQ₂, ?_⟩
      rw [hlen _ l hI]
      omega

theorem tc_nat (N k : ℕ) (h : k < 2 ^ N) : tc N (k : ℤ) = k := by
  unfold tc
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h)]
  simp

theorem tc_pred (N k : ℕ) (h : k + 1 < 2 ^ N) : tc N (((k + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) = k := by
  have e : (((k + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) = (k : ℤ) := by push_cast; ring
  rw [e, tc_nat N k (by omega)]

namespace RProg

/-- `r_i := 0`. -/
def clr (i : Fin K) : RProg K := .prim (.bit i i i fun _ _ => false)

/-- `r_i := r_j`. -/
def mov (i j : Fin K) : RProg K := .prim (.bit i j j fun x _ => x)

/-- `r_i := r_j AND r_k`. -/
def andR (i j k : Fin K) : RProg K := .prim (.bit i j k (· && ·))

/-- `x := x · 2^{r_c}` modulo `2^N`, counting down the copy `t` of `c` with the unit `o`. -/
def shlBy (x c t o : Fin K) : RProg K :=
  .seq (mov t c) (.loop t (.seq (.prim (.shl x x)) (.prim (.sub t t o))))

/-- `x := ⌊x / 2^{r_c}⌋`, counting down the copy `t` of `c` with the unit `o`. -/
def shrBy (x c t o : Fin K) : RProg K :=
  .seq (mov t c) (.loop t (.seq (.prim (.shr x x)) (.prim (.sub t t o))))

/-- `p := r_a · r_b` modulo `2^N`, by shift and add, with the scratch registers `x, y, t`. -/
def mulP (p a b x y t : Fin K) : RProg K :=
  .seq (.seq (.seq (mov x a) (mov y b)) (clr p))
    (.loop y (.seq (.seq (.seq (.seq (.prim (.spread t y)) (.prim (.bit t x t (· && ·))))
      (.prim (.add p p t))) (.prim (.shl x x))) (.prim (.shr y y))))

end RProg

/-! ### Clearing and copying -/

theorem run_clr (i : Fin K) (l : List (RC K)) :
    ∃ l', Run (RProg.clr i) l l' (2 * l.length + 2) ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) i 0 := by
  obtain ⟨hr, hlen, hv⟩ := run_prim (p := Prim.bit i i i fun _ _ => false) (by simp) l
  refine ⟨_, hr, hlen, ?_⟩
  rw [hv]; simp only [Prim.sem, bitv_false]

theorem run_mov (i j : Fin K) (l : List (RC K)) :
    ∃ l', Run (RProg.mov i j) l l' (2 * l.length + 2) ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) i (rv l j) := by
  obtain ⟨hr, hlen, hv⟩ := run_prim (p := Prim.bit i j j fun x _ => x) (by simp) l
  refine ⟨_, hr, hlen, ?_⟩
  rw [hv]; simp only [Prim.sem, bitv_fst, Nat.mod_eq_of_lt (rv_lt l j)]

/-! ### Shifts by a register amount -/

theorem run_shlBy {x c t o : Fin K} (hxt : x ≠ t) (hto : t ≠ o) (hxo : x ≠ o)
    (l : List (RC K)) (ho : rv l o = 1) :
    ∃ l' cst, Run (RProg.shlBy x c t o) l l' cst ∧ l'.length = l.length ∧
      rv l' x = rv l x * 2 ^ rv l c % 2 ^ l.length ∧ rv l' t = 0 ∧
      (∀ m, m ≠ x → m ≠ t → rv l' m = rv l m) ∧
      cst ≤ (2 * l.length + 2) + rv l c * (3 * (2 * l.length + 2)) + (2 * l.length + 2) := by
  set N := l.length with hN
  set X := rv l x
  set C := rv l c
  obtain ⟨l₁, hr₁, hlen₁, hv₁⟩ := run_mov t c l
  -- invariant: k iterations remain
  let I : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ k ≤ C ∧ rv l' t = k ∧
    rv l' x = X * 2 ^ (C - k) % 2 ^ N ∧ ∀ m, m ≠ x → m ≠ t → rv l' m = rv l m
  have hI₁ : I C l₁ := by
    refine ⟨hlen₁, le_rfl, by rw [hv₁, Function.update_self], ?_, fun m hmx hmt => ?_⟩
    · rw [hv₁, Function.update_of_ne hxt, Nat.sub_self, pow_zero, mul_one,
        Nat.mod_eq_of_lt (rv_lt l x)]
    · rw [hv₁, Function.update_of_ne hmt]
  have hloop := run_loop (j := t) (P := .seq (.prim (.shl x x)) (.prim (.sub t t o))) N
    (2 * (2 * N + 2)) I (fun l' => l'.length = N ∧ rv l' x = X * 2 ^ C % 2 ^ N ∧ rv l' t = 0 ∧
      ∀ m, m ≠ x → m ≠ t → rv l' m = rv l m)
    (fun k l' h => h.1) (fun l' h => h.2.2.1)
    (fun k l' h hz => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hk : k = 0 := by rw [← h3, hz]
      subst hk
      exact ⟨h1, by rw [h4, Nat.sub_zero], hz, h5⟩)
    (fun k l' h _ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨ha, hla, hva⟩ := run_prim (p := Prim.shl x x) (by simp) l'
      obtain ⟨hb, hlb, hvb⟩ := run_prim (p := Prim.sub t t o) (by simp) ((Prim.shl x x).apply l')
      refine ⟨_, _, Run.seq ha hb, ?_, ?_⟩
      · rw [hla, h1]; omega
      · have hto' : rv l' o = 1 := by rw [h5 o (Ne.symm hxo) (Ne.symm hto)]; exact ho
        have hkN : k + 1 < 2 ^ N := by rw [← h3, ← h1]; exact rv_lt l' t
        refine ⟨by rw [hlb, hla, h1], by omega, ?_, ?_, fun m hmx hmt => ?_⟩
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_self]
          rw [hva]
          simp only [Prim.sem, Function.update_of_ne (Ne.symm hxt), Function.update_of_ne (Ne.symm hxo)]
          rw [h3, hto', h1]
          exact tc_pred N k hkN
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_of_ne hxt]
          rw [hva]
          simp only [Prim.sem, Function.update_self]
          rw [h4, h1, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
          congr 1
          have e : C - k = (C - (k + 1)) + 1 := by omega
          rw [e, pow_succ]; ring
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_of_ne hmt]
          rw [hva]
          simp only [Prim.sem, Function.update_of_ne hmx]
          exact h5 m hmx hmt)
    C l₁ hI₁
  obtain ⟨l', cst, hr, ⟨hl', hx', ht', hm'⟩, hc⟩ := hloop
  refine ⟨l', _, Run.seq hr₁ hr, hl', hx', ht', hm', ?_⟩
  have e : 2 * N + 2 + 2 * (2 * N + 2) = 3 * (2 * N + 2) := by ring
  rw [e] at hc
  omega

theorem run_shrBy {x c t o : Fin K} (hxt : x ≠ t) (hto : t ≠ o) (hxo : x ≠ o)
    (l : List (RC K)) (ho : rv l o = 1) :
    ∃ l' cst, Run (RProg.shrBy x c t o) l l' cst ∧ l'.length = l.length ∧
      rv l' x = rv l x / 2 ^ rv l c ∧ rv l' t = 0 ∧
      (∀ m, m ≠ x → m ≠ t → rv l' m = rv l m) ∧
      cst ≤ (2 * l.length + 2) + rv l c * (3 * (2 * l.length + 2)) + (2 * l.length + 2) := by
  set N := l.length with hN
  set X := rv l x
  set C := rv l c
  obtain ⟨l₁, hr₁, hlen₁, hv₁⟩ := run_mov t c l
  let I : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ k ≤ C ∧ rv l' t = k ∧
    rv l' x = X / 2 ^ (C - k) ∧ ∀ m, m ≠ x → m ≠ t → rv l' m = rv l m
  have hI₁ : I C l₁ := by
    refine ⟨hlen₁, le_rfl, by rw [hv₁, Function.update_self], ?_, fun m hmx hmt => ?_⟩
    · rw [hv₁, Function.update_of_ne hxt, Nat.sub_self, pow_zero, Nat.div_one]
    · rw [hv₁, Function.update_of_ne hmt]
  have hloop := run_loop (j := t) (P := .seq (.prim (.shr x x)) (.prim (.sub t t o))) N
    (2 * (2 * N + 2)) I (fun l' => l'.length = N ∧ rv l' x = X / 2 ^ C ∧ rv l' t = 0 ∧
      ∀ m, m ≠ x → m ≠ t → rv l' m = rv l m)
    (fun k l' h => h.1) (fun l' h => h.2.2.1)
    (fun k l' h hz => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hk : k = 0 := by rw [← h3, hz]
      subst hk
      exact ⟨h1, by rw [h4, Nat.sub_zero], hz, h5⟩)
    (fun k l' h _ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨ha, hla, hva⟩ := run_prim (p := Prim.shr x x) (by simp) l'
      obtain ⟨hb, hlb, hvb⟩ := run_prim (p := Prim.sub t t o) (by simp) ((Prim.shr x x).apply l')
      refine ⟨_, _, Run.seq ha hb, ?_, ?_⟩
      · rw [hla, h1]; omega
      · have hto' : rv l' o = 1 := by rw [h5 o (Ne.symm hxo) (Ne.symm hto)]; exact ho
        have hkN : k + 1 < 2 ^ N := by rw [← h3, ← h1]; exact rv_lt l' t
        refine ⟨by rw [hlb, hla, h1], by omega, ?_, ?_, fun m hmx hmt => ?_⟩
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_self]
          rw [hva]
          simp only [Prim.sem, Function.update_of_ne (Ne.symm hxt), Function.update_of_ne (Ne.symm hxo)]
          rw [h3, hto', h1]
          exact tc_pred N k hkN
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_of_ne hxt]
          rw [hva]
          simp only [Prim.sem, Function.update_self]
          rw [h4, Nat.div_div_eq_div_mul]
          congr 1
          have e : C - k = (C - (k + 1)) + 1 := by omega
          rw [e, pow_succ]
        · rw [hvb, hla]
          simp only [Prim.sem, Function.update_of_ne hmt]
          rw [hva]
          simp only [Prim.sem, Function.update_of_ne hmx]
          exact h5 m hmx hmt)
    C l₁ hI₁
  obtain ⟨l', cst, hr, ⟨hl', hx', ht', hm'⟩, hc⟩ := hloop
  refine ⟨l', _, Run.seq hr₁ hr, hl', hx', ht', hm', ?_⟩
  have e : 2 * N + 2 + 2 * (2 * N + 2) = 3 * (2 * N + 2) := by ring
  rw [e] at hc
  omega

/-! ### Multiplication -/

theorem mul_step (A B d N : ℕ) :
    (A * (B % 2 ^ d) % 2 ^ N + (if B / 2 ^ d % 2 = 1 then A * 2 ^ d % 2 ^ N else 0)) % 2 ^ N =
      A * (B % 2 ^ (d + 1)) % 2 ^ N := by
  rw [pow_succ, Nat.mod_mul]
  rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ d) with h | h
  · rw [h, if_neg (by norm_num)]; simp
  · rw [h, if_pos rfl, ← Nat.add_mod]; congr 1; ring

theorem bitv_and_flag (N a : ℕ) (hc : Prop) [Decidable hc] (ha : a < 2 ^ N) :
    bitv (· && ·) N a (if hc then 2 ^ N - 1 else 0) = if hc then a else 0 := by
  split_ifs
  · rw [bitv_and_ones, Nat.mod_eq_of_lt ha]
  · exact bitv_and_zero N a

/-- The body of the multiplication loop. -/
def mulBody (p x y t : Fin K) : RProg K :=
  .seq (.seq (.seq (.seq (.prim (.spread t y)) (.prim (.bit t x t (· && ·))))
    (.prim (.add p p t))) (.prim (.shl x x))) (.prim (.shr y y))

theorem mulP_eq (p a b x y t : Fin K) :
    RProg.mulP p a b x y t =
      .seq (.seq (.seq (RProg.mov x a) (RProg.mov y b)) (RProg.clr p)) (.loop y (mulBody p x y t)) :=
  rfl

theorem run_mulBody {p x y t : Fin K} (hpx : p ≠ x) (hpy : p ≠ y) (hpt : p ≠ t) (hxy : x ≠ y)
    (hxt : x ≠ t) (hyt : y ≠ t) (l : List (RC K)) :
    ∃ l' c, Run (mulBody p x y t) l l' c ∧ c = 5 * (2 * l.length + 2) ∧ l'.length = l.length ∧
      rv l' p = (rv l p + (if rv l y % 2 = 1 then rv l x else 0)) % 2 ^ l.length ∧
      rv l' x = 2 * rv l x % 2 ^ l.length ∧ rv l' y = rv l y / 2 ∧
      ∀ m, m ≠ p → m ≠ x → m ≠ y → m ≠ t → rv l' m = rv l m := by
  obtain ⟨r1, n1, v1⟩ := run_prim (p := Prim.spread t y) (by simp) l
  obtain ⟨r2, n2, v2⟩ := run_prim (p := Prim.bit t x t (· && ·)) (by simp) ((Prim.spread t y).apply l)
  obtain ⟨r3, n3, v3⟩ := run_prim (p := Prim.add p p t) (by simp)
    ((Prim.bit t x t (· && ·)).apply ((Prim.spread t y).apply l))
  obtain ⟨r4, n4, v4⟩ := run_prim (p := Prim.shl x x) (by simp)
    ((Prim.add p p t).apply ((Prim.bit t x t (· && ·)).apply ((Prim.spread t y).apply l)))
  obtain ⟨r5, n5, v5⟩ := run_prim (p := Prim.shr y y) (by simp)
    ((Prim.shl x x).apply ((Prim.add p p t).apply ((Prim.bit t x t (· && ·)).apply
      ((Prim.spread t y).apply l))))
  refine ⟨_, _, Run.seq (Run.seq (Run.seq (Run.seq r1 r2) r3) r4) r5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [n4, n3, n2, n1]; ring
  · rw [n5, n4, n3, n2, n1]
  all_goals rw [v5, n4, v4, n3, v3, n2, v2, n1, v1]
  all_goals simp only [Prim.sem, Function.update_apply, hpx, hpy, hpt, hxy, hxt, hyt,
    Ne.symm hpx, Ne.symm hpy, Ne.symm hxy, if_true, if_false]
  · rw [bitv_and_flag _ _ _ (rv_lt l x)]
  · intro m hmp hmx hmy hmt
    simp only [hmp, hmx, hmy, hmt, if_false]

/-- **Multiplication modulo `2^N`.** -/
theorem run_mulP {p a b x y t : Fin K} (hpx : p ≠ x) (hpy : p ≠ y) (hpt : p ≠ t) (hxy : x ≠ y)
    (hxt : x ≠ t) (hyt : y ≠ t) (hbx : b ≠ x) (l : List (RC K)) :
    ∃ l' c, Run (RProg.mulP p a b x y t) l l' c ∧ l'.length = l.length ∧
      rv l' p = rv l a * rv l b % 2 ^ l.length ∧
      (∀ m, m ≠ p → m ≠ x → m ≠ y → m ≠ t → rv l' m = rv l m) ∧
      c ≤ (l.length + 4) * (6 * (2 * l.length + 2)) := by
  set N := l.length with hN
  obtain ⟨l₁, hr₁, hn₁, hv₁⟩ := run_mov x a l
  obtain ⟨l₂, hr₂, hn₂, hv₂⟩ := run_mov y b l₁
  obtain ⟨l₃, hr₃, hn₃, hv₃⟩ := run_clr p l₂
  let I : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ rv l' y < 2 ^ k ∧
    (∃ d, rv l' x = rv l a * 2 ^ d % 2 ^ N ∧ rv l' y = rv l b / 2 ^ d ∧
      rv l' p = rv l a * (rv l b % 2 ^ d) % 2 ^ N) ∧
    ∀ m, m ≠ p → m ≠ x → m ≠ y → m ≠ t → rv l' m = rv l m
  have hI₃ : I N l₃ := by
    have e3 : ∀ m, rv l₃ m = Function.update (Function.update (Function.update (rv l) x (rv l a)) y
        (Function.update (rv l) x (rv l a) b)) p 0 m := by
      intro m; rw [hv₃, hv₂, hv₁]
    refine ⟨by rw [hn₃, hn₂, hn₁], ?_, ⟨0, ?_, ?_, ?_⟩, fun m hmp hmx hmy hmt => ?_⟩
    · rw [e3]; simp only [Function.update_apply, Ne.symm hpy, hbx, if_true, if_false]
      exact rv_lt l b
    · rw [e3]; simp only [Function.update_apply, Ne.symm hpx, hxy, if_true, if_false]
      rw [pow_zero, mul_one, Nat.mod_eq_of_lt (rv_lt l a)]
    · rw [e3]; simp only [Function.update_apply, Ne.symm hpy, hbx, if_true, if_false]
      simp
    · rw [e3]; simp only [Function.update_apply, if_true]
      rw [pow_zero, Nat.mod_one, mul_zero, Nat.zero_mod]
    · rw [e3]; simp only [Function.update_apply, hmp, hmx, hmy, if_false]
  have hloop := run_loop (j := y) (P := mulBody p x y t) N (5 * (2 * N + 2)) I
    (fun l' => l'.length = N ∧ rv l' p = rv l a * rv l b % 2 ^ N ∧
      ∀ m, m ≠ p → m ≠ x → m ≠ y → m ≠ t → rv l' m = rv l m)
    (fun k l' h => h.1)
    (fun l' h => by have := h.2.1; rw [pow_zero] at this; omega)
    (fun k l' h hz => by
      obtain ⟨h1, -, ⟨d, -, hy, hp⟩, h5⟩ := h
      refine ⟨h1, ?_, h5⟩
      rw [hp]
      have hB : rv l b / 2 ^ d = 0 := by rw [← hy]; exact hz
      rw [Nat.div_eq_zero_iff] at hB
      rcases hB with hB | hB
      · exact absurd hB (by positivity)
      · rw [Nat.mod_eq_of_lt hB])
    (fun k l' h _ => by
      obtain ⟨h1, h2, ⟨d, hx, hy, hp⟩, h5⟩ := h
      obtain ⟨l'', c'', hr, hc'', hn, hvp, hvx, hvy, hvm⟩ := run_mulBody hpx hpy hpt hxy hxt hyt l'
      refine ⟨l'', c'', hr, by rw [hc'', h1], by rw [hn, h1], ?_, ⟨d + 1, ?_, ?_, ?_⟩, ?_⟩
      · rw [hvy, pow_succ] at *; omega
      · rw [hvx, hx, h1, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]; congr 1; ring
      · rw [hvy, hy, Nat.div_div_eq_div_mul, pow_succ]
      · rw [hvp, hp, hy, hx, h1, ← mul_step (rv l a) (rv l b) d N]
      · intro m hmp hmx hmy hmt
        rw [hvm m hmp hmx hmy hmt, h5 m hmp hmx hmy hmt])
    N l₃ hI₃
  obtain ⟨l', c, hr, ⟨hl', hp', hm'⟩, hc⟩ := hloop
  refine ⟨l', _, Run.seq (Run.seq (Run.seq hr₁ hr₂) hr₃) hr, hl', hp', hm', ?_⟩
  rw [hn₂, hn₁] at *
  have e : N * (2 * N + 2 + 5 * (2 * N + 2)) = N * (6 * (2 * N + 2)) := by ring
  rw [e] at hc
  have e2 : (N + 4) * (6 * (2 * N + 2)) = N * (6 * (2 * N + 2)) + 24 * (2 * N + 2) := by ring
  rw [e2]
  omega

/-! ### Division -/

theorem bitv_not (N a b : ℕ) : bitv (fun x _ => !x) N a b = 2 ^ N - 1 - a % 2 ^ N := by
  have h : ∀ M : ℕ, val (List.ofFn fun t : Fin M => !a.testBit t) + a % 2 ^ M = 2 ^ M - 1 := by
    intro M
    induction M generalizing a with
    | zero => rw [List.ofFn_zero, pow_zero, Nat.mod_one]; rfl
    | succ M ih =>
      rw [List.ofFn_succ, val]
      simp only [Fin.val_zero, Fin.val_succ]
      have e : (fun i : Fin M => !a.testBit (i + 1)) = fun i : Fin M => !(a / 2).testBit i := by
        funext i; rw [Nat.testBit_succ]
      rw [e]
      have ih' := ih (a / 2)
      rw [pow_succ', Nat.mod_mul, Nat.testBit_zero]
      have h2 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h] <;> omega
  unfold bitv
  have := h N
  show val (List.ofFn fun t : Fin N => !a.testBit t) = _
  omega

namespace RProg

/-- `r_i := 2^N − 1 − r_j` (bitwise complement). -/
def notR (i j : Fin K) : RProg K := .prim (.bit i j j fun x _ => !x)

/-- The flag `f := all ones` if `r_D ≤ r_r`, else zero. -/
def geF (f r D : Fin K) : RProg K := .seq (.prim (.lt f r D)) (notR f f)

/-- **Long division**: `q := ⌊a/d⌋`, `r := a mod d`, with scratch registers `D, s, f, m` and the
unit `o`. -/
def divP (q r a d D s f m o : Fin K) : RProg K :=
  .seq (.seq (.seq (.seq (.seq (mov r a) (clr q)) (mov D d)) (clr s)) (geF f r D))
    (.seq
      (.loop f (.seq (.seq (.prim (.shl D D)) (.prim (.add s s o))) (geF f r D)))
      (.loop s (.seq (.seq (.seq (.seq (.seq (.seq (.prim (.shr D D)) (.prim (.sub s s o)))
        (.prim (.shl q q))) (geF f r D)) (.seq (.prim (.bit m D f (· && ·))) (.prim (.sub r r m))))
        (.prim (.bit m o f (· && ·)))) (.prim (.add q q m)))))

end RProg

theorem run_geF (f r D : Fin K) (l : List (RC K)) :
    ∃ l' c, Run (RProg.geF f r D) l l' c ∧ c = 2 * (2 * l.length + 2) ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) f (if rv l D ≤ rv l r then 2 ^ l.length - 1 else 0) := by
  obtain ⟨r1, n1, v1⟩ := run_prim (p := Prim.lt f r D) (by simp) l
  obtain ⟨r2, n2, v2⟩ := run_prim (p := Prim.bit f f f fun x _ => !x) (by simp)
    ((Prim.lt f r D).apply l)
  refine ⟨_, _, Run.seq r1 r2, by rw [n1]; ring, by rw [n2, n1], ?_⟩
  rw [v2, n1, v1]
  simp only [Prim.sem, Function.update_self, Function.update_idem]
  congr 1
  rw [bitv_not]
  have h1 : 1 ≤ 2 ^ l.length := Nat.one_le_two_pow
  by_cases h : rv l r < rv l D
  · rw [if_pos h, if_neg (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [if_neg h, if_pos (by omega), Nat.zero_mod]; omega

/-- The doubling loop of the division. -/
def divUp (s D f r o : Fin K) : RProg K :=
  .seq (.seq (.prim (.shl D D)) (.prim (.add s s o))) (RProg.geF f r D)

/-- The restoring loop of the division. -/
def divDown (q r D s f m o : Fin K) : RProg K :=
  .seq (.seq (.seq (.seq (.seq (.seq (.prim (.shr D D)) (.prim (.sub s s o)))
    (.prim (.shl q q))) (RProg.geF f r D)) (.seq (.prim (.bit m D f (· && ·))) (.prim (.sub r r m))))
    (.prim (.bit m o f (· && ·)))) (.prim (.add q q m))

theorem divP_eq (q r a d D s f m o : Fin K) :
    RProg.divP q r a d D s f m o =
      .seq (.seq (.seq (.seq (.seq (RProg.mov r a) (RProg.clr q)) (RProg.mov D d)) (RProg.clr s))
        (RProg.geF f r D)) (.seq (.loop f (divUp s D f r o)) (.loop s (divDown q r D s f m o))) :=
  rfl

theorem run_divUp {s D f r o : Fin K} (hDs : D ≠ s) (hDf : D ≠ f) (hsf : s ≠ f) (hrD : r ≠ D)
    (hrs : r ≠ s) (hoD : o ≠ D) (l : List (RC K)) :
    ∃ l' c, Run (divUp s D f r o) l l' c ∧ c = 4 * (2 * l.length + 2) ∧ l'.length = l.length ∧
      rv l' D = 2 * rv l D % 2 ^ l.length ∧ rv l' s = (rv l s + rv l o) % 2 ^ l.length ∧
      rv l' f = (if 2 * rv l D % 2 ^ l.length ≤ rv l r then 2 ^ l.length - 1 else 0) ∧
      ∀ m, m ≠ D → m ≠ s → m ≠ f → rv l' m = rv l m := by
  obtain ⟨r1, n1, v1⟩ := run_prim (p := Prim.shl D D) (by simp) l
  obtain ⟨r2, n2, v2⟩ := run_prim (p := Prim.add s s o) (by simp) ((Prim.shl D D).apply l)
  obtain ⟨l3, c3, r3, hc3, n3, v3⟩ := run_geF f r D ((Prim.add s s o).apply ((Prim.shl D D).apply l))
  refine ⟨l3, _, Run.seq (Run.seq r1 r2) r3, by rw [hc3, n2, n1]; ring, by rw [n3, n2, n1],
    ?_, ?_, ?_, ?_⟩
  all_goals rw [v3, n2, v2, n1, v1]
  all_goals simp only [Prim.sem, Function.update_apply, hDs, hDf, hsf, hrD, hrs, hoD, Ne.symm hDs,
    Ne.symm hDf, Ne.symm hsf, if_true, if_false]
  · intro m hmD hms hmf
    simp only [hmD, hms, hmf, if_false]

theorem run_divDown {q r D s f m o : Fin K}
    (hqr : q ≠ r) (hqD : q ≠ D) (hqs : q ≠ s) (hqf : q ≠ f) (hqm : q ≠ m)
    (hrD : r ≠ D) (hrs : r ≠ s) (hrf : r ≠ f) (hrm : r ≠ m)
    (hDs : D ≠ s) (hDf : D ≠ f) (hDm : D ≠ m) (hsf : s ≠ f) (hsm : s ≠ m) (hfm : f ≠ m)
    (hoq : o ≠ q) (hor : o ≠ r) (hoD : o ≠ D) (hos : o ≠ s) (hof : o ≠ f) (hom : o ≠ m)
    (l : List (RC K)) :
    ∃ l' c, Run (divDown q r D s f m o) l l' c ∧ c = 9 * (2 * l.length + 2) ∧
      l'.length = l.length ∧
      rv l' D = rv l D / 2 ∧ rv l' s = tc l.length ((rv l s : ℤ) - rv l o) ∧
      rv l' r = tc l.length ((rv l r : ℤ) - (if rv l D / 2 ≤ rv l r then rv l D / 2 else 0)) ∧
      rv l' q = (2 * rv l q % 2 ^ l.length + (if rv l D / 2 ≤ rv l r then rv l o else 0)) %
        2 ^ l.length ∧
      ∀ m', m' ≠ q → m' ≠ r → m' ≠ D → m' ≠ s → m' ≠ f → m' ≠ m → rv l' m' = rv l m' := by
  obtain ⟨r1, n1, v1⟩ := run_prim (p := Prim.shr D D) (by simp) l
  obtain ⟨r2, n2, v2⟩ := run_prim (p := Prim.sub s s o) (by simp) ((Prim.shr D D).apply l)
  obtain ⟨r3, n3, v3⟩ := run_prim (p := Prim.shl q q) (by simp)
    ((Prim.sub s s o).apply ((Prim.shr D D).apply l))
  obtain ⟨l4, c4, r4, hc4, n4, v4⟩ := run_geF f r D
    ((Prim.shl q q).apply ((Prim.sub s s o).apply ((Prim.shr D D).apply l)))
  obtain ⟨r5, n5, v5⟩ := run_prim (p := Prim.bit m D f (· && ·)) (by simp) l4
  obtain ⟨r6, n6, v6⟩ := run_prim (p := Prim.sub r r m) (by simp) ((Prim.bit m D f (· && ·)).apply l4)
  obtain ⟨r7, n7, v7⟩ := run_prim (p := Prim.bit m o f (· && ·)) (by simp)
    ((Prim.sub r r m).apply ((Prim.bit m D f (· && ·)).apply l4))
  obtain ⟨r8, n8, v8⟩ := run_prim (p := Prim.add q q m) (by simp)
    ((Prim.bit m o f (· && ·)).apply ((Prim.sub r r m).apply ((Prim.bit m D f (· && ·)).apply l4)))
  have hN : l4.length = l.length := by rw [n4, n3, n2, n1]
  refine ⟨_, _, Run.seq (Run.seq (Run.seq (Run.seq (Run.seq (Run.seq r1 r2) r3) r4)
    (Run.seq r5 r6)) r7) r8, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [n7, n6, n5, hc4, n3, n2, n1, hN]; ring
  · rw [n8, n7, n6, n5, hN]
  all_goals rw [v8, n7, v7, n6, v6, n5, v5, v4, n3, v3, n2, v2, n1, v1, hN]
  all_goals simp only [Prim.sem, Function.update_apply, hqr, hqD, hqs, hqf, hqm, hrD, hrs, hrf,
    hrm, hDs, hDf, hDm, hsf, hsm, hfm, hoq, hor, hoD, hos, hof, hom, Ne.symm hqr, Ne.symm hqD,
    Ne.symm hqs, Ne.symm hqf, Ne.symm hqm, Ne.symm hrD, Ne.symm hrs, Ne.symm hrf, Ne.symm hrm,
    Ne.symm hDs, Ne.symm hDf, Ne.symm hDm, Ne.symm hsf, Ne.symm hsm, Ne.symm hfm, if_true,
    if_false]
  · rw [bitv_and_flag _ _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) (rv_lt l D))]
  · rw [bitv_and_flag _ _ _ (rv_lt l o)]
  · intro m' h1 h2 h3 h4 h5 h6
    simp only [h1, h2, h3, h4, h5, h6, if_false]

/-- **Long division**: `q := ⌊a/d⌋` and `r := a mod d`, for `d ≥ 1` and `2a < 2^N`. -/
theorem run_divP {q r a d D s f m o : Fin K}
    (hqr : q ≠ r) (hqD : q ≠ D) (hqs : q ≠ s) (hqf : q ≠ f) (hqm : q ≠ m)
    (hrD : r ≠ D) (hrs : r ≠ s) (hrf : r ≠ f) (hrm : r ≠ m)
    (hDs : D ≠ s) (hDf : D ≠ f) (hDm : D ≠ m) (hsf : s ≠ f) (hsm : s ≠ m) (hfm : f ≠ m)
    (hoq : o ≠ q) (hor : o ≠ r) (hoD : o ≠ D) (hos : o ≠ s) (hof : o ≠ f) (hom : o ≠ m)
    (hdr : d ≠ r) (hdq : d ≠ q) (l : List (RC K)) (ho : rv l o = 1) (hd : 1 ≤ rv l d)
    (ha : 2 * rv l a < 2 ^ l.length) :
    ∃ l' c, Run (RProg.divP q r a d D s f m o) l l' c ∧ l'.length = l.length ∧
      rv l' q = rv l a / rv l d ∧ rv l' r = rv l a % rv l d ∧
      (∀ m', m' ≠ q → m' ≠ r → m' ≠ D → m' ≠ s → m' ≠ f → m' ≠ m → rv l' m' = rv l m') ∧
      c ≤ 16 * (l.length + 1) * (2 * l.length + 2) := by
  set N := l.length with hN
  set A := rv l a with hA
  set d0 := rv l d with hd0
  have hN1 : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    have := rv_lt l d
    rw [← hN, h0, pow_zero] at this
    omega
  have hNpow : N < 2 ^ N := Nat.lt_two_pow_self
  have hone : 1 ≤ 2 ^ N - 1 := by
    have : 2 ≤ 2 ^ N := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN1
    omega
  let Fr : List (RC K) → Prop := fun l' =>
    ∀ m', m' ≠ q → m' ≠ r → m' ≠ D → m' ≠ s → m' ≠ f → m' ≠ m → rv l' m' = rv l m'
  -- the prefix
  obtain ⟨l₁, hr₁, hn₁, hv₁⟩ := run_mov r a l
  obtain ⟨l₂, hr₂, hn₂, hv₂⟩ := run_clr q l₁
  obtain ⟨l₃, hr₃, hn₃, hv₃⟩ := run_mov D d l₂
  obtain ⟨l₄, hr₄, hn₄, hv₄⟩ := run_clr s l₃
  obtain ⟨l₅, c₅, hr₅, hc₅, hn₅, hv₅⟩ := run_geF f r D l₄
  have hlen₅ : l₅.length = N := by rw [hn₅, hn₄, hn₃, hn₂, hn₁]
  have e₅ : ∀ m', rv l₅ m' = Function.update (Function.update (Function.update (Function.update
      (Function.update (rv l) r A) q 0) D d0) s 0) f (if d0 ≤ A then 2 ^ N - 1 else 0) m' := by
    intro m'
    rw [hv₅, hn₄, hn₃, hn₂, hn₁, hv₄, hv₃, hv₂, hv₁]
    simp only [Function.update_apply, hdr, hdq, hrD, hrs, hDs, Ne.symm hqr, Ne.symm hqD,
      Ne.symm hrD, if_false, if_true, ← hA, ← hd0, ← hN]
  -- the doubling loop
  let I1 : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ ∃ e, rv l' s = e ∧
    rv l' D = d0 * 2 ^ e ∧ rv l' q = 0 ∧ rv l' r = A ∧
    rv l' f = (if d0 * 2 ^ e ≤ A then 2 ^ N - 1 else 0) ∧ A < d0 * 2 ^ (e + k) ∧ Fr l'
  let Q1 : List (RC K) → Prop := fun l' => l'.length = N ∧ ∃ e, rv l' s = e ∧
    rv l' D = d0 * 2 ^ e ∧ rv l' q = 0 ∧ rv l' r = A ∧ A < d0 * 2 ^ e ∧ Fr l'
  have hI1 : I1 N l₅ := by
    refine ⟨hlen₅, 0, ?_, ?_, ?_, ?_, ?_, ?_, fun m' h1 h2 h3 h4 h5 _ => ?_⟩
    · rw [e₅]; simp only [Function.update_apply, hsf, if_true, if_false]
    · rw [e₅]; simp only [Function.update_apply, hDf, hDs, if_true, if_false]; ring
    · rw [e₅]; simp only [Function.update_apply, hqf, hqs, hqD, if_true, if_false]
    · rw [e₅]; simp only [Function.update_apply, hrf, hrs, hrD, Ne.symm hqr, if_true, if_false]
    · rw [e₅]; simp only [Function.update_apply, if_true, pow_zero, mul_one]
    · have := rv_lt l a
      rw [zero_add]
      calc A < 2 ^ N := this
        _ ≤ d0 * 2 ^ N := Nat.le_mul_of_pos_left _ hd
    · rw [e₅]; simp only [Function.update_apply, h1, h2, h3, h4, h5, if_false]
  have hloop1 := run_loop (j := f) (P := divUp s D f r o) N (4 * (2 * N + 2)) I1 Q1
    (fun k l' h => h.1)
    (fun l' h => by
      obtain ⟨_, e, _, _, _, _, hf, hlt, _⟩ := h
      rw [hf, if_neg (by rw [add_zero] at hlt; omega)])
    (fun k l' h hz => by
      obtain ⟨h1, e, hs, hD, hq, hr, hf, _, hfr⟩ := h
      refine ⟨h1, e, hs, hD, hq, hr, ?_, hfr⟩
      by_contra hc
      rw [hf, if_pos (by omega)] at hz
      omega)
    (fun k l' h hz => by
      obtain ⟨h1, e, hs, hD, hq, hr, hf, hlt, hfr⟩ := h
      have hc : d0 * 2 ^ e ≤ A := by
        by_contra hc; rw [hf, if_neg hc] at hz; exact hz rfl
      obtain ⟨l'', c'', hr'', hc'', hn'', hvD, hvs, hvf, hvm⟩ := run_divUp hDs hDf hsf hrD hrs hoD l'
      have h2D : 2 * rv l' D < 2 ^ N := by rw [hD]; omega
      have hpow : 2 ^ e ≤ d0 * 2 ^ e := Nat.le_mul_of_pos_left _ hd
      have he1 : e + 1 < 2 ^ N := by
        have h2e : 2 ^ (e + 1) < 2 ^ N := by rw [pow_succ]; omega
        have := Nat.pow_lt_pow_iff_right (a := 2) (by norm_num) |>.1 h2e
        omega
      have hoo : rv l' o = 1 := by
        rw [hfr o hoq hor hoD hos hof hom]; exact ho
      refine ⟨l'', c'', hr'', by rw [hc'', h1], by rw [hn'', h1], e + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hvs, hs, hoo, h1, Nat.mod_eq_of_lt he1]
      · rw [hvD, h1, Nat.mod_eq_of_lt h2D, hD, pow_succ]; ring
      · rw [hvm q hqD hqs hqf, hq]
      · rw [hvm r hrD hrs hrf, hr]
      · rw [hvf, h1, Nat.mod_eq_of_lt h2D, hr, hD, pow_succ]
        congr 1
        rw [show d0 * (2 ^ e * 2) = 2 * (d0 * 2 ^ e) by ring]
      · rw [show e + 1 + k = e + (k + 1) by ring]; exact hlt
      · intro m' h1' h2' h3' h4' h5' h6'
        rw [hvm m' h3' h4' h5', hfr m' h1' h2' h3' h4' h5' h6'])
    N l₅ hI1
  obtain ⟨l₆, c₆, hr₆, ⟨hn₆, e, hs₆, hD₆, hq₆, hr₆', hlt₆, hfr₆⟩, hc₆⟩ := hloop1
  have heN : e < N := by
    have h1 := rv_lt l₆ D
    rw [hD₆, hn₆] at h1
    have h2 : 2 ^ e ≤ d0 * 2 ^ e := Nat.le_mul_of_pos_left _ hd
    have h3 : 2 ^ e < 2 ^ N := lt_of_le_of_lt h2 h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  -- the restoring loop
  let I2 : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ rv l' s = k ∧
    rv l' D = d0 * 2 ^ k ∧ A = rv l' q * rv l' D + rv l' r ∧ rv l' r < rv l' D ∧ Fr l'
  have hI2 : I2 e l₆ := by
    refine ⟨hn₆, hs₆, hD₆, ?_, ?_, hfr₆⟩
    · rw [hq₆, hr₆']; ring
    · rw [hr₆', hD₆]; exact hlt₆
  have hloop2 := run_loop (j := s) (P := divDown q r D s f m o) N (9 * (2 * N + 2)) I2
    (fun l' => l'.length = N ∧ rv l' q = A / d0 ∧ rv l' r = A % d0 ∧ Fr l')
    (fun k l' h => h.1)
    (fun l' h => h.2.1)
    (fun k l' h hz => by
      obtain ⟨h1, hs, hD, hA', hlt, hfr⟩ := h
      have hk : k = 0 := by rw [← hs, hz]
      subst hk
      rw [pow_zero, mul_one] at hD
      rw [hD] at hA' hlt
      have hd0 : 0 < d0 := hd
      refine ⟨h1, ?_, ?_, hfr⟩
      · rw [hA', mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hd0, Nat.div_eq_of_lt hlt,
          zero_add]
      · rw [hA', mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt])
    (fun k l' h _ => by
      obtain ⟨h1, hs, hD, hA', hlt, hfr⟩ := h
      obtain ⟨l'', c'', hr'', hc'', hn'', hvD, hvs, hvr, hvq, hvm⟩ :=
        run_divDown hqr hqD hqs hqf hqm hrD hrs hrf hrm hDs hDf hDm hsf hsm hfm hoq hor hoD hos
          hof hom l'
      have hoo : rv l' o = 1 := by
        rw [hfr o hoq hor hoD hos hof hom]; exact ho
      have hD2 : rv l' D / 2 = d0 * 2 ^ k := by
        rw [hD, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
      have hk1 : k + 1 < 2 ^ N := by rw [← hs, ← h1]; exact rv_lt l' s
      have hq2 : 2 * rv l' q < 2 ^ N := by
        have hDge : 2 ≤ rv l' D := by
          rw [hD]
          calc 2 = 1 * 2 ^ 1 := by norm_num
            _ ≤ d0 * 2 ^ (k + 1) := Nat.mul_le_mul hd (Nat.pow_le_pow_right (by norm_num) (by omega))
        have h2 := Nat.mul_le_mul_left (rv l' q) hDge
        omega
      have hrN : rv l' r < 2 ^ N := by rw [← h1]; exact rv_lt l' r
      have h2N : 2 ^ N = 2 * 2 ^ (N - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h2q1 : 2 * rv l' q + 1 < 2 ^ N := by omega
      have hsub : d0 * 2 ^ k ≤ rv l' r →
          ((rv l' r : ℤ) - ((d0 * 2 ^ k : ℕ) : ℤ)) = ((rv l' r - d0 * 2 ^ k : ℕ) : ℤ) := by
        intro hb; push_cast [hb]; ring
      have hlt' : rv l' r < d0 * 2 ^ k * 2 := by rw [hD, pow_succ, ← mul_assoc] at hlt; exact hlt
      refine ⟨l'', c'', hr'', by rw [hc'', h1], by rw [hn'', h1], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hvs, hs, hoo, h1]; exact tc_pred N k hk1
      · rw [hvD, hD2]
      · by_cases hb : d0 * 2 ^ k ≤ rv l' r
        · rw [hvq, hvr, hvD, hD2, if_pos hb, if_pos hb, hoo, h1, Nat.mod_eq_of_lt hq2,
            Nat.mod_eq_of_lt h2q1, hsub hb,
            tc_nat N _ (lt_of_le_of_lt (Nat.sub_le _ _) hrN), hA', hD, pow_succ]
          zify [hb]
          ring
        · rw [hvq, hvr, hvD, hD2, if_neg hb, if_neg hb, h1, Nat.mod_eq_of_lt hq2, add_zero,
            Nat.mod_eq_of_lt hq2, Nat.cast_zero, sub_zero, tc_nat N _ hrN, hA', hD, pow_succ]
          ring
      · by_cases hb : d0 * 2 ^ k ≤ rv l' r
        · rw [hvr, hvD, hD2, if_pos hb, h1, hsub hb,
            tc_nat N _ (lt_of_le_of_lt (Nat.sub_le _ _) hrN)]
          omega
        · rw [hvr, hvD, hD2, if_neg hb, h1, Nat.cast_zero, sub_zero, tc_nat N _ hrN]
          omega
      · intro m' h1' h2' h3' h4' h5' h6'
        rw [hvm m' h1' h2' h3' h4' h5' h6', hfr m' h1' h2' h3' h4' h5' h6'])
    e l₆ hI2
  obtain ⟨l₇, c₇, hr₇, ⟨hn₇, hq₇, hr₇', hfr₇⟩, hc₇⟩ := hloop2
  refine ⟨l₇, _, Run.seq (Run.seq (Run.seq (Run.seq (Run.seq hr₁ hr₂) hr₃) hr₄) hr₅)
    (Run.seq hr₆ hr₇), hn₇, hq₇, hr₇', hfr₇, ?_⟩
  rw [hc₅, hn₄, hn₃, hn₂, hn₁]
  have e1 : N * (2 * N + 2 + 4 * (2 * N + 2)) = N * (5 * (2 * N + 2)) := by ring
  have e2 : e * (2 * N + 2 + 9 * (2 * N + 2)) = e * (10 * (2 * N + 2)) := by ring
  rw [e1] at hc₆
  rw [e2] at hc₇
  have h3 : e * (10 * (2 * N + 2)) ≤ N * (10 * (2 * N + 2)) :=
    Nat.mul_le_mul_right _ heN.le
  have e3 : 16 * (N + 1) * (2 * N + 2) = 16 * (2 * N + 2) + N * (16 * (2 * N + 2)) := by ring
  rw [e3]
  have e4 : N * (16 * (2 * N + 2)) = N * (5 * (2 * N + 2)) + N * (10 * (2 * N + 2)) +
      N * (2 * N + 2) := by ring
  omega

/-! ### Extending the tape -/

namespace RProg

/-- Extend the tape by `r_c` cells, counting `c` down with the unit `o`. -/
def extendBy (c o : Fin K) : RProg K := .loop c (.seq (.prim .extend) (.prim (.sub c c o)))

/-- The bit length of a marker `2^n − 1`: `b := n`, using the scratch register `t`. -/
def bitLen (b t src o : Fin K) : RProg K :=
  .seq (.seq (mov t src) (clr b)) (.loop t (.seq (.prim (.shr t t)) (.prim (.add b b o))))

end RProg

/-- **Tape extension**: the tape grows by `r_c` cells and every other register keeps its value. -/
theorem run_extendBy {c o : Fin K} (hco : c ≠ o) :
    ∀ (C : ℕ) (l : List (RC K)), rv l c = C → rv l o = 1 →
      ∃ l' cst, Run (RProg.extendBy c o) l l' cst ∧ l'.length = l.length + C ∧ rv l' c = 0 ∧
        (∀ m, m ≠ c → rv l' m = rv l m) ∧ cst ≤ (C + 1) * (6 * (l.length + C) + 9) := by
  intro C
  induction C with
  | zero =>
    intro l hc _
    refine ⟨l, _, Run.stop hc, by simp, hc, fun _ _ => rfl, ?_⟩
    simp only [add_zero]; omega
  | succ C ih =>
    intro l hc ho
    have hne : rv l c ≠ 0 := by rw [hc]; omega
    set l₁ := Prim.extend.apply l
    have hn₁ : l₁.length = l.length + 1 := extend_length l
    have hv₁ : rv l₁ = rv l := extend_rv l
    have hr₁ := Run.prim (Prim.extend (K := K)) l
    rw [extend_cost] at hr₁
    obtain ⟨hr₂, hn₂, hv₂⟩ := run_prim (p := Prim.sub c c o) (by simp) l₁
    set l₂ := (Prim.sub c c o).apply l₁
    have hC : C + 1 < 2 ^ l₁.length := by
      rw [hn₁, ← hc, pow_succ]; have := rv_lt l c; omega
    have hc₂ : rv l₂ c = C := by
      rw [hv₂]; simp only [Prim.sem, Function.update_self]
      rw [hv₁, hc, ho]; exact tc_pred _ C hC
    have ho₂ : rv l₂ o = 1 := by
      rw [hv₂]; simp only [Prim.sem, Function.update_of_ne (Ne.symm hco)]; rw [hv₁, ho]
    obtain ⟨l', cst, hr', hn', hc', hm', hcst⟩ := ih l₂ hc₂ ho₂
    refine ⟨l', _, Run.iter hne (Run.seq hr₁ hr₂) hr', ?_, hc', fun m hm => ?_, ?_⟩
    · rw [hn', hn₂, hn₁]; ring
    · rw [hm' m hm, hv₂]; simp only [Prim.sem, Function.update_of_ne hm]; rw [hv₁]
    · rw [hn₂, hn₁] at hcst
      rw [hn₁]
      have e : l.length + 1 + C = l.length + (C + 1) := by ring
      rw [e] at hcst
      have e2 : (C + 1 + 1) * (6 * (l.length + (C + 1)) + 9) =
          (C + 1) * (6 * (l.length + (C + 1)) + 9) + (6 * (l.length + (C + 1)) + 9) := by ring
      rw [e2]
      omega

/-- **The bit length of a marker.** If `r_src = 2^n − 1`, then `bitLen` sets `b := n`. -/
theorem run_bitLen {b t src o : Fin K} (hbt : b ≠ t) (hto : t ≠ o) (hbo : b ≠ o)
    (l : List (RC K)) (n : ℕ) (hsrc : rv l src = 2 ^ n - 1) (ho : rv l o = 1) :
    ∃ l' cst, Run (RProg.bitLen b t src o) l l' cst ∧ l'.length = l.length ∧ rv l' b = n ∧
      (∀ m, m ≠ b → m ≠ t → rv l' m = rv l m) ∧
      cst ≤ (n + 2) * (3 * (2 * l.length + 2)) := by
  set N := l.length with hN
  obtain ⟨l₁, hr₁, hn₁, hv₁⟩ := run_mov t src l
  obtain ⟨l₂, hr₂, hn₂, hv₂⟩ := run_clr b l₁
  have hnN : n < 2 ^ N := by
    have h1 : rv l src < 2 ^ N := rv_lt l src
    rw [hsrc] at h1
    have h2 : 2 ^ n ≤ 2 ^ N := by omega
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    exact lt_of_le_of_lt this Nat.lt_two_pow_self
  let I : ℕ → List (RC K) → Prop := fun k l' => l'.length = N ∧ k ≤ n ∧ rv l' t = 2 ^ k - 1 ∧
    rv l' b = n - k ∧ ∀ m, m ≠ b → m ≠ t → rv l' m = rv l m
  have hI : I n l₂ := by
    refine ⟨by rw [hn₂, hn₁], le_rfl, ?_, ?_, fun m hmb hmt => ?_⟩
    · rw [hv₂, Function.update_of_ne (Ne.symm hbt), hv₁, Function.update_self, hsrc]
    · rw [hv₂, Function.update_self, Nat.sub_self]
    · rw [hv₂, Function.update_of_ne hmb, hv₁, Function.update_of_ne hmt]
  have hloop := run_loop (j := t) (P := .seq (.prim (.shr t t)) (.prim (.add b b o))) N
    (2 * (2 * N + 2)) I (fun l' => l'.length = N ∧ rv l' b = n ∧
      ∀ m, m ≠ b → m ≠ t → rv l' m = rv l m)
    (fun k l' h => h.1)
    (fun l' h => by rw [h.2.2.1]; simp)
    (fun k l' h hz => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hk : k = 0 := by
        by_contra hk
        have : 1 ≤ 2 ^ k - 1 := by
          have : 2 ≤ 2 ^ k := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
      subst hk
      exact ⟨h1, by rw [h4, Nat.sub_zero], h5⟩)
    (fun k l' h _ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨ra, na, va⟩ := run_prim (p := Prim.shr t t) (by simp) l'
      obtain ⟨rb, nb, vb⟩ := run_prim (p := Prim.add b b o) (by simp) ((Prim.shr t t).apply l')
      have ho' : rv l' o = 1 := by rw [h5 o (Ne.symm hbo) (Ne.symm hto)]; exact ho
      refine ⟨_, _, Run.seq ra rb, by rw [na, h1]; omega, ⟨by rw [nb, na, h1], by omega, ?_, ?_,
        fun m hmb hmt => ?_⟩⟩
      · rw [vb, na]; simp only [Prim.sem, Function.update_of_ne hbt.symm]
        rw [va]; simp only [Prim.sem, Function.update_self]
        rw [h3]
        have : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          rw [pow_succ]; omega
        rw [this]; omega
      · rw [vb, na]; simp only [Prim.sem, Function.update_self]
        rw [va]; simp only [Prim.sem, Function.update_of_ne hbt, Function.update_of_ne hto.symm]
        rw [h4, ho', h1, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [vb, na]; simp only [Prim.sem, Function.update_of_ne hmb]
        rw [va]; simp only [Prim.sem, Function.update_of_ne hmt]
        exact h5 m hmb hmt)
    n l₂ hI
  obtain ⟨l', cst, hr, ⟨hn', hb', hm'⟩, hc⟩ := hloop
  refine ⟨l', _, Run.seq (Run.seq hr₁ hr₂) hr, hn', hb', hm', ?_⟩
  rw [hn₁]
  have e : n * (2 * N + 2 + 2 * (2 * N + 2)) = n * (3 * (2 * N + 2)) := by ring
  rw [e] at hc
  have e2 : (n + 2) * (3 * (2 * N + 2)) = n * (3 * (2 * N + 2)) + 6 * (2 * N + 2) := by ring
  rw [e2]
  omega

end PVNP.Discrete.SweepReg
