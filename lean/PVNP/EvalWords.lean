import PVNP.SweepRegLib
import PVNP.EvalKron

/-!
# Word-level register programs for the evaluator

Packed arrays live in registers as two's-complement codes of their Kronecker values
(`EvalKron.kv`). This module reads and writes single words and provides **clean** versions of
the library programs, which return their scratch registers to zero, so that the whole effect of a
program is one `Function.update` of the register file.

* `run_rdW`, `run_crd`: the signed coefficient at bit position `m·W_b` is
  `((V + E) >> m W_b) AND (2^{W_b} − 1) − 2^{W_b − 1}`, given the excess form of `V + E`
  (`EvalKron.kv_decode`).
* `run_wrW`, `run_cwr`: `O := O + z · 2^{bp}` modulo `2^N`.
* `run_cmul`, `run_cshl`, `run_cshr`, `run_cdiv`: clean multiplication, shifts and division.
* `bitv_and_mask`, `tc_add_nat`, `tc_mul_pow`, `tc_sub_tc`: masks and two's-complement arithmetic.
* `cprodC`: the complex product of register pairs.
-/

namespace PVNP.Discrete.SweepReg

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.SweepArith PVNP.Eval

variable {K : ℕ}

/-! ### Masks and two's complement -/

theorem bitv_and_mask (N a w : ℕ) (hw : w ≤ N) : bitv (· && ·) N a (2 ^ w - 1) = a % 2 ^ w := by
  unfold bitv
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_val, Nat.testBit_mod_two_pow]
  by_cases ht : t < N
  · rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn,
      Nat.testBit_two_pow_sub_one]
    simp only [Bool.and_comm]
  · rw [List.getD_eq_default _ _ (by simpa using ht)]
    have : ¬ t < w := by omega
    simp [this]

theorem tc_add_nat (N : ℕ) (x : ℤ) (y : ℕ) : (tc N x + y) % 2 ^ N = tc N (x + y) := by
  have h : (((tc N x + y) % 2 ^ N : ℕ) : ℤ) = ((tc N (x + y) : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.add_emod]
  exact_mod_cast h

theorem tc_of_nonneg_lt (N : ℕ) (x : ℤ) (h0 : 0 ≤ x) (h1 : x < 2 ^ N) : (tc N x : ℤ) = x := by
  rw [tc_cast, Int.emod_eq_of_lt h0 h1]

theorem tc_sub_nat (N : ℕ) (x : ℕ) (y : ℕ) : tc N ((x : ℤ) - y) = tc N ((x : ℤ) - (y : ℤ)) := rfl

theorem tc_mul_pow (N : ℕ) (z : ℤ) (c : ℕ) : tc N z * 2 ^ c % 2 ^ N = tc N (z * 2 ^ c) := by
  have h : ((tc N z * 2 ^ c % 2 ^ N : ℕ) : ℤ) = ((tc N (z * 2 ^ c) : ℕ) : ℤ) := by
    push_cast
    rw [tc_cast, tc_cast, Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.mul_emod]
  exact_mod_cast h

theorem tc_add_tc (N : ℕ) (x y : ℤ) : (tc N x + tc N y) % 2 ^ N = tc N (x + y) :=
  tc_add N x y

/-! ### Reading and writing one packed word -/

namespace RProg

/-- **Read a packed word**: `t := ((V + E) >> r_e) AND mask − half`, the signed coefficient at bit
position `r_e` of the packed register `V` with excess constant `E`. The register `c` is scratch. -/
def rdW (t V E e c mask half o : Fin K) : RProg K :=
  .seq (.seq (.seq (.prim (.add t V E)) (shrBy t e c o)) (.prim (.bit t t mask (· && ·))))
    (.prim (.sub t t half))

/-- **Write a packed word**: `O := O + (r_w << r_e)` modulo `2^N`. Registers `t, c` are scratch. -/
def wrW (O w e t c o : Fin K) : RProg K :=
  .seq (.seq (mov t w) (shlBy t e c o)) (.prim (.add O O t))

end RProg

theorem run_rdW {t V E e c mask half o : Fin K} (htc : t ≠ c) (hto : t ≠ o) (hco : c ≠ o)
    (htm : t ≠ mask) (hth : t ≠ half) (hte : t ≠ e) (hcm : c ≠ mask) (hch : c ≠ half)
    (l : List (RC K)) (Wb M m : ℕ) (w : ℕ → ℕ) (v : ℤ)
    (hw : ∀ p, w p < 2 ^ Wb) (hWbN : Wb ≤ l.length) (hMN : (2 ^ Wb) ^ M ≤ 2 ^ l.length)
    (hm : m < M) (hV : rv l V = tc l.length v)
    (hsum : v + (rv l E : ℤ) = ((∑ p ∈ Finset.range M, w p * (2 ^ Wb) ^ p : ℕ) : ℤ))
    (he : rv l e = m * Wb) (hmask : rv l mask = 2 ^ Wb - 1) (hhalf : rv l half = 2 ^ Wb / 2)
    (ho : rv l o = 1) :
    ∃ l' cst, Run (RProg.rdW t V E e c mask half o) l l' cst ∧ l'.length = l.length ∧
      rv l' t = tc l.length ((w m : ℤ) - (2 ^ Wb / 2 : ℕ)) ∧
      (∀ x, x ≠ t → x ≠ c → rv l' x = rv l x) ∧
      cst ≤ 3 * (2 * l.length + 2) + (2 * l.length + 2) + m * Wb * (3 * (2 * l.length + 2)) +
        (2 * l.length + 2) := by
  set N := l.length with hN
  set S := ∑ p ∈ Finset.range M, w p * (2 ^ Wb) ^ p with hS
  have hSlt : S < 2 ^ N := lt_of_lt_of_le (digits_sum_lt _ w hw M) hMN
  -- 1. t := V + E
  obtain ⟨r1, n1, v1⟩ := run_prim (p := Prim.add t V E) (by simp) l
  have ht1 : rv ((Prim.add t V E).apply l) t = S := by
    rw [v1]; simp only [Prim.sem, Function.update_self]
    rw [hV, tc_add_nat]
    have h := tc_of_nonneg_lt N (v + (rv l E : ℤ)) (by rw [hsum]; positivity)
      (by rw [hsum]; exact_mod_cast hSlt)
    rw [hsum] at h ⊢
    exact_mod_cast h
  -- 2. shift right
  set l₁ := (Prim.add t V E).apply l
  have ho1 : rv l₁ o = 1 := by
    rw [v1]; simp only [Prim.sem, Function.update_of_ne (Ne.symm hto)]; exact ho
  obtain ⟨l₂, c₂, r2, n2, x2, -, m2, k2⟩ := run_shrBy (c := e) htc hco hto l₁ ho1
  have he1 : rv l₁ e = m * Wb := by
    rw [v1]; simp only [Prim.sem, Function.update_of_ne (Ne.symm hte)]; exact he
  have ht2 : rv l₂ t = S / (2 ^ Wb) ^ m := by
    rw [x2, ht1, he1, ← pow_mul, mul_comm]
  have hn2 : l₂.length = N := by rw [n2, n1]
  -- 3. mask
  obtain ⟨r3, n3, v3⟩ := run_prim (p := Prim.bit t t mask (· && ·)) (by simp) l₂
  have hmask2 : rv l₂ mask = 2 ^ Wb - 1 := by
    rw [m2 mask (Ne.symm htm) (Ne.symm hcm), v1]
    simp only [Prim.sem, Function.update_of_ne (Ne.symm htm)]; exact hmask
  have ht3 : rv ((Prim.bit t t mask (· && ·)).apply l₂) t = w m := by
    rw [v3]; simp only [Prim.sem, Function.update_self]
    rw [ht2, hmask2, hn2, bitv_and_mask _ _ _ hWbN]
    exact digit_sum _ w hw m M hm
  -- 4. subtract the half
  set l₃ := (Prim.bit t t mask (· && ·)).apply l₂
  obtain ⟨r4, n4, v4⟩ := run_prim (p := Prim.sub t t half) (by simp) l₃
  have hhalf3 : rv l₃ half = 2 ^ Wb / 2 := by
    rw [v3]; simp only [Prim.sem, Function.update_of_ne (Ne.symm hth)]
    rw [m2 half (Ne.symm hth) (Ne.symm hch), v1]
    simp only [Prim.sem, Function.update_of_ne (Ne.symm hth)]; exact hhalf
  have hn3 : l₃.length = N := by rw [n3, hn2]
  refine ⟨_, _, Run.seq (Run.seq (Run.seq r1 r2) r3) r4, ?_, ?_, ?_, ?_⟩
  · rw [n4, hn3]
  · rw [v4]; simp only [Prim.sem, Function.update_self]
    rw [ht3, hhalf3, hn3]
  · intro x hxt hxc
    rw [v4]; simp only [Prim.sem, Function.update_of_ne hxt]
    rw [v3]; simp only [Prim.sem, Function.update_of_ne hxt]
    rw [m2 x hxt hxc, v1]; simp only [Prim.sem, Function.update_of_ne hxt]
  · have hl1 : l₁.length = N := n1
    have k2' : c₂ ≤ (2 * N + 2) + m * Wb * (3 * (2 * N + 2)) + (2 * N + 2) := by
      rw [hl1, he1] at k2; exact k2
    rw [hn2, hn3]
    generalize m * Wb * (3 * (2 * N + 2)) = P at k2' ⊢
    omega

theorem run_wrW {O w e t c o : Fin K} (htc : t ≠ c) (hto : t ≠ o) (hco : c ≠ o) (hte : t ≠ e)
    (hOt : O ≠ t) (hOc : O ≠ c) (l : List (RC K)) (y z : ℤ) (bp : ℕ)
    (hO : rv l O = tc l.length y) (hw : rv l w = tc l.length z) (he : rv l e = bp)
    (ho : rv l o = 1) :
    ∃ l' cst, Run (RProg.wrW O w e t c o) l l' cst ∧ l'.length = l.length ∧
      rv l' O = tc l.length (y + z * 2 ^ bp) ∧
      (∀ x, x ≠ O → x ≠ t → x ≠ c → rv l' x = rv l x) ∧
      cst ≤ (2 * l.length + 2) + (2 * l.length + 2) + bp * (3 * (2 * l.length + 2)) +
        (2 * l.length + 2) + (2 * l.length + 2) := by
  set N := l.length with hN
  obtain ⟨l₁, r1, n1, v1⟩ := run_mov t w l
  have ho1 : rv l₁ o = 1 := by rw [v1, Function.update_of_ne (Ne.symm hto)]; exact ho
  have he1 : rv l₁ e = bp := by rw [v1, Function.update_of_ne (Ne.symm hte)]; exact he
  obtain ⟨l₂, c₂, r2, n2, x2, -, m2, k2⟩ := run_shlBy (c := e) htc hco hto l₁ ho1
  have ht2 : rv l₂ t = tc N (z * 2 ^ bp) := by
    rw [x2, he1, v1, Function.update_self, hw, n1, tc_mul_pow]
  have hn2 : l₂.length = N := by rw [n2, n1]
  obtain ⟨r3, n3, v3⟩ := run_prim (p := Prim.add O O t) (by simp) l₂
  have hO2 : rv l₂ O = tc N y := by
    rw [m2 O hOt hOc, v1, Function.update_of_ne hOt]; exact hO
  refine ⟨_, _, Run.seq (Run.seq r1 r2) r3, by rw [n3, hn2], ?_, ?_, ?_⟩
  · rw [v3]; simp only [Prim.sem, Function.update_self]
    rw [hO2, ht2, hn2, tc_add]
  · intro x hxO hxt hxc
    rw [v3]; simp only [Prim.sem, Function.update_of_ne hxO]
    rw [m2 x hxt hxc, v1, Function.update_of_ne hxt]
  · have k2' : c₂ ≤ (2 * N + 2) + bp * (3 * (2 * N + 2)) + (2 * N + 2) := by
      rw [n1, he1] at k2; exact k2
    rw [hn2]
    generalize bp * (3 * (2 * N + 2)) = P at k2' ⊢
    omega

/-! ### Clean programs: scratch registers return to zero -/

namespace RProg

/-- Clear three registers. -/
def clr3 (x y t : Fin K) : RProg K := .seq (.seq (clr x) (clr y)) (clr t)

/-- Multiplication that leaves its scratch registers at zero. -/
def cmul (p a b x y t : Fin K) : RProg K := .seq (mulP p a b x y t) (clr3 x y t)

/-- Shifts that leave their scratch register at zero. -/
def cshl (x c t o : Fin K) : RProg K := .seq (shlBy x c t o) (clr t)

def cshr (x c t o : Fin K) : RProg K := .seq (shrBy x c t o) (clr t)

/-- Word reading and writing that leave their scratch registers at zero. -/
def crd (t V E e c mask half o : Fin K) : RProg K := .seq (rdW t V E e c mask half o) (clr c)

def cwr (O w e t c o : Fin K) : RProg K := .seq (wrW O w e t c o) (.seq (clr t) (clr c))

end RProg

theorem run_clr3 (x y t : Fin K) (l : List (RC K)) :
    ∃ l', Run (RProg.clr3 x y t) l l' (3 * (2 * l.length + 2)) ∧ l'.length = l.length ∧
      rv l' = Function.update (Function.update (Function.update (rv l) x 0) y 0) t 0 := by
  obtain ⟨l₁, r1, n1, v1⟩ := run_clr x l
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr y l₁
  obtain ⟨l₃, r3, n3, v3⟩ := run_clr t l₂
  refine ⟨l₃, ?_, by rw [n3, n2, n1], by rw [v3, v2, v1]⟩
  have h := Run.seq (Run.seq r1 r2) r3
  rw [n2, n1] at h
  convert h using 1; ring

/-- A register file with zeros in three registers is unchanged by clearing them again. -/
theorem update3_zero (σ : Fin K → ℕ) {x y t : Fin K} (hx : σ x = 0) (hy : σ y = 0)
    (ht : σ t = 0) (τ : Fin K → ℕ) (hτ : ∀ m, m ≠ x → m ≠ y → m ≠ t → τ m = σ m) :
    Function.update (Function.update (Function.update τ x 0) y 0) t 0 = σ := by
  funext m
  simp only [Function.update_apply]
  split_ifs with h1 h2 h3
  · rw [h1, ht]
  · rw [h2, hy]
  · rw [h3, hx]
  · exact hτ m h3 h2 h1

/-- **Clean multiplication**: `p := a b mod 2^N`, and nothing else changes. -/
theorem run_cmul {p a b x y t : Fin K} (hpx : p ≠ x) (hpy : p ≠ y) (hpt : p ≠ t) (hxy : x ≠ y)
    (hxt : x ≠ t) (hyt : y ≠ t) (hbx : b ≠ x) (l : List (RC K)) (hx : rv l x = 0)
    (hy : rv l y = 0) (ht : rv l t = 0) :
    ∃ l' c, Run (RProg.cmul p a b x y t) l l' c ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) p (rv l a * rv l b % 2 ^ l.length) ∧
      c ≤ (l.length + 5) * (6 * (2 * l.length + 2)) := by
  obtain ⟨l₁, c₁, r1, n1, v1, m1, k1⟩ := run_mulP hpx hpy hpt hxy hxt hyt hbx l
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr3 x y t l₁
  refine ⟨l₂, _, Run.seq r1 r2, by rw [n2, n1], ?_, ?_⟩
  · rw [v2]
    have hσ : ∀ m, Function.update (rv l) p (rv l a * rv l b % 2 ^ l.length) m =
        if m = p then rv l a * rv l b % 2 ^ l.length else rv l m := fun m => by
      rw [Function.update_apply]
    apply update3_zero
    · rw [Function.update_of_ne (Ne.symm hpx)]; exact hx
    · rw [Function.update_of_ne (Ne.symm hpy)]; exact hy
    · rw [Function.update_of_ne (Ne.symm hpt)]; exact ht
    · intro m h1 h2 h3
      by_cases hm : m = p
      · subst hm; rw [Function.update_self]; exact v1
      · rw [Function.update_of_ne hm]; exact m1 m hm h1 h2 h3
  · rw [n1]; nlinarith

/-- **Clean shifts**. -/
theorem run_cshl {x c t o : Fin K} (hxt : x ≠ t) (hto : t ≠ o) (hxo : x ≠ o) (l : List (RC K))
    (ho : rv l o = 1) (ht : rv l t = 0) :
    ∃ l' cst, Run (RProg.cshl x c t o) l l' cst ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) x (rv l x * 2 ^ rv l c % 2 ^ l.length) ∧
      cst ≤ 3 * (2 * l.length + 2) + rv l c * (3 * (2 * l.length + 2)) := by
  obtain ⟨l₁, c₁, r1, n1, v1, t1, m1, k1⟩ := run_shlBy hxt hto hxo l ho
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr t l₁
  refine ⟨l₂, _, Run.seq r1 r2, by rw [n2, n1], ?_, by rw [n1]; omega⟩
  rw [v2]
  funext m
  rw [Function.update_apply, Function.update_apply]
  by_cases h1 : m = t
  · subst h1; rw [if_pos rfl, if_neg (Ne.symm hxt)]; exact ht.symm
  · rw [if_neg h1]
    by_cases h2 : m = x
    · subst h2; rw [if_pos rfl]; exact v1
    · rw [if_neg h2]; exact m1 m h2 h1

theorem run_cshr {x c t o : Fin K} (hxt : x ≠ t) (hto : t ≠ o) (hxo : x ≠ o) (l : List (RC K))
    (ho : rv l o = 1) (ht : rv l t = 0) :
    ∃ l' cst, Run (RProg.cshr x c t o) l l' cst ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) x (rv l x / 2 ^ rv l c) ∧
      cst ≤ 3 * (2 * l.length + 2) + rv l c * (3 * (2 * l.length + 2)) := by
  obtain ⟨l₁, c₁, r1, n1, v1, t1, m1, k1⟩ := run_shrBy hxt hto hxo l ho
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr t l₁
  refine ⟨l₂, _, Run.seq r1 r2, by rw [n2, n1], ?_, by rw [n1]; omega⟩
  rw [v2]
  funext m
  rw [Function.update_apply, Function.update_apply]
  by_cases h1 : m = t
  · subst h1; rw [if_pos rfl, if_neg (Ne.symm hxt)]; exact ht.symm
  · rw [if_neg h1]
    by_cases h2 : m = x
    · subst h2; rw [if_pos rfl]; exact v1
    · rw [if_neg h2]; exact m1 m h2 h1

/-- A register file that agrees with `σ` off two registers holding zero there. -/
theorem update1_frame (σ τ : Fin K → ℕ) {x c : Fin K} (hxc : x ≠ c) (v : ℕ) (hc : σ c = 0)
    (hx : τ x = v) (hτ : ∀ m, m ≠ x → m ≠ c → τ m = σ m) :
    Function.update τ c 0 = Function.update σ x v := by
  funext m
  rw [Function.update_apply, Function.update_apply]
  by_cases h1 : m = c
  · subst h1; rw [if_pos rfl, if_neg (Ne.symm hxc)]; exact hc.symm
  · rw [if_neg h1]
    by_cases h2 : m = x
    · subst h2; rw [if_pos rfl]; exact hx
    · rw [if_neg h2]; exact hτ m h2 h1

/-- **Clean word reading.** -/
theorem run_crd {t V E e c mask half o : Fin K} (htc : t ≠ c) (hto : t ≠ o) (hco : c ≠ o)
    (htm : t ≠ mask) (hth : t ≠ half) (hte : t ≠ e) (hcm : c ≠ mask) (hch : c ≠ half)
    (l : List (RC K)) (Wb M m : ℕ) (w : ℕ → ℕ) (v : ℤ)
    (hw : ∀ p, w p < 2 ^ Wb) (hWbN : Wb ≤ l.length) (hMN : (2 ^ Wb) ^ M ≤ 2 ^ l.length)
    (hm : m < M) (hV : rv l V = tc l.length v)
    (hsum : v + (rv l E : ℤ) = ((∑ p ∈ Finset.range M, w p * (2 ^ Wb) ^ p : ℕ) : ℤ))
    (he : rv l e = m * Wb) (hmask : rv l mask = 2 ^ Wb - 1) (hhalf : rv l half = 2 ^ Wb / 2)
    (ho : rv l o = 1) (hc : rv l c = 0) :
    ∃ l' cst, Run (RProg.crd t V E e c mask half o) l l' cst ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) t (tc l.length ((w m : ℤ) - (2 ^ Wb / 2 : ℕ))) ∧
      cst ≤ 7 * (2 * l.length + 2) + m * Wb * (3 * (2 * l.length + 2)) := by
  obtain ⟨l₁, c₁, r1, n1, v1, m1, k1⟩ := run_rdW htc hto hco htm hth hte hcm hch l Wb M m w v
    hw hWbN hMN hm hV hsum he hmask hhalf ho
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr c l₁
  refine ⟨l₂, _, Run.seq r1 r2, by rw [n2, n1], ?_, by rw [n1]; omega⟩
  rw [v2]
  exact update1_frame _ _ htc _ hc v1 m1

/-- **Clean word writing.** -/
theorem run_cwr {O w e t c o : Fin K} (htc : t ≠ c) (hto : t ≠ o) (hco : c ≠ o) (hte : t ≠ e)
    (hOt : O ≠ t) (hOc : O ≠ c) (l : List (RC K)) (y z : ℤ) (bp : ℕ)
    (hO : rv l O = tc l.length y) (hw : rv l w = tc l.length z) (he : rv l e = bp)
    (ho : rv l o = 1) (ht : rv l t = 0) (hc : rv l c = 0) :
    ∃ l' cst, Run (RProg.cwr O w e t c o) l l' cst ∧ l'.length = l.length ∧
      rv l' = Function.update (rv l) O (tc l.length (y + z * 2 ^ bp)) ∧
      cst ≤ 6 * (2 * l.length + 2) + bp * (3 * (2 * l.length + 2)) := by
  obtain ⟨l₁, c₁, r1, n1, v1, m1, k1⟩ := run_wrW htc hto hco hte hOt hOc l y z bp hO hw he ho
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr t l₁
  obtain ⟨l₃, r3, n3, v3⟩ := run_clr c l₂
  refine ⟨l₃, _, Run.seq r1 (Run.seq r2 r3), by rw [n3, n2, n1], ?_, by rw [n2, n1]; omega⟩
  rw [v3, v2]
  funext m
  rw [Function.update_apply, Function.update_apply, Function.update_apply]
  by_cases h1 : m = c
  · subst h1; rw [if_pos rfl, if_neg (Ne.symm hOc)]; exact hc.symm
  · rw [if_neg h1]
    by_cases h2 : m = t
    · subst h2; rw [if_pos rfl, if_neg (Ne.symm hOt)]; exact ht.symm
    · rw [if_neg h2]
      by_cases h3 : m = O
      · subst h3; rw [if_pos rfl]; exact v1
      · rw [if_neg h3]; exact m1 m h3 h2 h1

namespace RProg

/-- Division that leaves its scratch registers at zero. -/
def cdiv (q r a d D s f m o : Fin K) : RProg K :=
  .seq (divP q r a d D s f m o) (.seq (.seq (clr D) (clr s)) (.seq (clr f) (clr m)))

end RProg

/-- **Clean division**: `q := ⌊a/d⌋`, `r := a mod d`, and nothing else changes. -/
theorem run_cdiv {q r a d D s f m o : Fin K}
    (hqr : q ≠ r) (hqD : q ≠ D) (hqs : q ≠ s) (hqf : q ≠ f) (hqm : q ≠ m)
    (hrD : r ≠ D) (hrs : r ≠ s) (hrf : r ≠ f) (hrm : r ≠ m)
    (hDs : D ≠ s) (hDf : D ≠ f) (hDm : D ≠ m) (hsf : s ≠ f) (hsm : s ≠ m) (hfm : f ≠ m)
    (hoq : o ≠ q) (hor : o ≠ r) (hoD : o ≠ D) (hos : o ≠ s) (hof : o ≠ f) (hom : o ≠ m)
    (hdr : d ≠ r) (hdq : d ≠ q) (l : List (RC K)) (ho : rv l o = 1) (hd : 1 ≤ rv l d)
    (ha : 2 * rv l a < 2 ^ l.length) (h0D : rv l D = 0) (h0s : rv l s = 0) (h0f : rv l f = 0)
    (h0m : rv l m = 0) :
    ∃ l' c, Run (RProg.cdiv q r a d D s f m o) l l' c ∧ l'.length = l.length ∧
      rv l' = Function.update (Function.update (rv l) q (rv l a / rv l d)) r (rv l a % rv l d) ∧
      c ≤ 16 * (l.length + 1) * (2 * l.length + 2) + 4 * (2 * l.length + 2) := by
  obtain ⟨l₁, c₁, r1, n1, vq, vr, m1, k1⟩ := run_divP hqr hqD hqs hqf hqm hrD hrs hrf hrm hDs hDf
    hDm hsf hsm hfm hoq hor hoD hos hof hom hdr hdq l ho hd ha
  obtain ⟨l₂, r2, n2, v2⟩ := run_clr D l₁
  obtain ⟨l₃, r3, n3, v3⟩ := run_clr s l₂
  obtain ⟨l₄, r4, n4, v4⟩ := run_clr f l₃
  obtain ⟨l₅, r5, n5, v5⟩ := run_clr m l₄
  refine ⟨l₅, _, Run.seq r1 (Run.seq (Run.seq r2 r3) (Run.seq r4 r5)), by
    rw [n5, n4, n3, n2, n1], ?_, by rw [n4, n3, n2, n1]; omega⟩
  rw [v5, v4, v3, v2]
  funext x
  simp only [Function.update_apply]
  by_cases h1 : x = m
  · subst h1; simp [hrm.symm, hqm.symm, h0m]
  by_cases h2 : x = f
  · subst h2; simp [h1, hrf.symm, hqf.symm, h0f]
  by_cases h3 : x = s
  · subst h3; simp [h1, h2, hrs.symm, hqs.symm, h0s]
  by_cases h4 : x = D
  · subst h4; simp [h1, h2, h3, hrD.symm, hqD.symm, h0D]
  by_cases h5 : x = r
  · subst h5; simp [h1, h2, h3, h4, vr]
  by_cases h6 : x = q
  · subst h6; simp [h1, h2, h3, h4, h5, vq]
  simp [h1, h2, h3, h4, h5, h6, m1 x h6 h5 h4 h3 h2 h1]

/-! ### Complex products on register pairs -/

theorem tc_mul_tc (N : ℕ) (x y : ℤ) : tc N x * tc N y % 2 ^ N = tc N (x * y) := tc_mul N x y

theorem tc_sub_tc (N : ℕ) (x y : ℤ) : tc N ((tc N x : ℤ) - (tc N y : ℤ)) = tc N (x - y) := by
  have h : ((tc N x : ℤ) - (tc N y : ℤ)) % 2 ^ N = (x - y) % 2 ^ N := by
    rw [tc_cast, tc_cast, Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _),
      Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]
  show (((tc N x : ℤ) - (tc N y : ℤ)) % 2 ^ N).toNat = ((x - y) % 2 ^ N).toNat
  rw [h]

namespace RProg

/-- **Complex product**: `(pR, pI) := (aR bR − aI bI, aR bI + aI bR)`, with temporaries `t1, t2`
and the multiplication scratch `x, y, t`. -/
def cprodC (pR pI aR aI bR bI t1 t2 x y t : Fin K) : RProg K :=
  .seq (.seq (.seq (cmul t1 aR bR x y t) (cmul t2 aI bI x y t)) (.prim (.sub pR t1 t2)))
    (.seq (.seq (.seq (cmul t1 aR bI x y t) (cmul t2 aI bR x y t)) (.prim (.add pI t1 t2)))
      (.seq (clr t1) (clr t2)))

end RProg

end PVNP.Discrete.SweepReg
