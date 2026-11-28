import PVNP.SweepLayout

/-!
# A register machine on tracks, compiled to single-tape Turing machines

The verified arithmetic of the earlier modules runs on fixed cell alphabets, one per primitive.
A large program, such as the restricted continuum evaluator (#99), needs many numbers at once and
control flow that depends on the data. This module provides a **register machine** whose
programs compile, with exact transition counts, to the repository's single-tape Turing machines.

* **Cells and registers.** A tape cell is `RC K = Fin K → Bool`: one bit of each of `K` registers.
  Register `i` holds the little-endian number on track `i` (`rv l i`), so every register is a
  number below `2^N` on a tape of length `N` (`rv_lt`).
* **Primitive instructions** (`Prim`). Each is one round trip of a sweep program (`primProg`), of
  exact cost `2N + 2` (`2N + 3` for the extension):
  - `sub`, `add`: `r_i := r_j ∓ r_k` modulo `2^N` (`sub_rv`, `add_rv`);
  - `shl`, `shr`: `r_i := 2 r_j mod 2^N` and `r_i := ⌊r_j / 2⌋` (`shl_rv`, `shr_rv`);
  - `bit`: any bitwise map of two registers (`bit_rv`);
  - `spread`: all ones if `r_j` is odd, else zero (`spread_rv`);
  - `lt`: all ones if `r_j < r_k`, else zero (`lt_rv`);
  - `one`: `r_i := 1` (`one_rv`);
  - `extend`: append one zero cell (`extend_rv`, `extend_length`, `extend_cost`).

  Every instruction changes only its target register (`Prim.rv_frame`).
* **Programs** (`RProg`): primitives, sequencing and `while r_j ≠ 0 do P`. `Run P l l' c` is the
  big-step semantics with the exact cost `c` of all round trips, loop tests included.
* **The compilation theorem** (`compile_first`). `compile` turns a program into a sweep program
  with an exit instruction, built from `ProgOn.seq` and `ProgOn.loop`. Every run is a first
  arrival of the compiled program at its exit, with the same output tape and **exactly the same
  cost**.
* **Deciders** (`decider`, `decider_firstAnswer`, `mem_P_TM_of_run`). After the program, one more
  round trip answers whether a register is nonzero. If the program runs on every input with cost
  bounded by a polynomial in the input length, the decided language is in `P_TM`. The input bits
  are lifted into register `0`, and register `1` marks the input cells (`rlift`, `rv_input`).

No property of any particular program is assumed here.
-/

namespace PVNP.Discrete.SweepReg

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.SweepArith

/-! ### Cells, registers and primitive instructions -/

/-- A tape cell of the register machine: one bit of each of `K` registers. -/
abbrev RC (K : ℕ) := Fin K → Bool

variable {K : ℕ}

/-- The value of register `i`: the little-endian number on track `i`. -/
def rv (l : List (RC K)) (i : Fin K) : ℕ := val (l.map fun x => x i)

theorem rv_lt (l : List (RC K)) (i : Fin K) : rv l i < 2 ^ l.length := by
  have h := val_lt (l.map fun x => x i)
  rwa [List.length_map] at h

/-- The buffers of the primitive instructions. -/
abbrev BB := Bool × Bool

/-- The borrow of one subtractor cell. -/
def bsub (a b w : Bool) : Bool := (!a && b) || (!(xor a b) && w)

/-- The carry of one adder cell. -/
def badd (a b c : Bool) : Bool := (a && b) || (c && xor a b)

/-- **The primitive instructions.** Each one is a single round trip over the tape. -/
inductive Prim (K : ℕ)
  /-- `r_i := r_j − r_k` modulo `2^N`. -/
  | sub (i j k : Fin K)
  /-- `r_i := r_j + r_k` modulo `2^N`. -/
  | add (i j k : Fin K)
  /-- `r_i := 2 r_j` modulo `2^N`. -/
  | shl (i j : Fin K)
  /-- `r_i := ⌊r_j / 2⌋`. -/
  | shr (i j : Fin K)
  /-- `r_i := op(r_j, r_k)` bitwise. -/
  | bit (i j k : Fin K) (op : Bool → Bool → Bool)
  /-- `r_i := 2^N − 1` if `r_j` is odd, else `0`. -/
  | spread (i j : Fin K)
  /-- `r_i := 2^N − 1` if `r_j < r_k`, else `0`. -/
  | lt (i j k : Fin K)
  /-- `r_i := 1` modulo `2^N`. -/
  | one (i : Fin K)
  /-- Append one cell holding zero bits. -/
  | extend

namespace Prim

/-- The initial forward buffer. -/
def init : Prim K → BB
  | one _ => (true, false)
  | _ => (false, false)

/-- The forward transducer. -/
def f : Prim K → BB → RC K → RC K × BB
  | sub i j k => fun w x =>
      (Function.update x i (xor (xor (x j) (x k)) w.1), (bsub (x j) (x k) w.1, false))
  | add i j k => fun c x =>
      (Function.update x i (xor (xor (x j) (x k)) c.1), (badd (x j) (x k) c.1, false))
  | shl i j => fun p x => (Function.update x i p.1, (x j, false))
  | shr _ _ => fun b x => (x, b)
  | bit i j k op => fun b x => (Function.update x i (op (x j) (x k)), b)
  | spread i j => fun s x =>
      if s.1 then (Function.update x i s.2, s) else (Function.update x i (x j), (true, x j))
  | lt _ j k => fun w x => (x, (bsub (x j) (x k) w.1, false))
  | one i => fun s x => (Function.update x i s.1, (false, false))
  | extend => fun b x => (x, b)

/-- The right-end extension. -/
def e : Prim K → BB → Option (RC K)
  | extend => fun _ => some fun _ => false
  | _ => fun _ => none

/-- The backward transducer. -/
def g : Prim K → BB → RC K → RC K × BB
  | shr i j => fun h x => (Function.update x i h.1, (x j, false))
  | lt i _ _ => fun w x => (Function.update x i w.1, w)
  | _ => fun b x => (x, b)

/-- The forward pass. -/
def fp (p : Prim K) (l : List (RC K)) : List (RC K) × BB := fscan p.f p.init l

/-- The tape after the round trip. -/
def apply (p : Prim K) (l : List (RC K)) : List (RC K) :=
  (bscan p.g (p.fp l).2 ((p.fp l).1 ++ (p.e (p.fp l).2).toList)).1

/-- The exact cost of the round trip. -/
def cost (p : Prim K) (l : List (RC K)) : ℕ := 2 * l.length + 2 + (p.e (p.fp l).2).toList.length

end Prim

/-- How an input bit is read: register `0` holds the input, register `1` marks its cells. -/
def rlift (b : Bool) : RC K := fun i => (decide (i.val = 0) && b) || decide (i.val = 1)

/-- The sweep program of one primitive instruction. -/
def primProg (p : Prim K) : ProgOn (RC K) where
  I := AddI
  B := BB
  lift := rlift
  start := .go
  init _ := p.init
  fwd
    | .go => p.f
    | .done => fun b x => (x, b)
  ext
    | .go => p.e
    | .done => fun _ => none
  bwd
    | .go => p.g
    | .done => fun b x => (x, b)
  next _ := fun _ => .inl .done

theorem prim_step (p : Prim K) (l : List (RC K)) :
    (primProg p).toProg.stepP (AddI.go, l) = .inl (AddI.done, p.apply l) := rfl

theorem prim_tripCost (p : Prim K) (l : List (RC K)) :
    (primProg p).toProg.tripCost AddI.go l = p.cost l := rfl

/-- **One primitive instruction** first-arrives at `done` with its exact cost. -/
theorem prim_first (p : Prim K) (l : List (RC K)) :
    ReachFirst (primProg p).toProg AddI.done (AddI.go, l) (p.apply l) (p.cost l) := by
  have h := ReachFirst.last (P := (primProg p).toProg) (e := AddI.done) (prim_step p l)
  rwa [prim_tripCost] at h


/-! ### Scan lemmas -/

theorem fscan_idR {B : Type} : ∀ (b : B) (l : List (RC K)), fscan (fun b x => (x, b)) b l = (l, b)
  | _, [] => rfl
  | b, x :: l => by simp [fscan, fscan_idR b l]

theorem fscan_track {B : Type} (f : B → RC K → RC K × B) (m : Fin K)
    (hf : ∀ b x, (f b x).1 m = x m) :
    ∀ (b : B) (l : List (RC K)), (fscan f b l).1.map (fun x => x m) = l.map (fun x => x m)
  | _, [] => rfl
  | b, x :: l => by
    simp only [fscan, List.map_cons, hf, fscan_track f m hf _ l]

theorem bscan_track {B : Type} (g : B → RC K → RC K × B) (m : Fin K)
    (hg : ∀ b x, (g b x).1 m = x m) :
    ∀ (b : B) (l : List (RC K)), (bscan g b l).1.map (fun x => x m) = l.map (fun x => x m)
  | _, [] => rfl
  | b, x :: l => by
    simp only [bscan, List.map_cons, hg, bscan_track g m hg b l]

theorem val_replicate (n : ℕ) (b : Bool) :
    val (List.replicate n b) = if b then 2 ^ n - 1 else 0 := by
  induction n with
  | zero => cases b <;> simp [val]
  | succ n ih =>
    rw [List.replicate_succ, val, ih, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    cases b
    · simp
    · simp
      omega

theorem bsub_spec (a b w : Bool) :
    (xor (xor a b) w).toNat + b.toNat + w.toNat = a.toNat + 2 * (bsub a b w).toNat := by
  cases a <;> cases b <;> cases w <;> rfl

theorem badd_spec (a b c : Bool) :
    (xor (xor a b) c).toNat + 2 * (badd a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

namespace Prim

/-- The register an instruction writes. -/
def tgt : Prim K → Option (Fin K)
  | sub i _ _ => some i
  | add i _ _ => some i
  | shl i _ => some i
  | shr i _ => some i
  | bit i _ _ _ => some i
  | spread i _ => some i
  | lt i _ _ => some i
  | one i => some i
  | extend => none

theorem f_frame (p : Prim K) {m : Fin K} (hm : p.tgt ≠ some m) (b : BB) (x : RC K) :
    (p.f b x).1 m = x m := by
  cases p with
  | sub i j k =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [f, Function.update_of_ne h]
  | add i j k =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [f, Function.update_of_ne h]
  | shl i j =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [f, Function.update_of_ne h]
  | shr i j => rfl
  | bit i j k op =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [f, Function.update_of_ne h]
  | spread i j =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp only [f]
    split_ifs <;> simp [Function.update_of_ne h]
  | lt i j k => rfl
  | one i =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [f, Function.update_of_ne h]
  | extend => rfl

theorem g_frame (p : Prim K) {m : Fin K} (hm : p.tgt ≠ some m) (b : BB) (x : RC K) :
    (p.g b x).1 m = x m := by
  cases p with
  | shr i j =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [g, Function.update_of_ne h]
  | lt i j k =>
    have h : m ≠ i := fun h => hm (by rw [h]; rfl)
    simp [g, Function.update_of_ne h]
  | _ => rfl

theorem e_none (p : Prim K) (hp : p ≠ extend) (b : BB) : p.e b = none := by
  cases p <;> first | rfl | exact absurd rfl hp

theorem apply_length (p : Prim K) (l : List (RC K)) :
    (p.apply l).length = l.length + (p.e (p.fp l).2).toList.length := by
  unfold apply fp
  rw [bscan_length, List.length_append, fscan_length]

theorem apply_length_of (p : Prim K) (hp : p ≠ extend) (l : List (RC K)) :
    (p.apply l).length = l.length := by
  rw [apply_length, e_none p hp]; rfl

theorem cost_of (p : Prim K) (hp : p ≠ extend) (l : List (RC K)) :
    p.cost l = 2 * l.length + 2 := by
  unfold cost; rw [e_none p hp]; rfl

theorem apply_of (p : Prim K) (hp : p ≠ extend) (l : List (RC K)) :
    p.apply l = (bscan p.g (p.fp l).2 (p.fp l).1).1 := by
  unfold apply; rw [e_none p hp]; simp

theorem apply_fwd (p : Prim K) (hp : p ≠ extend) (hg : p.g = fun b x => (x, b))
    (l : List (RC K)) : p.apply l = (fscan p.f p.init l).1 := by
  rw [apply_of p hp, hg, bscan_id]; rfl

/-- **The frame**: an instruction leaves every register but its target unchanged. -/
theorem apply_track (p : Prim K) (hp : p ≠ extend) {m : Fin K} (hm : p.tgt ≠ some m)
    (l : List (RC K)) : (p.apply l).map (fun x => x m) = l.map (fun x => x m) := by
  rw [apply_of p hp, bscan_track _ m (g_frame p hm), fp, fscan_track _ m (f_frame p hm)]

theorem rv_frame (p : Prim K) (hp : p ≠ extend) {m : Fin K} (hm : p.tgt ≠ some m)
    (l : List (RC K)) : rv (p.apply l) m = rv l m := by
  unfold rv; rw [apply_track p hp hm]

end Prim

theorem rv_eq_update {l l' : List (RC K)} {i : Fin K} {v : ℕ} (h1 : rv l' i = v)
    (h2 : ∀ m, m ≠ i → rv l' m = rv l m) : rv l' = Function.update (rv l) i v := by
  funext m
  by_cases hm : m = i
  · subst hm; rw [Function.update_self]; exact h1
  · rw [Function.update_of_ne hm]; exact h2 m hm

/-! ### The value of each instruction -/

theorem tc_of_eq (N R A B W : ℕ) (hR : R < 2 ^ N) (h : R + B = A + 2 ^ N * W) :
    R = tc N ((A : ℤ) - B) := by
  have e : ((A : ℤ) - B) = R + 2 ^ N * (-(W : ℤ)) := by
    have : ((R + B : ℕ) : ℤ) = ((A + 2 ^ N * W : ℕ) : ℤ) := by rw [h]
    push_cast at this; linarith
  have h2 : ((A : ℤ) - B) % 2 ^ N = R := by
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hR)]
  unfold tc; rw [h2]; simp

theorem fscan_sub_val (i j k : Fin K) : ∀ (w : BB) (l : List (RC K)),
    val ((fscan (Prim.sub i j k).f w l).1.map fun x => x i) + val (l.map fun x => x k) +
        w.1.toNat =
      val (l.map fun x => x j) + 2 ^ l.length * (fscan (Prim.sub i j k).f w l).2.1.toNat
  | w, [] => by simp [fscan, val]
  | w, x :: l => by
    have ih := fscan_sub_val i j k (bsub (x j) (x k) w.1, false) l
    have hs := bsub_spec (x j) (x k) w.1
    simp only [fscan, Prim.f, List.map_cons, val, List.length_cons, pow_succ,
      Function.update_self] at ih ⊢
    nlinarith [ih, hs]

/-- **Subtraction** modulo `2^N`. -/
theorem sub_rv (i j k : Fin K) (l : List (RC K)) :
    rv ((Prim.sub i j k).apply l) =
      Function.update (rv l) i (tc l.length ((rv l j : ℤ) - rv l k)) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (by simp [Prim.tgt]; exact Ne.symm hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  have h := fscan_sub_val i j k (Prim.sub i j k).init l
  have hR := val_lt ((fscan (Prim.sub i j k).f (Prim.sub i j k).init l).1.map fun x => x i)
  rw [List.length_map, fscan_length] at hR
  simp only [Prim.init, Bool.toNat_false, add_zero] at h
  exact tc_of_eq _ _ _ _ _ hR h


theorem tgt_ne {p : Prim K} {i m : Fin K} (hp : p.tgt = some i) (hm : m ≠ i) : p.tgt ≠ some m := by
  rw [hp]; intro h; exact hm (Option.some.inj h).symm

/-! ### Addition -/

theorem fscan_add_val (i j k : Fin K) : ∀ (c : BB) (l : List (RC K)),
    val ((fscan (Prim.add i j k).f c l).1.map fun x => x i) +
        2 ^ l.length * (fscan (Prim.add i j k).f c l).2.1.toNat =
      val (l.map fun x => x j) + val (l.map fun x => x k) + c.1.toNat
  | c, [] => by simp [fscan, val]
  | c, x :: l => by
    have ih := fscan_add_val i j k (badd (x j) (x k) c.1, false) l
    have hs := badd_spec (x j) (x k) c.1
    simp only [fscan, Prim.f, List.map_cons, val, List.length_cons, pow_succ,
      Function.update_self] at ih ⊢
    nlinarith [ih, hs]

/-- **Addition** modulo `2^N`. -/
theorem add_rv (i j k : Fin K) (l : List (RC K)) :
    rv ((Prim.add i j k).apply l) =
      Function.update (rv l) i ((rv l j + rv l k) % 2 ^ l.length) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  have h := fscan_add_val i j k (false, false) l
  have hR := val_lt ((fscan (Prim.add i j k).f (false, false) l).1.map fun x => x i)
  rw [List.length_map, fscan_length] at hR
  simp only [Bool.toNat_false, add_zero] at h
  show val ((fscan (Prim.add i j k).f (false, false) l).1.map fun x => x i) = _
  unfold rv
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

/-! ### Shifts -/

theorem fscan_shl_val (i j : Fin K) : ∀ (p : BB) (l : List (RC K)),
    val ((fscan (Prim.shl i j).f p l).1.map fun x => x i) +
        2 ^ l.length * (fscan (Prim.shl i j).f p l).2.1.toNat =
      p.1.toNat + 2 * val (l.map fun x => x j)
  | p, [] => by simp [fscan, val]
  | p, x :: l => by
    have ih := fscan_shl_val i j (x j, false) l
    simp only [fscan, Prim.f, List.map_cons, val, List.length_cons, pow_succ,
      Function.update_self] at ih ⊢
    linarith [ih]

/-- **Doubling** modulo `2^N`. -/
theorem shl_rv (i j : Fin K) (l : List (RC K)) :
    rv ((Prim.shl i j).apply l) = Function.update (rv l) i (2 * rv l j % 2 ^ l.length) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  have h := fscan_shl_val i j (false, false) l
  have hR := val_lt ((fscan (Prim.shl i j).f (false, false) l).1.map fun x => x i)
  rw [List.length_map, fscan_length] at hR
  simp only [Bool.toNat_false, zero_add] at h
  show val ((fscan (Prim.shl i j).f (false, false) l).1.map fun x => x i) = _
  unfold rv
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

theorem bscan_shr_val (i j : Fin K) (b : BB) : ∀ l : List (RC K),
    2 * val ((bscan (Prim.shr i j).g b l).1.map fun x => x i) +
        (bscan (Prim.shr i j).g b l).2.1.toNat =
      val (l.map fun x => x j) + 2 ^ l.length * b.1.toNat
  | [] => by simp [bscan, val]
  | x :: l => by
    have ih := bscan_shr_val i j b l
    simp only [bscan, Prim.g, List.map_cons, val, List.length_cons, pow_succ,
      Function.update_self] at ih ⊢
    linarith [ih]

/-- **Halving.** -/
theorem shr_rv (i j : Fin K) (l : List (RC K)) :
    rv ((Prim.shr i j).apply l) = Function.update (rv l) i (rv l j / 2) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_of _ (by simp), Prim.fp]
  have hf : fscan (Prim.shr i j).f (Prim.shr i j).init l = (l, (false, false)) := fscan_idR _ l
  rw [hf]
  dsimp only
  have h := bscan_shr_val i j (false, false) l
  simp only [Bool.toNat_false, mul_zero, add_zero] at h
  unfold rv
  have hb := Bool.toNat_le (bscan (Prim.shr i j).g (false, false) l).2.1
  omega

/-! ### Bitwise maps -/

theorem fscan_bit_track (i j k : Fin K) (op : Bool → Bool → Bool) : ∀ (b : BB) (l : List (RC K)),
    (fscan (Prim.bit i j k op).f b l).1.map (fun x => x i) = l.map fun x => op (x j) (x k)
  | _, [] => rfl
  | b, x :: l => by
    have ih := fscan_bit_track i j k op b l
    simp only [fscan, Prim.f, List.map_cons, Function.update_self] at ih ⊢
    rw [ih]

/-- **A bitwise map.** -/
theorem bit_rv (i j k : Fin K) (op : Bool → Bool → Bool) (l : List (RC K)) :
    rv ((Prim.bit i j k op).apply l) =
      Function.update (rv l) i (val (l.map fun x => op (x j) (x k))) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  unfold rv
  rw [fscan_bit_track]

/-! ### Spreading a bit -/

theorem fscan_spread_true (i j : Fin K) (bt : Bool) : ∀ l : List (RC K),
    (fscan (Prim.spread i j).f (true, bt) l).1.map (fun x => x i) = List.replicate l.length bt
  | [] => rfl
  | x :: l => by
    have ih := fscan_spread_true i j bt l
    simp only [fscan, Prim.f, if_true, List.map_cons, Function.update_self, List.length_cons,
      List.replicate_succ] at ih ⊢
    rw [ih]

/-- **Spreading the parity** of `r_j` over all bits of `r_i`. -/
theorem spread_rv (i j : Fin K) (l : List (RC K)) :
    rv ((Prim.spread i j).apply l) =
      Function.update (rv l) i (if rv l j % 2 = 1 then 2 ^ l.length - 1 else 0) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  cases l with
  | nil => simp [fscan, rv, val]
  | cons x l =>
    have h1 : (fscan (Prim.spread i j).f (Prim.spread i j).init (x :: l)).1.map (fun x => x i) =
        List.replicate (l.length + 1) (x j) := by
      have e : fscan (Prim.spread i j).f (Prim.spread i j).init (x :: l) =
          (Function.update x i (x j) :: (fscan (Prim.spread i j).f (true, x j) l).1,
            (fscan (Prim.spread i j).f (true, x j) l).2) := rfl
      rw [e, List.map_cons, fscan_spread_true, Function.update_self, List.replicate_succ]
    unfold rv
    rw [h1, val_replicate]
    simp only [List.map_cons, val, List.length_cons]
    cases x j <;> simp

/-! ### Comparison -/

theorem fscan_lt_eq (i j k : Fin K) : ∀ (w : BB) (l : List (RC K)),
    fscan (Prim.lt i j k).f w l = (l, (fscan (Prim.sub i j k).f w l).2)
  | _, [] => rfl
  | w, x :: l => by
    have ih := fscan_lt_eq i j k (bsub (x j) (x k) w.1, false) l
    simp only [fscan, Prim.f] at ih ⊢
    rw [ih]

theorem bscan_lt_const (i j k : Fin K) (w : BB) : ∀ l : List (RC K),
    (bscan (Prim.lt i j k).g w l).1.map (fun x => x i) = List.replicate l.length w.1 ∧
      (bscan (Prim.lt i j k).g w l).2 = w
  | [] => ⟨rfl, rfl⟩
  | x :: l => by
    obtain ⟨h1, h2⟩ := bscan_lt_const i j k w l
    have e : bscan (Prim.lt i j k).g w (x :: l) =
        (Function.update x i w.1 :: (bscan (Prim.lt i j k).g w l).1, w) := by
      show (((Prim.lt i j k).g (bscan (Prim.lt i j k).g w l).2 x).1 :: (bscan (Prim.lt i j k).g w l).1,
        ((Prim.lt i j k).g (bscan (Prim.lt i j k).g w l).2 x).2) = _
      rw [h2]; rfl
    rw [e]
    refine ⟨?_, rfl⟩
    rw [List.map_cons, h1, Function.update_self, List.length_cons, List.replicate_succ]

/-- **Comparison**: `r_i` becomes all ones if `r_j < r_k`, and zero otherwise. -/
theorem lt_rv (i j k : Fin K) (l : List (RC K)) :
    rv ((Prim.lt i j k).apply l) =
      Function.update (rv l) i (if rv l j < rv l k then 2 ^ l.length - 1 else 0) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_of _ (by simp), Prim.fp, fscan_lt_eq]
  dsimp only
  show rv (bscan (Prim.lt i j k).g (fscan (Prim.sub i j k).f (false, false) l).2 l).1 i = _
  have hflag : (fscan (Prim.sub i j k).f (false, false) l).2.1 = decide (rv l j < rv l k) := by
    have h := fscan_sub_val i j k (false, false) l
    have hR := val_lt ((fscan (Prim.sub i j k).f (false, false) l).1.map fun x => x i)
    rw [List.length_map, fscan_length] at hR
    simp only [Bool.toNat_false, add_zero] at h
    unfold rv
    cases hw : (fscan (Prim.sub i j k).f (false, false) l).2.1
    · rw [hw] at h
      simp only [Bool.toNat_false, mul_zero, add_zero] at h
      symm; rw [decide_eq_false_iff_not]; omega
    · rw [hw] at h
      simp only [Bool.toNat_true, mul_one] at h
      symm; rw [decide_eq_true_iff]; omega
  obtain ⟨h1, -⟩ := bscan_lt_const i j k (fscan (Prim.sub i j k).f (false, false) l).2 l
  have h2 : rv (bscan (Prim.lt i j k).g (fscan (Prim.sub i j k).f (false, false) l).2 l).1 i =
      val (List.replicate l.length (decide (rv l j < rv l k))) := by
    show val ((bscan (Prim.lt i j k).g (fscan (Prim.sub i j k).f (false, false) l).2 l).1.map
      fun x => x i) = _
    rw [h1, hflag]
  rw [h2, val_replicate]
  simp only [decide_eq_true_eq]

/-! ### The constant one and the extension -/

theorem fscan_one_false (i : Fin K) : ∀ l : List (RC K),
    (fscan (Prim.one i).f (false, false) l).1.map (fun x => x i) = List.replicate l.length false
  | [] => rfl
  | x :: l => by
    have ih := fscan_one_false i l
    simp only [fscan, Prim.f, List.map_cons, Function.update_self, List.length_cons,
      List.replicate_succ] at ih ⊢
    rw [ih]

/-- **The constant `1`** (modulo `2^N`). -/
theorem one_rv (i : Fin K) (l : List (RC K)) :
    rv ((Prim.one i).apply l) = Function.update (rv l) i (1 % 2 ^ l.length) := by
  refine rv_eq_update ?_ fun m hm => Prim.rv_frame _ (by simp) (tgt_ne rfl hm) l
  rw [Prim.apply_fwd _ (by simp) rfl]
  cases l with
  | nil => simp [fscan, rv, val]
  | cons x l =>
    have h1 : (fscan (Prim.one i).f (Prim.one i).init (x :: l)).1.map (fun x => x i) =
        true :: List.replicate l.length false := by
      have e : fscan (Prim.one i).f (Prim.one i).init (x :: l) =
          (Function.update x i true :: (fscan (Prim.one i).f (false, false) l).1,
            (fscan (Prim.one i).f (false, false) l).2) := rfl
      rw [e, List.map_cons, fscan_one_false, Function.update_self]
    unfold rv
    rw [h1]
    simp only [val, val_replicate, Bool.false_eq_true, if_false, Bool.toNat_true, mul_zero,
      add_zero, List.length_cons]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]

theorem extend_apply (l : List (RC K)) :
    Prim.extend.apply l = l ++ [fun _ => false] := by
  unfold Prim.apply Prim.fp
  have hf : fscan (Prim.extend (K := K)).f (Prim.extend (K := K)).init l = (l, (false, false)) :=
    fscan_idR _ l
  rw [hf]
  show (bscan (fun b x => (x, b)) (false, false) (l ++ [fun _ => false])).1 = _
  rw [bscan_id]

theorem extend_rv (l : List (RC K)) : rv (Prim.extend.apply l) = rv l := by
  funext m
  rw [extend_apply]
  unfold rv
  rw [List.map_append, val_append]
  simp [val]

theorem extend_length (l : List (RC K)) : (Prim.extend.apply l).length = l.length + 1 := by
  rw [extend_apply]; simp

theorem extend_cost (l : List (RC K)) : Prim.extend.cost l = 2 * l.length + 3 := by
  unfold Prim.cost Prim.fp
  have hf : fscan (Prim.extend (K := K)).f (Prim.extend (K := K)).init l = (l, (false, false)) :=
    fscan_idR _ l
  rw [hf]
  rfl


/-! ### Programs, their semantics and their compilation -/

/-- **Register programs**: primitive instructions, sequencing and while loops. -/
inductive RProg (K : ℕ)
  | prim (p : Prim K)
  | seq (P Q : RProg K)
  /-- `while r_j ≠ 0 do P`. -/
  | loop (j : Fin K) (P : RProg K)

/-- The loop test: is register `j` nonzero? -/
def nzProg (j : Fin K) : ProgOn (RC K) where
  I := TstI
  B := Bool
  lift := rlift
  start := .test
  init _ := false
  fwd
    | .test => fun b x => (x, b || x j)
    | _ => fun b x => (x, b)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next
    | .test => fun b => if b then .inl .yes else .inl .no
    | .yes => fun _ => .inl .yes
    | .no => fun _ => .inl .no

theorem or_decide_step (b c : Bool) (v : ℕ) :
    (b || c || decide (v ≠ 0)) = (b || decide (c.toNat + 2 * v ≠ 0)) := by
  cases b <;> cases c <;> simp

theorem fscan_nzR (j : Fin K) : ∀ (b : Bool) (l : List (RC K)),
    fscan (fun b x => (x, b || x j)) b l = (l, b || decide (rv l j ≠ 0))
  | b, [] => by simp [fscan, rv, val]
  | b, x :: l => by
    have ih := fscan_nzR j (b || x j) l
    simp only [fscan] at ih ⊢
    rw [ih]
    simp only [rv, List.map_cons, val]
    rw [or_decide_step]

theorem nz_trip (j : Fin K) (l : List (RC K)) :
    (nzProg j).toProg.trip TstI.test l = (l, decide (rv l j ≠ 0)) := by
  have hf : (nzProg j).toProg.fpass TstI.test l = (l, decide (rv l j ≠ 0)) := by
    show fscan (fun b x => (x, b || x j)) false l = _
    rw [fscan_nzR]; simp
  have hm : (nzProg j).toProg.mid TstI.test l = l := by
    unfold Prog.mid; rw [hf]
    show l ++ ([] : List (RC K)) = l
    exact List.append_nil l
  unfold Prog.trip
  rw [hm, hf]
  exact bscan_id _ l

theorem nz_next (j : Fin K) (b : Bool) :
    (nzProg j).toProg.next TstI.test b = if b then .inl .yes else .inl .no := rfl

theorem nz_step (j : Fin K) (l : List (RC K)) :
    (nzProg j).toProg.stepP (TstI.test, l) =
      .inl (if rv l j ≠ 0 then TstI.yes else TstI.no, l) := by
  unfold Prog.stepP
  rw [nz_trip]
  dsimp only
  rw [nz_next]
  by_cases h : rv l j ≠ 0
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

theorem nz_cost (j : Fin K) (l : List (RC K)) :
    (nzProg j).toProg.tripCost TstI.test l = 2 * l.length + 2 := rfl

/-- **The compiler**: a register program becomes a sweep program with an exit instruction. -/
def compile : RProg K → (A : ProgOn (RC K)) × A.I
  | .prim p => ⟨primProg p, AddI.done⟩
  | .seq P Q => ⟨ProgOn.seq (compile P).1 (compile Q).1 (compile P).2, .inr (compile Q).2⟩
  | .loop j P => ⟨ProgOn.loop (nzProg j) (compile P).1 TstI.yes (compile P).2, .inl TstI.no⟩

theorem compile_start_ne : ∀ P : RProg K, (compile P).1.start ≠ (compile P).2
  | .prim _ => show AddI.go ≠ AddI.done by decide
  | .seq _ _ => Sum.inl_ne_inr
  | .loop _ _ => fun h => by cases h

theorem compile_lift : ∀ P : RProg K, (compile P).1.lift = rlift
  | .prim _ => rfl
  | .seq P _ => compile_lift P
  | .loop _ _ => rfl

/-- **Big-step semantics with exact costs.** `Run P l l' c`: from the tape `l`, the program `P`
ends on the tape `l'` after round trips of total cost `c`. -/
inductive Run : RProg K → List (RC K) → List (RC K) → ℕ → Prop
  | prim (p : Prim K) (l : List (RC K)) : Run (.prim p) l (p.apply l) (p.cost l)
  | seq {P Q : RProg K} {l l₁ l₂ : List (RC K)} {c₁ c₂ : ℕ} :
      Run P l l₁ c₁ → Run Q l₁ l₂ c₂ → Run (.seq P Q) l l₂ (c₁ + c₂)
  | stop {j : Fin K} {P : RProg K} {l : List (RC K)} :
      rv l j = 0 → Run (.loop j P) l l (2 * l.length + 2)
  | iter {j : Fin K} {P : RProg K} {l l₁ l₂ : List (RC K)} {c₁ c₂ : ℕ} :
      rv l j ≠ 0 → Run P l l₁ c₁ → Run (.loop j P) l₁ l₂ c₂ →
        Run (.loop j P) l l₂ (2 * l.length + 2 + c₁ + c₂)

/-- **The compilation theorem**: every run of a register program is a first arrival of the
compiled sweep program at its exit, with the same output tape and exactly the same cost. -/
theorem compile_first {P : RProg K} {l l' : List (RC K)} {c : ℕ} (h : Run P l l' c) :
    ReachFirst (compile P).1.toProg (compile P).2 ((compile P).1.start, l) l' c := by
  induction h with
  | prim p l => exact prim_first p l
  | @seq P Q l l₁ l₂ c₁ c₂ _ _ ih1 ih2 =>
    exact ProgOn.seq_reachFirst (compile P).1 (compile Q).1 (compile P).2
      (compile_start_ne Q) ih1 ih2
  | @stop j P l h0 =>
    have hs := ProgOn.loop_stepP_inl_ne (nzProg j) (compile P).1 TstI.yes (compile P).2
      (nz_step j l) (by rw [if_neg (by simpa using h0)]; intro h; cases h)
    rw [if_neg (by simpa using h0)] at hs
    have h1 := ReachFirst.last (P := (ProgOn.loop (nzProg j) (compile P).1 TstI.yes
      (compile P).2).toProg) (e := .inl TstI.no) hs
    rwa [ProgOn.loop_tripCost_inl, nz_cost] at h1
  | @iter j P l l₁ l₂ c₁ c₂ hne _ _ ih1 ih2 =>
    have hs := ProgOn.loop_stepP_inl_exit (nzProg j) (compile P).1 TstI.yes (compile P).2
      (l := l) (l' := l) (by rw [nz_step, if_pos hne])
    have hb := ProgOn.loop_body_then (nzProg j) (compile P).1 TstI.yes (compile P).2
      (eF := TstI.no) (by intro h; cases h) ih1 ih2
    have h1 := ReachFirst.step (P := (ProgOn.loop (nzProg j) (compile P).1 TstI.yes
      (compile P).2).toProg) (e := .inl TstI.no) hs (fun h => by cases h) hb
    rw [ProgOn.loop_tripCost_inl, nz_cost] at h1
    convert h1 using 1
    ring

end PVNP.Discrete.SweepReg

namespace PVNP.Discrete.Sweep.ProgOn

variable {D : Type} [Fintype D] [DecidableEq D] (A B : ProgOn D) (e : A.I)

/-- A halting step of `B` is a halting step of the composite. -/
theorem stepP_inr_halt {j : B.I} {l l' : List D} {a : Bool}
    (h : B.toProg.stepP (j, l) = .inr (a, l')) :
    (seq A B e).toProg.stepP (.inr j, l) = .inr (a, l') := by
  have k : B.next j (B.toProg.trip j l).2 = .inr a ∧ (B.toProg.trip j l).1 = l' := by
    simp only [Prog.stepP] at h
    split at h
    · simp at h
    · rename_i a' heq
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨heq, rfl⟩
  have hn : (seq A B e).toProg.next (.inr j) (.inr (B.toProg.trip j l).2) = .inr a := by
    show (match B.next j (B.toProg.trip j l).2 with
      | .inl j' => Sum.inl (Sum.inr j')
      | .inr x => Sum.inr x) = _
    rw [k.1]
  simp only [Prog.stepP, trip_inr]
  rw [hn, k.2]

/-- **A first arrival followed by a halting trip halts**, with the costs added. -/
theorem seq_halts_of_first {s : A.toProg.I × List A.toProg.D} {l₁ : List D} {c₁ : ℕ}
    (hA : ReachFirst A.toProg e s l₁ c₁) {a : Bool} {l₂ : List D}
    (hB : B.toProg.stepP (B.start, l₁) = .inr (a, l₂)) :
    (seq A B e).toProg.Halts (.inl s.1, s.2) a (c₁ + B.toProg.tripCost B.start l₁) := by
  induction hA with
  | @last s l hs =>
    have h1 : (seq A B e).toProg.Halts (.inr B.start, l) a
        ((seq A B e).toProg.tripCost (.inr B.start) l) :=
      Prog.Halts.last (stepP_inr_halt A B e hB)
    have h2 := Prog.Halts.step (stepP_inl_exit A B e hs) h1
    rwa [tripCost_inl, tripCost_inr] at h2
  | @step s i l₁ l c hs hne _ ih =>
    have h2 := Prog.Halts.step (stepP_inl_ne A B e hs hne) (ih hB)
    rw [tripCost_inl, ← Nat.add_assoc] at h2
    exact h2

end PVNP.Discrete.Sweep.ProgOn

namespace PVNP.Discrete.SweepReg

open PVNP.Discrete PVNP.Discrete.Sweep PVNP.Discrete.SweepArith

variable {K : ℕ}

/-! ### Deciders -/

/-- The final trip: answer whether register `j` is nonzero. -/
def ansProg (j : Fin K) : ProgOn (RC K) where
  I := Unit
  B := Bool
  lift := rlift
  start := ()
  init _ := false
  fwd _ := fun b x => (x, b || x j)
  ext _ := fun _ => none
  bwd _ := fun b x => (x, b)
  next _ := fun b => .inr b

theorem ans_trip (j : Fin K) (l : List (RC K)) :
    (ansProg j).toProg.trip () l = (l, decide (rv l j ≠ 0)) := by
  have hf : (ansProg j).toProg.fpass () l = (l, decide (rv l j ≠ 0)) := by
    show fscan (fun b x => (x, b || x j)) false l = _
    rw [fscan_nzR]; simp
  have hm : (ansProg j).toProg.mid () l = l := by
    unfold Prog.mid; rw [hf]
    show l ++ ([] : List (RC K)) = l
    exact List.append_nil l
  unfold Prog.trip
  rw [hm, hf]
  exact bscan_id _ l

theorem ans_step (j : Fin K) (l : List (RC K)) :
    (ansProg j).toProg.stepP ((), l) = .inr (decide (rv l j ≠ 0), l) := by
  unfold Prog.stepP
  rw [ans_trip]
  rfl

theorem ans_cost (j : Fin K) (l : List (RC K)) :
    (ansProg j).toProg.tripCost (ansProg j).start l = 2 * l.length + 2 := rfl

/-- **The decider of a register program**: run the program, then answer whether register `j`
is nonzero. -/
def decider (P : RProg K) (j : Fin K) : Prog :=
  (ProgOn.seq (compile P).1 (ansProg j) (compile P).2).toProg

/-- **A run of a register program gives the first answer of the compiled single-tape TM.** -/
theorem decider_firstAnswer (P : RProg K) (j : Fin K) (x : List Bool) {l' : List (RC K)}
    {c : ℕ} (h : Run P (x.map rlift) l' c) :
    FirstAnswer ((decider P j).toTM.out x) (c + (2 * l'.length + 2) + 2)
      (decide (rv l' j ≠ 0)) := by
  have hf := compile_first h
  have hh := ProgOn.seq_halts_of_first (compile P).1 (ansProg j) (compile P).2 hf (ans_step j l')
  rw [ans_cost] at hh
  have hl : x.map (decider P j).lift = x.map rlift := by
    show x.map (compile P).1.lift = _
    rw [compile_lift]
  have hh' : (decider P j).Halts ((decider P j).start, x.map (decider P j).lift)
      (decide (rv l' j ≠ 0)) (c + (2 * l'.length + 2)) := by
    rw [hl]; exact hh
  exact (decider P j).toTM_firstAnswer x hh'

theorem firstAnswer_mono {out : ℕ → Option Bool} {T T' : ℕ} {b : Bool}
    (h : FirstAnswer out T b) (hT : T ≤ T') : FirstAnswer out T' b := by
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, hs.trans hT, h1, h2⟩

/-- **Register programs with polynomial cost decide languages of `P_TM`.** Suppose that on every
input `x` the program `P` runs from the lifted input to a tape `l'` with cost `c`, that
`c + 2|l'| + 4` is at most `p(|x|)`, and that register `j` of `l'` is nonzero exactly when
`x ∈ L`. Then `L ∈ P_TM`. -/
theorem mem_P_TM_of_run (P : RProg K) (j : Fin K) (L : Set (List Bool)) (p : Polynomial ℕ)
    (h : ∀ x : List Bool, ∃ l' c, Run P (x.map rlift) l' c ∧
      c + 2 * l'.length + 4 ≤ p.eval x.length ∧ (rv l' j ≠ 0 ↔ x ∈ L)) :
    L ∈ P_TM := by
  refine ⟨(decider P j).toTM, p, fun x => ?_⟩
  obtain ⟨l', c, hr, hc, hiff⟩ := h x
  refine ⟨decide (rv l' j ≠ 0), firstAnswer_mono (decider_firstAnswer P j x hr) (by dsimp only; omega), ?_⟩
  rw [decide_eq_true_iff]
  exact hiff

/-! ### The input registers -/

theorem rv_input (x : List Bool) (m : Fin K) :
    rv (x.map rlift) m =
      if m.val = 0 then val x else if m.val = 1 then 2 ^ x.length - 1 else 0 := by
  unfold rv
  rw [List.map_map]
  by_cases h0 : m.val = 0
  · rw [if_pos h0]
    congr 1
    conv_rhs => rw [← List.map_id x]
    refine List.map_congr_left fun b _ => ?_
    simp [rlift, h0]
  · rw [if_neg h0]
    by_cases h1 : m.val = 1
    · rw [if_pos h1]
      have e : x.map ((fun y : RC K => y m) ∘ rlift) = List.replicate x.length true := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        simp [rlift, h1]
      rw [e, val_replicate]
      simp
    · rw [if_neg h1]
      have e : x.map ((fun y : RC K => y m) ∘ rlift) = List.replicate x.length false := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        simp [rlift, h0, h1]
      rw [e, val_replicate]
      simp

end PVNP.Discrete.SweepReg
