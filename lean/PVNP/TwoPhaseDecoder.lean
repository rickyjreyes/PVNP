import PVNP.PartIIUniform

/-! A finite-control transducer for the decoder of the original two-phase machine.
It scans the canonical configuration, returns to cell zero, writes the three-valued
answer under the manuscript output convention, and halts. -/

namespace PVNP.TwoPhaseDecoder

open PartIITuring PartIIUniform PartIITwoPhase

inductive ScanQ (Q : Type)
  | read (q : Q)
  | back (answer : Option Bool)
  | write (answer : Option Bool)
  | clear
  | done
  deriving DecidableEq, Fintype

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def trans (move : Q → Bool → Q) (out : Q → Option Bool) :
    ScanQ Q → Option Bool → ScanQ Q × Option Bool × Mv
  | .read q, some b => (.read (move q b), some b, .R)
  | .read q, none => (.back (out q), none, .L)
  | .back a, some b => (.back a, some b, .L)
  | .back a, none => (.write a, none, .R)
  | .write a, _ => (.clear, a, .R)
  | .clear, _ => (.done, none, .R)
  | .done, g => (.done, g, .R)

def reader (q₀ : Q) (move : Q → Bool → Q) (out : Q → Option Bool) : MTM where
  Q := ScanQ Q
  Γ := Option Bool
  blank := none
  inp := some
  inp_inj := Option.some_injective _
  inp_ne_blank _ := by simp
  δ := trans move out
  q0 := .read q₀
  qacc := .done
  qrej := .done

section Reader
variable (q₀ : Q) (f : Q → Bool → Q) (out : Q → Option Bool)
local notation "D" => reader q₀ f out

private theorem read_prefix (z : List Bool) (k : ℕ) (hk : k ≤ z.length) :
    (D).run ((D).init z) k = ⟨(D).inputTape z, k, .read ((z.take k).foldl f q₀)⟩ := by
  induction k with
  | zero => simp [MTM.run_zero, MTM.init, reader]
  | succ k ih =>
    have hl : k < z.length := by omega
    have hd : (D).inputTape z k = some z[k] := by
      simp [MTM.inputTape, reader, hl]
    rw [MTM.run_succ, ih (by omega)]
    change (⟨Function.update ((D).inputTape z) (k : ℤ)
        (trans f out (.read _) ((D).inputTape z k)).2.1,
        (k : ℤ) + (trans f out (.read _) ((D).inputTape z k)).2.2.shift,
        (trans f out (.read _) ((D).inputTape z k)).1⟩ : (D).Cfg) = _
    rw [hd]
    simp only [trans, Mv.shift]
    rw [← hd, Function.update_eq_self]
    rw [← List.take_concat_get' z k hl, List.foldl_append]
    simp

private theorem read_end (z : List Bool) :
    (D).run ((D).init z) (z.length + 1) =
      ⟨(D).inputTape z, (z.length : ℤ) - 1, .back (out (z.foldl f q₀))⟩ := by
  rw [MTM.run_succ, read_prefix _ _ _ _ _ le_rfl]
  have hd : (D).inputTape z z.length = none := by simp [MTM.inputTape, reader]
  simp only [List.take_length]
  change (⟨Function.update _ _ (trans f out (.read _) ((D).inputTape z z.length)).2.1,
      (z.length : ℤ) + (trans f out (.read _) ((D).inputTape z z.length)).2.2.shift,
      (trans f out (.read _) ((D).inputTape z z.length)).1⟩ : (D).Cfg) = _
  rw [hd]
  simp only [trans, Mv.shift]
  rw [← hd, Function.update_eq_self]
  rfl

private theorem return_prefix (z : List Bool) (k : ℕ) (hk : k ≤ z.length) :
    (D).run ((D).init z) (z.length + 1 + k) =
      ⟨(D).inputTape z, (z.length : ℤ) - 1 - k, .back (out (z.foldl f q₀))⟩ := by
  induction k with
  | zero => simpa using read_end q₀ f out z
  | succ k ih =>
    let j : ℤ := (z.length : ℤ) - 1 - k
    have hj : 0 ≤ j ∧ j < z.length := by dsimp [j]; omega
    have hd : (D).inputTape z j = some (z.getD j.toNat false) := by
      simp [MTM.inputTape, hj, reader]
    rw [show z.length + 1 + (k + 1) = (z.length + 1 + k) + 1 by omega,
      MTM.run_succ, ih (by omega)]
    change (⟨Function.update _ j (trans f out (.back _) ((D).inputTape z j)).2.1,
      j + (trans f out (.back _) ((D).inputTape z j)).2.2.shift,
      (trans f out (.back _) ((D).inputTape z j)).1⟩ : (D).Cfg) = _
    rw [hd]
    simp only [trans, Mv.shift]
    rw [← hd, Function.update_eq_self]
    congr 1
    dsimp [j]; omega

/-- The explicit transducer takes exactly two scans and four end operations,
including the empty input. Both halting controls coincide. -/
theorem reader_outputs (z : List Bool) :
    (D).Outputs z (decOut (out (z.foldl f q₀))) (2*z.length + 4) := by
  let a := out (z.foldl f q₀)
  let T := (D).inputTape z
  have hback : (D).run ((D).init z) (2*z.length+1) = ⟨T, -1, .back a⟩ := by
    convert return_prefix q₀ f out z z.length le_rfl using 2 <;> omega
  have ht : T (-1) = none := by simp [T, MTM.inputTape, reader]
  have hw : (D).run ((D).init z) (2*z.length+2) = ⟨T, 0, .write a⟩ := by
    rw [show 2*z.length+2 = 2*z.length+1+1 by omega, MTM.run_succ, hback]
    change (⟨Function.update T (-1) (trans f out (.back a) (T (-1))).2.1,
      (-1) + (trans f out (.back a) (T (-1))).2.2.shift,
      (trans f out (.back a) (T (-1))).1⟩ : (D).Cfg) = _
    rw [ht]; simp only [trans, Mv.shift]; rw [← ht, Function.update_eq_self]; rfl
  have hc : (D).run ((D).init z) (2*z.length+3) = ⟨Function.update T 0 a, 1, .clear⟩ := by
    rw [show 2*z.length+3 = 2*z.length+2+1 by omega, MTM.run_succ, hw]; rfl
  have hf : (D).run ((D).init z) (2*z.length+4) =
      ⟨Function.update (Function.update T 0 a) 1 none, 2, .done⟩ := by
    rw [show 2*z.length+4 = 2*z.length+3+1 by omega, MTM.run_succ, hc]; rfl
  refine ⟨_, le_rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [hf]; exact Or.inl rfl
  · intro t ht'
    by_cases h : t ≤ z.length
    · rw [read_prefix _ _ _ _ _ h]; simp [MTM.Halting, reader]
    by_cases h' : t ≤ 2*z.length+1
    · let k := t - (z.length + 1)
      have hk : k ≤ z.length := by dsimp [k]; omega
      rw [show t = z.length + 1 + k by dsimp [k]; omega, return_prefix _ _ _ _ _ hk]
      simp [MTM.Halting, reader]
    rcases (show t = 2*z.length+2 ∨ t = 2*z.length+3 by omega) with rfl | rfl
    · rw [hw]; simp [MTM.Halting, reader]
    · rw [hc]; simp [MTM.Halting, reader]
  · rw [hf]; change _ ∧ _
    change (∀ i : ℕ, i < (decOut a).length →
      Function.update (Function.update T (0 : ℤ) a) 1 none i = some ((decOut a).getD i false)) ∧
      Function.update (Function.update T (0 : ℤ) a) 1 none ((decOut a).length : ℤ) = none
    cases a with
    | none => simp [decOut, Function.update]
    | some b =>
      constructor
      · intro i hi
        have : i = 0 := by simp [decOut] at hi; omega
        subst i; simp [decOut, Function.update]
      · simp [decOut, Function.update]

end Reader

/-- Each identity bit occupies a tagged pair. A true tag starts a cell header. -/
def pack : List Bool → List Bool
  | [] => []
  | b :: l => false :: b :: pack l

theorem pack_length (l : List Bool) : (pack l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [pack, ih]; omega

private theorem pack_inj : Function.Injective pack := by
  intro l
  induction l with
  | nil => intro r h; cases r <;> simp_all [pack]
  | cons b l ih =>
    intro r h
    cases r with
    | nil => simp [pack] at h
    | cons b' r =>
      simp only [pack, List.cons.injEq, true_and] at h
      rw [h.1, ih h.2]

variable (M : MTM)

/-- The fixed identity table of the manuscript alphabet can be chosen once for M. -/
noncomputable def identityBits (s : S M) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card (S M)) => decide (i = Fintype.equivFin (S M) s)

def hasQ (q : M.Q) (s : S M) : Bool := decide (s.2.1 = some (.inl q))

noncomputable def stateBits (s : S M) : List Bool :=
  true :: hasQ M M.qacc s :: hasQ M M.qrej s :: pack (identityBits M s)

theorem stateBits_length (s : S M) :
    (stateBits M s).length = 3 + 2 * Fintype.card (S M) := by
  simp [stateBits, pack_length, identityBits]; omega

theorem stateBits_injective : Function.Injective (stateBits M) := by
  intro s t h
  have hp : pack (identityBits M s) = pack (identityBits M t) := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2
  have hi := List.ofFn_injective (pack_inj hp : identityBits M s = identityBits M t)
  have atS := congrFun hi (Fintype.equivFin (S M) s)
  apply (Fintype.equivFin (S M)).injective
  simpa using atS

inductive Parser
  | pre
  | tag (acc rej : Bool)
  | skip (acc rej : Bool)
  | accBit (acc rej : Bool)
  | rejBit (acc rej : Bool)
  deriving DecidableEq, Fintype

def parse : Parser → Bool → Parser
  | .pre, true => .pre
  | .pre, false => .tag false false
  | .tag a r, true => .accBit a r
  | .tag a r, false => .skip a r
  | .skip a r, _ => .tag a r
  | .accBit a r, b => .rejBit (a || b) r
  | .rejBit a r, b => .tag a (r || b)

def verdict (a r : Bool) : Option Bool := if a then some true else if r then some false else none

def result : Parser → Option Bool
  | .tag a r => verdict a r
  | _ => none

private theorem parse_pre (n : ℕ) :
    (List.replicate n true).foldl parse .pre = .pre := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, parse] using ih

private theorem parse_pack (l : List Bool) (a r : Bool) :
    (pack l).foldl parse (.tag a r) = .tag a r := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [pack, parse] using ih

private theorem parse_states (l : List (S M)) (a r : Bool) :
    (l.flatMap (stateBits M)).foldl parse (.tag a r) =
      .tag (a || l.any (hasQ M M.qacc)) (r || l.any (hasQ M M.qrej)) := by
  induction l generalizing a r with
  | nil => simp
  | cons s l ih =>
    simp [stateBits, List.foldl_append, parse, parse_pack, ih, Bool.or_assoc]

def window (L : ℕ) : Set (Fin 1 → ℤ) := fun i => InWin L (i 0)

instance (L : ℕ) : DecidablePred (· ∈ window L) := fun i => inferInstanceAs (Decidable (InWin L (i 0)))

def indices (L : ℕ) := (boxIdx 1 (L+1)).filter fun j => decide (site 1 (L+1) j ∈ window L)

private theorem indices_length (L : ℕ) : (indices L).length ≤ 2*(L+1)+1 := by
  simpa [indices, boxIdx, side] using
    List.length_filter_le (fun j => decide (site 1 (L+1) j ∈ window L)) (boxIdx 1 (L+1))

private theorem window_any (L : ℕ) (C : ℤ → S M) (q : M.Q) :
    ((indices L).map (fun j => C (site 1 (L+1) j 0))).any (hasQ M q) = true ↔
      ∃ i ∈ Finset.Icc (-(L : ℤ)) L, (C i).2.1 = some (.inl q) := by
  simp only [List.any_eq_true, List.mem_map, indices, List.mem_filter, boxIdx, List.mem_range,
    decide_eq_true_eq, hasQ, exists_exists_and_eq_and]
  constructor
  · rintro ⟨j, ⟨_, hw⟩, h⟩
    exact ⟨_, Finset.mem_Icc.mpr hw, h⟩
  · rintro ⟨i, hi, hq⟩
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
    let j := (i + (L+1 : ℕ)).toNat
    have hj : (j : ℤ) = i + (L+1 : ℕ) := Int.toNat_of_nonneg (by omega)
    have hlt : j < side (L+1) := by unfold side; omega
    have he : site 1 (L+1) j 0 = i := by simp [site, Nat.mod_eq_of_lt hlt]; omega
    exact ⟨j, ⟨by simpa using hlt, show InWin L _ from he ▸ ⟨hlo, hhi⟩⟩, he ▸ hq⟩

/-- The first-answer decoder reads every canonical configuration, including malformed
head arrangements. An accepting head anywhere has precedence over every rejecting head. -/
theorem decM_outputs (n L : ℕ) (C : ℤ → S M) :
    (reader .pre parse result).Outputs
      (List.replicate n true ++ false :: cfgCode (stateBits M) 1 (L+1) (window L) (fun i => C (i 0)))
      (decOut (decM M L C)) (2*(n + 1 + (2*(L+1)+1)*(3+2*Fintype.card (S M)))+4) := by
  let states := (indices L).map (fun j => C (site 1 (L+1) j 0))
  let z := List.replicate n true ++ false :: states.flatMap (stateBits M)
  have hcfg : cfgCode (stateBits M) 1 (L+1) (window L) (fun i => C (i 0)) =
      states.flatMap (stateBits M) := by simp [states, cfgCode, indices, List.flatMap_map]
  have hf : result (z.foldl parse .pre) = decM M L C := by
    simp only [z, List.foldl_append, parse_pre, List.foldl_cons, parse, parse_states, Bool.false_or, result, verdict]
    simp only [decM, states, window_any]
  have hlen : (states.flatMap (stateBits M)).length = states.length * (3+2*Fintype.card (S M)) := by
    generalize states = l
    induction l with
    | nil => simp
    | cons s l ih => simp [ih, stateBits_length, Nat.succ_mul, Nat.add_comm]
  have hb : z.length ≤ n + 1 + (2*(L+1)+1)*(3+2*Fintype.card (S M)) := by
    have h := Nat.mul_le_mul_right (3+2*Fintype.card (S M)) (indices_length L)
    simpa [z, hlen, states, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_left h (n+1)
  obtain ⟨t,ht,hh,hs⟩ := reader_outputs .pre parse result z
  rw [hf] at hs
  rw [hcfg]
  exact ⟨t, by omega, hh, hs⟩

/-- The `UWCC.dec_fp` polynomial bound for the original window with any fixed
polynomial radius clock, with the two-phase alphabet and decoder unaltered. -/
theorem decM_fp (p : Polynomial ℕ) :
    ∃ (D : MTM) (t : Polynomial ℕ), ∀ (n : ℕ) (C : (Fin 1 → ℤ) → S M),
      D.Outputs (List.replicate n true ++ false ::
        cfgCode (stateBits M) 1 (p.eval n + 1) (window (p.eval n)) C)
        (decOut (decM M (p.eval n) (fun i => C (fun _ => i)))) (t.eval n) := by
  refine ⟨reader .pre parse result,
    2*(Polynomial.X+1+(2*(p+1)+1)*Polynomial.C (3+2*Fintype.card (S M)))+4, ?_⟩
  intro n C
  have hc : (fun i : Fin 1 → ℤ => C (fun _ => i 0)) = C := by
    funext i; congr 1; funext j; fin_cases j; rfl
  simpa [hc] using decM_outputs M n (p.eval n) (fun i => C (fun _ => i))

end PVNP.TwoPhaseDecoder
