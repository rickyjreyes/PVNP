import PVNP.BooleanNetwork
import PVNP.CrossingSAT

/-! A bounded-fan-in circuit has an existential CNF certificate with at most
one fresh variable and four clauses per charged node. Fan-out uses the same
variable wherever the wire is read. -/
namespace PVNP.CircuitCNF

open PVNP.BooleanNetwork PVNP.PartI PVNP.CrossingSAT

abbrev Assignment := ℕ → Bool
def Holds (a : Assignment) (F : Formula) := ∀ c ∈ F, evalClause a c = true
def Bounded (F : Formula) (k : ℕ) := ∀ c ∈ F, ∀ l ∈ c, l.1 < k
def Agree (k : ℕ) (a b : Assignment) := ∀ j < k, a j = b j

theorem holds_append : Holds a (F ++ G) ↔ Holds a F ∧ Holds a G := by
  simp only [Holds, List.mem_append]
  grind

theorem holds_congr (hb : Bounded F k) (h : Agree k a b) (ha : Holds a F) : Holds b F := by
  intro c hc
  have hh := ha c hc
  rw [Discrete.SATV.evalClause_eq_any, List.any_eq_true] at hh ⊢
  obtain ⟨l,hl,he⟩ := hh
  exact ⟨l, hl, by simpa only [evalLiteral, ← h l.1 (hb c hc l hl)] using he⟩

/-- Certificate relative to already assigned input variables below k. -/
structure Cert {I O : Type} (f : (I → Bool) → O → Bool) (p : I → ℕ) (k cost : ℕ) where
  last : ℕ
  grows : k ≤ last
  room : last ≤ k + cost
  clauses : Formula
  count : clauses.length ≤ 4*cost
  bounds : Bounded clauses last
  port : O → ℕ
  valid : ∀ o, port o < last
  sound : ∀ a, Holds a clauses → ∀ o, a (port o) = f (a ∘ p) o
  extend : ∀ a, ∃ b, Agree k a b ∧ Holds b clauses

def Good {I O : Type} (cost : ℕ) (f : (I → Bool) → O → Bool) : Prop :=
  ∀ k (p : I → ℕ), (∀ i, p i < k) → Nonempty (Cert f p k cost)

theorem wiring (g : O → I) : Good 0 (fun x => x ∘ g) := by
  intro k p hp
  exact ⟨⟨k, le_rfl, by omega, [], by simp, by simp [Bounded], p ∘ g, fun i => hp _, 
    fun _ _ _ => rfl, fun a => ⟨a, fun _ _ => rfl, by simp [Holds]⟩⟩⟩

/-- Compile two constructions in succession. The second may use both the
original inputs and the first outputs. -/
theorem join {f : (I → Bool) → A → Bool} {g : ((I ⊕ A) → Bool) → B → Bool}
    (hf : Good u f) (hg : Good v g) :
    Good (u+v) (fun x => g (Sum.elim x (f x))) := by
  intro k p hp
  obtain ⟨c⟩ := hf k p hp
  obtain ⟨d⟩ := hg c.last (Sum.elim p c.port) (by
    intro i; cases i with
    | inl j => exact (hp j).trans_le c.grows
    | inr j => exact c.valid j)
  refine ⟨⟨d.last, c.grows.trans d.grows, by
    have := c.room; have := d.room; omega,
    c.clauses ++ d.clauses, by rw [List.length_append]; have := c.count; have := d.count; omega,
    ?_, d.port, d.valid, ?_, ?_⟩⟩
  · intro C hC l hl
    rcases List.mem_append.1 hC with h|h
    · exact (c.bounds C h l hl).trans_le d.grows
    · exact d.bounds C h l hl
  · intro a ha o
    obtain ⟨hc,hd⟩ := holds_append.mp ha
    rw [d.sound _ hd]
    congr 1
    funext i
    cases i with
    | inl _ => rfl
    | inr j => exact c.sound a hc j
  · intro a
    obtain ⟨b,hab,hb⟩ := c.extend a
    obtain ⟨e,hbe,he⟩ := d.extend b
    exact ⟨e, fun j hj => (hab j hj).trans (hbe j (hj.trans_le c.grows)),
      holds_append.mpr ⟨holds_congr c.bounds hbe hb, he⟩⟩

theorem pre {f : (A → Bool) → B → Bool} (hf : Good u f) (g : A → I) :
    Good u (fun x => f (x ∘ g)) := by
  intro k p hp
  obtain ⟨c⟩ := hf k (p ∘ g) (fun i => hp _)
  exact ⟨{c with sound := c.sound}⟩

theorem post {f : (I → Bool) → A → Bool} (hf : Good u f) (g : B → A) :
    Good u (fun x => f x ∘ g) := by
  intro k p hp
  obtain ⟨c⟩ := hf k p hp
  exact ⟨{c with port := c.port ∘ g, valid := fun i => c.valid _, sound := fun a ha o => c.sound a ha _}⟩

theorem parallel {f : (I → Bool) → A → Bool} {g : (I → Bool) → B → Bool}
    (hf : Good u f) (hg : Good v g) : Good (u+v) (fun x => Sum.elim (f x) (g x)) := by
  have hg' := pre (I := I ⊕ A) hg Sum.inl
  have keep := join hg' (wiring (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
    A ⊕ B → (I ⊕ A) ⊕ B))
  convert join hf keep using 1
  funext x i; cases i <;> rfl

private def gateRows (p r k : ℕ) (f : Bool → Bool → Bool) : Formula :=
  [false, true].flatMap fun a => [false, true].map fun b => [(p,!a),(r,!b),(k,f a b)]

private theorem gateRows_ok (p r k : ℕ) (f : Bool → Bool → Bool) (w : Assignment) :
    Holds w (gateRows p r k f) ↔ w k = f (w p) (w r) := by
  simp only [Holds, gateRows, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, forall_exists_index, and_imp]
  constructor
  · intro h
    have hx : w p = false ∨ w p = true := by cases w p <;> simp
    have hy : w r = false ∨ w r = true := by cases w r <;> simp
    have ht := h _ _ hx _ hy rfl
    simpa [evalClause, evalLiteral, literalTrue] using ht
  · rintro h c a _ b _ rfl
    by_cases ha : w p = a <;> by_cases hb : w r = b <;>
      cases a <;> cases b <;> simp_all [evalClause, evalLiteral, literalTrue]

theorem gate (a b : I) (f : Bool → Bool → Bool) :
    Good 1 (fun (x : I → Bool) (_ : Unit) => f (x a) (x b)) := by
  intro k p hp
  refine ⟨⟨k+1, by omega, le_rfl, gateRows (p a) (p b) k f, by rfl, ?_, fun _ => k,
    fun _ => Nat.lt_succ_self k, ?_, ?_⟩⟩
  · intro c hc l hl
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.1 hc
    obtain ⟨j,_,rfl⟩ := List.mem_map.1 hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl|rfl|rfl <;> simp only <;> first | exact Nat.lt_succ_of_lt (hp _) | omega
  · intro w hw _
    exact (gateRows_ok _ _ _ _ _).1 hw
  · intro w
    let z := Function.update w k (f (w (p a)) (w (p b)))
    have same : Agree k w z := fun j hj => (Function.update_of_ne (by omega) _ _).symm
    refine ⟨z, same, (gateRows_ok _ _ _ _ _).2 ?_⟩
    rw [← same _ (hp a), ← same _ (hp b)]
    exact Function.update_self ..

private theorem literal (b : Bool) : Good 1 (fun (_ : I → Bool) (_ : Unit) => b) := by
  intro k p _
  refine ⟨⟨k+1, by omega, le_rfl, [[(k,b)]], by simp, ?_, fun _ => k, fun _ => Nat.lt_succ_self k,
    ?_, ?_⟩⟩
  · intro c hc l hl; simp only [List.mem_singleton] at hc; subst c
    simp only [List.mem_singleton] at hl; subst l; exact Nat.lt_succ_self k
  · simp [Holds, evalClause, evalLiteral, literalTrue]
  · intro a
    refine ⟨Function.update a k b, fun j hj => (Function.update_of_ne (by omega) _ _).symm, ?_⟩
    simp [Holds, evalClause, evalLiteral, literalTrue]

private theorem weaken {f : (I → Bool) → O → Bool} (hf : Good u f) (h : u ≤ v) : Good v f := by
  intro k p hp
  obtain ⟨c⟩ := hf k p hp
  exact ⟨{c with room := by have := c.room; omega, count := by have := c.count; omega}⟩

private theorem expr_good (e : Expr I) : Good e.size (fun x (_ : Unit) => e.eval x) := by
  induction e with
  | var i => exact weaken (wiring (fun _ => i)) (Nat.zero_le _)
  | lit b => exact literal b
  | neg e h =>
    exact join h (gate (Sum.inr ()) (Sum.inr ()) (fun a _ => !a))
  | conj a b ha hb =>
    exact join (parallel ha hb) (gate (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr ())) and)
  | disj a b ha hb =>
    exact join (parallel ha hb) (gate (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inr ())) or)

private theorem layer_good [Fintype O] (g : O → Expr I) :
    Good (∑ o, (g o).size) (fun x o => (g o).eval x) := by
  classical
  have aux (s : Finset O) : Good (∑ o ∈ s, (g o).size)
      (fun x (o : {i // i ∈ s}) => (g o.val).eval x) := by
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      let no (i : {j : O // j ∈ (∅ : Finset O)}) : I := False.elim (Finset.notMem_empty _ i.property)
      convert wiring no using 1
      funext x i; exact False.elim (Finset.notMem_empty _ i.property)
    | @insert a s h ih =>
      rw [Finset.sum_insert h]
      let choose (o : {i // i ∈ insert a s}) : Unit ⊕ {j // j ∈ s} :=
        if e : o.val = a then .inl () else .inr ⟨o.val, (Finset.mem_insert.1 o.property).resolve_left e⟩
      have hh := post (parallel (expr_good (g a)) ih) choose
      convert hh using 1
      funext x o
      by_cases e : o.val = a <;> simp [choose, e]
  exact post (aux Finset.univ) (fun o => ⟨o, Finset.mem_univ o⟩)

/-- Linear-size CNF certificate for the entire network. -/
theorem circuit_good (C : Net I O) : Good C.size C.eval := by
  induction C with
  | wires g => exact wiring g
  | @layer I O _ g => exact layer_good g
  | seq a b ha hb => exact join ha (pre hb Sum.inr)
  | par a b ha hb => exact parallel ha hb

end PVNP.CircuitCNF
