import PVNP.TMBooleanTableau
import PVNP.WitnessSizeUniformity

/-! Non-uniform literal projections, and verifier circuits which allow every
witness length through q(n), including the empty witness. -/
namespace PVNP.VerifierCircuits

open PVNP.BooleanNetwork PVNP.Discrete PVNP.TMBooleanTableau

inductive Bit (I : Type) where
  | const (b : Bool)
  | input (i : I) (positive : Bool)

namespace Bit

def eval (x : I → Bool) : Bit I → Bool
  | .const b => b
  | .input i positive => if positive then x i else !(x i)

def expr : Bit I → Expr I
  | .const b => .lit b
  | .input i true => .var i
  | .input i false => .neg (.var i)

@[simp] theorem expr_eval (b : Bit I) (x : I → Bool) : b.expr.eval x = b.eval x := by
  cases b with
  | const => rfl
  | input i s => cases s <;> rfl

theorem expr_size (b : Bit I) : b.expr.size ≤ 2 := by
  cases b with
  | const => simp [expr, Expr.size]
  | input i s => cases s <;> simp [expr, Expr.size]
end Bit

def plug (R : List (Bit I)) : Net I (Fin R.length) := .layer (fun j => (R.get j).expr)

theorem plug_size (R : List (Bit I)) : (plug R).size ≤ 2*R.length := by
  change ∑ j : Fin R.length, (R.get j).expr.size ≤ _
  calc _ ≤ ∑ _ : Fin R.length, 2 := Finset.sum_le_sum (fun j _ => Bit.expr_size _)
       _ = _ := by simp [Nat.mul_comm]

theorem plug_word (R : List (Bit I)) (x : I → Bool) :
    List.ofFn ((plug R).eval x) = R.map (Bit.eval x) := by
  apply List.ext_getElem <;> simp [plug, Net.eval]

/-- One output bit is a constant, an input wire, or its negation.
The length-dependent port lists have one polynomial output-length bound. -/
def Reduces (L K : Set (List Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, ∃ R : List (Bit (Fin n)), R.length ≤ p.eval n ∧
    ∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ R.map (Bit.eval x) ∈ K

theorem closed_under_projections {L K : Set (List Bool)} (h : Reduces L K) (hK : K ∈ PPoly) :
    L ∈ PPoly := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := hK
  refine ⟨2*p + q.comp p, fun n => ?_⟩
  obtain ⟨r,hr,sem⟩ := hp n
  obtain ⟨c,hc,hcs⟩ := hq r.length
  refine ⟨.seq (plug r) c, ?_, fun x => ?_⟩
  · change (plug r).size + c.size ≤ _
    have := plug_size r
    have := eval_mono_nat q hr
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_comp]
    omega
  · change c.eval ((plug r).eval x) () = true ↔ _
    rw [hcs, plug_word, ← sem]

/-- The output circuits in a finite collection share the same inputs. -/
private theorem collect {O : Type} [Fintype O] (cs : O → Net I Unit) :
    ∃ d : Net I O, d.size ≤ ∑ o, (cs o).size ∧ ∀ x o, d.eval x o = (cs o).eval x () := by
  classical
  have aux (s : Finset O) : ∃ d : Net I {i // i ∈ s}, d.size ≤ ∑ o ∈ s, (cs o).size ∧
      ∀ x i, d.eval x i = (cs i.val).eval x () := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨.layer (fun _ => .lit false), ?_, fun _ i => False.elim (Finset.notMem_empty _ i.property)⟩
      simp [Net.size]
    | @insert a s h ih =>
      obtain ⟨d,hd,he⟩ := ih
      let choose (o : {i // i ∈ insert a s}) : Unit ⊕ {j // j ∈ s} :=
        if e : o.val = a then .inl () else .inr ⟨o.val, (Finset.mem_insert.1 o.property).resolve_left e⟩
      refine ⟨.seq (.par (cs a) d) (.wires choose), ?_, ?_⟩
      · simp [Net.size, Finset.sum_insert h, hd]
      · intro x o
        by_cases e : o.val = a <;> simp [Net.eval, choose, e, he]
  obtain ⟨d,hd,he⟩ := aux Finset.univ
  exact ⟨.seq d (.wires (fun i => ⟨i,Finset.mem_univ i⟩)), by simpa [Net.size] using hd,
    fun x o => he x _⟩

private def payload (n q : ℕ) (k : Fin (q+1)) : List (Bit (Fin n ⊕ Fin q)) :=
  (List.ofFn fun i : Fin n => ([Bit.const true, Bit.input (.inl i) true] : List (Bit _))).flatten ++
    Bit.const false :: List.ofFn fun j : Fin k.val => Bit.input (.inr ⟨j.val, by omega⟩) true

private theorem payload_word (n q : ℕ) (k : Fin (q+1)) (x : Fin n → Bool) (w : Fin q → Bool) :
    (payload n q k).map (Bit.eval (Sum.elim x w)) =
      pair (List.ofFn x) (List.ofFn fun j : Fin k.val => w ⟨j.val, by omega⟩) := by
  simp [payload, pair, List.map_flatten, List.flatMap, List.map_ofFn, Function.comp_def, Bit.eval]

private theorem payload_len (n q : ℕ) (k : Fin (q+1)) : (payload n q k).length = 2*n+1+k.val := by
  have he := congrArg List.length (payload_word n q k (fun _ => false) (fun _ => false))
  simpa [pair_length] using he

private def prefixW (q : ℕ) (k : Fin (q+1)) (w : Fin q → Bool) :=
  List.ofFn fun j : Fin k.val => w ⟨j.val, by omega⟩

private theorem exists_prefix (q : ℕ) (P : List Bool → Prop) :
    (∃ v : List Bool, v.length ≤ q ∧ P v) ↔
      ∃ w : Fin q → Bool, ∃ k : Fin (q+1), P (prefixW q k w) := by
  constructor
  · rintro ⟨v,hv,hp⟩
    let w (j : Fin q) := v.getD j.val false
    refine ⟨w,⟨v.length,by omega⟩,?_⟩
    have eqn : prefixW q ⟨v.length,by omega⟩ w = v := by
      apply List.ext_getElem <;> simp [prefixW,w]
    rwa [eqn]
  · rintro ⟨w,k,h⟩
    exact ⟨_, by simp [prefixW]; omega, h⟩

/-- A single polynomial bounds the joint input/certificate circuits.
Existentially choosing the padded witness realizes the repository NP semantics. -/
theorem verifier_family {L : Set (List Bool)} (hL : L ∈ NP_TM) :
    ∃ q p : Polynomial ℕ, ∀ n, ∃ C : Net (Fin n ⊕ Fin (q.eval n)) Unit,
      C.size ≤ p.eval n ∧ ∀ x : Fin n → Bool, List.ofFn x ∈ L ↔
        ∃ w, C.eval (Sum.elim x w) () = true := by
  classical
  obtain ⟨V,hV,q,h⟩ := hL
  obtain ⟨s,hs⟩ := P_TM_subset_PPoly hV
  let B : Polynomial ℕ := 2*Polynomial.X+1+q
  refine ⟨q,(q+1)*(2*B+s.comp B) + (1+2*(q+1)),fun n => ?_⟩
  let m := q.eval n
  let r := payload n m
  choose c hc he using hs
  let cs (k : Fin (m+1)) : Net (Fin n ⊕ Fin m) Unit := .seq (plug (r k)) (c (r k).length)
  have len (k : Fin (m+1)) : (r k).length ≤ B.eval n := by
    rw [show (r k).length = 2*n+1+k.val from payload_len ..]
    simp [B,m] at *; omega
  have hsize (k : Fin (m+1)) : (cs k).size ≤ 2*B.eval n + s.eval (B.eval n) := by
    change (plug (r k)).size + (c _).size ≤ _
    exact Nat.add_le_add ((plug_size _).trans (Nat.mul_le_mul_left _ (len _)))
      ((hc _).trans (eval_mono_nat _ (len _)))
  obtain ⟨d,hd,hdsem⟩ := collect cs
  let g : Expr (Fin (m+1)) := Expr.any (Expr.elems _) Expr.var
  refine ⟨.seq d (.layer (fun _ => g)),?_,?_⟩
  · have hds := hd.trans (Finset.sum_le_sum fun k _ => hsize k)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hds
    have hgs := Expr.size_any (Expr.elems (Fin (m+1))) Expr.var (k := 1) (fun _ => le_rfl)
    rw [Expr.length_elems,Fintype.card_fin] at hgs
    change d.size + (∑ _ : Unit, g.size) ≤ _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_comp, Polynomial.eval_ofNat]
    change g.size ≤ _ at hgs
    dsimp only [m] at hds hgs
    exact Nat.add_le_add hds hgs
  · intro x
    rw [h, List.length_ofFn, exists_prefix]
    change _ ↔ ∃ w, g.eval (d.eval (Sum.elim x w)) = true
    simp only [g, Expr.eval_any, Expr.mem_elems, true_and, Expr.eval, hdsem]
    apply exists_congr
    intro w
    apply exists_congr
    intro k
    change _ ↔ (c _).eval ((plug (r k)).eval (Sum.elim x w)) () = true
    rw [he, plug_word, payload_word]
    rfl

end PVNP.VerifierCircuits
