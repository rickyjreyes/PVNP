import PVNP.CircuitCNF
import PVNP.VerifierCircuits

/-! Exact non-uniform signed projections to the repository dense CNF format.
The only input-dependent clauses pin the first n variables to the input.
Every dense output bit is a constant, an input bit, or its complement. -/
namespace PVNP.SATProjection

open PVNP.BooleanNetwork PVNP.CircuitCNF PVNP.VerifierCircuits PVNP.Discrete
open PVNP.PartI PVNP.CrossingSAT PVNP.Discrete.SATV

private def pin (k : ℕ) (i : Fin n) : List (Bit (Fin n)) :=
  (List.range k).flatMap fun j => [if j = i.val then Bit.input i true else Bit.const false,
    if j = i.val then Bit.input i false else Bit.const false, Bit.const (decide (j+1=k))]

private theorem pin_sem (k : ℕ) (i : Fin n) (x : Fin n → Bool) :
    (pin k i).map (Bit.eval x) = encClause k [(i.val,x i)] := by
  rw [pin, List.map_flatMap, encClause]
  apply List.flatMap_congr
  intro j _
  by_cases h : j = i.val <;> cases e : x i <;> simp [slotBits, Bit.eval, h, e]

private def pins (x : Fin n → Bool) : Formula := List.ofFn (fun i : Fin n => [(i.val,x i)])

private def projection (n k : ℕ) (F : Formula) : List (Bit (Fin n)) :=
  (encDense k F).map Bit.const ++ (List.ofFn (pin k : Fin n → _)).flatten

private theorem projection_sem (k : ℕ) (F : Formula) (x : Fin n → Bool) :
    (projection n k F).map (Bit.eval x) = encDense k (F ++ pins x) := by
  simp [projection, encDense, pins, List.map_flatten, List.flatMap,
    List.map_ofFn, List.map_map, Function.comp_def, Bit.eval, pin_sem]

private theorem pin_holds (a : Assignment) (x : Fin n → Bool) :
    Holds a (pins x) ↔ ∀ i, a i.val = x i := by
  simp [Holds, pins, List.mem_ofFn, evalClause, evalLiteral, literalTrue]

private def inputs (n m : ℕ) : Fin n ⊕ Fin m → ℕ :=
  Sum.elim Fin.val (fun j => n+j.val)

private theorem inputs_valid (i : Fin n ⊕ Fin m) : inputs n m i < n+m := by
  cases i <;> simp [inputs]; omega

private theorem load (x : Fin n → Bool) (w : Fin m → Bool) :
    ∃ a : Assignment, a ∘ inputs n m = Sum.elim x w := by
  let a (j : ℕ) := if h : j < n then x ⟨j,h⟩ else if g : j-n < m then w ⟨j-n,g⟩ else false
  refine ⟨a,funext fun i => ?_⟩
  cases i with
  | inl j => simp [inputs, a, j.isLt]
  | inr j => simp [inputs, a, j.isLt]

/-- Project existential acceptance of a single circuit. The dense width
and number of clauses are bounded separately, including all input pins. -/
theorem project_circuit (C : Net (Fin n ⊕ Fin m) Unit) :
    ∃ R : List (Bit (Fin n)), R.length ≤ 3*(n+m+C.size+1)*(4*C.size+1+n) ∧
      ∀ x : Fin n → Bool, (∃ w, C.eval (Sum.elim x w) () = true) ↔ R.map (Bit.eval x) ∈ SAT_dense := by
  obtain ⟨c⟩ := circuit_good C (n+m) (inputs n m) inputs_valid
  let F := c.clauses ++ [[(c.port (),true)]]
  refine ⟨projection n (c.last+1) F, ?_, ?_⟩
  · have he := congrArg List.length (projection_sem (c.last+1) F (fun _ : Fin n => false))
    rw [List.length_map,length_encDense,List.length_append] at he
    simp only [pins,List.length_ofFn,F,List.length_append,List.length_singleton] at he
    rw [he]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 (by have := c.room; omega))
      (by have := c.count; omega)
  · intro x
    have bounds : Bounded (F ++ pins x) (c.last+1) := by
      intro d hd l hl
      rcases List.mem_append.mp hd with hd|hd
      · rcases List.mem_append.mp hd with hd|hd
        · exact (c.bounds _ hd _ hl).trans_le (Nat.le_succ _)
        · simp only [List.mem_singleton] at hd; subst d
          simp only [List.mem_singleton] at hl; subst l; exact (c.valid ()).trans_le (Nat.le_succ _)
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
        simp only [List.mem_singleton] at hl; subst l
        exact (inputs_valid (m := m) (Sum.inl i)).trans_le (c.grows.trans (Nat.le_succ _))
    rw [projection_sem, encDense_mem_SAT_iff _ (by omega) _ bounds]
    have hf (a : Assignment) : Holds a F ↔ Holds a c.clauses ∧ a (c.port ()) = true := by
      dsimp only [F]
      rw [holds_append]
      simp [Holds, evalClause, evalLiteral, literalTrue]
    constructor
    · rintro ⟨w,hw⟩
      obtain ⟨a,ha⟩ := load x w
      obtain ⟨b,hab,hb⟩ := c.extend a
      have hp : b ∘ inputs n m = Sum.elim x w := by
        rw [← ha]; exact funext fun i => (hab _ (inputs_valid i)).symm
      refine ⟨b, (evalFormula_iff _ _).2 (holds_append.mpr ⟨(hf b).2 ⟨hb,?_⟩,
        (pin_holds b x).2 (fun i => congrFun hp (Sum.inl i))⟩)⟩
      rwa [c.sound _ hb, hp]
    · rintro ⟨b,hb⟩
      obtain ⟨hF,hp⟩ := holds_append.mp ((evalFormula_iff _ _).1 hb)
      obtain ⟨hc,yes⟩ := (hf b).1 hF
      let w (j : Fin m) := b (n+j.val)
      have he : b ∘ inputs n m = Sum.elim x w := by
        funext i
        cases i with
        | inl j => exact (pin_holds b x).1 hp j
        | inr j => rfl
      exact ⟨w, by rwa [c.sound _ hc, he] at yes⟩

/-- Every repository NP language non-uniformly reduces by literal projections
to SAT_dense. This statement makes no claim about a machine generating them. -/
theorem NP_projects_to_SAT {L : Set (List Bool)} (hL : L ∈ NP_TM) : Reduces L SAT_dense := by
  obtain ⟨q,p,h⟩ := verifier_family hL
  refine ⟨3*(Polynomial.X+q+p+1)*(4*p+1+Polynomial.X),fun n => ?_⟩
  obtain ⟨C,hc,he⟩ := h n
  obtain ⟨r,hr,hs⟩ := project_circuit C
  refine ⟨r,hr.trans ?_,fun x => (he x).trans (hs x)⟩
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_X,
    Polynomial.eval_one]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

theorem NP_subset_PPoly_of_SAT (h : SAT_dense ∈ PPoly) : NP_TM ⊆ PPoly :=
  fun _ hL => closed_under_projections (NP_projects_to_SAT hL) h

theorem SAT_circuit_lower_iff : SAT_dense ∉ PPoly ↔ ¬ NP_TM ⊆ PPoly :=
  ⟨fun h sub => h (sub SAT_dense_mem_NP_TM), fun h hs => h (NP_subset_PPoly_of_SAT hs)⟩

theorem SATLowerBound_of_NP_circuit_lower (h : ¬ NP_TM ⊆ PPoly) : SATLowerBound :=
  fun hp => (SAT_circuit_lower_iff.mpr h) (TMBooleanTableau.P_TM_subset_PPoly hp)

end PVNP.SATProjection
