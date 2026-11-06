import PVNP.CrossingSATSets
import PVNP.BooleanNetwork

/-! A quadratic decision-time lower bound for dense SAT on a single tape.
A row address z has n Boolean bits and selects one of 2^n rows. A selected
column j is marked by a separate Boolean variable. Each row clause stores n
independent incidence bits. The fixed middle block enforces at most one column.
The two outer blocks are jointly satisfiable exactly for a matrix difference. -/
namespace PVNP.CrossingSATMatrix

open PVNP.Discrete PVNP.Discrete.SATV PVNP.PartI PVNP.CrossingSAT PVNP.CrossingSATSets

abbrev Entry (n : ℕ) := Pt n × Fin n
abbrev Matrix (n : ℕ) := Finset (Entry n)

private def rowClause {n : ℕ} (p : Pt n) (marks : Fin n → Bool) : Clause :=
  exC p ++ ((List.finRange n).filter marks).map (fun j => (n+j.val,true))

private theorem rowClause_sem (w : ℕ → Bool) (p : Pt n) (marks : Fin n → Bool) :
    evalClause w (rowClause p marks) = true ↔ (fun i : Fin n => w i) ≠ p ∨
      ∃ j, marks j = true ∧ w (n+j.val) = true := by
  rw [rowClause, evalClause_eq_any, List.any_append, Bool.or_eq_true, ← evalClause_eq_any,
    evalClause_exC, List.any_eq_true]
  simp [List.mem_finRange,evalLiteral,literalTrue]

private noncomputable def block {n : ℕ} (S : Matrix n) (b : Bool) : Formula :=
  (pts n).map fun p => rowClause p (fun j => decide ((p,j) ∈ S) == b)

private def exclusive {n : ℕ} (ij : Fin n × Fin n) : Clause :=
  if ij.1 = ij.2 then tautC 0 else [(n+ij.1.val,false),(n+ij.2.val,false)]

private theorem exclusive_sem (w : ℕ → Bool) (ij : Fin n × Fin n) :
    evalClause w (exclusive ij) = true ↔ (w (n+ij.1.val) = true → w (n+ij.2.val) = true → ij.1 = ij.2) := by
  by_cases h : ij.1 = ij.2
  · simp [exclusive,h,evalClause_tautC]
  · cases h₁ : w (n+ij.1.val) <;> cases h₂ : w (n+ij.2.val) <;>
      simp [exclusive,h,h₁,h₂,evalClause,evalLiteral,literalTrue]

private noncomputable def mid (n : ℕ) : Formula :=
  (BooleanNetwork.Expr.elems (Fin n × Fin n)).map exclusive ++ pad (2^n)

private noncomputable def formula {n : ℕ} (S U : Matrix n) : Formula :=
  block S true ++ mid n ++ block U false

noncomputable def instanceWord {n : ℕ} (S U : Matrix n) : List Bool := encDense (2*n) (formula S U)

private theorem formula_sem (S U : Matrix n) :
    satisfiable (formula S U) ↔ ∃ e ∈ S, e ∉ U := by
  constructor
  · rintro ⟨w, hw⟩
    have all := (evalFormula_iff ..).1 hw
    let p : Pt n := fun i => w i
    have left := all _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨p,mem_pts p,rfl⟩)))
    have right := all _ (List.mem_append_right _ (List.mem_map.mpr ⟨p,mem_pts p,rfl⟩))
    obtain ⟨i,hi,wi⟩ := ((rowClause_sem _ _ _).1 left).resolve_left (fun h => h rfl)
    obtain ⟨j,hj,wj⟩ := ((rowClause_sem _ _ _).1 right).resolve_left (fun h => h rfl)
    have uniq := all _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_map.mpr ⟨(i,j),BooleanNetwork.Expr.mem_elems _,rfl⟩))))
    have hij : i = j := (exclusive_sem _ _).1 uniq wi wj
    subst j
    exact ⟨(p,i),by simpa using hi,by simpa using hj⟩
  · rintro ⟨⟨p,j⟩,hs,hu⟩
    let w (v : ℕ) := if h : v < n then p ⟨v,h⟩ else decide (v=n+j.val)
    have addr : (fun i : Fin n => w i.val) = p := by funext i; simp [w,i.isLt]
    have col (i : Fin n) : w (n+i.val) = decide (i=j) := by simp [w,Fin.ext_iff]
    refine ⟨w,(evalFormula_iff ..).2 ?_⟩
    intro c hc
    simp only [formula,block,mid,pad,List.mem_append,List.mem_map,List.mem_replicate] at hc
    rcases hc with (⟨v,_,rfl⟩ | (⟨ij,_,rfl⟩ | ⟨_,rfl⟩)) | ⟨v,_,rfl⟩
    · rw [rowClause_sem,addr]
      by_cases e : p=v
      · subst v; exact Or.inr ⟨j,by simp [hs],by simp [col]⟩
      · exact Or.inl e
    · rw [exclusive_sem]
      simp only [col,decide_eq_true_eq]
      intro h h'; exact h.trans h'.symm
    · exact evalClause_tautC ..
    · rw [rowClause_sem,addr]
      by_cases e : p=v
      · subst v; exact Or.inr ⟨j,by simp [hu],by simp [col]⟩
      · exact Or.inl e

private theorem vars (hn : 1 ≤ n) (S U : Matrix n) :
    ∀ c ∈ formula S U, ∀ l ∈ c, l.1 < 2*n := by
  have rt (p : Pt n) (f : Fin n → Bool) (l : Literal) (hl : l ∈ rowClause p f) : l.1 < 2*n := by
    rcases List.mem_append.mp hl with h|h
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h; simp only; omega
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h; simp only; omega
  have tt (l : Literal) (hl : l ∈ tautC 0) : l.1 < 2*n := by
    simp [tautC] at hl; rcases hl with rfl|rfl <;> simp <;> omega
  intro c hc l hl
  simp only [formula,block,mid,pad,List.mem_append,List.mem_map,List.mem_replicate] at hc
  rcases hc with (⟨v,_,rfl⟩ | (⟨ij,_,rfl⟩ | ⟨_,rfl⟩)) | ⟨v,_,rfl⟩
  · exact rt _ _ _ hl
  · unfold exclusive at hl
    split_ifs at hl
    · exact tt _ hl
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl|rfl <;> simp only <;> omega
  · exact tt _ hl
  · exact rt _ _ _ hl

theorem instanceWord_mem (hn : 1 ≤ n) (S U : Matrix n) :
    instanceWord S U ∈ SAT_dense ↔ ∃ e ∈ S, e ∉ U :=
  (encDense_mem_SAT_iff _ (by omega) _ (vars hn S U)).trans (formula_sem S U)

private theorem diagonal (hn : 1 ≤ n) (S : Matrix n) : instanceWord S S ∉ SAT_dense := by
  rw [instanceWord_mem hn]
  rintro ⟨e,he,he'⟩; exact he' he

private noncomputable def side {n : ℕ} (S : Matrix n) (b : Bool) := encDense (2*n) (block S b)
private noncomputable def middle (n : ℕ) := encDense (2*n) (mid n)

-- A = bit length of either outer block. G counts the middle bits.
def A (n : ℕ) := 6*n*2^n
def G (n : ℕ) := 6*n*(n*n+2^n)
def N (n : ℕ) := 2*A n+G n

private theorem side_length (S : Matrix n) (b : Bool) : (side S b).length = A n := by
  simp [side,length_encDense,block,length_pts,A]; ring
private theorem middle_length (n : ℕ) : (middle n).length = G n := by
  simp [middle,length_encDense,mid,pad,G]; ring
private theorem layout (S U : Matrix n) : instanceWord S U = side S true ++ middle n ++ side U false := by
  simp only [instanceWord,formula,side,middle,encDense_append]
theorem word_length (S U : Matrix n) : (instanceWord S U).length = N n := by
  simp [layout,side_length,middle_length,N]; ring
private theorem split_word (S U : Matrix n) (j : ℕ) :
    instanceWord S U = (side S true ++ (middle n).take j) ++ ((middle n).drop j ++ side U false) := by
  rw [layout,List.append_assoc,List.append_assoc,← List.append_assoc (List.take _ _),List.take_append_drop]

private def cut (n j : ℕ) := ((A n+j : ℕ) : ℤ)

private theorem mixed {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) (hn : 1 ≤ n)
    (hj : j ≤ G n) (S U : Matrix n)
    (ht : dtrace M (cut n j) (instanceWord S S) = dtrace M (cut n j) (instanceWord U U)) : S ⊆ U := by
  have hx := decides_false hM (diagonal hn S)
  have hy := decides_false hM (diagonal hn U)
  let u := side S true ++ (middle n).take j
  let v := (middle n).drop j ++ side S false
  let u' := side U true ++ (middle n).take j
  let v' := (middle n).drop j ++ side U false
  have sx : instanceWord S S = u++v := split_word ..
  have sy : instanceWord U U = u'++v' := split_word ..
  have sz : instanceWord S U = u++v' := split_word ..
  have len (V : Matrix n) : (side V true ++ (middle n).take j).length = A n+j := by
    simp [side_length,middle_length,min_eq_left hj]
  have h0 : 0 < u.length := by rw [show u.length = _ from len S]; unfold A; positivity
  have same : u'.length = u.length := (len U).trans (len S).symm
  have hcut : cut n j = (u.length : ℤ) := by rw [cut,show u.length = _ from len S]
  rw [sx] at hx
  rw [sy] at hy
  unfold dtrace at ht
  rw [sx,sy,hcut] at ht
  have h := splice_nmem M hM u v u' v' h0 same hx.2.1 hx.2.2 hy.2.1 hy.2.2 ht
  rw [← sz, instanceWord_mem hn] at h
  intro e he; by_contra hU; exact h ⟨e,he,hU⟩

private theorem matrix_card (n : ℕ) : Fintype.card (Matrix n) = 2^(n*2^n) := by
  change Fintype.card (Finset ((Fin n → Bool) × Fin n)) = _
  rw [Fintype.card_finset,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    Nat.mul_comm (2^n) n]

private theorem count {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n ℓ u : ℕ}
    (hn : 1 ≤ n) (hl : 2*(Fintype.card (M.Λ × Dir)+1)^ℓ ≤ 2^(n*2^n))
    (ht : ∀ S : Matrix n, ftime M (instanceWord S S) ≤ u) : (G n+1)*ℓ ≤ 2*u := by
  exact fooling_time_bound (M := M) (fun S : Matrix n => instanceWord S S) (cut n)
    (by intro a b h; unfold cut at h; omega) ht
    (fun _ hj S U h => Finset.Subset.antisymm (mixed hM hn (by omega) S U h)
      (mixed hM hn (by omega) U S h.symm)) (by rwa [matrix_card])

theorem matrix_time {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n ℓ : ℕ}
    (hn : 1 ≤ n) (hl : 2*(Fintype.card (M.Λ × Dir)+1)^ℓ ≤ 2^(n*2^n)) :
    (G n+1)*ℓ ≤ 2*T (N n) :=
  count hM hn hl fun S => by have h := (decides_false hM (diagonal hn S)).1; rwa [word_length] at h

/-- Bits sufficient for a padded crossing symbol, for this fixed machine. -/
def symbolBits (M : TM) := Nat.log 2 (Fintype.card (M.Λ × Dir)+1)+1

private theorem sq_le_exp {n : ℕ} (hn : 4 ≤ n) : n*n ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

/-- A concrete rejected instance with an actual quadratic first-answer time.
The inequality holds at every parameter n from the stated threshold on. -/
theorem quadratic_diagonal {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) {n : ℕ}
    (hn : 4 ≤ n) (hm : symbolBits M < n*2^n) :
    ∃ S : Matrix n, (N n)^2 ≤ 384 * symbolBits M * ftime M (instanceWord S S) := by
  classical
  let b := n*2^n
  let L := symbolBits M
  let ℓ := (b-1)/L
  have hL : 0 < L := Nat.zero_lt_succ _
  have hb : L < b := hm
  have hd : L*ℓ ≤ b-1 := Nat.mul_div_le _ _
  have hrem := Nat.mod_add_div (b-1) L
  have hr := Nat.mod_lt (b-1) hL
  have hpos : 1 ≤ ℓ := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have hmin : b ≤ 2*(L*ℓ) := by
    change (b-1)%L + L*ℓ = b-1 at hrem
    have hlower : L ≤ L*ℓ := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left L hpos
    omega
  have hC : Fintype.card (M.Λ × Dir)+1 < 2^L := Nat.lt_pow_succ_log_self (by norm_num) _
  have hl : 2*(Fintype.card (M.Λ × Dir)+1)^ℓ ≤ 2^b := by
    calc _ ≤ 2*(2^L)^ℓ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hC.le _)
         _ = 2^(L*ℓ+1) := by rw [pow_succ', pow_mul]
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨S,_,hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Matrix n))
    (fun U => ftime M (instanceWord U U)) ⟨∅,Finset.mem_univ _⟩
  have htime := count hM (by omega : 1 ≤ n) hl (fun U => hs U (Finset.mem_univ _))
  refine ⟨S,?_⟩
  have hsmall := sq_le_exp hn
  have hN : N n ≤ 24*b := by
    unfold N A G b
    nlinarith [Nat.mul_le_mul_left n hsmall]
  have hG : 6*b ≤ G n+1 := by unfold G b; nlinarith
  have hprice : 3*b*ℓ ≤ ftime M (instanceWord S S) := by nlinarith [Nat.mul_le_mul_right ℓ hG]
  calc (N n)^2 ≤ (24*b)^2 := Nat.pow_le_pow_left hN 2
       _ ≤ 384*L*ftime M (instanceWord S S) := by
         nlinarith [Nat.mul_le_mul_left b hmin,Nat.mul_le_mul_left L hprice]

/-- The family occurs at unbounded encoded input lengths for every correct decider. -/
theorem quadratic_arbitrarily_large {M : TM} {T : ℕ → ℕ} (hM : M.Decides SAT_dense T) (N₀ : ℕ) :
    ∃ x : List Bool, N₀ ≤ x.length ∧ x ∉ SAT_dense ∧ x.length^2 ≤ 384*symbolBits M*ftime M x := by
  let n := N₀ + symbolBits M + 4
  have hn : 4 ≤ n := by dsimp [n]; omega
  have he : n ≤ n*2^n := by simpa using Nat.mul_le_mul_left n (Nat.one_le_two_pow (n := n))
  obtain ⟨S,hS⟩ := quadratic_diagonal hM hn (by dsimp [n] at he ⊢; omega)
  refine ⟨instanceWord S S, ?_,diagonal (by omega) S, ?_⟩
  · rw [word_length]; unfold N A G; dsimp only [n] at he ⊢; nlinarith
  · rwa [word_length]

/-! The same input family has a linear-size promise circuit on its actual
dense bit strings. Array subscripts below are fixed by n and the entry. -/

private theorem block_port {α : Type} {a : α} {xs : List α} (ha : a ∈ xs) (width : ℕ) :
    ∃ k < xs.length, ∀ f : α → List Bool, (∀ u, (f u).length = width) → ∀ i < width,
      (xs.flatMap f).getD (k*width+i) false = (f a).getD i false := by
  obtain ⟨u,v,rfl⟩ := List.append_of_mem ha
  refine ⟨u.length,by simp,?_⟩
  intro f hf i hi
  have hu : (u.flatMap f).length = u.length*width := by simp [hf]
  rw [List.flatMap_append,List.flatMap_cons,List.getD_append_right _ _ _ _ (by rw [hu]; omega),
    hu,Nat.add_sub_cancel_left,List.getD_append _ _ _ _ (by rw [hf]; exact hi)]

private theorem row_mark (p : Pt n) (j : Fin n) (mark : Fin n → Bool) :
    (n+j.val,true) ∈ rowClause p mark ↔ mark j = true := by
  have h : (n+j.val,true) ∉ exC p := by
    intro h
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
    have he := congrArg Prod.fst hi
    change i.val = n+j.val at he
    omega
  simp only [rowClause,List.mem_append,h,false_or,List.mem_map,List.mem_filter,List.mem_finRange,
    true_and,Prod.mk.injEq,Nat.add_left_cancel_iff,and_true]
  exact ⟨fun ⟨i,hi,e⟩ => (Fin.ext e) ▸ hi,fun hj => ⟨j,hj,rfl⟩⟩

private theorem side_port (e : Entry n) : ∃ k < A n, ∀ (S : Matrix n) (b : Bool),
    (side S b).getD k false = (decide (e ∈ S) == b) := by
  obtain ⟨a,ha,readRow⟩ := block_port (mem_pts e.1) (3*(2*n))
  obtain ⟨c,hc,readCol⟩ := block_port (List.mem_range.mpr (by omega : n+e.2.val < 2*n)) 3
  have hc' : c < 2*n := by simpa using hc
  rw [length_pts] at ha
  have inside : c*3+0 < 3*(2*n) := by omega
  refine ⟨a*(3*(2*n))+(c*3+0),?_,?_⟩
  · have := Nat.mul_le_mul_right (3*(2*n)) (show a+1 ≤ 2^n by omega)
    unfold A; nlinarith
  · intro S b
    let R (p : Pt n) := rowClause p (fun j => decide ((p,j) ∈ S) == b)
    change (encDense (2*n) ((pts n).map R)).getD _ _ = _
    simp only [encDense,List.flatMap_map]
    rw [readRow _ (fun _ => length_encClause ..) _ inside]
    rw [encClause,readCol _ (fun _ => rfl) 0 (by decide)]
    change decide ((n+e.2.val,true) ∈ rowClause e.1 _) = _
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq,row_mark]

/-- On valid packed matrix instances, a single-layer Boolean expression reads
the two fixed literal-presence coordinates for each table entry. -/
theorem matrix_promise_circuit {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : BooleanNetwork.Net (Fin (N n)) Unit, C.size ≤ 1+4*(n*2^n) ∧
      ∀ (S U : Matrix n) (x : Fin (N n) → Bool), List.ofFn x = instanceWord S U →
        (C.eval x () = true ↔ List.ofFn x ∈ SAT_dense) := by
  classical
  choose port bound read using (side_port (n := n))
  let left (e : Entry n) : Fin (N n) := ⟨port e, by unfold N; have := bound e; omega⟩
  let right (e : Entry n) : Fin (N n) := ⟨A n+G n+port e, by unfold N; have := bound e; omega⟩
  let term (e : Entry n) : BooleanNetwork.Expr (Fin (N n)) := .conj (.var (left e)) (.var (right e))
  let expr := BooleanNetwork.Expr.any (BooleanNetwork.Expr.elems (Entry n)) term
  refine ⟨.layer (fun _ => expr), ?_, ?_⟩
  · have he := BooleanNetwork.Expr.size_any (BooleanNetwork.Expr.elems (Entry n)) term (k := 3)
      (fun _ => le_rfl)
    have cc : Fintype.card (Entry n) = n*2^n := by
      change Fintype.card ((Fin n → Bool) × Fin n) = _
      rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.mul_comm]
    rw [BooleanNetwork.Expr.length_elems,cc] at he
    simpa [BooleanNetwork.Net.size,expr] using he
  · intro S U x h
    have get (i : Fin (N n)) : x i = (instanceWord S U).getD i.val false := by
      rw [← h]; simp [i.isLt]
    have hl (e : Entry n) : x (left e) = decide (e ∈ S) := by
      rw [get,layout]
      change ((side S true ++ middle n) ++ side U false).getD (port e) false = _
      rw [List.getD_append _ _ _ _ (by simp [side_length,middle_length]; have := bound e; omega),
        List.getD_append _ _ _ _ (by rw [side_length]; exact bound e),read]
      simp
    have hr (e : Entry n) : x (right e) = !decide (e ∈ U) := by
      rw [get,layout]
      change ((side S true ++ middle n) ++ side U false).getD (A n+G n+port e) false = _
      rw [List.getD_append_right _ _ _ _ (by simp [side_length,middle_length]),
        List.length_append,side_length,middle_length,Nat.add_sub_cancel_left,read]
      simp
    change expr.eval x = true ↔ _
    rw [h,instanceWord_mem hn]
    simp only [expr, BooleanNetwork.Expr.eval_any, BooleanNetwork.Expr.mem_elems, true_and, term,
      BooleanNetwork.Expr.eval, Bool.and_eq_true,hl,hr,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]

end PVNP.CrossingSATMatrix
