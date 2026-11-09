import PVNP.SATVerifier

/-! Bounded serial witness search and its instantaneous data on dense SAT. -/
namespace PVNP.SerialWitness
open PVNP.Discrete PVNP.Discrete.SATV

/-- Depth-first search, extending the current word at the front without
materializing a list of assignments. -/
def search (ok : List Bool → Bool) : ℕ → List Bool → Option (List Bool)
  | 0, p => if ok p then some p else none
  | k+1, p => if ok p then some p else
      match search ok k (false :: p) with
      | some w => some w
      | none => search ok k (true :: p)

theorem sound (ok : List Bool → Bool) (k : ℕ) (p w : List Bool)
    (h : search ok k p = some w) :
    ok w = true ∧ ∃ a : List Bool, a.length ≤ k ∧ w = a ++ p := by
  induction k generalizing p with
  | zero =>
    simp only [search] at h
    split at h
    · cases h; exact ⟨by assumption, [], by simp, rfl⟩
    · contradiction
  | succ k ih =>
    have lift (b) (hh : search ok k (b::p) = some w) :
        ok w = true ∧ ∃ a : List Bool, a.length ≤ k+1 ∧ w = a ++ p := by
      obtain ⟨hw,a,ha,he⟩ := ih (b::p) hh
      exact ⟨hw,a++[b],by simp; omega,by simpa using he⟩
    simp only [search] at h
    split at h
    · cases h; exact ⟨by assumption,[],by simp,rfl⟩
    · split at h
      next he => cases h; exact lift false he
      next => exact lift true h

theorem complete (ok : List Bool → Bool) (k : ℕ) (p a : List Bool)
    (hlen : a.length ≤ k) (h : ok (a++p) = true) : (search ok k p).isSome := by
  induction k generalizing p a with
  | zero => have : a = [] := List.length_eq_zero_iff.mp (by omega)
            subst a; simpa [search] using h
  | succ k ih =>
    rcases List.eq_nil_or_concat' a with rfl | ⟨l,b,rfl⟩
    · simp_all [search]
    · have hl : l.length ≤ k := by simpa using hlen
      have hh : ok (l ++ (b::p)) = true := by simpa using h
      have sub := ih (b::p) l hl hh
      by_cases hp : ok p = true
      · simp [search,hp]
      cases b <;> cases hf : search ok k (false::p) <;> simp_all [search]

theorem dense_iff (x : List Bool) :
    (search (fun w => chkFrom w x 0 false true) x.length []).isSome ↔ x ∈ SAT_dense := by
  let ok := fun w => chkFrom w x 0 false true
  constructor
  · intro h
    obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hok,a,ha,rfl⟩ := sound ok x.length [] w hw
    exact ⟨a,ha,by simpa using hok⟩
  · rintro ⟨a,ha,hh⟩
    exact complete ok x.length [] a ha (by simpa using hh)

/-- Reachable calls in the unpruned tree. Early success visits a subset. -/
inductive Call (n : ℕ) : ℕ → List Bool → Prop
  | root : Call n n []
  | child {k p} : Call n (k+1) p → (b : Bool) → Call n k (b::p)

theorem call_width {n k p} (h : Call n k p) : p.length + k = n := by
  induction h with
  | root => simp
  | child _ _ ih => simp only [List.length_cons]; omega

/-- For any input and any visited node, the original one-tape verifier
receives a linear-size word and gives its first answer in quadratic time. -/
theorem verifier_call_bound (x : List Bool) {k : ℕ} {p : List Bool}
    (h : Call x.length k p) :
    (pair x p).length ≤ 3*x.length+1 ∧
    DecidesAt (satTM.out (pair x p)) (2*(3*x.length+4)^2) (pair x p) V_SAT := by
  have hw := call_width h
  have hl : (pair x p).length ≤ 3*x.length+1 := by rw [pair_length]; omega
  obtain ⟨b,⟨t,ht,hd,hb⟩,hc⟩ := satTM_decides (pair x p)
  refine ⟨hl,b,⟨t,ht.trans ?_,hd,hb⟩,hc⟩
  change 2*((pair x p).length+3)^2 ≤ 2*(3*x.length+4)^2
  gcongr

end PVNP.SerialWitness
