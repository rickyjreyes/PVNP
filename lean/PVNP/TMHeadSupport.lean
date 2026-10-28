import PVNP.TMHeadMotion

/-!
# Causal support of the compiled Turing head marker

For the independent TMConfiguration, the unique original marker is at p.
A synchronized radius-one compiled step cannot spontaneously create a
marker at any site outside {p-1, p, p+1}, for ANY transition table.
The lemma is a necessary condition on head propagation and does not
yet assert global uniqueness after valid moving steps.
-/

namespace PVNP.TMHeadSupport

open PVNP.PartII PVNP.TMCellCompiler PVNP.TMGlobal

variable {Q Gamma : Type}

theorem headless_outside_original_neighborhood
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n)
    (hcenter : i ≠ c.headPos)
    (hleft : i.val ≠ c.headPos.val + 1)
    (hright : i.val + 1 ≠ c.headPos.val) :
    ((step (compile T) (encode c)) i).head = none := by
  have hc : (encode c i).head = none := by
    simp [encode, hcenter]
  have hl : (left (compile T) (encode c) i).head = none := by
    by_cases hz : i.val = 0
    · simp [left, hz, compile]
    · have hp : i.val - 1 < n := by omega
      have hne : (⟨i.val - 1, hp⟩ : Fin n) ≠ c.headPos := by
        intro he
        have heq := congrArg Fin.val he
        change i.val - 1 = c.headPos.val at heq
        omega
      simp [left, hz, sample, hp, encode, hne]
  have hr : (right (compile T) (encode c) i).head = none := by
    by_cases hp : i.val + 1 < n
    · have hne : (⟨i.val + 1, hp⟩ : Fin n) ≠ c.headPos := by
        intro he
        have heq := congrArg Fin.val he
        change i.val + 1 = c.headPos.val at heq
        exact hright heq
      simp [right, sample, hp, encode, hne]
    · simp [right, sample, hp, compile]
  have h := no_head_appears_from_empty_stencil T
    (left (compile T) (encode c) i)
    (encode c i)
    (right (compile T) (encode c) i)
    hl hc hr
  simpa [step, compile] using h

/-- Every head marker present after one compiled step is in the
    original head's radius-one causal neighborhood. -/
theorem head_marker_support
    (T : TMTable Q Gamma) {n : Nat}
    (c : TMConfiguration n Q Gamma) (i : Fin n)
    (hmark : ((step (compile T) (encode c)) i).head ≠ none) :
    i = c.headPos ∨
      i.val = c.headPos.val + 1 ∨
      i.val + 1 = c.headPos.val := by
  by_contra h
  push_neg at h
  exact hmark (headless_outside_original_neighborhood
    T c i h.1 h.2.1 h.2.2)

end PVNP.TMHeadSupport
