import PVNP.PartII

/-! R12 (DOI 10.5281/zenodo.17732642).
A retraction of a commuting discrete state encoding preserves finite
trajectories. Uniform polynomial time for arbitrary machines is OPEN. -/
namespace PVNP.R12

theorem decode_simulated_trajectory
    {A B : Type*} (stepA : A → A) (stepB : B → B)
    (encode : A → B) (decode : B → A)
    (hstep : ∀ a, encode (stepA a) = stepB (encode a))
    (hleft : ∀ a, decode (encode a) = a)
    (n : ℕ) (a : A) :
    decode (PVNP.PartII.iterate stepB n (encode a)) =
      PVNP.PartII.iterate stepA n a := by
  have h := PVNP.PartII.encode_iterate stepA stepB encode hstep n a
  rw [← h, hleft]

end PVNP.R12
