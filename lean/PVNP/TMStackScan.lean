import PVNP.TMScan

/-!
# Phase VI: charged delimiter scan on an ordinary single-tape TM

A concrete finite-control TM traverses a marked finite tape segment,
recognizes the blank immediately after it, and returns to the marker.
The tape is unchanged and the total is exactly 2*n+3 TM transitions.

This is one charged subroutine for D-1. It does not yet implement stack
operations, multi-dimensional cell addressing, or the full WCCD compiler.
-/

namespace PVNP.Discrete.TMStackScan

/-- Explicit delimiter, payload symbols, and blank. -/
inductive TapeSym (α : Type) where
  | marker
  | datum (a : α)
  | blank
  deriving DecidableEq, Fintype

/-- Finite control for a forward and backward sweep. -/
inductive Phase where
  | right
  | left
  | halt
  deriving DecidableEq, Fintype

def delta {α : Type} : Phase → TapeSym α → Option (Phase × TapeSym α × Dir)
  | .right, .blank => some (.left, .blank, .L)
  | .right, z => some (.right, z, .R)
  | .left, .marker => some (.halt, .marker, .S)
  | .left, z => some (.left, z, .L)
  | .halt, _ => none

/-- This is an ordinary single-tape TM, not an abstract array program. -/
def machine (α : Type) [Fintype α] [DecidableEq α] : TM where
  Λ := Phase
  Γ := TapeSym α
  blank := .blank
  inp _ := .marker
  start := .right
  δ := delta
  acc q := decide (q = .halt)
  rej _ := false

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Exact step bound for traversing n payload cells and returning to the
delimiter. The assumptions describe the represented tape segment. -/
theorem scan_return (T : ℤ → TapeSym α) (n : ℕ)
    (hmark : T 0 = .marker)
    (hbody : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∃ a : α, T (i : ℤ) = .datum a)
    (hend : T ((n + 1 : ℕ) : ℤ) = .blank) :
    (machine α).run ⟨.right, T, 0⟩ (2 * n + 3) = ⟨.halt, T, 0⟩ := by
  let M := machine α
  have hright : ∀ i : ℕ, i < n + 1 →
      M.δ .right (T ((0 : ℤ) + i * Dir.R.shift)) =
        some (.right, T ((0 : ℤ) + i * Dir.R.shift), .R) := by
    intro i hi
    by_cases hzero : i = 0
    · subst i
      simp [M, machine, delta, hmark, Dir.shift]
    · obtain ⟨a, ha⟩ := hbody i (by omega) (by omega)
      simpa [M, machine, delta, ha, Dir.shift]
  have hR : M.run ⟨.right, T, 0⟩ (n + 1) =
      ⟨.right, T, ((n + 1 : ℕ) : ℤ)⟩ := by
    simpa [Dir.shift] using M.scan1 .right .R T 0 (n + 1) hright
  have hturn : M.δ .right (T ((n + 1 : ℕ) : ℤ)) =
      some (.left, T ((n + 1 : ℕ) : ℤ), .L) := by
    simp [M, machine, delta, hend]
  have hB : M.run ⟨.right, T, ((n + 1 : ℕ) : ℤ)⟩ 1 =
      ⟨.left, T, (n : ℤ)⟩ := by
    simpa [Dir.shift, Nat.cast_add] using
      (M.run_step' (q := .right) (T := T) (p := ((n + 1 : ℕ) : ℤ))
        (q' := .left) (d := .L) hturn)
  have hleft : ∀ i : ℕ, i < n →
      M.δ .left (T ((n : ℤ) + i * Dir.L.shift)) =
        some (.left, T ((n : ℤ) + i * Dir.L.shift), .L) := by
    intro i hi
    have hk1 : 1 ≤ n - i := by omega
    have hk2 : n - i ≤ n := by omega
    obtain ⟨a, ha⟩ := hbody (n - i) hk1 hk2
    have heq : (n : ℤ) + (i : ℤ) * Dir.L.shift = ((n - i : ℕ) : ℤ) := by
      simp only [Dir.shift]
      omega
    rw [heq]
    simp [M, machine, delta, ha]
  have hL : M.run ⟨.left, T, (n : ℤ)⟩ n = ⟨.left, T, 0⟩ := by
    convert M.scan1 .left .L T (n : ℤ) n hleft using 1
    · simp [Dir.shift]
  have hstop : M.δ .left (T 0) = some (.halt, T 0, .S) := by
    simp [M, machine, delta, hmark]
  have hD : M.run ⟨.left, T, 0⟩ 1 = ⟨.halt, T, 0⟩ := by
    simpa [Dir.shift] using
      (M.run_step' (q := .left) (T := T) (p := 0)
        (q' := .halt) (d := .S) hstop)
  change M.run ⟨.right, T, 0⟩ (2 * n + 3) = ⟨.halt, T, 0⟩
  calc
    M.run ⟨.right, T, 0⟩ (2 * n + 3) =
        M.run ⟨.right, T, 0⟩ ((n + 1) + (1 + (n + 1))) := by
          congr 1
          omega
    _ = M.run (M.run ⟨.right, T, 0⟩ (n + 1)) (1 + (n + 1)) := by
          rw [M.run_add]
    _ = M.run ⟨.right, T, ((n + 1 : ℕ) : ℤ)⟩ (1 + (n + 1)) := by
          rw [hR]
    _ = M.run (M.run ⟨.right, T, ((n + 1 : ℕ) : ℤ)⟩ 1) (n + 1) := by
          rw [M.run_add]
    _ = M.run ⟨.left, T, (n : ℤ)⟩ (n + 1) := by rw [hB]
    _ = M.run (M.run ⟨.left, T, (n : ℤ)⟩ n) 1 := by rw [M.run_add]
    _ = M.run ⟨.left, T, 0⟩ 1 := by rw [hL]
    _ = ⟨.halt, T, 0⟩ := hD

end PVNP.Discrete.TMStackScan
