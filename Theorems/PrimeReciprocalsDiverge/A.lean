import Mathlib

/-!
# Divergence of the sum of prime reciprocals — statement A (Noether)

Source (issue TuriMath/prime-reciprocals-diverge#1, Wikipedia lead; Wiedijk 100, item 81):
> The sum of the reciprocals of all prime numbers diverges; that is:
> ∑_{p prime} 1/p = 1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + ⋯ = ∞
-/

namespace TuriMath.PrimeReciprocalsDiverge.A

open Filter

/-- The partial sum `∑_{p prime, p ≤ N} 1/p`, as a real number. -/
noncomputable def partialSum (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic N), (1 : ℝ) / p

/-- Source ↦ Lean, one line each:
* "all prime numbers" ↦ `p : ℕ` with `Nat.Prime p` (Mathlib's primes: naturals ≥ 2, so 2, 3, 5, …).
* "the reciprocals" `1/p` ↦ `(1 : ℝ) / p`, real division (ℝ, not ℕ, so `1/p` is not truncated to 0).
* "the sum ∑_{p prime}" ↦ the partial sums `partialSum N` over primes `p ≤ N` (`Finset.Iic N`).
* "diverges; … = ∞" ↦ `Tendsto partialSum atTop atTop`: the partial sums grow without bound
  as `N → ∞` (issue note). All terms are positive, so this is exactly divergence to `+∞`.
-/
def Statement : Prop :=
  Tendsto partialSum atTop atTop

/-! ## Sanity section
The statement has no hypotheses, so there is nothing to show jointly satisfiable.
Instead, check that `partialSum` is the sum the source writes out: its first terms are
`1/2 + 1/3` (primes ≤ 4) and `1/2 + 1/3 + 1/5` (primes ≤ 5). -/

example : partialSum 4 = 1 / 2 + 1 / 3 := by
  unfold partialSum
  rw [show Finset.filter Nat.Prime (Finset.Iic 4) = {2, 3} by decide]
  norm_num

example : partialSum 5 = 1 / 2 + 1 / 3 + 1 / 5 := by
  unfold partialSum
  rw [show Finset.filter Nat.Prime (Finset.Iic 5) = {2, 3, 5} by decide]
  norm_num

end TuriMath.PrimeReciprocalsDiverge.A
