import Mathlib

/-!
# Divergence of the sum of prime reciprocals — statement B (Gauss)

Source (issue TuriMath/prime-reciprocals-diverge#1, Wikipedia lead; Wiedijk 100, item 81):
> The sum of the reciprocals of all prime numbers diverges; that is:
> ∑_{p prime} 1/p = 1/2 + 1/3 + 1/5 + 1/7 + 1/11 + 1/13 + 1/17 + ⋯ = ∞

Mapping, one line each:
* "the reciprocals of all prime numbers"   ↦ the terms `(1 : ℝ) / p` for `p` with `Nat.Prime p`
* "the sum … 1/2 + 1/3 + 1/5 + ⋯"          ↦ the partial sum `primeRecipSum N`, over primes `p ≤ N`
                                             (`p ∈ (Finset.range (N + 1)).filter Nat.Prime`)
* "diverges", "= ∞"                         ↦ `∀ M : ℝ, ∃ N : ℕ, M < primeRecipSum N`
                                             (the real partial sums exceed every bound)

Elementary phrasing on purpose: no `Summable`, no `Filter.Tendsto`, just finite sums and
an ε–N style "exceeds every bound". The partial sums only grow with `N` (all terms are
positive), so "exceeds every bound for some N" is the same as "tends to +∞".
-/

namespace TuriMath.PrimeReciprocalsDiverge.B

/-- Sum of `1/p` over the primes `p ≤ N`, as a real number. -/
noncomputable def primeRecipSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- The sum of the reciprocals of the primes diverges: its partial sums exceed every real bound. -/
def Statement : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, M < primeRecipSum N

/-! ## Sanity section and concrete checks -/

/-- The primes up to 10 are exactly 2, 3, 5, 7. -/
example : (Finset.range 11).filter Nat.Prime = {2, 3, 5, 7} := by decide

/-- Primes `≤ 4`: 1/2 + 1/3 = 5/6. (No 1/0, no 1/1, no 1/4 sneak in.) -/
example : primeRecipSum 4 = 5 / 6 := by
  unfold primeRecipSum
  rw [show (Finset.range 5).filter Nat.Prime = {2, 3} by decide]
  norm_num

/-- Primes `≤ 10`: 1/2 + 1/3 + 1/5 + 1/7 = 247/210. -/
example : primeRecipSum 10 = 247 / 210 := by
  unfold primeRecipSum
  rw [show (Finset.range 11).filter Nat.Prime = {2, 3, 5, 7} by decide]
  norm_num

/-- `N = 0` and `N = 1`: no primes yet, the partial sum is 0. -/
example : primeRecipSum 1 = 0 := by
  unfold primeRecipSum
  rw [show (Finset.range 2).filter Nat.Prime = ∅ by decide]
  simp

/-- The statement is not vacuous: the bound `M = 1` is genuinely beaten, by `N = 10`
(247/210 > 1), while `N = 4` (5/6) is not enough. -/
example : ∃ N : ℕ, (1 : ℝ) < primeRecipSum N := by
  refine ⟨10, ?_⟩
  unfold primeRecipSum
  rw [show (Finset.range 11).filter Nat.Prime = {2, 3, 5, 7} by decide]
  norm_num

example : ¬ ((1 : ℝ) < primeRecipSum 4) := by
  unfold primeRecipSum
  rw [show (Finset.range 5).filter Nat.Prime = {2, 3} by decide]
  norm_num

/-- Negative bounds are beaten trivially (partial sums are `≥ 0`), so the content is in large `M`. -/
example : ∃ N : ℕ, (-1 : ℝ) < primeRecipSum N := by
  refine ⟨0, ?_⟩
  unfold primeRecipSum
  rw [show (Finset.range 1).filter Nat.Prime = ∅ by decide]
  norm_num

end TuriMath.PrimeReciprocalsDiverge.B
