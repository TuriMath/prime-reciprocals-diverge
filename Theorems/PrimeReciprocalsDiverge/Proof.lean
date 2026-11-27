import Theorems.PrimeReciprocalsDiverge.A
import Theorems.PrimeReciprocalsDiverge.B
import Theorems.PrimeReciprocalsDiverge.Equiv

/-!
# Proof of A.Statement (Euler)

Prove the B form (partial sums exceed every bound) from Mathlib's
`not_summable_one_div_on_primes`, via `summable_of_sum_range_le` (nonnegative terms with
bounded partial sums are summable); then transfer through the locked equivalence.
-/

namespace TuriMath.PrimeReciprocalsDiverge

theorem main_B : B.Statement := by
  unfold B.Statement
  by_contra hcon
  push Not at hcon
  obtain ⟨M, hM⟩ := hcon
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := M) (fun n => ?_) (fun n => ?_)
  · exact Set.indicator_nonneg (fun _ _ => by positivity) n
  · calc ∑ i ∈ Finset.range n, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i
        = ∑ i ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / i := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : i.Prime <;> simp [Set.indicator, h]
      _ ≤ B.primeRecipSum n := by
          unfold B.primeRecipSum
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
            exact ⟨by omega, hx.2⟩
          · intros; positivity
      _ ≤ M := hM n

theorem main : A.Statement := equiv.mpr main_B

end TuriMath.PrimeReciprocalsDiverge
