import Theorems.PrimeReciprocalsDiverge.A
import Theorems.PrimeReciprocalsDiverge.B

/-!
# A ↔ B for the divergence of the prime reciprocal sum (Euler)

The two partial sums agree pointwise (`Iic N = range (N+1)`); then A is `Tendsto … atTop atTop`
and B is the "exceeds every bound" form. B → A uses monotonicity of the partial sums
(all terms are nonnegative).
-/

namespace TuriMath.PrimeReciprocalsDiverge

open Filter

lemma partialSum_eq (N : ℕ) : A.partialSum N = B.primeRecipSum N := by
  unfold A.partialSum B.primeRecipSum
  congr 2
  ext x; simp

lemma primeRecipSum_mono : Monotone B.primeRecipSum := by
  intro m n hmn
  unfold B.primeRecipSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  · intros; positivity

theorem equiv : A.Statement ↔ B.Statement := by
  unfold A.Statement B.Statement
  constructor
  · intro h M
    have := (h.eventually_gt_atTop M).exists
    obtain ⟨N, hN⟩ := this
    exact ⟨N, by rwa [← partialSum_eq]⟩
  · intro h
    have hf : A.partialSum = B.primeRecipSum := funext partialSum_eq
    rw [hf]
    exact tendsto_atTop_atTop_of_monotone primeRecipSum_mono
      (fun M => by obtain ⟨N, hN⟩ := h M; exact ⟨N, hN.le⟩)

end TuriMath.PrimeReciprocalsDiverge
