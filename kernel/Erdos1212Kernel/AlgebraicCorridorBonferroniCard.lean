import Erdos1212Kernel.AlgebraicCorridorPrimeAsymptotics
import Mathlib.Data.Nat.Choose.Bounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

theorem powerset_filter_card_lt_le
    {α : Type*} [DecidableEq α] (Q : Finset α) (K : ℕ) :
    (Q.powerset.filter fun subset => subset.card < K).card ≤
      K * (Q.card + 1) ^ K := by
  classical
  rw [Finset.card_filter]
  have hregroup := Finset.sum_powerset_apply_card
    (fun k : ℕ => if k < K then 1 else 0) (x := Q)
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at hregroup
  rw [hregroup]
  calc
    (∑ k ∈ Finset.range (Q.card + 1),
        if k < K then Q.card.choose k else 0) ≤
      ∑ k ∈ Finset.range (Q.card + 1),
        if k < K then (Q.card + 1) ^ K else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkK : k < K
      · simp only [hkK, if_true]
        exact (Nat.choose_le_pow Q.card k).trans
          ((Nat.pow_le_pow_left Q.card.le_succ k).trans
            (Nat.pow_le_pow_right (by omega : 0 < Q.card + 1) hkK.le))
      · simp [hkK]
    _ = ((Finset.range (Q.card + 1)).filter fun k => k < K).card *
        (Q.card + 1) ^ K := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ K * (Q.card + 1) ^ K := by
      apply Nat.mul_le_mul_right
      have hsub : ((Finset.range (Q.card + 1)).filter fun k => k < K) ⊆
          Finset.range K := by
        intro k hk
        rw [Finset.mem_filter] at hk
        exact Finset.mem_range.mpr hk.2
      simpa using Finset.card_le_card hsub

theorem rosserTruncatedSubsets_card_le (Q : Finset ℕ) (r : ℕ) :
    (rosserTruncatedSubsets Q r).card ≤
      (2 * r) * (Q.card + 1) ^ (2 * r) := by
  exact powerset_filter_card_lt_le Q (2 * r)

theorem corridorEvenTruncatedSubsets_card_le (Q : Finset ℕ) (r : ℕ) :
    (corridorEvenTruncatedSubsets Q r).card ≤
      (2 * r + 1) * (Q.card + 1) ^ (2 * r + 1) := by
  exact powerset_filter_card_lt_le Q (2 * r + 1)

end

end Erdos1212Kernel
