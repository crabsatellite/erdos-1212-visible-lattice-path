import Erdos1212Kernel.VaughanSieveParameters
import Erdos1212Kernel.IwaniecReferenceSupportErrorBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- Any strict real prime pool is exactly the first card(pool) primes.
The equality follows from nested cutoffs and equal cardinality, including
the empty pool; no replacement of a real cutoff by a floor is assumed. -/
theorem iwaniecStrictPrimePool_eq_reference_card (X : Real) :
    iwaniecStrictPrimePool X = iwaniecReferencePrimePool (iwaniecStrictPrimePool X).card := by
  let K := (iwaniecStrictPrimePool X).card
  by_cases h : X ≤ (iwaniecStrictReferenceCutoff K : Real)
  · apply Finset.eq_of_subset_of_card_le
    · rw [← iwaniecStrictPrimePool_referenceCutoff K]
      exact iwaniecStrictPrimePool_mono h
    · rw [iwaniecReferencePrimePool_card]
  · symm
    apply Finset.eq_of_subset_of_card_le
    · rw [← iwaniecStrictPrimePool_referenceCutoff K]
      exact iwaniecStrictPrimePool_mono (le_of_not_ge h)
    · rw [iwaniecReferencePrimePool_card]

theorem iwaniecStrictReferenceCutoff_card_le_add_one {X : Real} (hX : 1 ≤ X) :
    (iwaniecStrictReferenceCutoff (iwaniecStrictPrimePool X).card : Real) ≤ X + 1 := by
  let K := (iwaniecStrictPrimePool X).card
  by_cases hK : K = 0
  · change (iwaniecStrictReferenceCutoff K : Real) ≤ X + 1
    rw [iwaniecStrictReferenceCutoff, if_pos hK]
    norm_num
    linarith only [hX]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hmem : iwaniecReferencePrimeCutoff K ∈ iwaniecReferencePrimePool K := by
      rw [iwaniecReferencePrimePool_eq_vaughanPrimePool hKpos]
      exact Nat.mem_primesLE.mpr ⟨le_rfl, Nat.prime_nth_prime (K - 1)⟩
    have hpool : iwaniecReferencePrimeCutoff K ∈ iwaniecStrictPrimePool X := by
      rw [iwaniecStrictPrimePool_eq_reference_card X]
      exact hmem
    have hlt := (mem_iwaniecStrictPrimePool.mp hpool).2
    change (iwaniecStrictReferenceCutoff K : Real) ≤ X + 1
    rw [iwaniecStrictReferenceCutoff, if_neg hK, Nat.cast_add, Nat.cast_one]
    linarith only [hlt]

theorem iwaniecStrictPrimePool_euler_ratio (X : Real) :
    iwaniecActualPrimeStateEuler (iwaniecStrictPrimePool X) /
      iwaniecReferencePrimePoolEuler (iwaniecStrictPrimePool X).card = 1 := by
  have heq : iwaniecActualPrimeStateEuler (iwaniecStrictPrimePool X) =
      iwaniecReferencePrimePoolEuler (iwaniecStrictPrimePool X).card := by
    rw [iwaniecActualPrimeStateEuler_eq_actualProduct]
    unfold iwaniecReferencePrimePoolEuler iwaniecShiftedSubsetEuler
    rw [← iwaniecStrictPrimePool_eq_reference_card X]
  rw [heq, div_self (iwaniecReferencePrimePoolEuler_pos _).ne']

/-- The current logarithmic-square support error on the literal strict
real pool. The reference Euler ratio is cancelled only after its exact
identity has been proved for this pool. -/
theorem exists_iwaniecStrictPrimePool_interval_error_bound :
    ∃ D : Real, 0 < D ∧ ∀ (r y lower length : Nat) (X : Real), 0 < r →
      iwaniecStrictReferenceCutoff (iwaniecStrictPrimePool X).card ^ 2 ≤ y →
      (length : Real) * iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool X) -
        D * (y : Real) / Real.log (y : Real) ^ 2 ≤
          (primeStateAvoidingIndices (iwaniecStrictPrimePool X) lower length).card := by
  obtain ⟨D, hD, hbound⟩ := exists_iwaniecPrimeState_reference_error_bound
  refine ⟨D, hD, ?_⟩
  intro r y lower length X hr hsq
  have hprime : ∀ p ∈ iwaniecStrictPrimePool X, Nat.Prime p :=
    fun p hp => (mem_iwaniecStrictPrimePool.mp hp).1
  have hh := hbound r y lower length (iwaniecStrictPrimePool X) hr hprime hsq
  rw [iwaniecStrictPrimePool_euler_ratio X, one_mul,
    ← iwaniecStrictPrimePool_eq_reference_card X] at hh
  exact hh

end

end Erdos1212Kernel
