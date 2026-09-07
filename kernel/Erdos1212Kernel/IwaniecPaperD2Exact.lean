import Erdos1212Kernel.IwaniecPaperD2Suffix

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Consumed equality, not a proxy definition: the canonical r=2
threshold tree is exactly the paper's d₂ double-prime sum. -/
theorem iwaniecCubicThresholdMass_eq_paperD2 (y : Nat) (z : Real) :
    iwaniecCubicThresholdMass 2 (iwaniecCubicEvenRestriction y)
      iwaniecReciprocalFactorWeight []
      (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) = iwaniecPaperD2At y z := by
  classical
  rw [iwaniecCubicThresholdMass_firstPair_root]
  calc
    _ = ∑ i : Fin (iwaniecDescendingFactors (iwaniecStrictPrimePool z)).length,
        (((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Nat) : Real)⁻¹ *
          ∑ q ∈ iwaniecStrictPrimePool
              ((iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] : Real),
            if y ≤ q ^ 3 * (iwaniecDescendingFactors (iwaniecStrictPrimePool z))[i] then
              iwaniecPaperR (q : Real) / q else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [iwaniecStrictPrimeSuffix z i, iwaniecCubicThresholdMass_singleton_paperR]
      unfold iwaniecReciprocalFactorWeight
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    _ = ∑ p ∈ iwaniecStrictPrimePool z, (p : Real)⁻¹ *
        ∑ q ∈ iwaniecStrictPrimePool (p : Real),
          if y ≤ q ^ 3 * p then iwaniecPaperR (q : Real) / q else 0 :=
      iwaniecSum_descendingFactors_real (iwaniecStrictPrimePool z)
        (fun p : Nat => (p : Real)⁻¹ * ∑ q ∈ iwaniecStrictPrimePool (p : Real),
          if y ≤ q ^ 3 * p then iwaniecPaperR (q : Real) / (q : Real) else 0)
    _ = _ := by
      unfold iwaniecPaperD2At
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (0 : Real) < p := by exact_mod_cast (mem_iwaniecStrictPrimePool.mp hp).1.pos
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hcond : (y : Real) / p ≤ (q : Real) ^ 3 ↔ y ≤ q ^ 3 * p := by
        rw [div_le_iff₀ hp0]
        exact_mod_cast Iff.rfl
      simp only [hcond]
      split <;> simp only [div_eq_mul_inv, mul_inv_rev, mul_zero] <;> ring

theorem iwaniecCubicWeightedMainExpansion_r_two (y : Nat) (z : Real) :
    iwaniecCubicWeightedMainExpansion 2 y (iwaniecStrictPrimePool z) =
      iwaniecPaperR z - iwaniecPaperD2At y z -
        iwaniecCubicTerminalMass 2 (iwaniecCubicEvenRestriction y)
          iwaniecReciprocalFactorWeight [] (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) := by
  rw [iwaniecCubicWeightedMainExpansion_paperR (by decide : 0 < 2),
    iwaniecCubicThresholdMass_eq_paperD2]

end

end Erdos1212Kernel
