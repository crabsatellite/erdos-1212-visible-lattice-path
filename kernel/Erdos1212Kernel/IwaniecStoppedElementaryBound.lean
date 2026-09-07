import Erdos1212Kernel.IwaniecLemma15
import Erdos1212Kernel.IwaniecPrimePoolTerminalBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- The actual stopped layer is bounded by the elementary symmetric
mass on the same list. The suffix Euler factor is proved at most one. -/
theorem iwaniecCubicRealThresholdLayer_le_elementary (offset : Nat) (level : Real)
    (factors : List Nat) (k : Nat)
    (hfactor : ∀ p ∈ factors, |1 - iwaniecReciprocalFactorWeight p| ≤ 1) :
    iwaniecCubicRealThresholdLayer offset level factors k ≤
      iwaniecElementaryMass iwaniecReciprocalFactorWeight k factors := by
  induction factors generalizing offset level k with
  | nil => cases k <;> simp [iwaniecElementaryMass]
  | cons p tail ih =>
      have ht : ∀ q ∈ tail, |1 - iwaniecReciprocalFactorWeight q| ≤ 1 := fun q hq => hfactor q (by simp [hq])
      cases k with
      | zero => simp [iwaniecElementaryMass]
      | succ k =>
          have hs := ih offset level (k + 1) ht
          have hchild := ih (offset + 1) (level / p) k ht
          have hp0 : 0 ≤ (p : Real)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
          have hw : |iwaniecReciprocalFactorWeight p| = (p : Real)⁻¹ := by
            unfold iwaniecReciprocalFactorWeight
            exact abs_of_nonneg hp0
          rw [iwaniecCubicRealThresholdLayer, iwaniecElementaryMass, hw]
          by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
          · rw [if_pos hc]
            exact add_le_add hs (mul_le_mul_of_nonneg_left hchild hp0)
          · rw [if_neg hc]
            by_cases hk : k = 0
            · subst k
              simp only [if_true, iwaniecElementaryMass]
              have he := abs_iwaniecListEulerProduct_le_one iwaniecReciprocalFactorWeight tail ht
              exact add_le_add hs (mul_le_mul_of_nonneg_left he hp0)
            · rw [if_neg hk]
              exact add_le_add hs (mul_nonneg hp0 (iwaniecElementaryMass_nonneg _ _ _))

theorem factorial_mul_iwaniecPaperStoppedLayer_le (offset : Nat) (level z : Real) (k : Nat) :
    (k.factorial : Real) * iwaniecPaperStoppedLayer offset level z k ≤
      (∑ p ∈ iwaniecStrictPrimePool z, (p : Real)⁻¹) ^ k := by
  have hf : ∀ p ∈ iwaniecDescendingFactors (iwaniecStrictPrimePool z),
      |1 - iwaniecReciprocalFactorWeight p| ≤ 1 := by
    intro p hp
    have hpPool : p ∈ iwaniecStrictPrimePool z := by simpa [iwaniecDescendingFactors] using hp
    exact reciprocalPrime_eulerFactor_abs_le_one (mem_iwaniecStrictPrimePool.mp hpPool).1
  have hh := mul_le_mul_of_nonneg_left
    (iwaniecCubicRealThresholdLayer_le_elementary offset level _ k hf)
    (Nat.cast_nonneg k.factorial : (0 : Real) ≤ k.factorial)
  have hE := factorial_mul_iwaniecElementaryMass_le_sum_pow iwaniecReciprocalFactorWeight k
    (iwaniecDescendingFactors (iwaniecStrictPrimePool z))
  rw [sum_abs_reciprocal_descendingFactors] at hE
  exact hh.trans hE

theorem iwaniecPaperStoppedLayer_le_reciprocal_factorial (offset : Nat) (level z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer offset level z k ≤
      (∑ p ∈ iwaniecStrictPrimePool z, (p : Real)⁻¹) ^ k / (k.factorial : Real) := by
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos k : (0 : Real) < k.factorial)).mpr
  simpa only [mul_comm] using factorial_mul_iwaniecPaperStoppedLayer_le offset level z k

end

end Erdos1212Kernel
