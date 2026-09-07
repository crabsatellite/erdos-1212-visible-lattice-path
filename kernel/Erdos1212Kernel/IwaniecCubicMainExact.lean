import Erdos1212Kernel.IwaniecWeightedDefectExact
import Erdos1212Kernel.IwaniecPaperRRate

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 600000

theorem iwaniecReciprocalFactorWeight_bounds (pool : Finset Nat)
    (hprime : ∀ p ∈ pool, Nat.Prime p) :
    ∀ p ∈ iwaniecDescendingFactors pool, 0 ≤ iwaniecReciprocalFactorWeight p ∧ iwaniecReciprocalFactorWeight p ≤ 1 := by
  intro p hp
  have hpPool : p ∈ pool := by simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hp
  have hp1 : (1 : Real) < p := by exact_mod_cast (hprime p hpPool).one_lt
  unfold iwaniecReciprocalFactorWeight
  exact ⟨inv_nonneg.mpr (Nat.cast_nonneg p), (inv_lt_one_of_one_lt₀ hp1).le⟩

/-- Exact finite main term with both the threshold and the 2r cutoff
masses retained. This is the lower-tree side of the paper's (2.15). -/
theorem iwaniecCubicWeightedMainExpansion_exact {r y : Nat} (hr : 0 < r)
    (pool : Finset Nat) (hprime : ∀ p ∈ pool, Nat.Prime p) :
    iwaniecCubicWeightedMainExpansion r y pool =
      (∏ p ∈ pool, (1 - (p : Real)⁻¹)) -
        iwaniecCubicThresholdMass r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
          (iwaniecDescendingFactors pool) -
        iwaniecCubicTerminalMass r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
          (iwaniecDescendingFactors pool) := by
  unfold iwaniecCubicWeightedMainExpansion
  rw [iwaniecWeightedExpansionSum_eq_tree,
    iwaniecLowerTree_eq_euler_sub_stoppedMass hr _ _ _ (iwaniecReciprocalFactorWeight_bounds pool hprime),
    iwaniecListEulerProduct_descendingFactors, iwaniecWeightedStoppedMass_eq_terminal_add_threshold]
  ring

theorem iwaniecCubicWeightedMainExpansion_paperR {r y : Nat} (hr : 0 < r) (z : Real) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) = iwaniecPaperR z -
      iwaniecCubicThresholdMass r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) -
      iwaniecCubicTerminalMass r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) := by
  exact iwaniecCubicWeightedMainExpansion_exact hr _ (fun p hp => (mem_iwaniecStrictPrimePool.mp hp).1)

/-- Only the finite sieve-depth cutoff vanishes here. This is not the
outer history-terminal charge in the Erdős problem. -/
theorem iwaniecCubicWeightedMainExpansion_no_sieve_terminal {r y : Nat} (hr : 0 < r) (z : Real)
    (hcard : (iwaniecStrictPrimePool z).card < 2 * r) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) = iwaniecPaperR z -
      iwaniecCubicThresholdMass r (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) := by
  have hzero := iwaniecCubicTerminalMass_eq_zero_of_totalDepth r (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight [] (iwaniecDescendingFactors (iwaniecStrictPrimePool z))
    (by simpa [iwaniecDescendingFactors] using hcard)
  rw [iwaniecCubicWeightedMainExpansion_paperR hr z, hzero, sub_zero]

end

end Erdos1212Kernel
