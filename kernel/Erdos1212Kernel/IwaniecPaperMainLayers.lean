import Erdos1212Kernel.IwaniecTerminalLayerSplit
import Erdos1212Kernel.IwaniecCubicMainExact

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- The precise layered form of the paper's (2.15): include failures
through depth 2r and retain only the successful depth-2r terminal mass. -/
theorem iwaniecCubicWeightedMainExpansion_full_layers {r y : Nat} (hr : 0 < r) (z : Real) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) = iwaniecPaperR z -
      iwaniecThresholdPartialMass (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r) -
      iwaniecSurvivalLayer (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r) := by
  have hk : 2 * r - 1 + 1 = 2 * r := by omega
  have hsum := iwaniecThresholdPartialMass_succ (iwaniecCubicEvenRestriction y)
    iwaniecReciprocalFactorWeight [] (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r - 1)
  rw [hk] at hsum
  rw [iwaniecCubicWeightedMainExpansion_paperR hr z,
    iwaniecCubicThresholdMass_root_eq_layers hr, iwaniecCubicTerminalMass_root_eq_layers hr, hsum]
  ring

theorem iwaniecCubicWeightedMainExpansion_full_layers_no_tail {r y : Nat} (hr : 0 < r) (z : Real)
    (hcard : (iwaniecStrictPrimePool z).card < 2 * r) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool z) = iwaniecPaperR z -
      iwaniecThresholdPartialMass (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
        (iwaniecDescendingFactors (iwaniecStrictPrimePool z)) (2 * r) := by
  rw [iwaniecCubicWeightedMainExpansion_full_layers hr z,
    iwaniecSurvivalLayer_eq_zero_of_length _ _ _ _ _ (by simpa [iwaniecDescendingFactors] using hcard), sub_zero]

end

end Erdos1212Kernel
