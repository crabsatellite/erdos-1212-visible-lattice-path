import Erdos1212Kernel.IwaniecAuxiliaryWeightError
import Erdos1212Kernel.IwaniecAuxiliaryWeightAbsorption
import Erdos1212Kernel.IwaniecAuxiliaryXiWeightScale

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

theorem iwaniecAuxRange_error_lt_one
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    iwaniecAuxWeightError level s < 1 := by
  have hC : 0 < iwaniecAuxCorollaryConstant := by linarith [iwaniecAuxCorollaryConstant_gt_three_hundred]
  have hsPos : 0 < s := by linarith [iwaniecAuxSZero_large]
  have hz : 0 < s ^ 2 / Real.log level ^ 2 := div_pos (sq_pos_of_pos hsPos) (sq_pos_of_pos (Real.log_pos hy))
  have h := iwaniecWeight_error_lt_one hC hz (iwaniecAuxSZero_log_ge_one hs)
    (iwaniecAuxRange_normalized_scale hy hs hxi) (iwaniecAuxSZero_log_two_fifths hs)
  unfold iwaniecAuxWeightError
  convert h using 1 <;> ring

theorem iwaniecAuxRange_weight_absorption
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    1 < iwaniecAuxWeightBase level s ^ 5 * (1 - iwaniecAuxWeightError level s) := by
  have hC : 0 < iwaniecAuxCorollaryConstant := by linarith [iwaniecAuxCorollaryConstant_gt_three_hundred]
  have hsPos : 0 < s := by linarith [iwaniecAuxSZero_large]
  have hz : 0 < s ^ 2 / Real.log level ^ 2 := div_pos (sq_pos_of_pos hsPos) (sq_pos_of_pos (Real.log_pos hy))
  have h := iwaniecWeight_absorbs_error hC hz (iwaniecAuxSZero_log_ge_one hs)
    (iwaniecAuxRange_normalized_scale hy hs hxi) (iwaniecAuxSZero_log_two_fifths hs)
  unfold iwaniecAuxWeightBase iwaniecAuxWeightError
  convert h using 1 <;> ring

/-- Source (3.16), now with its actual s0 and xi conditions supplying
every logarithm, power, and error-absorption input. -/
theorem iwaniecAuxWeightedIntegrand_lt_neg_tau_deriv (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    iwaniecAuxWeightedIntegrand rank level s < -deriv (iwaniecAuxTau rank level) s := by
  have hsThree : 3 < s := by linarith [iwaniecAuxSZero_large]
  have hraw := neg_deriv_iwaniecAuxTau_gt_error_bound rank hy hsThree (iwaniecAuxSZero_log_ge_one hs)
  have habsorb := iwaniecAuxRange_weight_absorption hy hs hxi
  have hpos : 0 < iwaniecAuxWeightLowerPower level s * iwaniecAuxGKernel rank s :=
    mul_pos (iwaniecAuxWeightLowerPower_pos level (by linarith)) (iwaniecAuxGKernel_pos rank hsThree.le)
  have hscaled := mul_lt_mul_of_pos_left habsorb hpos
  have hmiddle : iwaniecAuxWeightedIntegrand rank level s <
      iwaniecAuxWeightPower level s * iwaniecAuxGKernel rank s * (1 - iwaniecAuxWeightError level s) := by
    rw [iwaniecAuxWeightedIntegrand_eq, iwaniecAuxWeightPower_split level (show 1 ≤ s by linarith)]
    convert hscaled using 1 <;> ring
  exact hmiddle.trans hraw

theorem iwaniecAuxTau_deriv_neg (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    deriv (iwaniecAuxTau rank level) s < 0 := by
  have h := iwaniecAuxWeightedIntegrand_lt_neg_tau_deriv rank hy hs hxi
  have hp := iwaniecAuxWeightedIntegrand_pos rank level (s := s) (by linarith [iwaniecAuxSZero_large])
  linarith

theorem iwaniecAuxTau_strictAntiOn (rank : Nat) {level : Real} (hy : 1 < level) :
    StrictAntiOn (iwaniecAuxTau rank level) (Set.Ioo iwaniecAuxSZero (iwaniecPaperXi level)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro s hs
    exact (iwaniecAuxTau_hasDerivAt rank hy (by linarith [hs.1, iwaniecAuxSZero_large])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Set.Ioo iwaniecAuxSZero (iwaniecPaperXi level) := interior_subset hs
    exact iwaniecAuxTau_deriv_neg rank hy hs'.1 hs'.2.le

end

end Erdos1212Kernel
