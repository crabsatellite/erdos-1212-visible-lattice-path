import Erdos1212Kernel.IwaniecAuxiliaryWeightedDerivative

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

def iwaniecAuxLowerPowerLogDerivative (level s : Real) : Real :=
  5 * Real.log (iwaniecAuxWeightBase level s) +
    5 * (s - 1) * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) /
      (s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2)

theorem iwaniecAuxWeightLowerPower_hasDerivAt
    {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) :
    HasDerivAt (iwaniecAuxWeightLowerPower level)
      (iwaniecAuxWeightLowerPower level s * iwaniecAuxLowerPowerLogDerivative level s) s := by
  have hbase := iwaniecAuxWeightBase_hasDerivAt level (show 0 < s by linarith)
  have hexp : HasDerivAt (fun t : Real => 5 * (t - 1)) 5 s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).sub_const 1).const_mul 5
  have hraw := hbase.rpow hexp (iwaniecAuxWeightBase_pos level hs)
  refine hraw.congr_deriv ?_
  rw [Real.rpow_sub_one (iwaniecAuxWeightBase_pos level hs).ne']
  have hid := iwaniecAuxWeightBase_logDerivative_identity hy hs
  unfold iwaniecAuxWeightLowerPower iwaniecAuxLowerPowerLogDerivative
  calc
    _ = iwaniecAuxWeightBase level s ^ (5 * (s - 1)) *
        (5 * Real.log (iwaniecAuxWeightBase level s) + 5 * (s - 1) *
          (((2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) / Real.log level ^ 2) /
            iwaniecAuxWeightBase level s)) := by ring
    _ = _ := by rw [hid]; ring

theorem iwaniecAuxLowerPowerLogDerivative_le_full
    {level s : Real} (hy : 1 < level) (hs : 1 ≤ s) :
    iwaniecAuxLowerPowerLogDerivative level s ≤ iwaniecAuxWeightLogDerivative level s := by
  have hlog := Real.log_nonneg hs
  have hs0 : 0 ≤ s := by linarith
  have hnum : 0 ≤ 5 * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) := by positivity
  have hden : 0 ≤ s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2 := by positivity
  have hnonneg := div_nonneg hnum hden
  calc
    _ = iwaniecAuxWeightLogDerivative level s -
        5 * (2 * s * Real.log s ^ 5 + 5 * s * Real.log s ^ 4) /
          (s ^ 2 * Real.log s ^ 5 + Real.log level ^ 2) := by
      unfold iwaniecAuxLowerPowerLogDerivative iwaniecAuxWeightLogDerivative
      ring
    _ ≤ _ := sub_le_self _ hnonneg

theorem iwaniec_log_le_two_log_pred {s : Real} (hs : 3 ≤ s) :
    Real.log s ≤ 2 * Real.log (s - 1) := by
  have hs0 : 0 < s := by linarith
  have hsq : s ≤ (s - 1) ^ 2 := by nlinarith [sq_nonneg (s - 3)]
  have hh := Real.log_le_log hs0 hsq
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

/-- The original derivative-loss estimate, at the literal shifted G
argument occurring in Corollary 3. No shifted weight is substituted. -/
theorem iwaniecAuxLowerPower_shifted_loss_lt
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s)
    (hxi : s ≤ iwaniecPaperXi level) :
    iwaniecAuxCorollaryConstant * iwaniecAuxLowerPowerLogDerivative level s < Real.log (s - 1) := by
  have hC : 0 < iwaniecAuxCorollaryConstant := by linarith [iwaniecAuxCorollaryConstant_gt_three_hundred]
  have hs3 : 3 ≤ s := by linarith [iwaniecAuxSZero_large]
  have hlog : 1 ≤ Real.log s := iwaniecAuxSZero_log_ge_one hs
  have hlog0 : 0 < Real.log s := by linarith
  have hlow := iwaniecAuxLowerPowerLogDerivative_le_full hy (show 1 ≤ s by linarith)
  have hfull := iwaniecAuxWeightLogDerivative_le_forty hy (show 1 ≤ s by linarith) hlog
  have herror := iwaniecAuxRange_error_lt_one hy hs hxi
  have hlogpred := iwaniec_log_le_two_log_pred hs3
  calc
    _ ≤ iwaniecAuxCorollaryConstant * (40 * s ^ 2 * Real.log s ^ 5 / Real.log level ^ 2) :=
      mul_le_mul_of_nonneg_left (hlow.trans hfull) hC.le
    _ = ((2 / 5 : Real) * Real.log s) * iwaniecAuxWeightError level s := by
      unfold iwaniecAuxWeightError
      ring
    _ < ((2 / 5 : Real) * Real.log s) * 1 :=
      mul_lt_mul_of_pos_left herror (by positivity)
    _ ≤ Real.log (s - 1) := by linarith only [hlogpred, hlog0]

end

end Erdos1212Kernel
