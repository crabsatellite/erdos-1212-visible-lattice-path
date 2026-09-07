import Erdos1212Kernel.IwaniecAuxPrimeSquaredWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecAuxWeightLowerPower_le_upper_at (level : Real)
    {s T : Real} (hs : 1 ≤ s) (hsT : s ≤ T) :
    iwaniecAuxWeightLowerPower level s ≤ iwaniecAuxWeightPower level T := by
  have hT : 1 ≤ T := hs.trans hsT
  have hbase := iwaniecAuxWeightBase_monotoneOn level hs hT hsT
  have hexp : 0 ≤ 5 * (s - 1) := by linarith
  unfold iwaniecAuxWeightLowerPower iwaniecAuxWeightPower
  exact (Real.rpow_le_rpow (iwaniecAuxWeightBase_pos level hs).le hbase hexp).trans
    (Real.rpow_le_rpow_of_exponent_le (iwaniecAuxWeightBase_one_le level hT) (by linarith))

theorem iwaniecCorollaryThreePrimeWeight_eq_lowerPower_mul (rank : Nat)
    {level x : Real} (hy : 1 < level) (hx : 1 < x) :
    iwaniecCorollaryThreePrimeWeight rank level x =
      iwaniecAuxWeightLowerPower level (Real.log level / Real.log x) *
        iwaniecAuxPrimeSquaredWeight rank level x := by
  rw [iwaniecCorollaryThreePrimeWeight_literal_normalization rank hy hx,
    iwaniecAuxPrimeSquaredWeight_normalized rank hy hx]
  unfold iwaniecCorollaryThreeProfile
  ring

theorem iwaniecCorollaryThreePrimeWeight_pos_exactDomain (rank : Nat)
    {level s T x : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s)
    (hsT : s ≤ T) (hx : x ∈ Set.Icc (iwaniecExpReciprocalScale (Real.log level) T)
      (iwaniecExpReciprocalScale (Real.log level) s)) :
    0 < iwaniecCorollaryThreePrimeWeight rank level x := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  obtain ⟨hx1, _hxy, htx⟩ := iwaniecReciprocalLog_coordinate_mem hy (by linarith) hsT hx
  rw [iwaniecCorollaryThreePrimeWeight_eq_lowerPower_mul rank hy hx1]
  exact mul_pos (iwaniecAuxWeightLowerPower_pos level (by linarith [htx.1]))
    (iwaniecAuxPrimeSquaredWeight_pos_on rank hy hs hsT hx)

theorem iwaniecCorollaryThreePrimeWeight_small_bound (rank : Nat)
    {level s x : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s)
    (hs0 : s ≤ iwaniecAuxSZero)
    (hx : x ∈ Set.Icc (iwaniecExpReciprocalScale (Real.log level) iwaniecAuxSZero)
      (iwaniecExpReciprocalScale (Real.log level) s)) :
    iwaniecCorollaryThreePrimeWeight rank level x ≤
      iwaniecAuxWeightPower level iwaniecAuxSZero * iwaniecAuxPrimeSquaredWeight rank level x := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  obtain ⟨hx1, _hxy, htx⟩ := iwaniecReciprocalLog_coordinate_mem hy (by linarith) hs0 hx
  have hweight := iwaniecAuxWeightLowerPower_le_upper_at level (show 1 ≤ Real.log level / Real.log x by linarith [htx.1]) htx.2
  rw [iwaniecCorollaryThreePrimeWeight_eq_lowerPower_mul rank hy hx1]
  exact mul_le_mul_of_nonneg_right hweight (iwaniecAuxPrimeSquaredWeight_pos_on rank hy hs hs0 hx).le

end

end Erdos1212Kernel
