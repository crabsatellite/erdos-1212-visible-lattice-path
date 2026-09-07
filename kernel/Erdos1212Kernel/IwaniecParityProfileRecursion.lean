import Erdos1212Kernel.IwaniecPaperQBandRecursion

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 550000

theorem iwaniecParitySieveProfile_kernel_integrable (rank : Nat) {s : Real}
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    IntegrableOn (fun t : Real => iwaniecParitySieveProfile rank (t - 1) / (t - 1)) (Set.Ioi s) := by
  by_cases hr : Even rank
  · have hs3 : 3 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr] at hs
      exact hs
    simpa only [iwaniecParitySieveProfile, hr, if_true, iwaniecEvenSeriesKernel] using
      integrableOn_iwaniecEvenSeriesKernel_Ioi hs3
  · have hs2 : 2 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr] at hs
      exact hs
    simpa only [iwaniecParitySieveProfile, hr, if_false, iwaniecOddSeriesKernel] using
      integrableOn_iwaniecOddSeriesKernel_Ioi hs2

/-- Equations (3.6)--(3.7) in the precise successor-parity form used in
the Q induction. The even parent's g2 term is retained. -/
theorem iwaniecParitySieveProfile_successor_tail (rank : Nat) {s : Real}
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecParitySieveProfile (rank + 1) s =
      (∫ t in Set.Ioi s, iwaniecParitySieveProfile rank (t - 1) / (t - 1)) +
      if Even (rank + 1) then iwaniecGTwo s else 0 := by
  by_cases hr : Even rank
  · have hs3 : 3 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr] at hs
      exact hs
    simpa only [iwaniecParitySieveProfile, Nat.even_add_one, hr, not_true_eq_false,
      if_true, if_false, add_zero] using iwaniecOddSieveSeries_eq_integral_Ioi hs3
  · have hs2 : 2 ≤ s := by
      norm_num [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, hr] at hs
      exact hs
    simpa only [iwaniecParitySieveProfile, Nat.even_add_one, hr, not_false_eq_true,
      if_true, if_false] using iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo hs2

/-- The literal finite main integral is bounded by the full successor
profile. This is a consequence of the proved improper-integral equations,
not an assumption about a truncated rank sum. -/
theorem iwaniecParitySieveProfile_finite_integral_bound (rank : Nat) {s T : Real}
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) (hsT : s ≤ T) (hT : 4 ≤ T) :
    (∫ t in s..T, iwaniecParitySieveProfile rank (t - 1) / (t - 1)) +
      (if Even (rank + 1) then iwaniecGTwo s else 0) ≤ iwaniecParitySieveProfile (rank + 1) s := by
  have hdiff := integral_Ioi_sub_Ioi (iwaniecParitySieveProfile_kernel_integrable rank hs) hsT
  have hleft := iwaniecParitySieveProfile_successor_tail rank hs
  have hright := iwaniecParitySieveProfile_successor_tail rank (hs.trans hsT)
  rw [iwaniecGTwo_eq_zero_of_four_le hT, ite_self, add_zero] at hright
  have hnonneg := iwaniecParitySieveProfile_nonneg (rank + 1) (by linarith : 2 ≤ T)
  linarith only [hdiff, hleft, hright, hnonneg]

end

end Erdos1212Kernel
