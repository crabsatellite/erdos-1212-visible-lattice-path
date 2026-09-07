import Erdos1212Kernel.IwaniecAuxPrimeSquaredWeight
import Erdos1212Kernel.IwaniecCorollaryThreeIntegral

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 600000

theorem iwaniecAuxPrimeSquared_integrand_transform (rank : Nat)
    {level t : Real} (hy : 1 < level) (ht : 1 < t) :
    (iwaniecAuxPrimeSquaredWeight rank level (iwaniecExpReciprocalScale (Real.log level) t) /
      (iwaniecExpReciprocalScale (Real.log level) t *
        Real.log (iwaniecExpReciprocalScale (Real.log level) t))) *
      (-Real.exp (Real.log level / t) * Real.log level / t ^ 2) =
      -(iwaniecAuxGKernel rank t / Real.log level ^ 2) := by
  rw [iwaniecAuxPrimeSquaredWeight_at_scale rank hy ht]
  unfold iwaniecExpReciprocalScale iwaniecAuxGKernel
  rw [Real.log_exp]
  have hL : Real.log level ≠ 0 := (Real.log_pos hy).ne'
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have he : Real.exp (Real.log level / t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hL, ht0, ht1, he]
  <;> ring

theorem iwaniecAuxPrimeSquared_integral_transform (rank : Nat)
    {level s T : Real} (hy : 1 < level) (hs : 1 < s) (hsT : s ≤ T) :
    (∫ x in (iwaniecExpReciprocalScale (Real.log level) T)..
      (iwaniecExpReciprocalScale (Real.log level) s),
      iwaniecAuxPrimeSquaredWeight rank level x / (x * Real.log x)) =
      (Real.log level ^ 2)⁻¹ * ∫ t in s..T, iwaniecAuxGKernel rank t := by
  rw [iwaniec_integral_expReciprocal_change _ (Real.log_pos hy) hs hsT]
  have hpoint : (∫ t in T..s,
      iwaniecAuxPrimeSquaredWeight rank level (iwaniecExpReciprocalScale (Real.log level) t) /
        (iwaniecExpReciprocalScale (Real.log level) t *
          Real.log (iwaniecExpReciprocalScale (Real.log level) t)) *
        (-Real.exp (Real.log level / t) * Real.log level / t ^ 2)) =
        ∫ t in T..s, -(Real.log level ^ 2)⁻¹ * iwaniecAuxGKernel rank t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_comm, Set.uIcc_of_le hsT] at ht
    dsimp only
    rw [iwaniecAuxPrimeSquared_integrand_transform rank hy (hs.trans_le ht.1)]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, intervalIntegral.integral_symm]
  ring

theorem iwaniecAuxGKernel_finite_integral (rank : Nat)
    {s T : Real} (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, iwaniecAuxGKernel rank t) =
      iwaniecAuxG (rank + 1) s - iwaniecAuxG (rank + 1) T := by
  have hsTail : iwaniecAuxGTailStart (rank + 1) ≤ s := by
    rwa [← iwaniecCorollaryThreeDomainStart_eq_tail]
  have hfun : (fun t : Real => iwaniecAuxG ((rank + 1) + 1) (t - 1) * t / (t - 1) ^ 2) =
      iwaniecAuxGKernel rank := by
    funext t
    rw [show (rank + 1) + 1 = rank + 2 by omega, iwaniecAuxG_add_two]
    rfl
  have hstart := iwaniecAuxG_tail (rank + 1) hsTail
  have hend := iwaniecAuxG_tail (rank + 1) (hsTail.trans hsT)
  have hi := iwaniecAuxG_tail_integrable (rank + 1) hsTail
  rw [hfun] at hstart hend hi
  have hh := intervalIntegral.integral_Ioi_sub_Ioi hi hsT
  rw [← hstart, ← hend] at hh
  exact hh.symm

theorem iwaniecAuxPrimeSquared_integral_finite (rank : Nat)
    {level s T : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) (hsT : s ≤ T) :
    (∫ x in (iwaniecExpReciprocalScale (Real.log level) T)..
      (iwaniecExpReciprocalScale (Real.log level) s),
      iwaniecAuxPrimeSquaredWeight rank level x / (x * Real.log x)) =
      (iwaniecAuxG (rank + 1) s - iwaniecAuxG (rank + 1) T) / Real.log level ^ 2 := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  rw [iwaniecAuxPrimeSquared_integral_transform rank hy (by linarith) hsT,
    iwaniecAuxGKernel_finite_integral rank hs hsT]
  ring

end

end Erdos1212Kernel
