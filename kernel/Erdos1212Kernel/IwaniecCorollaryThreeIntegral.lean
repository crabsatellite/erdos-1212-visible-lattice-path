import Erdos1212Kernel.IwaniecCorollaryThreeWeight

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 650000

theorem iwaniec_integral_expReciprocal_change (g : Real → Real)
    {L s T : Real} (hL : 0 < L) (hs : 1 < s) (hsT : s ≤ T) :
    (∫ x in (iwaniecExpReciprocalScale L T)..(iwaniecExpReciprocalScale L s), g x) =
      ∫ t in T..s, g (iwaniecExpReciprocalScale L t) * (-Real.exp (L / t) * L / t ^ 2) := by
  let scale := iwaniecExpReciprocalScale L
  let scaleDeriv := fun t : Real => -Real.exp (L / t) * L / t ^ 2
  have hd : ∀ t ∈ Set.uIcc T s, HasDerivAt scale (scaleDeriv t) t := by
    intro t ht
    rw [Set.uIcc_comm, Set.uIcc_of_le hsT] at ht
    exact iwaniecExpReciprocalScale_hasDerivAt (by linarith [ht.1])
  have hc : ContinuousOn scale (Set.uIcc T s) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hnonpos : ∀ t ∈ Set.Ioo (min T s) (max T s), scaleDeriv t ≤ 0 := by
    intro t _ht
    dsimp [scaleDeriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hL.le) (sq_nonneg t)
  have hh := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := T) (b := s) (g := g)
    hc (fun t ht => hd t (by
      rw [Set.uIcc_comm, Set.uIcc_of_le hsT]
      rw [min_eq_right hsT, max_eq_left hsT] at ht
      exact ⟨ht.1.le, ht.2.le⟩)) hnonpos
  exact hh.symm

theorem iwaniecCorollaryThree_integrand_transform (rank : Nat)
    {level t : Real} (hy : 1 < level) (ht : 1 < t) :
    (iwaniecCorollaryThreePrimeWeight rank level
      (iwaniecExpReciprocalScale (Real.log level) t) /
      (iwaniecExpReciprocalScale (Real.log level) t *
        Real.log (iwaniecExpReciprocalScale (Real.log level) t))) *
      (-Real.exp (Real.log level / t) * Real.log level / t ^ 2) =
      -(iwaniecAuxWeightedIntegrand rank level t / Real.log level ^ 2) := by
  rw [iwaniecCorollaryThreePrimeWeight_at_scale rank hy ht]
  unfold iwaniecExpReciprocalScale iwaniecCorollaryThreeScaledProfile
    iwaniecCorollaryThreeProfile iwaniecAuxWeightedIntegrand
  rw [Real.log_exp]
  have hL : Real.log level ≠ 0 := (Real.log_pos hy).ne'
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have he : Real.exp (Real.log level / t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hL, ht0, ht1, he]
  <;> ring

theorem iwaniecCorollaryThree_integral (rank : Nat)
    {level s T : Real} (hy : 1 < level) (hs : 1 < s) (hsT : s ≤ T) :
    (∫ x in (iwaniecExpReciprocalScale (Real.log level) T)..
      (iwaniecExpReciprocalScale (Real.log level) s),
      iwaniecCorollaryThreePrimeWeight rank level x / (x * Real.log x)) =
      (Real.log level ^ 2)⁻¹ * ∫ t in s..T, iwaniecAuxWeightedIntegrand rank level t := by
  rw [iwaniec_integral_expReciprocal_change _ (Real.log_pos hy) hs hsT]
  have hpoint : (∫ t in T..s,
      iwaniecCorollaryThreePrimeWeight rank level (iwaniecExpReciprocalScale (Real.log level) t) /
        (iwaniecExpReciprocalScale (Real.log level) t *
          Real.log (iwaniecExpReciprocalScale (Real.log level) t)) *
        (-Real.exp (Real.log level / t) * Real.log level / t ^ 2)) =
        ∫ t in T..s, -(Real.log level ^ 2)⁻¹ * iwaniecAuxWeightedIntegrand rank level t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_comm, Set.uIcc_of_le hsT] at ht
    dsimp only
    rw [iwaniecCorollaryThree_integrand_transform rank hy (hs.trans_le ht.1)]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, intervalIntegral.integral_symm]
  ring

end

end Erdos1212Kernel
