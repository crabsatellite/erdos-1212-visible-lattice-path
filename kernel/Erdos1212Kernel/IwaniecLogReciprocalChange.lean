import Erdos1212Kernel.IwaniecWeightedIntegralSandwich
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def iwaniecExpReciprocalScale (L t : Real) : Real :=
  Real.exp (L / t)

def iwaniecReciprocalLogWeight
    (L : Real) (profile : Real → Real) (x : Real) : Real :=
  profile (L / Real.log x - 1) / (L - Real.log x)

theorem iwaniecExpReciprocalScale_hasDerivAt
    {L t : Real} (ht : t ≠ 0) :
    HasDerivAt (iwaniecExpReciprocalScale L)
      (-Real.exp (L / t) * L / t ^ 2) t := by
  unfold iwaniecExpReciprocalScale
  have hquot := (hasDerivAt_const t L).div (hasDerivAt_id t) ht
  have hexp := hquot.exp
  convert hexp using 1
  simp only [Pi.div_apply, id_eq]
  field_simp [ht]
  ring_nf

theorem iwaniecReciprocalLog_integrand_transform
    (profile : Real → Real) {L t : Real}
    (hL : 0 < L) (ht : 1 < t) :
    (iwaniecReciprocalLogWeight L profile
        (iwaniecExpReciprocalScale L t) *
      iwaniecLogKernel (iwaniecExpReciprocalScale L t)) *
        (-Real.exp (L / t) * L / t ^ 2) =
      -(profile (t - 1) / (L * (t - 1))) := by
  unfold iwaniecReciprocalLogWeight iwaniecExpReciprocalScale
    iwaniecLogKernel
  rw [Real.log_exp]
  have hLne : L ≠ 0 := hL.ne'
  have htne : t ≠ 0 := by linarith
  have htOne : t - 1 ≠ 0 := by linarith
  have hexp : Real.exp (L / t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hLne, htne, htOne, hexp]

/-- Exact reciprocal-logarithm change of variables behind Iwaniec 1971,
Corollary 1 to Lemma 13.  Writing `L = log y`, this is the substitution
`t = L / log x`. -/
theorem iwaniecWeightedLogKernelIntegral_reciprocalLog_change
    (profile : Real → Real) {L alpha beta : Real}
    (hL : 0 < L) (halpha : 1 < alpha) (hab : alpha ≤ beta) :
    iwaniecWeightedLogKernelIntegral
        (iwaniecReciprocalLogWeight L profile)
        (iwaniecExpReciprocalScale L beta)
        (iwaniecExpReciprocalScale L alpha) =
      L⁻¹ *
        (∫ t in alpha..beta, profile (t - 1) / (t - 1)) := by
  let scale := iwaniecExpReciprocalScale L
  let scaleDeriv := fun t : Real => -Real.exp (L / t) * L / t ^ 2
  let integrand := fun x : Real =>
    iwaniecReciprocalLogWeight L profile x * iwaniecLogKernel x
  have hbeta : 1 < beta := halpha.trans_le hab
  have hscaleDeriv : ∀ t ∈ Set.uIcc beta alpha,
      HasDerivAt scale (scaleDeriv t) t := by
    intro t ht
    have htOne : 1 < t := by
      rw [Set.uIcc_comm, Set.uIcc_of_le hab] at ht
      exact halpha.trans_le ht.1
    exact iwaniecExpReciprocalScale_hasDerivAt (by linarith)
  have hscaleCont : ContinuousOn scale (Set.uIcc beta alpha) := by
    intro t ht
    exact (hscaleDeriv t ht).continuousAt.continuousWithinAt
  have hscaleDerivNonpos : ∀ t ∈ Set.Ioo (min beta alpha) (max beta alpha),
      scaleDeriv t ≤ 0 := by
    intro t ht
    dsimp [scaleDeriv]
    have htOne : 1 < t := by
      rw [min_eq_right hab, max_eq_left hab] at ht
      exact halpha.trans ht.1
    have htSq : 0 < t ^ 2 := sq_pos_of_pos (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.exp_pos _).le) hL.le) htSq.le
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := beta) (b := alpha) (g := integrand)
    hscaleCont
    (fun t ht => hscaleDeriv t (by
      rw [Set.uIcc_comm, Set.uIcc_of_le hab]
      rw [min_eq_right hab, max_eq_left hab] at ht
      exact ⟨ht.1.le, ht.2.le⟩))
    hscaleDerivNonpos
  have hsimplify :
      (∫ t in beta..alpha, (integrand ∘ scale) t * scaleDeriv t) =
        ∫ t in beta..alpha,
          -(profile (t - 1) / (L * (t - 1))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htOne : 1 < t := by
      rw [Set.uIcc_comm, Set.uIcc_of_le hab] at ht
      exact halpha.trans_le ht.1
    exact iwaniecReciprocalLog_integrand_transform profile hL htOne
  unfold iwaniecWeightedLogKernelIntegral
  change (∫ x in scale beta..scale alpha, integrand x) = _
  rw [← hsubst, hsimplify]
  have hfactor :
      (∫ t in beta..alpha,
          -(profile (t - 1) / (L * (t - 1)))) =
        (-L⁻¹) *
          (∫ t in beta..alpha, profile (t - 1) / (t - 1)) := by
    calc
      (∫ t in beta..alpha,
          -(profile (t - 1) / (L * (t - 1)))) =
        ∫ t in beta..alpha,
          (-L⁻¹) * (profile (t - 1) / (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htOne : 1 < t := by
          rw [Set.uIcc_comm, Set.uIcc_of_le hab] at ht
          exact halpha.trans_le ht.1
        have htne : t - 1 ≠ 0 := by linarith
        field_simp [hL.ne', htne]
      _ = (-L⁻¹) *
          (∫ t in beta..alpha, profile (t - 1) / (t - 1)) := by
        rw [intervalIntegral.integral_const_mul]
  rw [hfactor, intervalIntegral.integral_symm]
  ring

theorem intervalIntegral_one_div_sub_one_general
    {alpha beta : Real} (halpha : 1 < alpha) (hab : alpha ≤ beta) :
    (∫ t in alpha..beta, (1 : Real) / (t - 1)) =
      Real.log ((beta - 1) / (alpha - 1)) := by
  let primitive := fun t : Real => Real.log (t - 1)
  have hderiv : ∀ t ∈ Set.uIcc alpha beta,
      HasDerivAt primitive ((1 : Real) / (t - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htNe : t - 1 ≠ 0 := by linarith [ht.1]
    dsimp [primitive]
    simpa [one_div] using ((hasDerivAt_id t).sub_const 1).log htNe
  have hint : IntervalIntegrable (fun t : Real => (1 : Real) / (t - 1))
      volume alpha beta := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc alpha beta) := by fun_prop
    apply continuousOn_const.div hsub
    intro t ht
    linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [primitive]
  rw [← Real.log_div (by linarith : beta - 1 ≠ 0)
    (by linarith : alpha - 1 ≠ 0)]

/-- Constant-profile specialization, matching the main integral in Iwaniec
1971, Corollary 2. -/
theorem iwaniecWeightedLogKernelIntegral_reciprocalLog_constant
    {L alpha beta : Real}
    (hL : 0 < L) (halpha : 1 < alpha) (hab : alpha ≤ beta) :
    iwaniecWeightedLogKernelIntegral
        (iwaniecReciprocalLogWeight L (fun _t => 1))
        (iwaniecExpReciprocalScale L beta)
        (iwaniecExpReciprocalScale L alpha) =
      L⁻¹ * Real.log ((beta - 1) / (alpha - 1)) := by
  rw [iwaniecWeightedLogKernelIntegral_reciprocalLog_change
    (fun _t => 1) hL halpha hab]
  rw [intervalIntegral_one_div_sub_one_general halpha hab]

end

end Erdos1212Kernel
