import Erdos1212Kernel.IwaniecAuxiliaryWindowCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

def iwaniecAuxWInitialPrimitive (s : Real) : Real := (Real.log (s - 1) + 1) / s

def iwaniecAuxMInitialPrimitive (s : Real) : Real :=
  3 * s + (2 - s) * Real.log (s - 1) - (Real.log (s - 1) - 1) / (2 * s)

theorem iwaniecAuxWInitialPrimitive_hasDerivAt
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    HasDerivAt iwaniecAuxWInitialPrimitive (iwaniecAuxWWindowKernel s) s := by
  have hsNe : s ≠ 0 := by linarith [hs.1]
  have hsSub : s - 1 ≠ 0 := by linarith [hs.1]
  have hlog := ((hasDerivAt_id s).sub_const 1).log hsSub
  have hraw := (hlog.add_const 1).div (hasDerivAt_id s) hsNe
  refine hraw.congr_deriv ?_
  unfold iwaniecAuxWWindowKernel
  rw [iwaniecAuxW_initial hs.2]
  simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  field_simp [hsNe, hsSub]
  ring

theorem iwaniecAuxMInitialPrimitive_hasDerivAt
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    HasDerivAt iwaniecAuxMInitialPrimitive (iwaniecAuxMWindowKernel s) s := by
  have hsNe : s ≠ 0 := by linarith [hs.1]
  have hsSub : s - 1 ≠ 0 := by linarith [hs.1]
  have hlog := ((hasDerivAt_id s).sub_const 1).log hsSub
  have hfirst := (hasDerivAt_id s).const_mul 3
  have hsecond := ((hasDerivAt_const s (2 : Real)).sub (hasDerivAt_id s)).mul hlog
  have hthird := (hlog.sub_const 1).div ((hasDerivAt_id s).const_mul 2)
    (mul_ne_zero (by norm_num) hsNe)
  have hraw := (hfirst.add hsecond).sub hthird
  refine hraw.congr_deriv ?_
  unfold iwaniecAuxMWindowKernel iwaniecAuxMWindowWeight
  rw [iwaniecAuxM_initial hs.2]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
  field_simp [hsNe, hsSub]
  ring

theorem iwaniecAuxWWindowKernel_initial_integral :
    (∫ s in (2 : Real)..3, iwaniecAuxWWindowKernel s) = (2 * Real.log 2 - 1) / 6 := by
  have hderiv : ∀ s ∈ Set.uIcc (2 : Real) 3,
      HasDerivAt iwaniecAuxWInitialPrimitive (iwaniecAuxWWindowKernel s) s := by
    intro s hs
    apply iwaniecAuxWInitialPrimitive_hasDerivAt
    simpa only [Set.uIcc_of_le (show (2 : Real) ≤ 3 by norm_num)] using hs
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (iwaniecIntervalIntegrable_of_continuousOn_one _
      iwaniecAuxWWindowKernel_continuousOn (by norm_num) (by norm_num))]
  norm_num [iwaniecAuxWInitialPrimitive]
  ring

theorem iwaniecAuxMWindowKernel_initial_integral :
    (∫ s in (2 : Real)..3, iwaniecAuxMWindowKernel s) = (35 - 14 * Real.log 2) / 12 := by
  have hderiv : ∀ s ∈ Set.uIcc (2 : Real) 3,
      HasDerivAt iwaniecAuxMInitialPrimitive (iwaniecAuxMWindowKernel s) s := by
    intro s hs
    apply iwaniecAuxMInitialPrimitive_hasDerivAt
    simpa only [Set.uIcc_of_le (show (2 : Real) ≤ 3 by norm_num)] using hs
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (iwaniecIntervalIntegrable_of_continuousOn_one _
      iwaniecAuxMWindowKernel_continuousOn (by norm_num) (by norm_num))]
  norm_num [iwaniecAuxMInitialPrimitive]
  ring

theorem iwaniecAuxWConservation_three : iwaniecAuxWConservation 3 = 0 := by
  unfold iwaniecAuxWConservation
  rw [iwaniecPrimitiveWindow_eq_integral _ iwaniecAuxWWindowKernel_continuousOn (by norm_num)]
  norm_num only [show (3 : Real) - 1 = 2 by norm_num]
  rw [iwaniecAuxWWindowKernel_initial_integral, iwaniecAuxW_initial (le_refl 3)]
  norm_num
  ring

theorem iwaniecAuxMConservation_three : iwaniecAuxMConservation 3 = 0 := by
  unfold iwaniecAuxMConservation
  rw [iwaniecPrimitiveWindow_eq_integral _ iwaniecAuxMWindowKernel_continuousOn (by norm_num)]
  norm_num only [show (3 : Real) - 1 = 2 by norm_num]
  rw [iwaniecAuxMWindowKernel_initial_integral, iwaniecAuxM_initial (le_refl 3)]
  norm_num [iwaniecAuxMCoefficient]
  ring

theorem iwaniecConstant_from_three
    (f : Real → Real) (hcont : ContinuousOn f (Set.Ici (3 : Real)))
    (hderiv : ∀ s : Real, 3 < s → HasDerivAt f 0 s)
    {s : Real} (hs : 3 ≤ s) : f s = f 3 := by
  have hc : ContinuousOn f (Set.Icc (3 : Real) s) :=
    hcont.mono (fun _ ht => ht.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hc
    (f' := fun _t : Real => 0) (fun t ht => hderiv t ht.1)
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

theorem iwaniecAuxWConservation_zero {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxWConservation s = 0 := by
  rw [iwaniecConstant_from_three _ iwaniecAuxWConservation_continuousOn
    (fun _ ht => iwaniecAuxWConservation_hasDerivAt ht) hs, iwaniecAuxWConservation_three]

theorem iwaniecAuxMConservation_zero {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxMConservation s = 0 := by
  rw [iwaniecConstant_from_three _ iwaniecAuxMConservation_continuousOn
    (fun _ ht => iwaniecAuxMConservation_hasDerivAt ht) hs, iwaniecAuxMConservation_three]

/-- Equation (3.11), including the initial endpoint `s=3`. -/
theorem iwaniecAuxW_window_identity {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxW s = -s * (∫ x in (s - 1)..s, iwaniecAuxW x / x ^ 2) := by
  have h := iwaniecAuxWConservation_zero hs
  unfold iwaniecAuxWConservation at h
  rw [iwaniecPrimitiveWindow_eq_integral _ iwaniecAuxWWindowKernel_continuousOn (by linarith)] at h
  have hdiv : iwaniecAuxW s / s = -(∫ x in (s - 1)..s, iwaniecAuxW x / x ^ 2) := by
    exact eq_neg_of_add_eq_zero_left h
  have hmul := (div_eq_iff (by linarith : s ≠ 0)).1 hdiv
  simpa only [neg_mul, mul_neg, mul_comm] using hmul

/-- Equation (3.12), with the exact coefficient and weighted window. -/
theorem iwaniecAuxM_window_identity {s : Real} (hs : 3 ≤ s) :
    (((s - 1) ^ 2 - 1 / 2) / s) * iwaniecAuxM s =
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * iwaniecAuxM x := by
  have h := iwaniecAuxMConservation_zero hs
  unfold iwaniecAuxMConservation at h
  rw [iwaniecPrimitiveWindow_eq_integral _ iwaniecAuxMWindowKernel_continuousOn (by linarith)] at h
  exact sub_eq_zero.mp h

end

end Erdos1212Kernel
