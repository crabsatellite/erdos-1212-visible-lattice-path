import Erdos1212Kernel.DeBruijnF1RayTailControl
import Erdos1212Kernel.DeBruijnSaddleScale
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn_shifted_exponential_integrable {u : Real} (hu : 0 < u) (r : Real) :
    IntegrableOn (fun x : Real => Real.exp (-u * (x - r))) (Set.Ioi r) := by
  have h := (integrableOn_exp_mul_Ioi (a := -u) (by linarith) r).const_mul (Real.exp (u * r))
  apply h.congr
  filter_upwards with x
  rw [← Real.exp_add]
  congr 1
  ring

theorem deBruijn_shifted_exponential_integral {u : Real} (hu : 0 < u) (r : Real) :
    (∫ x in Set.Ioi r, Real.exp (-u * (x - r))) = 1 / u := by
  have hfun : (fun x : Real => Real.exp (-u * (x - r))) =
      (fun x : Real => Real.exp (u * r) * Real.exp (-u * x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (a := -u) (by linarith) r]
  rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
  simp only [add_neg_cancel, neg_mul, Real.exp_zero]

theorem deBruijnF1SaddleUpper_norm_bound {u : Real} (hu : 1 < u) :
    ‖deBruijnF1SaddleUpper u‖ ≤ deBruijnSaddleHeight u / u := by
  have hi := (deBruijn_shifted_exponential_integrable (show 0 < u by linarith) (deBruijnSaddle u)).const_mul (deBruijnSaddleHeight u)
  have h := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun x : Real => deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)) hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1_upper_saddle_tail_pointwise hu hx.le)
  rw [MeasureTheory.integral_const_mul, deBruijn_shifted_exponential_integral (show 0 < u by linarith)] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem deBruijnF1SaddleLower_norm_bound {u : Real} (hu : 1 < u) :
    ‖deBruijnF1SaddleLower u‖ ≤ deBruijnSaddleHeight u / u := by
  have hi := (deBruijn_shifted_exponential_integrable (show 0 < u by linarith) (deBruijnSaddle u)).const_mul (deBruijnSaddleHeight u)
  have h := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun x : Real => deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)) hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1_lower_saddle_tail_pointwise hu hx.le)
  rw [MeasureTheory.integral_const_mul, deBruijn_shifted_exponential_integral (show 0 < u by linarith)] at h
  simpa only [div_eq_mul_inv, one_mul] using h

theorem deBruijnF1_normalized_tail_norm {u : Real} (hu : 1 < u) (z : Complex)
    (hz : ‖z‖ ≤ deBruijnSaddleHeight u / u) :
    ‖(Real.sqrt (deBruijnSaddleCurvature u) : Complex) * z / (deBruijnSaddleHeight u : Complex)‖ ≤
      1 / Real.sqrt (deBruijnSaddleCurvature u) := by
  have hC := deBruijnSaddleCurvature_pos u
  have hs : 0 < Real.sqrt (deBruijnSaddleCurvature u) := Real.sqrt_pos.mpr hC
  have hH := deBruijnSaddleHeight_pos u
  have hu0 : 0 < u := by linarith
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hH]
  calc
    _ ≤ Real.sqrt (deBruijnSaddleCurvature u) * (deBruijnSaddleHeight u / u) / deBruijnSaddleHeight u :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz hs.le) hH.le
    _ = Real.sqrt (deBruijnSaddleCurvature u) / u := by field_simp
    _ ≤ 1 / Real.sqrt (deBruijnSaddleCurvature u) := by
      rw [div_le_div_iff₀ hu0 hs]
      nlinarith [Real.sq_sqrt hC.le, deBruijnSaddleCurvature_le hu]

theorem tendsto_deBruijnF1SaddleUpper_normalized :
    Tendsto (fun u : Real => (Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1SaddleUpper u /
      (deBruijnSaddleHeight u : Complex)) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun u : Real => 1 / Real.sqrt (deBruijnSaddleCurvature u)) _ tendsto_deBruijnSaddle_gaussian_width
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact deBruijnF1_normalized_tail_norm hu _ (deBruijnF1SaddleUpper_norm_bound hu)

theorem tendsto_deBruijnF1SaddleLower_normalized :
    Tendsto (fun u : Real => (Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1SaddleLower u /
      (deBruijnSaddleHeight u : Complex)) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun u : Real => 1 / Real.sqrt (deBruijnSaddleCurvature u)) _ tendsto_deBruijnSaddle_gaussian_width
  filter_upwards [eventually_gt_atTop (1 : Real)] with u hu
  exact deBruijnF1_normalized_tail_norm hu _ (deBruijnF1SaddleLower_norm_bound hu)

end

end Erdos1212Kernel
