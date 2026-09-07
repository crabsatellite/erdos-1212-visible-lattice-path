import Erdos1212Kernel.DeBruijnVerticalPhaseLoss
import Erdos1212Kernel.DeBruijnSaddleLocalGaussian

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The full shifted vertical segment, after its literal curvature
rescaling. The growing support is not replaced by a fixed cutoff. -/
def deBruijnF1ScaledDensity (u v : Real) : Complex :=
  (Set.Icc (-(Real.pi * Real.sqrt (deBruijnSaddleCurvature u))) (Real.pi * Real.sqrt (deBruijnSaddleCurvature u))).indicator
    (fun v => deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) +
      ((v / Real.sqrt (deBruijnSaddleCurvature u) : Real) : Complex) * Complex.I) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) v

theorem deBruijnF1ScaledDensity_measurable (u : Real) : Measurable (deBruijnF1ScaledDensity u) := by
  have hc : Continuous (fun v : Real => deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) +
      ((v / Real.sqrt (deBruijnSaddleCurvature u) : Real) : Complex) * Complex.I) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) :=
    ((deBruijnF1Integrand_continuous (u : Complex)).comp
      (continuous_const.add ((Complex.continuous_ofReal.comp (continuous_id.div_const _)).mul_const Complex.I))).div_const _
  exact hc.measurable.indicator measurableSet_Icc

theorem deBruijnF1ScaledDensity_norm (u v : Real) :
    ‖deBruijnF1ScaledDensity u v‖ ≤ Real.exp (-(2 / Real.pi ^ 2) * v ^ 2) := by
  have hC := deBruijnSaddleCurvature_pos u
  have hs : 0 < Real.sqrt (deBruijnSaddleCurvature u) := Real.sqrt_pos.mpr hC
  by_cases hv : v ∈ Set.Icc (-(Real.pi * Real.sqrt (deBruijnSaddleCurvature u))) (Real.pi * Real.sqrt (deBruijnSaddleCurvature u))
  · rw [deBruijnF1ScaledDensity, Set.indicator_of_mem hv]
    have hθ : |v / Real.sqrt (deBruijnSaddleCurvature u)| ≤ Real.pi := by
      rw [abs_div, abs_of_pos hs]
      exact (div_le_iff₀ hs).mpr (abs_le.mpr hv)
    have h := deBruijnF1_vertical_ratio_bound u hθ
    have hsq : (v / Real.sqrt (deBruijnSaddleCurvature u)) ^ 2 * deBruijnSaddleCurvature u = v ^ 2 := by
      rw [div_pow, Real.sq_sqrt hC.le]
      exact div_mul_cancel₀ _ hC.ne'
    have he : (-(2 / Real.pi ^ 2) * (v / Real.sqrt (deBruijnSaddleCurvature u)) ^ 2) * deBruijnSaddleCurvature u =
        -(2 / Real.pi ^ 2) * v ^ 2 := by rw [mul_assoc, hsq]
    rw [he] at h
    exact h
  · rw [deBruijnF1ScaledDensity, Set.indicator_of_notMem hv, norm_zero]
    exact (Real.exp_pos _).le

theorem deBruijnF1ScaledDensity_integrable (u : Real) : Integrable (deBruijnF1ScaledDensity u) := by
  have hg := integrable_exp_neg_mul_sq (show (0 : Real) < 2 / Real.pi ^ 2 by positivity)
  apply hg.mono' (deBruijnF1ScaledDensity_measurable u).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v => deBruijnF1ScaledDensity_norm u v)

theorem tendsto_deBruijnF1ScaledDensity (v : Real) :
    Tendsto (fun u : Real => deBruijnF1ScaledDensity u v) atTop (nhds ((Real.exp (-v ^ 2 / 2) : Real) : Complex)) := by
  have hr : Tendsto (fun u : Real => Real.pi * Real.sqrt (deBruijnSaddleCurvature u)) atTop atTop :=
    tendsto_deBruijnSaddle_sqrt_curvature.const_mul_atTop Real.pi_pos
  apply (deBruijnF1_vertical_local_gaussian v).congr'
  filter_upwards [hr.eventually_ge_atTop |v|] with u hu
  have hm : v ∈ Set.Icc (-(Real.pi * Real.sqrt (deBruijnSaddleCurvature u))) (Real.pi * Real.sqrt (deBruijnSaddleCurvature u)) :=
    abs_le.mp hu
  rw [deBruijnF1ScaledDensity, Set.indicator_of_mem hm]

theorem deBruijn_real_gaussian_integral :
    (∫ v : Real, Real.exp (-v ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : Real)
  have he : (fun v : Real => Real.exp (-(1 / 2 : Real) * v ^ 2)) = (fun v : Real => Real.exp (-v ^ 2 / 2)) := by
    funext v
    congr 1
    ring
  rw [he, show Real.pi / (1 / 2 : Real) = 2 * Real.pi by ring] at h
  exact h

theorem tendsto_deBruijnF1ScaledDensity_integral :
    Tendsto (fun u : Real => ∫ v : Real, deBruijnF1ScaledDensity u v) atTop (nhds (Real.sqrt (2 * Real.pi) : Complex)) := by
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun v : Real => Real.exp (-(2 / Real.pi ^ 2) * v ^ 2))
    (Filter.Eventually.of_forall (fun u : Real => (deBruijnF1ScaledDensity_measurable u).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun u : Real => Filter.Eventually.of_forall (fun v => deBruijnF1ScaledDensity_norm u v)))
    (integrable_exp_neg_mul_sq (show (0 : Real) < 2 / Real.pi ^ 2 by positivity))
    (Filter.Eventually.of_forall (fun v : Real => tendsto_deBruijnF1ScaledDensity v))
  rw [integral_complex_ofReal, deBruijn_real_gaussian_integral] at h
  exact h

end

end Erdos1212Kernel
