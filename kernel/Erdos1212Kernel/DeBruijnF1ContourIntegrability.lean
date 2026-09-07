import Erdos1212Kernel.DeBruijnF1Integrand
import Erdos1212Kernel.DeBruijnF1RayBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1RayAmplitude (M : Real) : Real := Real.exp (deBruijnF1RayConstant + Real.pi * M + 4 * M ^ 2)

theorem deBruijnF1Integrand_norm_of_ray_phase {u z : Complex} {x M : Real}
    (hM : ‖u‖ ≤ M) (hnorm : ‖z‖ ≤ x + Real.pi)
    (hphase : (deBruijnComplexExpIntegral z).re ≤ deBruijnF1RayConstant - x ^ 2 / 8) :
    ‖deBruijnF1Integrand u z‖ ≤ deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg u).trans hM
  have hneg : (-u * z).re ≤ M * (x + Real.pi) := by
    calc
      _ ≤ ‖-u * z‖ := Complex.re_le_norm _
      _ = ‖u‖ * ‖z‖ := by rw [norm_mul, norm_neg]
      _ ≤ _ := mul_le_mul hM hnorm (norm_nonneg z) hM0
  unfold deBruijnF1Integrand deBruijnF1RayAmplitude
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Complex.add_re]
  nlinarith [sq_nonneg (x - 8 * M)]

theorem deBruijnF1Integrand_upper_ray_bound {u : Complex} {x M : Real} (hx : 0 ≤ x) (hM : ‖u‖ ≤ M) :
    ‖deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2) :=
  deBruijnF1Integrand_norm_of_ray_phase hM (deBruijnF1_upper_ray_norm hx) (deBruijnF1RayPhase_upper_bound hx)

theorem deBruijnF1Integrand_lower_ray_bound {u : Complex} {x M : Real} (hx : 0 ≤ x) (hM : ‖u‖ ≤ M) :
    ‖deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnF1RayAmplitude M * Real.exp (-(1 / 16 : Real) * x ^ 2) := by
  apply deBruijnF1Integrand_norm_of_ray_phase hM (deBruijnF1_lower_ray_norm hx)
  rw [deBruijnF1_lower_ray_phase_re]
  exact deBruijnF1RayPhase_upper_bound hx

theorem deBruijnF1_upper_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have hm := hg.const_mul (deBruijnF1RayAmplitude ‖u‖)
  apply hm.mono'
  · exact ((deBruijnF1Integrand_continuous u).comp (Complex.continuous_ofReal.add continuous_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1Integrand_upper_ray_bound hx.le le_rfl

theorem deBruijnF1_lower_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have hm := hg.const_mul (deBruijnF1RayAmplitude ‖u‖)
  apply hm.mono'
  · exact ((deBruijnF1Integrand_continuous u).comp (Complex.continuous_ofReal.sub continuous_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1Integrand_lower_ray_bound hx.le le_rfl

theorem deBruijnF1_vertical_integrable (u : Complex) :
    IntervalIntegrable (fun t : Real => deBruijnF1Integrand u ((t : Complex) * Complex.I) * Complex.I) volume (-Real.pi) Real.pi :=
  (((deBruijnF1Integrand_continuous u).comp (Complex.continuous_ofReal.mul_const Complex.I)).mul_const Complex.I).intervalIntegrable _ _

end

end Erdos1212Kernel
