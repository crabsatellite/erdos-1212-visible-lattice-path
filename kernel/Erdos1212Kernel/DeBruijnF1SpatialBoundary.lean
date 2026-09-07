import Erdos1212Kernel.DeBruijnF1ShiftBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1_upper_ray_hasDerivAt (u : Complex) (x : Real) :
    HasDerivAt (fun y : Real => deBruijnF1Integrand u ((y : Complex) + (Real.pi : Complex) * Complex.I))
      (deBruijnF1SpatialFlux u ((x : Complex) + (Real.pi : Complex) * Complex.I)) x := by
  have hl : HasDerivAt (fun y : Real => (y : Complex) + (Real.pi : Complex) * Complex.I) (1 : Complex) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((Real.pi : Complex) * Complex.I)
  have h := (deBruijnF1Integrand_hasDerivAt u ((x : Complex) + (Real.pi : Complex) * Complex.I)).comp x hl
  simpa only [mul_one, deBruijnF1SpatialFlux] using h

theorem deBruijnF1_lower_ray_hasDerivAt (u : Complex) (x : Real) :
    HasDerivAt (fun y : Real => deBruijnF1Integrand u ((y : Complex) - (Real.pi : Complex) * Complex.I))
      (deBruijnF1SpatialFlux u ((x : Complex) - (Real.pi : Complex) * Complex.I)) x := by
  have hl : HasDerivAt (fun y : Real => (y : Complex) - (Real.pi : Complex) * Complex.I) (1 : Complex) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const ((Real.pi : Complex) * Complex.I)
  have h := (deBruijnF1Integrand_hasDerivAt u ((x : Complex) - (Real.pi : Complex) * Complex.I)).comp x hl
  simpa only [mul_one, deBruijnF1SpatialFlux] using h

theorem deBruijnF1_vertical_hasDerivAt (u : Complex) (x : Real) :
    HasDerivAt (fun y : Real => deBruijnF1Integrand u ((y : Complex) * Complex.I))
      (deBruijnF1SpatialFlux u ((x : Complex) * Complex.I) * Complex.I) x := by
  have hl : HasDerivAt (fun y : Real => (y : Complex) * Complex.I) Complex.I x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
  have h := (deBruijnF1Integrand_hasDerivAt u ((x : Complex) * Complex.I)).comp x hl
  simpa only [deBruijnF1SpatialFlux] using h

theorem tendsto_deBruijnF1_gaussian :
    Tendsto (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) atTop (nhds 0) := by
  have hs : Tendsto (fun x : Real => (1 / 16 : Real) * x ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : Nat) ≠ 0)).const_mul_atTop (by norm_num)
  simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs

theorem tendsto_deBruijnF1_upper_ray (u : Complex) :
    Tendsto (fun x : Real => deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun x : Real => deBruijnF1RayAmplitude ‖u‖ * Real.exp (-(1 / 16 : Real) * x ^ 2))
  · filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    exact deBruijnF1Integrand_upper_ray_bound hx le_rfl
  · simpa only [mul_zero] using tendsto_deBruijnF1_gaussian.const_mul (deBruijnF1RayAmplitude ‖u‖)

theorem tendsto_deBruijnF1_lower_ray (u : Complex) :
    Tendsto (fun x : Real => deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := fun x : Real => deBruijnF1RayAmplitude ‖u‖ * Real.exp (-(1 / 16 : Real) * x ^ 2))
  · filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    exact deBruijnF1Integrand_lower_ray_bound hx le_rfl
  · simpa only [mul_zero] using tendsto_deBruijnF1_gaussian.const_mul (deBruijnF1RayAmplitude ‖u‖)

theorem deBruijnF1SpatialFlux_upper_integral (u : Complex) :
    (∫ x in Set.Ioi (0 : Real), deBruijnF1SpatialFlux u ((x : Complex) + (Real.pi : Complex) * Complex.I)) =
      -deBruijnF1Integrand u ((Real.pi : Complex) * Complex.I) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    ((deBruijnF1Integrand_continuous u).comp (Complex.continuous_ofReal.add continuous_const)).continuousAt.continuousWithinAt
    (fun x _hx => deBruijnF1_upper_ray_hasDerivAt u x)
    (deBruijnF1SpatialFlux_upper_ray_integrable u) (tendsto_deBruijnF1_upper_ray u)
  simpa only [zero_sub, Function.comp_apply, Pi.add_apply, Complex.ofReal_zero, zero_add] using h

theorem deBruijnF1SpatialFlux_lower_integral (u : Complex) :
    (∫ x in Set.Ioi (0 : Real), deBruijnF1SpatialFlux u ((x : Complex) - (Real.pi : Complex) * Complex.I)) =
      -deBruijnF1Integrand u (-((Real.pi : Complex) * Complex.I)) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    ((deBruijnF1Integrand_continuous u).comp (Complex.continuous_ofReal.sub continuous_const)).continuousAt.continuousWithinAt
    (fun x _hx => deBruijnF1_lower_ray_hasDerivAt u x)
    (deBruijnF1SpatialFlux_lower_ray_integrable u) (tendsto_deBruijnF1_lower_ray u)
  simpa only [Function.comp_apply, Complex.ofReal_zero, zero_sub] using h

theorem deBruijnF1SpatialFlux_vertical_integral (u : Complex) :
    (∫ x in (-Real.pi)..Real.pi, deBruijnF1SpatialFlux u ((x : Complex) * Complex.I) * Complex.I) =
      deBruijnF1Integrand u ((Real.pi : Complex) * Complex.I) - deBruijnF1Integrand u (-((Real.pi : Complex) * Complex.I)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _hx => deBruijnF1_vertical_hasDerivAt u x)
    (deBruijnF1SpatialFlux_vertical_integrable u)
  simpa only [Complex.ofReal_neg, neg_mul] using h

end

end Erdos1212Kernel
