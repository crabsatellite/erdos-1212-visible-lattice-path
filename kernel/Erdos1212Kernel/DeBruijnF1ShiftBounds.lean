import Erdos1212Kernel.DeBruijnF1Shift

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnF1ShiftAverage_norm {u z : Complex} {C : Real}
    (hbound : ∀ t ∈ Set.Icc (0 : Real) 1, ‖deBruijnF1Integrand (u - (t : Complex)) z‖ ≤ C) :
    ‖deBruijnF1ShiftAverage u z‖ ≤ C := by
  rw [deBruijnF1ShiftAverage_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : Real)) (b := 1)
    (f := fun t : Real => deBruijnF1Integrand (u - (t : Complex)) z) (C := C) (by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
      exact hbound t ⟨ht.1.le, ht.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using h

theorem deBruijnF1ShiftAverage_upper_ray_bound (u : Complex) {x : Real} (hx : 0 ≤ x) :
    ‖deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnF1RayAmplitude (‖u‖ + 1) * Real.exp (-(1 / 16 : Real) * x ^ 2) := by
  apply deBruijnF1ShiftAverage_norm
  intro t ht
  exact deBruijnF1Integrand_upper_ray_bound hx (deBruijnF1_shift_parameter_norm u ht)

theorem deBruijnF1ShiftAverage_lower_ray_bound (u : Complex) {x : Real} (hx : 0 ≤ x) :
    ‖deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)‖ ≤
      deBruijnF1RayAmplitude (‖u‖ + 1) * Real.exp (-(1 / 16 : Real) * x ^ 2) := by
  apply deBruijnF1ShiftAverage_norm
  intro t ht
  exact deBruijnF1Integrand_lower_ray_bound hx (deBruijnF1_shift_parameter_norm u ht)

theorem deBruijnF1ShiftAverage_upper_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  apply (hg.const_mul (deBruijnF1RayAmplitude (‖u‖ + 1))).mono'
  · exact ((deBruijnF1ShiftAverage_continuous u).comp (Complex.continuous_ofReal.add continuous_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1ShiftAverage_upper_ray_bound u hx.le

theorem deBruijnF1ShiftAverage_lower_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  apply (hg.const_mul (deBruijnF1RayAmplitude (‖u‖ + 1))).mono'
  · exact ((deBruijnF1ShiftAverage_continuous u).comp (Complex.continuous_ofReal.sub continuous_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deBruijnF1ShiftAverage_lower_ray_bound u hx.le

theorem deBruijnF1ShiftAverage_vertical_integrable (u : Complex) :
    IntervalIntegrable (fun t : Real => deBruijnF1ShiftAverage u ((t : Complex) * Complex.I) * Complex.I) volume (-Real.pi) Real.pi :=
  (((deBruijnF1ShiftAverage_continuous u).comp (Complex.continuous_ofReal.mul_const Complex.I)).mul_const Complex.I).intervalIntegrable _ _

theorem deBruijnF1SpatialFlux_upper_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1SpatialFlux u ((x : Complex) + (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  apply (((deBruijnF1_upper_ray_integrable u).const_mul (-u)).add (deBruijnF1ShiftAverage_upper_ray_integrable u)).congr
  filter_upwards with x
  exact (deBruijnF1SpatialFlux_eq u _).symm

theorem deBruijnF1SpatialFlux_lower_ray_integrable (u : Complex) :
    IntegrableOn (fun x : Real => deBruijnF1SpatialFlux u ((x : Complex) - (Real.pi : Complex) * Complex.I)) (Set.Ioi (0 : Real)) := by
  apply (((deBruijnF1_lower_ray_integrable u).const_mul (-u)).add (deBruijnF1ShiftAverage_lower_ray_integrable u)).congr
  filter_upwards with x
  exact (deBruijnF1SpatialFlux_eq u _).symm

theorem deBruijnF1SpatialFlux_vertical_integrable (u : Complex) :
    IntervalIntegrable (fun t : Real => deBruijnF1SpatialFlux u ((t : Complex) * Complex.I) * Complex.I) volume (-Real.pi) Real.pi :=
  (((deBruijnF1SpatialFlux_continuous u).comp (Complex.continuous_ofReal.mul_const Complex.I)).mul_const Complex.I).intervalIntegrable _ _

end

end Erdos1212Kernel
