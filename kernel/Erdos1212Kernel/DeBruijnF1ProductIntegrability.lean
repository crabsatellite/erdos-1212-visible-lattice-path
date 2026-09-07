import Erdos1212Kernel.DeBruijnF1Shift
import Mathlib.MeasureTheory.Integral.Prod

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1_upper_shift_product_integrable (u : Complex) :
    Integrable (fun p : Real × Real => deBruijnF1Integrand (u - (p.1 : Complex))
      ((p.2 : Complex) + (Real.pi : Complex) * Complex.I))
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have hm : Integrable (fun p : Real × Real => deBruijnF1RayAmplitude (‖u‖ + 1) * Real.exp (-(1 / 16 : Real) * p.2 ^ 2))
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) :=
    (hg.const_mul _).comp_snd _
  apply hm.mono'
  · exact (deBruijnF1_shift_joint_continuous u (Complex.continuous_ofReal.add continuous_const)).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
    exact deBruijnF1Integrand_upper_ray_bound hp.2.le (deBruijnF1_shift_parameter_norm u ⟨hp.1.1.le, hp.1.2⟩)

theorem deBruijnF1_lower_shift_product_integrable (u : Complex) :
    Integrable (fun p : Real × Real => deBruijnF1Integrand (u - (p.1 : Complex))
      ((p.2 : Complex) - (Real.pi : Complex) * Complex.I))
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) := by
  have hg : IntegrableOn (fun x : Real => Real.exp (-(1 / 16 : Real) * x ^ 2)) (Set.Ioi (0 : Real)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 16)).integrableOn
  have hm : Integrable (fun p : Real × Real => deBruijnF1RayAmplitude (‖u‖ + 1) * Real.exp (-(1 / 16 : Real) * p.2 ^ 2))
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) :=
    (hg.const_mul _).comp_snd _
  apply hm.mono'
  · exact (deBruijnF1_shift_joint_continuous u (Complex.continuous_ofReal.sub continuous_const)).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
    exact deBruijnF1Integrand_lower_ray_bound hp.2.le (deBruijnF1_shift_parameter_norm u ⟨hp.1.1.le, hp.1.2⟩)

theorem deBruijnF1_vertical_shift_product_integrable (u : Complex) :
    Integrable (fun p : Real × Real => deBruijnF1Integrand (u - (p.1 : Complex)) ((p.2 : Complex) * Complex.I) * Complex.I)
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := by
  let B := Real.exp ((‖u‖ + 1) * Real.pi + Real.pi * Real.exp Real.pi)
  have hB : IntegrableOn (fun _x : Real => B) (Set.Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)).mp _root_.intervalIntegrable_const
  have hm : Integrable (fun _p : Real × Real => B)
      ((volume.restrict (Set.Ioc (0 : Real) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := hB.comp_snd _
  apply hm.mono'
  · exact ((deBruijnF1_shift_joint_continuous u (Complex.continuous_ofReal.mul_const Complex.I)).mul_const Complex.I).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hz : ‖(p.2 : Complex) * Complex.I‖ ≤ Real.pi := by
      simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr ⟨hp.2.1.le, hp.2.2⟩
    have h := deBruijnF1Integrand_norm_on_balls (deBruijnF1_shift_parameter_norm u ⟨hp.1.1.le, hp.1.2⟩) hz
    simpa only [norm_mul, Complex.norm_I, mul_one] using h

end

end Erdos1212Kernel
