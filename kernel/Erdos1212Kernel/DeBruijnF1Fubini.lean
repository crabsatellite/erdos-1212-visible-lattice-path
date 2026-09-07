import Erdos1212Kernel.DeBruijnF1ProductIntegrability
import Erdos1212Kernel.DeBruijnF1Contour

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnF1UpperIntegral_shift_average (u : Complex) :
    (∫ t in (0 : Real)..1, deBruijnF1UpperIntegral (u - (t : Complex))) =
      ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I) := by
  have hi : Integrable (Function.uncurry (fun t x : Real => deBruijnF1Integrand (u - (t : Complex))
      ((x : Complex) + (Real.pi : Complex) * Complex.I)))
      ((volume.restrict (Set.uIoc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] using deBruijnF1_upper_shift_product_integrable u
  unfold deBruijnF1UpperIntegral
  rw [intervalIntegral_integral_swap hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  exact (deBruijnF1ShiftAverage_eq_integral u _).symm

theorem deBruijnF1LowerIntegral_shift_average (u : Complex) :
    (∫ t in (0 : Real)..1, deBruijnF1LowerIntegral (u - (t : Complex))) =
      ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I) := by
  have hi : Integrable (Function.uncurry (fun t x : Real => deBruijnF1Integrand (u - (t : Complex))
      ((x : Complex) - (Real.pi : Complex) * Complex.I)))
      ((volume.restrict (Set.uIoc (0 : Real) 1)).prod (volume.restrict (Set.Ioi (0 : Real)))) := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] using deBruijnF1_lower_shift_product_integrable u
  unfold deBruijnF1LowerIntegral
  rw [intervalIntegral_integral_swap hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  exact (deBruijnF1ShiftAverage_eq_integral u _).symm

theorem deBruijnF1VerticalIntegral_shift_average (u : Complex) :
    (∫ t in (0 : Real)..1, deBruijnF1VerticalIntegral (u - (t : Complex))) =
      ∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I := by
  have hi : Integrable (Function.uncurry (fun t x : Real =>
      deBruijnF1Integrand (u - (t : Complex)) ((x : Complex) * Complex.I) * Complex.I))
      ((volume.restrict (Set.uIoc (0 : Real) 1)).prod (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] using deBruijnF1_vertical_shift_product_integrable u
  unfold deBruijnF1VerticalIntegral
  simp only [intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
  rw [intervalIntegral_integral_swap hi]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _hx
  dsimp only
  rw [intervalIntegral.integral_mul_const, ← deBruijnF1ShiftAverage_eq_integral]

end

end Erdos1212Kernel
