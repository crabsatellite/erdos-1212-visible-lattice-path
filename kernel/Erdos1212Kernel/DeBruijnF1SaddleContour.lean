import Erdos1212Kernel.DeBruijnF1Contour
import Erdos1212Kernel.DeBruijnSaddlePoint
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1_upper_tail_integrable (u : Complex) {r : Real} (hr : 0 ≤ r) :
    IntegrableOn (fun x : Real => deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) (Set.Ioi r) :=
  (deBruijnF1_upper_ray_integrable u).mono_set (Set.Ioi_subset_Ioi hr)

theorem deBruijnF1_lower_tail_integrable (u : Complex) {r : Real} (hr : 0 ≤ r) :
    IntegrableOn (fun x : Real => deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) (Set.Ioi r) :=
  (deBruijnF1_lower_ray_integrable u).mono_set (Set.Ioi_subset_Ioi hr)

theorem deBruijnF1_shifted_vertical_integrable (u : Complex) (r : Real) :
    IntervalIntegrable (fun t : Real => deBruijnF1Integrand u ((r : Complex) + (t : Complex) * Complex.I) * Complex.I)
      volume (-Real.pi) Real.pi :=
  (((deBruijnF1Integrand_continuous u).comp (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I))).mul_const Complex.I).intervalIntegrable _ _

theorem deBruijnF1_rectangle_identity (u : Complex) (r : Real) :
    (∫ x in (0 : Real)..r, deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) -
      (∫ x in (0 : Real)..r, deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) +
      (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((r : Complex) + (t : Complex) * Complex.I) * Complex.I) -
      deBruijnF1VerticalIntegral u = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (deBruijnF1Integrand u)
    (⟨0, -Real.pi⟩ : Complex) (⟨r, Real.pi⟩ : Complex)
    (fun z _hz => (deBruijnF1Integrand_hasDerivAt u z).differentiableAt.differentiableWithinAt)
  dsimp only at h
  simp only [Complex.ofReal_zero, Complex.ofReal_neg, neg_mul, zero_add, ← sub_eq_add_neg, smul_eq_mul] at h
  have hvR : (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((r : Complex) + (t : Complex) * Complex.I) * Complex.I) =
      Complex.I * (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((r : Complex) + (t : Complex) * Complex.I)) := by
    rw [intervalIntegral.integral_mul_const]
    ring
  have hvL : deBruijnF1VerticalIntegral u =
      Complex.I * (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((t : Complex) * Complex.I)) := by
    unfold deBruijnF1VerticalIntegral
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [hvR, hvL]
  exact h

/-- The original W contour is moved to the parallel three-piece contour
through r without dropping either infinite tail or changing orientation. -/
theorem deBruijnF1ContourIntegral_deformation (u : Complex) {r : Real} (hr : 0 ≤ r) :
    deBruijnF1ContourIntegral u =
      -(∫ x in Set.Ioi r, deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
      (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((r : Complex) + (t : Complex) * Complex.I) * Complex.I) +
      (∫ x in Set.Ioi r, deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) := by
  have hL := intervalIntegral.integral_interval_add_Ioi (deBruijnF1_lower_ray_integrable u) (deBruijnF1_lower_tail_integrable u hr)
  have hU := intervalIntegral.integral_interval_add_Ioi (deBruijnF1_upper_ray_integrable u) (deBruijnF1_upper_tail_integrable u hr)
  change (∫ x in (0 : Real)..r, deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
    (∫ x in Set.Ioi r, deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) = deBruijnF1LowerIntegral u at hL
  change (∫ x in (0 : Real)..r, deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) +
    (∫ x in Set.Ioi r, deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)) = deBruijnF1UpperIntegral u at hU
  have hrect := sub_eq_zero.mp (deBruijnF1_rectangle_identity u r)
  unfold deBruijnF1ContourIntegral
  rw [← hL, ← hU, ← hrect]
  ring

theorem deBruijnF1Complex_saddle_contour {u : Real} (hu : 1 < u) :
    deBruijnF1Complex (u : Complex) = (1 / (2 * (Real.pi : Complex) * Complex.I)) *
      (-(∫ x in Set.Ioi (deBruijnSaddle u), deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
        (∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + (t : Complex) * Complex.I) * Complex.I) +
        (∫ x in Set.Ioi (deBruijnSaddle u), deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I))) := by
  unfold deBruijnF1Complex
  rw [deBruijnF1ContourIntegral_deformation (u : Complex) (deBruijnSaddle_pos hu).le]

end

end Erdos1212Kernel
