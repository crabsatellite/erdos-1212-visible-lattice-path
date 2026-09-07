import Erdos1212Kernel.DeBruijnF1SpatialBoundary
import Erdos1212Kernel.DeBruijnF1Contour

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1_upper_balance (u : Complex) :
    u * deBruijnF1UpperIntegral u =
      (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) +
        deBruijnF1Integrand u ((Real.pi : Complex) * Complex.I) := by
  have hiG := (deBruijnF1_upper_ray_integrable u).const_mul (-u)
  have hiQ := deBruijnF1ShiftAverage_upper_ray_integrable u
  have hlin : (∫ x in Set.Ioi (0 : Real), deBruijnF1SpatialFlux u ((x : Complex) + (Real.pi : Complex) * Complex.I)) =
      -u * deBruijnF1UpperIntegral u + ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I) := by
    calc
      _ = ∫ x in Set.Ioi (0 : Real), -u * deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I) +
          deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        exact deBruijnF1SpatialFlux_eq u _
      _ = _ := by rw [MeasureTheory.integral_add hiG hiQ, MeasureTheory.integral_const_mul]; rfl
  have h := deBruijnF1SpatialFlux_upper_integral u
  rw [hlin] at h
  calc
    _ = (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) -
        (-u * deBruijnF1UpperIntegral u + ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) := by ring
    _ = _ := by rw [h]; ring

theorem deBruijnF1_lower_balance (u : Complex) :
    u * deBruijnF1LowerIntegral u =
      (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
        deBruijnF1Integrand u (-((Real.pi : Complex) * Complex.I)) := by
  have hiG := (deBruijnF1_lower_ray_integrable u).const_mul (-u)
  have hiQ := deBruijnF1ShiftAverage_lower_ray_integrable u
  have hlin : (∫ x in Set.Ioi (0 : Real), deBruijnF1SpatialFlux u ((x : Complex) - (Real.pi : Complex) * Complex.I)) =
      -u * deBruijnF1LowerIntegral u + ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I) := by
    calc
      _ = ∫ x in Set.Ioi (0 : Real), -u * deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I) +
          deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        exact deBruijnF1SpatialFlux_eq u _
      _ = _ := by rw [MeasureTheory.integral_add hiG hiQ, MeasureTheory.integral_const_mul]; rfl
  have h := deBruijnF1SpatialFlux_lower_integral u
  rw [hlin] at h
  calc
    _ = (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) -
        (-u * deBruijnF1LowerIntegral u + ∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) := by ring
    _ = _ := by rw [h]; ring

theorem deBruijnF1_vertical_balance (u : Complex) :
    u * deBruijnF1VerticalIntegral u =
      (∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I) -
        deBruijnF1Integrand u ((Real.pi : Complex) * Complex.I) + deBruijnF1Integrand u (-((Real.pi : Complex) * Complex.I)) := by
  have hiG := (deBruijnF1_vertical_integrable u).const_mul (-u)
  have hiQ := deBruijnF1ShiftAverage_vertical_integrable u
  have hlin : (∫ x in (-Real.pi)..Real.pi, deBruijnF1SpatialFlux u ((x : Complex) * Complex.I) * Complex.I) =
      -u * deBruijnF1VerticalIntegral u + ∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I := by
    calc
      _ = ∫ x in (-Real.pi)..Real.pi, -u * (deBruijnF1Integrand u ((x : Complex) * Complex.I) * Complex.I) +
          deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only
        rw [deBruijnF1SpatialFlux_eq]
        ring
      _ = _ := by rw [intervalIntegral.integral_add hiG hiQ, intervalIntegral.integral_const_mul]; rfl
  have h := deBruijnF1SpatialFlux_vertical_integral u
  rw [hlin] at h
  calc
    _ = (∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I) -
        (-u * deBruijnF1VerticalIntegral u + ∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I) := by ring
    _ = _ := by rw [h]; ring

theorem deBruijnF1ContourIntegral_balance (u : Complex) :
    u * deBruijnF1ContourIntegral u =
      -(∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
      (∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I) +
      (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) := by
  unfold deBruijnF1ContourIntegral
  rw [mul_add, mul_add, mul_neg, deBruijnF1_lower_balance, deBruijnF1_vertical_balance, deBruijnF1_upper_balance]
  ring

end

end Erdos1212Kernel
