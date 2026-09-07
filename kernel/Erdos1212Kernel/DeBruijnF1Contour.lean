import Erdos1212Kernel.DeBruijnF1ContourIntegrability

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

def deBruijnF1LowerIntegral (u : Complex) : Complex :=
  ∫ x in Set.Ioi (0 : Real), deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)

def deBruijnF1UpperIntegral (u : Complex) : Complex :=
  ∫ x in Set.Ioi (0 : Real), deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)

def deBruijnF1VerticalIntegral (u : Complex) : Complex :=
  ∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand u ((t : Complex) * Complex.I) * Complex.I

/-- W follows the lower ray from infinity to -pi*i, the vertical segment
upward, and the upper ray out to infinity. Each component's absolute
integrability has been proved in the imported module. -/
def deBruijnF1ContourIntegral (u : Complex) : Complex :=
  -deBruijnF1LowerIntegral u + deBruijnF1VerticalIntegral u + deBruijnF1UpperIntegral u

/-- The literal normalized contour formula (2.4), for complex u. -/
def deBruijnF1Complex (u : Complex) : Complex :=
  (1 / (2 * (Real.pi : Complex) * Complex.I)) * deBruijnF1ContourIntegral u

theorem deBruijnF1LowerIntegral_conj (u : Complex) :
    deBruijnF1LowerIntegral (starRingEnd Complex u) = starRingEnd Complex (deBruijnF1UpperIntegral u) := by
  unfold deBruijnF1LowerIntegral deBruijnF1UpperIntegral
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  dsimp only
  rw [← deBruijnF1_ray_conj]
  exact deBruijnF1Integrand_conj u _

theorem deBruijnF1UpperIntegral_conj (u : Complex) :
    deBruijnF1UpperIntegral (starRingEnd Complex u) = starRingEnd Complex (deBruijnF1LowerIntegral u) := by
  have h := congrArg (starRingEnd Complex) (deBruijnF1LowerIntegral_conj (starRingEnd Complex u))
  simpa only [starRingEnd_apply, star_star] using h.symm

theorem deBruijnF1VerticalIntegral_conj (u : Complex) :
    deBruijnF1VerticalIntegral (starRingEnd Complex u) = -starRingEnd Complex (deBruijnF1VerticalIntegral u) := by
  have hflip : (∫ t in (-Real.pi)..Real.pi,
      deBruijnF1Integrand (starRingEnd Complex u) (((-t : Real) : Complex) * Complex.I) * Complex.I) =
      deBruijnF1VerticalIntegral (starRingEnd Complex u) := by
    have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
      (f := fun t : Real => deBruijnF1Integrand (starRingEnd Complex u) ((t : Complex) * Complex.I) * Complex.I)
    simpa only [neg_neg, deBruijnF1VerticalIntegral] using h
  have hconj : (∫ t in (-Real.pi)..Real.pi,
      starRingEnd Complex (deBruijnF1Integrand u ((t : Complex) * Complex.I) * Complex.I)) =
      starRingEnd Complex (deBruijnF1VerticalIntegral u) := by
    simpa only [Complex.conjCLE_apply, deBruijnF1VerticalIntegral] using
      Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm (deBruijnF1_vertical_integrable u)
  calc
    _ = ∫ t in (-Real.pi)..Real.pi,
        deBruijnF1Integrand (starRingEnd Complex u) (((-t : Real) : Complex) * Complex.I) * Complex.I := hflip.symm
    _ = ∫ t in (-Real.pi)..Real.pi, -starRingEnd Complex (deBruijnF1Integrand u ((t : Complex) * Complex.I) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      have hz : starRingEnd Complex ((t : Complex) * Complex.I) = ((-t : Real) : Complex) * Complex.I := by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
        ring
      rw [← hz, deBruijnF1Integrand_conj]
      simp only [map_mul, Complex.conj_I]
      ring
    _ = _ := by rw [intervalIntegral.integral_neg, hconj]

theorem deBruijnF1ContourIntegral_conj (u : Complex) :
    deBruijnF1ContourIntegral (starRingEnd Complex u) = -starRingEnd Complex (deBruijnF1ContourIntegral u) := by
  unfold deBruijnF1ContourIntegral
  rw [deBruijnF1LowerIntegral_conj, deBruijnF1VerticalIntegral_conj, deBruijnF1UpperIntegral_conj]
  simp only [map_add, map_neg]
  ring

theorem deBruijnF1Complex_conj (u : Complex) :
    deBruijnF1Complex (starRingEnd Complex u) = starRingEnd Complex (deBruijnF1Complex u) := by
  have hc : starRingEnd Complex (1 / (2 * (Real.pi : Complex) * Complex.I)) =
      -(1 / (2 * (Real.pi : Complex) * Complex.I)) := by
    simp only [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, mul_neg, div_neg]
  unfold deBruijnF1Complex
  rw [deBruijnF1ContourIntegral_conj, map_mul, hc]
  ring

def deBruijnF1 (u : Real) : Real := (deBruijnF1Complex (u : Complex)).re

/-- The real-valued F1 is identified with the full complex contour
integral, not merely assigned its real part without justification. -/
theorem deBruijnF1_ofReal (u : Real) : (deBruijnF1 u : Complex) = deBruijnF1Complex (u : Complex) := by
  have h := deBruijnF1Complex_conj (u : Complex)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_re.mp h.symm

end

end Erdos1212Kernel
