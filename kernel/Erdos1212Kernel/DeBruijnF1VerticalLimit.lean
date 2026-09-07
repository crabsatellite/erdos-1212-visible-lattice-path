import Erdos1212Kernel.DeBruijnF1ScaledDensity
import Erdos1212Kernel.DeBruijnF1SaddlePieces

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1ScaledDensity_integral_rescale (u : Real) :
    (∫ v : Real, deBruijnF1ScaledDensity u v) = (Real.sqrt (deBruijnSaddleCurvature u) : Complex) *
      ((∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand (u : Complex)
        ((deBruijnSaddle u : Complex) + (t : Complex) * Complex.I)) /
        deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) := by
  let s := Real.sqrt (deBruijnSaddleCurvature u)
  let f := fun v : Real => deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + ((v / s : Real) : Complex) * Complex.I) /
    deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)
  have hs : 0 < s := Real.sqrt_pos.mpr (deBruijnSaddleCurvature_pos u)
  have hR : -(Real.pi * s) ≤ Real.pi * s := by nlinarith [Real.pi_pos]
  have hD : (∫ v : Real, deBruijnF1ScaledDensity u v) = ∫ v in (-(Real.pi * s))..(Real.pi * s), f v := by
    change (∫ v : Real, (Set.Icc (-(Real.pi * s)) (Real.pi * s)).indicator f v) = _
    rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hR]
  have hscale := intervalIntegral.smul_integral_comp_mul_right (a := -Real.pi) (b := Real.pi) (f := f) s
  simp only [neg_mul] at hscale
  have hfun : (fun t : Real => f (t * s)) = (fun t : Real => deBruijnF1Integrand (u : Complex)
      ((deBruijnSaddle u : Complex) + (t : Complex) * Complex.I) /
      deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)) := by
    funext t
    dsimp [f]
    rw [mul_div_cancel_right₀ _ hs.ne']
  rw [hD, ← hscale, Complex.real_smul, hfun, intervalIntegral.integral_div]

theorem deBruijnF1SaddleVertical_normalized (u : Real) :
    (Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1SaddleVertical u / (deBruijnSaddleHeight u : Complex) =
      Complex.I * ∫ v : Real, deBruijnF1ScaledDensity u v := by
  rw [deBruijnF1ScaledDensity_integral_rescale, deBruijnF1Integrand_saddle_value]
  unfold deBruijnF1SaddleVertical
  rw [intervalIntegral.integral_mul_const]
  ring

/-- The limit of the entire original shifted vertical segment, with its
differential, Jacobian, and amplitude retained. -/
theorem tendsto_deBruijnF1SaddleVertical_normalized :
    Tendsto (fun u : Real => (Real.sqrt (deBruijnSaddleCurvature u) : Complex) * deBruijnF1SaddleVertical u /
      (deBruijnSaddleHeight u : Complex)) atTop (nhds (Complex.I * (Real.sqrt (2 * Real.pi) : Complex))) := by
  have h := tendsto_deBruijnF1ScaledDensity_integral.const_mul Complex.I
  apply h.congr'
  filter_upwards with u
  exact (deBruijnF1SaddleVertical_normalized u).symm

end

end Erdos1212Kernel
