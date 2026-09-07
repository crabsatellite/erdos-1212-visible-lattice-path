import Erdos1212Kernel.DeBruijnSaddlePoint
import Erdos1212Kernel.DeBruijnSaddleMoment

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The exact psi in the source's saddle-point calculation. -/
def deBruijnSaddlePhase (u : Real) (z : Complex) : Complex := -(u : Complex) * z + deBruijnComplexExpIntegral z

def deBruijnSaddleCurvature (u : Real) : Real := deBruijnSaddleMoment (deBruijnSaddle u)

theorem deBruijnF1Integrand_eq_saddlePhase (u : Real) (z : Complex) :
    deBruijnF1Integrand (u : Complex) z = Complex.exp (deBruijnSaddlePhase u z) := rfl

theorem deBruijnSaddlePhase_ofReal (u x : Real) :
    deBruijnSaddlePhase u (x : Complex) = ((-u * x + deBruijn1951ExpIntegral x : Real) : Complex) := by
  unfold deBruijnSaddlePhase
  rw [deBruijnComplexExpIntegral_ofReal]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]

theorem deBruijnSaddlePhase_hasDerivAt (u : Real) (z : Complex) :
    HasDerivAt (deBruijnSaddlePhase u) (-(u : Complex) + deBruijnComplexExpAverage z) z := by
  have h := ((hasDerivAt_id z).const_mul (-(u : Complex))).add (deBruijnComplexExpIntegral_hasDerivAt z)
  simpa only [mul_one] using h

theorem deBruijnSaddlePhase_deriv (u : Real) (z : Complex) :
    deriv (deBruijnSaddlePhase u) z = -(u : Complex) + deBruijnComplexExpAverage z :=
  (deBruijnSaddlePhase_hasDerivAt u z).deriv

theorem deBruijnSaddlePhase_critical {u : Real} (hu : 1 < u) :
    HasDerivAt (deBruijnSaddlePhase u) 0 (deBruijnSaddle u : Complex) := by
  have h := deBruijnSaddlePhase_hasDerivAt u (deBruijnSaddle u : Complex)
  rw [← deBruijnSaddleAverage_ofReal, deBruijnSaddle_average hu] at h
  simpa only [neg_add_cancel] using h

theorem deBruijnSaddlePhase_second_hasDerivAt (u : Real) (z : Complex) :
    HasDerivAt (deriv (deBruijnSaddlePhase u)) (deBruijnComplexSaddleMoment z) z := by
  have h := (deBruijnComplexExpAverage_hasDerivAt z).const_add (-(u : Complex))
  apply h.congr_of_eventuallyEq
  filter_upwards with w
  exact deBruijnSaddlePhase_deriv u w

theorem deBruijnSaddlePhase_second_at_saddle (u : Real) :
    deriv (deriv (deBruijnSaddlePhase u)) (deBruijnSaddle u : Complex) = (deBruijnSaddleCurvature u : Complex) := by
  rw [(deBruijnSaddlePhase_second_hasDerivAt u (deBruijnSaddle u : Complex)).deriv,
    ← deBruijnSaddleMoment_ofReal]
  rfl

theorem deBruijnSaddleCurvature_pos (u : Real) : 0 < deBruijnSaddleCurvature u := deBruijnSaddleMoment_pos _

theorem deBruijnSaddleCurvature_le {u : Real} (hu : 1 < u) : deBruijnSaddleCurvature u ≤ u := by
  have h := deBruijnSaddleMoment_le_average (deBruijnSaddle u)
  rw [deBruijnSaddle_average hu] at h
  exact h

/-- The exact displayed identity (2.6) for the actual second derivative. -/
theorem deBruijnSaddleCurvature_formula {u : Real} (hu : 1 < u) :
    deBruijnSaddleCurvature u = u - (u - 1) / deBruijnSaddle u := by
  unfold deBruijnSaddleCurvature
  rw [deBruijnSaddleMoment_eq_quot (deBruijnSaddle_pos hu).ne']
  have he : Real.exp (deBruijnSaddle u) = 1 + u * deBruijnSaddle u := by linarith [deBruijnSaddle_equation hu]
  rw [he]
  field_simp [(deBruijnSaddle_pos hu).ne']
  <;> ring

theorem deBruijnSaddleCurvature_ratio {u : Real} (hu : 1 < u) :
    deBruijnSaddleCurvature u / u = 1 - (1 - 1 / u) / deBruijnSaddle u := by
  rw [deBruijnSaddleCurvature_formula hu]
  field_simp [(deBruijnSaddle_pos hu).ne', show u ≠ 0 by linarith]
  <;> ring

end

end Erdos1212Kernel
