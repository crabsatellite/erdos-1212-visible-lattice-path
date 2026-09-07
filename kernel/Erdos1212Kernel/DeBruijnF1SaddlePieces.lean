import Erdos1212Kernel.DeBruijnF1SaddleContour
import Erdos1212Kernel.DeBruijnSaddleGeometry

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

def deBruijnSaddleHeight (u : Real) : Real :=
  Real.exp (-u * deBruijnSaddle u + deBruijn1951ExpIntegral (deBruijnSaddle u))

theorem deBruijnSaddleHeight_pos (u : Real) : 0 < deBruijnSaddleHeight u := Real.exp_pos _

theorem deBruijnF1Integrand_saddle_value (u : Real) :
    deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex) = (deBruijnSaddleHeight u : Complex) := by
  rw [deBruijnF1Integrand_eq_saddlePhase, deBruijnSaddlePhase_ofReal, ← Complex.ofReal_exp]
  rfl

theorem deBruijnF1Integrand_saddle_norm (u : Real) :
    ‖deBruijnF1Integrand (u : Complex) (deBruijnSaddle u : Complex)‖ = deBruijnSaddleHeight u := by
  rw [deBruijnF1Integrand_saddle_value, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (deBruijnSaddleHeight_pos u)]

def deBruijnF1SaddleUpper (u : Real) : Complex :=
  ∫ x in Set.Ioi (deBruijnSaddle u), deBruijnF1Integrand (u : Complex) ((x : Complex) + (Real.pi : Complex) * Complex.I)

def deBruijnF1SaddleLower (u : Real) : Complex :=
  ∫ x in Set.Ioi (deBruijnSaddle u), deBruijnF1Integrand (u : Complex) ((x : Complex) - (Real.pi : Complex) * Complex.I)

def deBruijnF1SaddleVertical (u : Real) : Complex :=
  ∫ t in (-Real.pi)..Real.pi, deBruijnF1Integrand (u : Complex) ((deBruijnSaddle u : Complex) + (t : Complex) * Complex.I) * Complex.I

theorem deBruijnF1_saddle_pieces {u : Real} (hu : 1 < u) :
    deBruijnF1Complex (u : Complex) = (1 / (2 * (Real.pi : Complex) * Complex.I)) *
      (-deBruijnF1SaddleLower u + deBruijnF1SaddleVertical u + deBruijnF1SaddleUpper u) :=
  deBruijnF1Complex_saddle_contour hu

end

end Erdos1212Kernel
