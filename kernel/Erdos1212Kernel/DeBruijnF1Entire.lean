import Erdos1212Kernel.DeBruijnF1ContourDerivatives

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

def deBruijnF1ComplexDerivative (u : Complex) : Complex :=
  (1 / (2 * (Real.pi : Complex) * Complex.I)) *
    (-(∫ x in Set.Ioi (0 : Real), -((x : Complex) - (Real.pi : Complex) * Complex.I) *
        deBruijnF1Integrand u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
      (∫ t in (-Real.pi)..Real.pi,
        (-((t : Complex) * Complex.I) * deBruijnF1Integrand u ((t : Complex) * Complex.I)) * Complex.I) +
      (∫ x in Set.Ioi (0 : Real), -((x : Complex) + (Real.pi : Complex) * Complex.I) *
        deBruijnF1Integrand u ((x : Complex) + (Real.pi : Complex) * Complex.I)))

/-- The source F1 is complex differentiable at every complex parameter,
with differentiation under the three literal contour integrals justified. -/
theorem deBruijnF1Complex_hasDerivAt (u : Complex) :
    HasDerivAt deBruijnF1Complex (deBruijnF1ComplexDerivative u) u := by
  have h := (((deBruijnF1LowerIntegral_hasDerivAt u).neg.add (deBruijnF1VerticalIntegral_hasDerivAt u)).add
    (deBruijnF1UpperIntegral_hasDerivAt u)).const_mul (1 / (2 * (Real.pi : Complex) * Complex.I))
  exact h

theorem deBruijnF1Complex_differentiable : Differentiable Complex deBruijnF1Complex :=
  fun u => (deBruijnF1Complex_hasDerivAt u).differentiableAt

theorem deBruijnF1Complex_continuous : Continuous deBruijnF1Complex :=
  deBruijnF1Complex_differentiable.continuous

theorem deBruijnF1_hasDerivAt (u : Real) :
    HasDerivAt deBruijnF1 (deBruijnF1ComplexDerivative (u : Complex)).re u :=
  (deBruijnF1Complex_hasDerivAt (u : Complex)).real_of_complex

theorem deBruijnF1_continuous : Continuous deBruijnF1 :=
  continuous_iff_continuousAt.mpr (fun u => (deBruijnF1_hasDerivAt u).continuousAt)

end

end Erdos1212Kernel
