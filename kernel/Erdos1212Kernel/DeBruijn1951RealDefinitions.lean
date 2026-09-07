import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

/-- The real restriction of the primitive in de Bruijn 1951 (2.4),
retaining its displayed integrand. The value of the quotient at 0 does
not change the integral. -/
def deBruijn1951ExpIntegral (z : Real) : Real :=
  ∫ t in (0 : Real)..z, (Real.exp t - 1) / t

def deBruijnNegativeExpQuot (t : Real) : Real := (Real.exp (-t) - 1) / t

/-- The literal real phi in de Bruijn 1951, equation (2.16). -/
def deBruijn1951Phi (x : Real) : Real := x⁻¹ * Real.exp (-deBruijn1951ExpIntegral (-x))

def deBruijn1951BoundaryKernel (a x : Real) : Real := Real.exp (-a * x) * deBruijn1951Phi x

def deBruijn1951BoundaryAverage (a : Real) : Real := a * ∫ x in Set.Ioi (1 : Real), deBruijn1951BoundaryKernel a x

end

end Erdos1212Kernel
