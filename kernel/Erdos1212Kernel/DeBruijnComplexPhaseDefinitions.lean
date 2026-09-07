import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

/-- The source primitive along the straight segment from 0 to z,
including the differential dz=z dt. The quotient's value at 0 has
no effect on this integral. -/
def deBruijnComplexExpIntegral (z : Complex) : Complex :=
  ∫ t in (0 : Real)..1, z * ((Complex.exp ((t : Complex) * z) - 1) / ((t : Complex) * z))

def deBruijnComplexPhaseIntegrand (z : Complex) (t : Real) : Complex :=
  (Complex.exp ((t : Complex) * z) - 1) / (t : Complex)

def deBruijnComplexExpAverage (z : Complex) : Complex :=
  ∫ t in (0 : Real)..1, Complex.exp ((t : Complex) * z)

end

end Erdos1212Kernel
