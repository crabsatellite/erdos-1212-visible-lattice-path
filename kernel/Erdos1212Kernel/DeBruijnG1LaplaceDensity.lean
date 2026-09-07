import Erdos1212Kernel.DeBruijnG1RealPhase
import Erdos1212Kernel.DeBruijnAdjointPrincipalValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

def deBruijnG1LaplaceDensity (u b x : Real) : Real :=
  Real.exp (-deBruijnRealSaddlePhase u x) * Real.exp (b * x) / x

/-- Exact transport of the two source cases b=1 and b=0, without changing
the saddle parameter u or losing the pole factor 1/x. -/
theorem deBruijnG1LaplaceDensity_source (u b x : Real) :
    deBruijn1951AdjointDensity (u - 1 + b) x = deBruijnG1LaplaceDensity u b x := by
  unfold deBruijn1951AdjointDensity deBruijn1951AdjointNumerator deBruijnG1LaplaceDensity deBruijnRealSaddlePhase
  rw [← Real.exp_add]
  congr 2
  ring

theorem deBruijnG1LaplaceDensity_pos (u b : Real) {x : Real} (hx : 0 < x) :
    0 < deBruijnG1LaplaceDensity u b x := by
  unfold deBruijnG1LaplaceDensity
  exact div_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hx

theorem deBruijnG1LaplaceDensity_integrable (u b : Real) {a : Real} (ha : 0 < a) :
    IntegrableOn (deBruijnG1LaplaceDensity u b) (Set.Ioi a) := by
  have h := deBruijn1951AdjointDensity_integrable_positive (u - 1 + b) ha
  apply h.congr_fun _ measurableSet_Ioi
  intro x _hx
  exact deBruijnG1LaplaceDensity_source u b x

end

end Erdos1212Kernel
