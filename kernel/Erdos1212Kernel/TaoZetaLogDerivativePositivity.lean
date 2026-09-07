import Erdos1212Kernel.TaoLittlewoodFinalThreshold
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace Erdos1212Kernel

noncomputable section

open scoped ArithmeticFunction

set_option maxHeartbeats 1900000

def taoZetaLogDerivative (s : Complex) : Complex :=
  -deriv riemannZeta s / riemannZeta s

/-- Exact right-half-plane identification used by the de la Vallée
Poussin positivity argument. -/
theorem taoZetaLogDerivative_eq_vonMangoldtLSeries {s : Complex}
    (hs : 1 < s.re) :
    taoZetaLogDerivative s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) s := by
  unfold taoZetaLogDerivative
  exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

theorem taoZeta_three_four_one_identity (θ : Real) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) =
      2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- The literal nonnegative trigonometric polynomial used to combine
the logarithmic derivatives at `σ`, `σ+it`, and `σ+2it`. -/
theorem taoZeta_three_four_one_nonneg (θ : Real) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [taoZeta_three_four_one_identity]
  positivity

end

end Erdos1212Kernel
