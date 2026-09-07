import Erdos1212Kernel.DeBruijnSaddleLogExpansion
import Erdos1212Kernel.DeBruijnLogPrimitiveCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem deBruijnRhoLogErrorDerivative_lower {u : Real} (hL : 4 ≤ Real.log u) (hl : 1 ≤ Real.log (Real.log u)) :
    deBruijnSaddleLogErrorScale u / 2 ≤ deBruijnRhoLogErrorDerivative u := by
  have hL0 : 0 < Real.log u := by linarith
  have hl0 : 0 ≤ Real.log (Real.log u) := by linarith
  have hw : 0 ≤ deBruijnSaddleLogErrorScale u := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hi : 2 / Real.log u ≤ (1 / 2 : Real) := (div_le_iff₀ hL0).mpr (by linarith)
  have hprod := mul_le_mul_of_nonneg_left (show (1 / 2 : Real) ≤ 1 - 2 / Real.log u by linarith) hw
  have htail : 0 ≤ 2 * Real.log (Real.log u) / (Real.log u) ^ 3 := by positivity
  unfold deBruijnRhoLogErrorDerivative
  change deBruijnSaddleLogErrorScale u / 2 ≤ deBruijnSaddleLogErrorScale u * (1 - 2 / Real.log u) + _
  linarith

theorem deBruijnRhoLogMainDerivative_remainder {u : Real} (hL : 0 < Real.log u) (hl : 1 ≤ Real.log (Real.log u)) :
    |deBruijnRhoLogMainDerivative u - deBruijnSaddleLogMain u| ≤ deBruijnSaddleLogErrorScale u := by
  have hnum : |2 - Real.log (Real.log u)| ≤ (Real.log (Real.log u)) ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (Real.log (Real.log u) - 1)]
  have he : deBruijnRhoLogMainDerivative u - deBruijnSaddleLogMain u =
      (2 - Real.log (Real.log u)) / (Real.log u) ^ 2 := by
    unfold deBruijnRhoLogMainDerivative deBruijnSaddleLogMain
    ring
  rw [he, abs_div, abs_of_pos (sq_pos_of_pos hL)]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg _)

theorem eventually_deBruijnSaddle_primitive_error_bound :
    ∀ᶠ u : Real in atTop, |deBruijnSaddle u - deBruijnRhoLogMainDerivative u| ≤ 22 * deBruijnRhoLogErrorDerivative u := by
  have hloglog : Tendsto (fun u : Real => Real.log (Real.log u)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_deBruijnSaddle_log_expansion_bound, Real.tendsto_log_atTop.eventually_ge_atTop 4,
    hloglog.eventually_ge_atTop 1] with u hu hL hl
  have hrem := deBruijnRhoLogMainDerivative_remainder (by linarith : 0 < Real.log u) hl
  have hderiv := deBruijnRhoLogErrorDerivative_lower hL hl
  have htri : |deBruijnSaddle u - deBruijnRhoLogMainDerivative u| ≤
      |deBruijnSaddle u - deBruijnSaddleLogMain u| + |deBruijnRhoLogMainDerivative u - deBruijnSaddleLogMain u| := by
    have h := abs_add_le (deBruijnSaddle u - deBruijnSaddleLogMain u)
      (-(deBruijnRhoLogMainDerivative u - deBruijnSaddleLogMain u))
    rw [abs_neg, show deBruijnSaddle u - deBruijnSaddleLogMain u + -(deBruijnRhoLogMainDerivative u - deBruijnSaddleLogMain u) =
      deBruijnSaddle u - deBruijnRhoLogMainDerivative u by ring] at h
    exact h
  linarith

end

end Erdos1212Kernel
