import Erdos1212Kernel.DeBruijnSaddleLogWindow
import Erdos1212Kernel.DeBruijnLogIterationEstimate
import Mathlib.Analysis.Asymptotics.Defs

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

def deBruijnSaddleLogMain (u : Real) : Real :=
  Real.log u + Real.log (Real.log u) + Real.log (Real.log u) / Real.log u

def deBruijnSaddleLogErrorScale (u : Real) : Real :=
  (Real.log (Real.log u)) ^ 2 / (Real.log u) ^ 2

theorem deBruijnSaddle_log_expansion_bound {u : Real} (hu : 1 < u) (hL : 4 ≤ Real.log u)
    (hl : 1 ≤ Real.log (Real.log u)) (hU : (Real.log u) ^ 2 ≤ u) :
    |deBruijnSaddle u - deBruijnSaddleLogMain u| ≤ 10 * deBruijnSaddleLogErrorScale u := by
  have hL0 : 0 < Real.log u := by linarith
  have hξ1 : 1 ≤ deBruijnSaddle u := by linarith [deBruijnSaddle_log_lower hu]
  have hδ : deBruijnSaddleLogCorrection u ≤ 1 / (Real.log u) ^ 2 :=
    (deBruijnSaddleLogCorrection_le_inverse hu hξ1).trans (one_div_le_one_div_of_le (sq_pos_of_pos hL0) hU)
  have hid := deBruijnSaddle_log_split hu
  rw [deBruijnSaddle_log_increment_identity hu hL0] at hid
  have hiter : deBruijnSaddle u = Real.log u + Real.log (Real.log u) +
      Real.log (1 + (deBruijnSaddle u - Real.log u) / Real.log u) + deBruijnSaddleLogCorrection u := by linarith
  have hwidth := deBruijnSaddle_log_width hu hL hU
  have h := deBruijn_log_iteration_estimate hL hl (deBruijnSaddleLogCorrection_bounds hu).1 hδ hwidth.1 hwidth.2 hiter
  simpa only [deBruijnSaddleLogMain, deBruijnSaddleLogErrorScale, mul_div_assoc] using h

theorem eventually_deBruijnSaddle_log_expansion_bound :
    ∀ᶠ u : Real in atTop, |deBruijnSaddle u - deBruijnSaddleLogMain u| ≤ 10 * deBruijnSaddleLogErrorScale u := by
  have hloglog : Tendsto (fun u : Real => Real.log (Real.log u)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : Real), Real.tendsto_log_atTop.eventually_ge_atTop 4,
    hloglog.eventually_ge_atTop 1, eventually_deBruijn_log_square_le] with u hu hL hl hU
  exact deBruijnSaddle_log_expansion_bound hu hL hl hU

theorem deBruijnSaddle_log_expansion :
    Asymptotics.IsBigO atTop (fun u : Real => deBruijnSaddle u - deBruijnSaddleLogMain u) deBruijnSaddleLogErrorScale := by
  apply Asymptotics.IsBigO.of_bound 10
  filter_upwards [eventually_deBruijnSaddle_log_expansion_bound] with u hu
  have he : 0 ≤ deBruijnSaddleLogErrorScale u := div_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg he] using hu

end

end Erdos1212Kernel
