import Erdos1212Kernel.TaoZetaPoleRemovedBounds

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

theorem norm_logDeriv_taoZetaPoleRemoved_le_off_center
    {α t R E : Real} {z : Complex}
    (hα : 1 < α) (hR : 0 < R)
    (hz : z ∈ ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3))
    (hHnz : ∀ w ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R,
      taoZetaPoleRemoved w ≠ 0)
    (hHupper : ∀ w ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R,
      ‖taoZetaPoleRemoved w‖ ≤ E) :
    ‖logDeriv taoZetaPoleRemoved z‖ ≤
      24 * (1 + Real.log E - Real.log (α - 1) +
        4 * Real.log (1 + 1 / (α - 1))) / R := by
  let c : Complex := (α : Complex) + (t : Complex) * Complex.I
  let M : Real := 1 + Real.log E - Real.log (α - 1) +
    4 * Real.log (1 + 1 / (α - 1))
  have hc : c ∈ ball c R := mem_ball_self hR
  have hHc : taoZetaPoleRemoved c ≠ 0 := hHnz c hc
  have hHcpos : 0 < ‖taoZetaPoleRemoved c‖ := norm_pos_iff.mpr hHc
  have hEpos : 0 < E := hHcpos.trans_le (hHupper c hc)
  have hcenterLower : Real.log (α - 1) -
      4 * Real.log (1 + 1 / (α - 1)) ≤
      Real.log ‖taoZetaPoleRemoved c‖ := by
    simpa only [c] using log_norm_taoZetaPoleRemoved_center_lower hα
  have hcenterUpper : Real.log ‖taoZetaPoleRemoved c‖ ≤ Real.log E :=
    Real.log_le_log hHcpos (hHupper c hc)
  have hM : 0 < M := by
    dsimp only [M]
    linarith
  have hdiff : DifferentiableOn Complex taoZetaPoleRemoved (ball c R) := by
    intro w _hw
    exact (analyticAt_taoZetaPoleRemoved_global w).differentiableAt.differentiableWithinAt
  have hlogNorm : ∀ w ∈ ball c R,
      Real.log ‖taoZetaPoleRemoved w‖ -
        Real.log ‖taoZetaPoleRemoved c‖ ≤ M := by
    intro w hw
    have hHw : taoZetaPoleRemoved w ≠ 0 := hHnz w hw
    have hHwpos : 0 < ‖taoZetaPoleRemoved w‖ := norm_pos_iff.mpr hHw
    have hupper : Real.log ‖taoZetaPoleRemoved w‖ ≤ Real.log E :=
      Real.log_le_log hHwpos (hHupper w hw)
    dsimp only [M]
    linarith
  have hmain :=
    norm_logDeriv_le_twenty_four_mul_div_of_log_norm_sub_le_of_mem_third
      hR hM hdiff hHnz hlogNorm hz
  simpa only [M, c] using hmain

theorem norm_taoZetaLogDerivative_le_of_poleRemoved_bound
    {s : Complex} (hs : s ≠ 1) (hzeta : riemannZeta s ≠ 0)
    {B : Real} (hB : ‖logDeriv taoZetaPoleRemoved s‖ ≤ B) :
    ‖taoZetaLogDerivative s‖ ≤ 1 / ‖s - 1‖ + B := by
  rw [taoZetaLogDerivative_eq_inv_sub_logDeriv_poleRemoved_of_ne_zero hs hzeta]
  calc
    ‖1 / (s - 1) - logDeriv taoZetaPoleRemoved s‖ ≤
        ‖1 / (s - 1)‖ + ‖logDeriv taoZetaPoleRemoved s‖ := norm_sub_le _ _
    _ ≤ 1 / ‖s - 1‖ + B := by
      rw [norm_div, norm_one]
      exact add_le_add le_rfl hB

end

end Erdos1212Kernel
