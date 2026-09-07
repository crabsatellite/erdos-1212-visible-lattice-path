import Erdos1212Kernel.TaoPerronKernelBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem norm_taoZetaPoleRemoved_le_of_ne_one
    {s : Complex} (hs : s ≠ 1) {C D : Real}
    (hzeta : ‖riemannZeta s‖ ≤ C) (hdist : ‖s - 1‖ ≤ D) :
    ‖taoZetaPoleRemoved s‖ ≤ D * C := by
  rw [taoZetaPoleRemoved_of_ne_one hs, norm_mul]
  have hD0 : 0 ≤ D := (norm_nonneg (s - 1)).trans hdist
  exact mul_le_mul hdist hzeta (norm_nonneg _) hD0

theorem log_norm_taoZetaPoleRemoved_center_lower
    {α t : Real} (hα : 1 < α) :
    Real.log (α - 1) -
        4 * Real.log (1 + 1 / (α - 1)) ≤
      Real.log ‖taoZetaPoleRemoved
        ((α : Complex) + (t : Complex) * Complex.I)‖ := by
  let c : Complex := (α : Complex) + (t : Complex) * Complex.I
  have hc1 : c ≠ 1 := by
    intro hc
    have hre := congrArg Complex.re hc
    simp [c] at hre
    linarith
  have hzeta : riemannZeta c ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [c, hα]
  have hsub : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hsubpos : 0 < ‖c - 1‖ := norm_pos_iff.mpr hsub
  have hzetapos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hzeta
  have hreal : α - 1 ≤ ‖c - 1‖ := by
    have hre := Complex.abs_re_le_norm (c - 1)
    have hα0 : 0 ≤ α - 1 := by linarith
    simpa [c, abs_of_nonneg hα0] using hre
  have hlogSub : Real.log (α - 1) ≤ Real.log ‖c - 1‖ :=
    Real.log_le_log (by linarith) hreal
  have hlogZeta : -4 * Real.log (1 + 1 / (α - 1)) ≤
      Real.log ‖riemannZeta c‖ := by
    simpa only [c] using
      neg_four_mul_log_pseriesBound_le_log_norm_riemannZeta α t hα
  rw [taoZetaPoleRemoved_of_ne_one hc1, norm_mul,
    Real.log_mul hsubpos.ne' hzetapos.ne']
  linarith

theorem log_norm_taoZetaPoleRemoved_le_of_bounds
    {s : Complex} (hs : s ≠ 1) (hH : taoZetaPoleRemoved s ≠ 0)
    {C D : Real} (hC : 0 < C) (hD : 0 < D)
    (hzeta : ‖riemannZeta s‖ ≤ C) (hdist : ‖s - 1‖ ≤ D) :
    Real.log ‖taoZetaPoleRemoved s‖ ≤ Real.log (D * C) := by
  have hHpos : 0 < ‖taoZetaPoleRemoved s‖ := norm_pos_iff.mpr hH
  have hDCpos : 0 < D * C := mul_pos hD hC
  exact Real.log_le_log hHpos
    (norm_taoZetaPoleRemoved_le_of_ne_one hs hzeta hdist)

end

end Erdos1212Kernel
