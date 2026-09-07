import Erdos1212Kernel.DeBruijnLogPrimitiveCalculus

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

theorem eventually_deBruijn_log_cube_le : ∀ᶠ u : Real in atTop, (Real.log u) ^ 3 ≤ u := by
  have h := (tendsto_deBruijn_log_power_div 3).eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [h, eventually_gt_atTop (0 : Real)] with u hu hu0
  have hmul := (div_lt_iff₀ hu0).mp hu
  simpa only [one_mul] using hmul.le

theorem eventually_deBruijnRhoLogErrorScale_ge_log :
    ∀ᶠ u : Real in atTop, Real.log u ≤ deBruijnRhoLogErrorScale u := by
  have hloglog : Tendsto (fun u : Real => Real.log (Real.log u)) atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (0 : Real), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hloglog.eventually_ge_atTop 1, eventually_deBruijn_log_cube_le] with u hu hL hl hcube
  have hL0 : 0 < Real.log u := by linarith
  have hlSq : 1 ≤ (Real.log (Real.log u)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlSq hu.le
  unfold deBruijnRhoLogErrorScale
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hL0)]
  nlinarith

theorem tendsto_deBruijnRhoLogErrorScale : Tendsto deBruijnRhoLogErrorScale atTop atTop :=
  tendsto_atTop_mono' atTop eventually_deBruijnRhoLogErrorScale_ge_log Real.tendsto_log_atTop

end

end Erdos1212Kernel
