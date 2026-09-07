import Erdos1212Kernel.IwaniecAuxiliaryXiRange

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

theorem iwaniecAuxSZero_log_ge_one {s : Real} (hs : iwaniecAuxSZero < s) : 1 ≤ Real.log s := by
  have hC := iwaniecAuxCorollaryConstant_gt_three_hundred
  have hb : 1 ≤ 120 * iwaniecAuxCorollaryConstant := by linarith
  have hp := Real.self_le_rpow_of_one_le hb (by norm_num : (1 : Real) ≤ 5 / 2)
  have hlog := iwaniecAuxSZero_log_threshold hs
  linarith

/-- Source xi-scale inequality, including the finite-level side condition:
`s>s0` and `s<=xi(y)` imply all its needed logarithms have the right sign. -/
theorem iwaniecAuxRange_log_power_scale
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    s ^ 2 * Real.log s ^ (22 / 5 : Real) ≤ Real.log level ^ 2 := by
  let u := Real.log (Real.log (3 * level))
  have hu : 0 < u := by
    have h := iwaniecAuxRange_loglog_gt_one hy hs hxi
    dsimp [u]
    linarith
  have hsPos : 0 < s := by linarith [iwaniecAuxSZero_large]
  have hv := iwaniecAuxSZero_log_ge_one hs
  have hvu := iwaniecAuxRange_log_le_shiftedLogLog hy hs hxi
  have hp := Real.rpow_le_rpow (show 0 ≤ Real.log s by linarith) hvu
    (show (0 : Real) ≤ 22 / 5 by norm_num)
  have hpow : 0 < u ^ (11 / 5 : Real) := Real.rpow_pos_of_pos hu _
  have hxi' : s ≤ Real.log level / u ^ (11 / 5 : Real) := hxi
  have hprod := (le_div_iff₀ hpow).mp hxi'
  have hprodNonneg : 0 ≤ s * u ^ (11 / 5 : Real) := mul_nonneg hsPos.le hpow.le
  have hsq := pow_le_pow_left₀ hprodNonneg hprod 2
  have hpowSq : (u ^ (11 / 5 : Real)) ^ 2 = u ^ (22 / 5 : Real) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hu.le]
    norm_num
  rw [mul_pow, hpowSq] at hsq
  exact (mul_le_mul_of_nonneg_left hp (sq_nonneg s)).trans hsq

theorem iwaniecAuxRange_normalized_scale
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    (s ^ 2 / Real.log level ^ 2) * Real.log s ^ (22 / 5 : Real) ≤ 1 := by
  have h := iwaniecAuxRange_log_power_scale hy hs hxi
  rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos (Real.log_pos hy))]
  exact h

end

end Erdos1212Kernel
