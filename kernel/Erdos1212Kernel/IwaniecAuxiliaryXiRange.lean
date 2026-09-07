import Erdos1212Kernel.IwaniecXiScaleGrowth
import Erdos1212Kernel.IwaniecAuxiliaryCorollary
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

/-- The literal lower threshold in source Lemma 11. -/
def iwaniecAuxSZero : Real := Real.exp ((120 * iwaniecAuxCorollaryConstant) ^ (5 / 2 : Real))

theorem iwaniecAuxSZero_large : (12288 : Real) < iwaniecAuxSZero := by
  have hC := iwaniecAuxCorollaryConstant_gt_three_hundred
  have hb : 1 ≤ 120 * iwaniecAuxCorollaryConstant := by linarith
  have hp := Real.self_le_rpow_of_one_le hb (by norm_num : (1 : Real) ≤ 5 / 2)
  have he := Real.add_one_le_exp ((120 * iwaniecAuxCorollaryConstant) ^ (5 / 2 : Real))
  unfold iwaniecAuxSZero
  linarith

theorem iwaniecAuxSZero_log_threshold {s : Real} (hs : iwaniecAuxSZero < s) :
    (120 * iwaniecAuxCorollaryConstant) ^ (5 / 2 : Real) < Real.log s := by
  have h := Real.log_lt_log (Real.exp_pos ((120 * iwaniecAuxCorollaryConstant) ^ (5 / 2 : Real))) hs
  simpa only [iwaniecAuxSZero, Real.log_exp] using h

theorem iwaniecAuxSZero_log_two_fifths {s : Real} (hs : iwaniecAuxSZero < s) :
    120 * iwaniecAuxCorollaryConstant < Real.log s ^ (2 / 5 : Real) := by
  have hC := iwaniecAuxCorollaryConstant_gt_three_hundred
  have hb : 0 ≤ 120 * iwaniecAuxCorollaryConstant := by linarith
  have h := Real.rpow_lt_rpow (Real.rpow_nonneg hb _) (iwaniecAuxSZero_log_threshold hs)
    (by norm_num : (0 : Real) < 2 / 5)
  rw [← Real.rpow_mul hb] at h
  norm_num at h
  exact h

theorem log_three_ge_sixteen_fifteenths : (16 / 15 : Real) ≤ Real.log 3 := by
  have htwo := Real.le_log_one_add_of_nonneg (show (0 : Real) ≤ 1 by norm_num)
  have hhalf := Real.le_log_one_add_of_nonneg (show (0 : Real) ≤ 1 / 2 by norm_num)
  norm_num at htwo hhalf
  have heq : Real.log (3 : Real) = Real.log (3 / 2 : Real) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (3 / 2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    norm_num
  linarith

theorem loglog_three_ge_two_thirty_firsts : (2 / 31 : Real) ≤ Real.log (Real.log 3) := by
  have h := Real.le_log_one_add_of_nonneg (show (0 : Real) ≤ 1 / 15 by norm_num)
  norm_num at h
  exact h.trans (Real.log_le_log (by norm_num : (0 : Real) < 16 / 15) log_three_ge_sixteen_fifteenths)

theorem iwaniecShiftedLogLog_gt_sixteenth {level : Real} (hy : 1 < level) :
    (1 / 16 : Real) < Real.log (Real.log (3 * level)) := by
  have hlog3 : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hinner : Real.log (3 : Real) ≤ Real.log (3 * level) :=
    Real.log_le_log (by norm_num) (by linarith)
  have houter := Real.log_le_log hlog3 hinner
  linarith [loglog_three_ge_two_thirty_firsts]

theorem iwaniecPaperXi_le_small_when_loglog_small
    {level : Real} (hy : 1 < level) (hu : Real.log (Real.log (3 * level)) ≤ 1) :
    iwaniecPaperXi level ≤ 12288 := by
  let u := Real.log (Real.log (3 * level))
  have huLower : (1 / 16 : Real) < u := iwaniecShiftedLogLog_gt_sixteenth hy
  have huPos : 0 < u := by linarith
  have huOne : u ≤ 1 := hu
  have hpow : (1 / 4096 : Real) ≤ u ^ (11 / 5 : Real) := by
    have hcube : (1 / 4096 : Real) ≤ u ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 1 / 16) huLower.le 3
      norm_num at h
      exact h
    have hexponent := Real.rpow_le_rpow_of_exponent_ge huPos huOne (show (11 / 5 : Real) ≤ 3 by norm_num)
    norm_num at hexponent
    exact hcube.trans hexponent
  have hlogInner : 0 < Real.log (3 * level) := Real.log_pos (by linarith)
  have hupperInner : Real.log (3 * level) ≤ Real.exp 1 := by
    have h := Real.exp_le_exp.mpr hu
    rw [Real.exp_log hlogInner] at h
    exact h
  have hL : Real.log level < 3 :=
    (Real.log_le_log (by linarith : 0 < level) (by linarith : level ≤ 3 * level)).trans_lt
      (hupperInner.trans_lt Real.exp_one_lt_three)
  unfold iwaniecPaperXi
  change Real.log level / u ^ (11 / 5 : Real) ≤ 12288
  rw [div_le_iff₀ (Real.rpow_pos_of_pos huPos _)]
  linarith

theorem iwaniecAuxRange_loglog_gt_one
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    1 < Real.log (Real.log (3 * level)) := by
  by_contra hnot
  have hsmall := iwaniecPaperXi_le_small_when_loglog_small hy (le_of_not_gt hnot)
  linarith [iwaniecAuxSZero_large]

theorem iwaniecAuxRange_log_le_shiftedLogLog
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero < s) (hxi : s ≤ iwaniecPaperXi level) :
    Real.log s ≤ Real.log (Real.log (3 * level)) := by
  have hu := iwaniecAuxRange_loglog_gt_one hy hs hxi
  have hden : 1 ≤ Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) :=
    Real.one_le_rpow hu.le (by norm_num)
  have hL := Real.log_pos hy
  have hxiL : iwaniecPaperXi level ≤ Real.log level := by
    exact div_le_self hL.le hden
  have hsPos : 0 < s := by linarith [iwaniecAuxSZero_large]
  have hLUpper : Real.log level ≤ Real.log (3 * level) := Real.log_le_log (by linarith) (by linarith)
  exact Real.log_le_log hsPos ((hxi.trans hxiL).trans hLUpper)

end

end Erdos1212Kernel
