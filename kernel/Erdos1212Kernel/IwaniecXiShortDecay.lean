import Erdos1212Kernel.IwaniecPaperAXiPoint

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem iwaniecPaperXi_log
    {level : Real} (hlevel : 1 < level)
    (hu : 0 < Real.log (Real.log (3 * level))) :
    Real.log (iwaniecPaperXi level) =
      Real.log (Real.log level) -
        (11 / 5 : Real) * Real.log (Real.log (Real.log (3 * level))) := by
  unfold iwaniecPaperXi
  rw [Real.log_div (Real.log_pos hlevel).ne' (Real.rpow_pos_of_pos hu _).ne',
    Real.log_rpow hu]

theorem eventually_iwaniecLog_two_xi_le_shiftedLogLog :
    ∀ᶠ level : Real in atTop,
      Real.log (2 * iwaniecPaperXi level) ≤ Real.log (Real.log (3 * level)) := by
  filter_upwards [eventually_iwaniecXi_denominator_bound,
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (2 : Real))]
    with level hdata ht
  obtain ⟨hy, htOne, hu, hden⟩ := hdata
  have hlogLevel : Real.log level ≤ Real.log (3 * level) :=
    Real.log_le_log (zero_lt_one.trans hy) (by linarith)
  have hlu : Real.log (Real.log level) ≤ Real.log (Real.log (3 * level)) :=
    Real.log_le_log (Real.log_pos hy) hlogLevel
  have huTwo : 2 ≤ Real.log (Real.log (3 * level)) := ht.trans hlu
  have hlogu : Real.log 2 ≤ Real.log (Real.log (Real.log (3 * level))) :=
    Real.log_le_log (by norm_num) huTwo
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxiPos : 0 < iwaniecPaperXi level :=
    div_pos (Real.log_pos hy) (Real.rpow_pos_of_pos hu _)
  rw [Real.log_mul (by norm_num) hxiPos.ne', iwaniecPaperXi_log hy hu]
  nlinarith

/-- Exact source-scale comparison for the short sum. -/
theorem eventually_iwaniecXi_short_exponent_bound :
    ∀ᶠ level : Real in atTop,
      iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real) ≤
        Real.log level / Real.log (2 * iwaniecPaperXi level) := by
  filter_upwards [eventually_iwaniecXi_denominator_bound,
    eventually_iwaniecLog_two_xi_le_shiftedLogLog,
    tendsto_iwaniecPaperXi_atTop.eventually (eventually_gt_atTop (1 : Real))]
    with level hdata hlogUpper hxi
  obtain ⟨hy, ht, hu, hden⟩ := hdata
  have hxiPos : 0 < iwaniecPaperXi level := zero_lt_one.trans hxi
  have hlogXiPos : 0 < Real.log (iwaniecPaperXi level) := Real.log_pos hxi
  have hlogOrder : Real.log (iwaniecPaperXi level) ≤
      Real.log (2 * iwaniecPaperXi level) :=
    Real.log_le_log hxiPos (by linarith)
  have hlogTwoPos : 0 < Real.log (2 * iwaniecPaperXi level) :=
    hlogXiPos.trans_le hlogOrder
  have hpowLow := Real.rpow_le_rpow hlogXiPos.le hlogOrder
    (show (0 : Real) ≤ 6 / 5 by norm_num)
  have hpowHigh := Real.rpow_le_rpow hlogTwoPos.le hlogUpper
    (show (0 : Real) ≤ 11 / 5 by norm_num)
  have hquot := div_le_div_of_nonneg_right hpowHigh hlogTwoPos.le
  have hidentity : Real.log (2 * iwaniecPaperXi level) ^ (6 / 5 : Real) =
      Real.log (2 * iwaniecPaperXi level) ^ (11 / 5 : Real) /
        Real.log (2 * iwaniecPaperXi level) := by
    convert Real.rpow_sub_one hlogTwoPos.ne' (11 / 5 : Real) using 1 <;> norm_num
  have hbase : Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real) ≤
      Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) /
        Real.log (2 * iwaniecPaperXi level) := by
    exact hpowLow.trans (by rw [hidentity]; exact hquot)
  have hscaled := mul_le_mul_of_nonneg_left hbase hxiPos.le
  have hcancel : iwaniecPaperXi level *
      Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) = Real.log level := by
    unfold iwaniecPaperXi
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hu _).ne'
  rwa [← mul_div_assoc, hcancel] at hscaled

theorem eventually_iwaniecXiShortMajorant_source_bound :
    ∀ᶠ level : Real in atTop,
      iwaniecXiShortMajorant level ≤
        level * Real.exp
          (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real) +
            iwaniecPaperXi level) := by
  have hexpXi := (Real.tendsto_exp_atTop.comp tendsto_iwaniecPaperXi_atTop).eventually
    (eventually_ge_atTop (3 : Real))
  filter_upwards [eventually_iwaniecXi_short_exponent_bound,
    eventually_gt_atTop (1 : Real), hexpXi] with level hexponent hlevel hthree
  have hdecay : Real.exp (-Real.log level / Real.log (2 * iwaniecPaperXi level)) ≤
      Real.exp (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real)) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hexponent using 1 <;> ring
  unfold iwaniecXiShortMajorant
  calc
    3 * level * Real.exp (-Real.log level / Real.log (2 * iwaniecPaperXi level)) ≤
        3 * level * Real.exp
          (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ ≤ Real.exp (iwaniecPaperXi level) *
        (level * Real.exp (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real))) := by
      have h := mul_le_mul_of_nonneg_right hthree
        (show 0 ≤ level * Real.exp
          (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) ^ (6 / 5 : Real)) by positivity)
      convert h using 1 <;> ring
    _ = _ := by rw [Real.exp_add]; ring

end

end Erdos1212Kernel
