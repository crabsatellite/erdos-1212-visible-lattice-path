import Erdos1212Kernel.IwaniecXiRounding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

/-- The exact parameter in Iwaniec 1971: `log y/(log log(3y))^(11/5)`. -/
def iwaniecPaperXi (level : Real) : Real :=
  Real.log level / (Real.log (Real.log (3 * level))) ^ (11 / 5 : Real)

theorem tendsto_iwaniecLogLog_atTop :
    Tendsto (fun level : Real => Real.log (Real.log level)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

theorem tendsto_iwaniecShiftedLogLog_difference :
    Tendsto (fun level : Real =>
      Real.log (Real.log (3 * level)) - Real.log (Real.log level)) atTop (nhds 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log (Real.log 3)).comp
    Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with level hlevel
  rw [Real.log_mul (by norm_num) hlevel.ne']
  simp only [Function.comp_apply, add_comm]

theorem eventually_iwaniecXi_denominator_bound :
    ∀ᶠ level : Real in atTop,
      1 < level ∧ 1 ≤ Real.log (Real.log level) ∧
      0 < Real.log (Real.log (3 * level)) ∧
      (Real.log (Real.log (3 * level))) ^ (11 / 5 : Real) ≤
        8 * Real.log (Real.log level) ^ 3 := by
  have hsmall := tendsto_iwaniecShiftedLogLog_difference.eventually
    (gt_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [eventually_gt_atTop (1 : Real),
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (1 : Real)), hsmall]
    with level hlevel ht hdiff
  have hlogLevel : Real.log level ≤ Real.log (3 * level) :=
    Real.log_le_log (zero_lt_one.trans hlevel) (by linarith)
  have hlu : Real.log (Real.log level) ≤ Real.log (Real.log (3 * level)) :=
    Real.log_le_log (Real.log_pos hlevel) hlogLevel
  have huPos : 0 < Real.log (Real.log (3 * level)) := by linarith
  have huUpper : Real.log (Real.log (3 * level)) ≤ 2 * Real.log (Real.log level) := by
    linarith
  refine ⟨hlevel, ht, huPos, ?_⟩
  calc
    (Real.log (Real.log (3 * level))) ^ (11 / 5 : Real) ≤
        (2 * Real.log (Real.log level)) ^ (11 / 5 : Real) :=
      Real.rpow_le_rpow huPos.le huUpper (by norm_num)
    _ ≤ (2 * Real.log (Real.log level)) ^ (3 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = 8 * Real.log (Real.log level) ^ 3 := by
      norm_num [mul_pow]

theorem tendsto_iwaniecLog_over_loglog_four_atTop :
    Tendsto (fun level : Real =>
      Real.log level / (8 * Real.log (Real.log level) ^ 4)) atTop atTop := by
  have hzero : Tendsto (fun level : Real =>
      8 * Real.log (Real.log level) ^ 4 / Real.log level) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      Real.tendsto_log_atTop
    have h8 := h.const_mul 8
    simpa only [Function.comp_def, one_mul, add_zero, mul_zero, ← mul_div_assoc] using h8
  have hpos : ∀ᶠ level : Real in atTop,
      0 < 8 * Real.log (Real.log level) ^ 4 / Real.log level := by
    filter_upwards [eventually_gt_atTop (1 : Real),
      tendsto_iwaniecLogLog_atTop.eventually (eventually_gt_atTop (0 : Real))]
      with level hlevel ht
    have hlog := Real.log_pos hlevel
    positivity
  have hwithin : Tendsto (fun level : Real =>
      8 * Real.log (Real.log level) ^ 4 / Real.log level)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  simpa only [Function.comp_def, inv_div] using hinv

theorem eventually_iwaniecPaperXi_div_loglog_lower :
    ∀ᶠ level : Real in atTop,
      Real.log level / (8 * Real.log (Real.log level) ^ 4) ≤
        iwaniecPaperXi level / Real.log (Real.log level) := by
  filter_upwards [eventually_iwaniecXi_denominator_bound] with level hlevel
  obtain ⟨hy, ht, hu, hden⟩ := hlevel
  have htPos : 0 < Real.log (Real.log level) := by linarith
  have hpowPos : 0 < (Real.log (Real.log (3 * level))) ^ (11 / 5 : Real) :=
    Real.rpow_pos_of_pos hu _
  have hdenMul : (Real.log (Real.log (3 * level))) ^ (11 / 5 : Real) *
      Real.log (Real.log level) ≤ 8 * Real.log (Real.log level) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hden htPos.le
    nlinarith
  have hdiv := div_le_div_of_nonneg_left (Real.log_pos hy).le
    (mul_pos hpowPos htPos) hdenMul
  simpa only [iwaniecPaperXi, div_div] using hdiv

theorem tendsto_iwaniecPaperXi_div_loglog_atTop :
    Tendsto (fun level : Real => iwaniecPaperXi level / Real.log (Real.log level))
      atTop atTop :=
  tendsto_atTop_mono' atTop eventually_iwaniecPaperXi_div_loglog_lower
    tendsto_iwaniecLog_over_loglog_four_atTop

theorem tendsto_iwaniecPaperXi_atTop :
    Tendsto iwaniecPaperXi atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_iwaniecPaperXi_div_loglog_atTop
  filter_upwards [eventually_iwaniecXi_denominator_bound] with level hlevel
  obtain ⟨hy, ht, hu, hden⟩ := hlevel
  have hxi : 0 ≤ iwaniecPaperXi level := by
    unfold iwaniecPaperXi
    exact div_nonneg (Real.log_pos hy).le (Real.rpow_nonneg hu.le _)
  exact div_le_self hxi ht

theorem eventually_iwaniecPaperXiSplit_ge_six_loglog :
    ∀ᶠ level : Real in atTop,
      6 * Real.log (Real.log level) ≤ iwaniecXiSplit (iwaniecPaperXi level) := by
  have hxiLog : Tendsto (fun level : Real => Real.log (iwaniecPaperXi level))
      atTop atTop := Real.tendsto_log_atTop.comp tendsto_iwaniecPaperXi_atTop
  filter_upwards [hxiLog.eventually (eventually_ge_atTop (2 : Real)),
    tendsto_iwaniecPaperXi_div_loglog_atTop.eventually (eventually_ge_atTop (12 : Real)),
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (1 : Real))]
    with level hlog hratio ht
  have htPos : 0 < Real.log (Real.log level) := by linarith
  have hlarge := (le_div_iff₀ htPos).1 hratio
  have hxiPos : 0 ≤ iwaniecPaperXi level := by linarith
  have hhalf : iwaniecPaperXi level / Real.log (iwaniecPaperXi level) ≤
      iwaniecPaperXi level / 2 :=
    div_le_div_of_nonneg_left hxiPos (by norm_num) hlog
  unfold iwaniecXiSplit
  linarith

end

end Erdos1212Kernel
