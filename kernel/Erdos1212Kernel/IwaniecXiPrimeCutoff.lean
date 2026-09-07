import Erdos1212Kernel.IwaniecXiShortDecay

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

def iwaniecXiPrimeCutoff (level : Real) : Real :=
  Real.exp (Real.log level / (iwaniecPaperXi level - 1))

theorem iwaniecShiftedLogLog_ge_logLog
    {level : Real} (hlevel : 1 < level) :
    Real.log (Real.log level) ≤ Real.log (Real.log (3 * level)) := by
  apply Real.log_le_log (Real.log_pos hlevel)
  exact Real.log_le_log (zero_lt_one.trans hlevel) (by linarith)

theorem tendsto_iwaniecShiftedLogLog_atTop :
    Tendsto (fun level : Real => Real.log (Real.log (3 * level))) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_iwaniecLogLog_atTop
  filter_upwards [eventually_gt_atTop (1 : Real)] with level hlevel
  exact iwaniecShiftedLogLog_ge_logLog hlevel

theorem iwaniecLogLevel_div_xi
    {level : Real} (hlevel : 1 < level)
    (hu : 0 < Real.log (Real.log (3 * level))) :
    Real.log level / iwaniecPaperXi level =
      Real.log (Real.log (3 * level)) ^ (11 / 5 : Real) := by
  unfold iwaniecPaperXi
  field_simp [(Real.log_pos hlevel).ne', (Real.rpow_pos_of_pos hu _).ne']

theorem tendsto_iwaniecXiPrimeCutoff_log_atTop :
    Tendsto (fun level : Real => Real.log level / (iwaniecPaperXi level - 1))
      atTop atTop := by
  have hpow := (tendsto_rpow_atTop (show (0 : Real) < 11 / 5 by norm_num)).comp
    tendsto_iwaniecShiftedLogLog_atTop
  apply tendsto_atTop_mono' atTop _ hpow
  filter_upwards [eventually_iwaniecXi_denominator_bound,
    tendsto_iwaniecPaperXi_atTop.eventually (eventually_gt_atTop (1 : Real))]
    with level hdata hxi
  obtain ⟨hy, ht, hu, hden⟩ := hdata
  dsimp only [Function.comp_def]
  rw [← iwaniecLogLevel_div_xi hy hu]
  exact div_le_div_of_nonneg_left (Real.log_pos hy).le (by linarith) (by linarith)

theorem tendsto_iwaniecXiPrimeCutoff_atTop :
    Tendsto iwaniecXiPrimeCutoff atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_iwaniecXiPrimeCutoff_log_atTop

theorem eventually_iwaniecXiPrimeCutoff_loglog_upper :
    ∀ᶠ level : Real in atTop,
      Real.log (Real.log (iwaniecXiPrimeCutoff level)) ≤
        Real.log 2 + (11 / 5 : Real) * Real.log (Real.log (Real.log (3 * level))) := by
  filter_upwards [eventually_iwaniecXi_denominator_bound,
    tendsto_iwaniecPaperXi_atTop.eventually (eventually_ge_atTop (2 : Real))]
    with level hdata hxi
  obtain ⟨hy, ht, hu, hden⟩ := hdata
  have hxiPos : 0 < iwaniecPaperXi level := by linarith
  have hxiSub : 0 < iwaniecPaperXi level - 1 := by linarith
  have hratio : Real.log level / (iwaniecPaperXi level - 1) ≤
      2 * (Real.log level / iwaniecPaperXi level) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hxiSub hxiPos]
    nlinarith [Real.log_pos hy]
  rw [iwaniecLogLevel_div_xi hy hu] at hratio
  have hlog := Real.log_le_log (div_pos (Real.log_pos hy) hxiSub) hratio
  unfold iwaniecXiPrimeCutoff
  rw [Real.log_exp]
  rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hu _).ne', Real.log_rpow hu] at hlog

theorem eventually_iwaniecXiPrimeReciprocal_loglog_bound :
    ∀ᶠ level : Real in atTop,
      iwaniecStrictPrimeReciprocalSum (iwaniecXiPrimeCutoff level) ≤
        20 * (1 + Real.log (Real.log (Real.log level))) := by
  have hM := tendsto_iwaniecXiPrimeCutoff_atTop.eventually
    eventually_iwaniecStrictPrimeReciprocalSum_le_three_loglog
  have hdiff := tendsto_iwaniecShiftedLogLog_difference.eventually
    (gt_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [hM, hdiff, eventually_iwaniecXi_denominator_bound,
    eventually_iwaniecXiPrimeCutoff_loglog_upper]
    with level hM hdiff hdata hcutoff
  obtain ⟨hy, ht, hu, hden⟩ := hdata
  have huUpper : Real.log (Real.log (3 * level)) ≤ 2 * Real.log (Real.log level) := by
    linarith
  have hlogu := Real.log_le_log hu huUpper
  have htPos : 0 < Real.log (Real.log level) := by linarith
  rw [Real.log_mul (by norm_num) htPos.ne'] at hlogu
  have hlogt : 0 ≤ Real.log (Real.log (Real.log level)) := Real.log_nonneg ht
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    linarith
  have hrecip := hM (iwaniecXiPrimeCutoff level) le_rfl
  linarith

theorem tendsto_iwaniecLog_over_sqrt_zero :
    Tendsto (fun t : Real => 60 * (1 + Real.log t) / Real.sqrt t) atTop (nhds 0) := by
  have hlog : Tendsto (fun t : Real => Real.log t / Real.sqrt t) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 / 2 : Real)) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.sqrt_eq_rpow] using h
  have hone : Tendsto (fun t : Real => (1 : Real) / Real.sqrt t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have h := (hone.add hlog).const_mul 60
  simpa only [add_zero, mul_zero, ← add_div, ← mul_div_assoc] using h

/-- Retain the actual prime cutoff of the paper's far point.  Its reciprocal
sum is much smaller than the upper bound at `y` itself. -/
theorem eventually_iwaniecXiPrimeReciprocal_exp_le_sqrt_loglog :
    ∀ᶠ level : Real in atTop,
      Real.exp 1 * iwaniecStrictPrimeReciprocalSum (iwaniecXiPrimeCutoff level) ≤
        Real.sqrt (Real.log (Real.log level)) := by
  have hsmall := (tendsto_iwaniecLog_over_sqrt_zero.comp tendsto_iwaniecLogLog_atTop).eventually
    (gt_mem_nhds (show (0 : Real) < 1 by norm_num))
  filter_upwards [eventually_iwaniecXiPrimeReciprocal_loglog_bound, hsmall,
    tendsto_iwaniecLogLog_atTop.eventually (eventually_ge_atTop (1 : Real))]
    with level hM hsmall ht
  have hMNonneg : 0 ≤ iwaniecStrictPrimeReciprocalSum (iwaniecXiPrimeCutoff level) :=
    Finset.sum_nonneg (fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have heM : Real.exp 1 * iwaniecStrictPrimeReciprocalSum (iwaniecXiPrimeCutoff level) ≤
      60 * (1 + Real.log (Real.log (Real.log level))) := by
    have he := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hMNonneg
    linarith
  have hroot : 0 < Real.sqrt (Real.log (Real.log level)) := Real.sqrt_pos.mpr (by linarith)
  have hbound := (div_lt_iff₀ hroot).1 hsmall
  exact heM.trans (by linarith)

end

end Erdos1212Kernel
