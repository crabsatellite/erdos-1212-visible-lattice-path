import Erdos1212Kernel.IwaniecAuxSharpExponent

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniec_tendsto_sub_two : Tendsto (fun s : Real => s - 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b + 2)] with s hs
  linarith

theorem iwaniec_tendsto_shift_ratio : Tendsto (fun s : Real => (s - 2) / s) atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : Real))).sub
    ((tendsto_const_nhds (x := (2 : Real))).div_atTop tendsto_id)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with s hs
  change 1 - 2 / s = (s - 2) / s
  field_simp

theorem iwaniec_tendsto_inverse_shift_ratio : Tendsto (fun s : Real => s / (s - 2)) atTop (nhds 1) := by
  simpa only [inv_div, inv_one] using iwaniec_tendsto_shift_ratio.inv₀ (by norm_num : (1 : Real) ≠ 0)

theorem iwaniec_tendsto_log_shift_difference :
    Tendsto (fun s : Real => Real.log s - Real.log (s - 2)) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp iwaniec_tendsto_inverse_shift_ratio
  rw [Real.log_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3 : Real)] with s hs
  exact Real.log_div (by linarith : s ≠ 0) (by linarith : s - 2 ≠ 0)

theorem iwaniec_tendsto_log_shift_ratio :
    Tendsto (fun s : Real => Real.log s / Real.log (s - 2)) atTop (nhds 1) := by
  have hlag : Tendsto (fun s : Real => Real.log (s - 2)) atTop atTop := Real.tendsto_log_atTop.comp iwaniec_tendsto_sub_two
  have h := (tendsto_const_nhds (x := (1 : Real))).add (iwaniec_tendsto_log_shift_difference.div_atTop hlag)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3 : Real)] with s hs
  have hL := Real.log_pos (show 1 < s - 2 by linarith)
  field_simp [hL.ne']
  <;> ring

theorem iwaniec_tendsto_loglog_shift_difference :
    Tendsto (fun s : Real => Real.log (Real.log s) - Real.log (Real.log (s - 2))) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp iwaniec_tendsto_log_shift_ratio
  rw [Real.log_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3 : Real)] with s hs
  exact Real.log_div (Real.log_pos (show 1 < s by linarith)).ne' (Real.log_pos (show 1 < s - 2 by linarith)).ne'

/-- The literal s-2 shift in the source upper bound costs o(s) in the
main exponent. Its two logarithmic components are both retained. -/
theorem iwaniecAuxSharpExponent_shift_difference :
    Tendsto (fun s : Real => (iwaniecAuxSharpExponent s - iwaniecAuxSharpExponent (s - 2)) / s) atTop (nhds 0) := by
  have hlog : Tendsto (fun s : Real => Real.log s / s) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_deBruijn_log_power_div 1
  have h := ((hlog.add iwaniec_tendsto_loglog_div_self).const_mul 2).add
    (iwaniec_tendsto_shift_ratio.mul (iwaniec_tendsto_log_shift_difference.add iwaniec_tendsto_loglog_shift_difference))
  simp only [zero_add, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with s hs
  unfold iwaniecAuxSharpExponent
  field_simp
  <;> ring

end

end Erdos1212Kernel
