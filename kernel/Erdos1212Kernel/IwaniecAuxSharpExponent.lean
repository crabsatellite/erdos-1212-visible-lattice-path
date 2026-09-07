import Erdos1212Kernel.DeBruijnSaddleLogWindow

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

/-- The literal main exponent in Iwaniec 1971, Lemma 9. -/
def iwaniecAuxSharpExponent (s : Real) : Real := s * Real.log s + s * Real.log (Real.log s)

theorem iwaniecAuxSharpExponent_continuousOn : ContinuousOn iwaniecAuxSharpExponent (Set.Ioi (1 : Real)) := by
  intro s hs
  have hs0 : 0 < s := by linarith [hs.out]
  have hL := Real.continuousAt_log hs0.ne'
  have hll := (Real.continuousAt_log (Real.log_pos hs).ne').comp hL
  exact ((continuousAt_id.mul hL).add (continuousAt_id.mul hll)).continuousWithinAt

theorem iwaniec_tendsto_loglog_div_log :
    Tendsto (fun s : Real => Real.log (Real.log s) / Real.log s) atTop (nhds 0) := by
  simpa only [pow_one, Function.comp_apply] using (tendsto_deBruijn_log_power_div 1).comp Real.tendsto_log_atTop

theorem iwaniec_tendsto_log_inverse : Tendsto (fun s : Real => 1 / Real.log s) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

theorem iwaniec_tendsto_loglog_div_self :
    Tendsto (fun s : Real => Real.log (Real.log s) / s) atTop (nhds 0) := by
  have hlog : Tendsto (fun s : Real => Real.log s / s) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_deBruijn_log_power_div 1
  have h := iwaniec_tendsto_loglog_div_log.mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with s hs
  field_simp [(Real.log_pos hs).ne']

end

end Erdos1212Kernel
