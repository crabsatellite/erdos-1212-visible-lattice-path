import Erdos1212Kernel.IwaniecAuxSharpExponent
import Erdos1212Kernel.DeBruijnRhoLogExpansion
import Mathlib.Analysis.Asymptotics.Lemmas

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

theorem tendsto_deBruijnSaddleLogErrorScale : Tendsto deBruijnSaddleLogErrorScale atTop (nhds 0) := by
  have h := iwaniec_tendsto_loglog_div_log.pow 2
  simpa only [zero_pow (by decide : (2 : Nat) ≠ 0), div_pow, deBruijnSaddleLogErrorScale] using h

theorem tendsto_deBruijnRhoLogRemainder : Tendsto deBruijnRhoLogRemainder atTop (nhds 0) :=
  deBruijnRhoLogRemainder_bound.trans_tendsto tendsto_deBruijnSaddleLogErrorScale

def iwaniecDickmanSharpCorrection (s : Real) : Real :=
  (Real.log (iwaniecDickman s) + iwaniecAuxSharpExponent s) / s

theorem iwaniecDickmanSharpCorrection_eq {s : Real} (hs : 1 < s) :
    iwaniecDickmanSharpCorrection s = 1 + 1 / Real.log s - Real.log (Real.log s) / Real.log s - deBruijnRhoLogRemainder s := by
  have hs0 : 0 < s := by linarith
  have h := congrArg Real.log (deBruijnRho_logarithmic_identity hs)
  rw [deBruijnRho_eq_dickman hs0.le, Real.log_exp] at h
  unfold iwaniecDickmanSharpCorrection iwaniecAuxSharpExponent
  rw [h]
  field_simp [hs0.ne']
  <;> ring

theorem tendsto_iwaniecDickmanSharpCorrection : Tendsto iwaniecDickmanSharpCorrection atTop (nhds 1) := by
  have h := (((tendsto_const_nhds (x := (1 : Real))).add iwaniec_tendsto_log_inverse).sub
    iwaniec_tendsto_loglog_div_log).sub tendsto_deBruijnRhoLogRemainder
  simp only [add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with s hs
  exact (iwaniecDickmanSharpCorrection_eq hs).symm

end

end Erdos1212Kernel
