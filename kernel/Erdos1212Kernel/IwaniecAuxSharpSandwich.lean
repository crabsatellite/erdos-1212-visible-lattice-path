import Erdos1212Kernel.IwaniecDickmanSharpExponent
import Erdos1212Kernel.IwaniecSharpShiftLimits
import Erdos1212Kernel.IwaniecAuxiliaryDickmanComparison

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1300000

def iwaniecAuxSharpLowerLog (s : Real) : Real :=
  (Real.log (iwaniecDickman s) - Real.log 3 + iwaniecAuxSharpExponent s) / s

def iwaniecAuxSharpUpperLog (s : Real) : Real :=
  (Real.log 2 + Real.log (iwaniecDickman (s - 2)) + iwaniecAuxSharpExponent s) / s

theorem tendsto_iwaniecAuxSharpLowerLog : Tendsto iwaniecAuxSharpLowerLog atTop (nhds 1) := by
  have h := tendsto_iwaniecDickmanSharpCorrection.sub
    ((tendsto_const_nhds (x := Real.log 3)).div_atTop tendsto_id)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards with s
  simp only [id_eq]
  unfold iwaniecDickmanSharpCorrection iwaniecAuxSharpLowerLog
  ring

theorem tendsto_iwaniecAuxSharpUpperLog : Tendsto iwaniecAuxSharpUpperLog atTop (nhds 1) := by
  have h := (((tendsto_iwaniecDickmanSharpCorrection.comp iwaniec_tendsto_sub_two).mul iwaniec_tendsto_shift_ratio).add
    iwaniecAuxSharpExponent_shift_difference).add ((tendsto_const_nhds (x := Real.log 2)).div_atTop tendsto_id)
  simp only [mul_one, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (3 : Real)] with s hs
  simp only [Function.comp_apply, id_eq]
  unfold iwaniecDickmanSharpCorrection iwaniecAuxSharpUpperLog
  field_simp [show s - 2 ≠ 0 by linarith]
  <;> ring

theorem iwaniecAuxG_log_sandwich (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    Real.log (iwaniecDickman s) - Real.log 3 < Real.log (iwaniecAuxG rank s) ∧
      Real.log (iwaniecAuxG rank s) < Real.log 2 + Real.log (iwaniecDickman (s - 2)) := by
  have hρ := iwaniecDickman_pos (s := s) (by linarith)
  have hlag := iwaniecDickman_pos (s := s - 2) (by linarith)
  have hG := iwaniecAuxG_dickman_sandwich rank hs
  have hlo := Real.log_lt_log (div_pos hρ (by norm_num : (0 : Real) < 3)) hG.1
  have hhi := Real.log_lt_log (iwaniecAuxG_pos rank (by linarith : 2 ≤ s)) hG.2
  rw [Real.log_div hρ.ne' (by norm_num : (3 : Real) ≠ 0)] at hlo
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hlag.ne'] at hhi
  exact ⟨hlo, hhi⟩

theorem iwaniecAuxG_normalized_log_sandwich (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxSharpLowerLog s < (Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s) / s ∧
      (Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s) / s < iwaniecAuxSharpUpperLog s := by
  have h := iwaniecAuxG_log_sandwich rank hs
  have hs0 : 0 < s := by linarith
  constructor
  · exact div_lt_div_of_pos_right (by linarith [h.1]) hs0
  · exact div_lt_div_of_pos_right (by linarith [h.2]) hs0

/-- One common eventual set for every rank, obtained from the source's
rank-independent Dickman sandwich and the actual s-2 transport. -/
theorem eventually_iwaniecAuxG_sharp_log_bounds :
    ∀ᶠ s : Real in atTop, ∀ rank : Nat,
      s / 2 ≤ Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s ∧
      Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s ≤ 2 * s := by
  have hlo := tendsto_iwaniecAuxSharpLowerLog.eventually (Ioi_mem_nhds (show (1 / 2 : Real) < 1 by norm_num))
  have hhi := tendsto_iwaniecAuxSharpUpperLog.eventually (Iio_mem_nhds (show (1 : Real) < 2 by norm_num))
  filter_upwards [eventually_ge_atTop (3 : Real), hlo, hhi] with s hs hlow hhigh
  intro rank
  have hs0 : 0 < s := by linarith
  have h := iwaniecAuxG_normalized_log_sandwich rank hs
  have hl := (lt_div_iff₀ hs0).mp (lt_trans hlow h.1)
  have hh := (div_lt_iff₀ hs0).mp (lt_trans h.2 hhigh)
  exact ⟨by linarith, hh.le⟩

theorem eventually_iwaniecAuxG_sharp_exponential_bounds :
    ∀ᶠ s : Real in atTop, ∀ rank : Nat,
      Real.exp (s / 2) ≤ iwaniecAuxG rank s * Real.exp (iwaniecAuxSharpExponent s) ∧
      iwaniecAuxG rank s * Real.exp (iwaniecAuxSharpExponent s) ≤ Real.exp (2 * s) := by
  filter_upwards [eventually_iwaniecAuxG_sharp_log_bounds, eventually_ge_atTop (2 : Real)] with s hs htwo
  intro rank
  have hG := iwaniecAuxG_pos rank htwo
  have he : Real.exp (Real.log (iwaniecAuxG rank s) + iwaniecAuxSharpExponent s) =
      iwaniecAuxG rank s * Real.exp (iwaniecAuxSharpExponent s) := by rw [Real.exp_add, Real.exp_log hG]
  constructor
  · simpa only [he] using Real.exp_le_exp.mpr (hs rank).1
  · simpa only [he] using Real.exp_le_exp.mpr (hs rank).2

end

end Erdos1212Kernel
