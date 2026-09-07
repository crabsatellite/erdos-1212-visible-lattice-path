import Erdos1212Kernel.IwaniecFarPointwiseComparison
import Erdos1212Kernel.IwaniecXiLongDecay
import Erdos1212Kernel.IwaniecAuxiliaryLemmaNine

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 700000

theorem eventually_iwaniec_far_log_loss :
    ∀ᶠ level : Real in atTop, 1 < Real.log level ∧
      8 * Real.log (Real.log level) ≤ iwaniecPaperXi level := by
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1,
    tendsto_iwaniecPaperXi_div_loglog_atTop.eventually_ge_atTop 8] with level hL hratio
  exact ⟨hL, (le_div_iff₀ (Real.log_pos hL)).mp hratio⟩

/-- The actual xi-1 count, compared with the full s-dependent majorant
on both sides of the source's xi/2 split. -/
theorem eventually_iwaniecPaperA_far_relative_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart (rank + 1) ≤ s → s ≤ iwaniecPaperXi level →
      (iwaniecPaperA rank level (iwaniecPaperXi level - 1) : Real) ≤
        (iwaniecAuxWeightPower level s * iwaniecAuxG (rank + 1) s / Real.log level ^ 4) * level := by
  obtain ⟨D, hD, hG⟩ := iwaniecAuxG_sharp_decay_bounds
  let C := max (max D (5 * Real.log 128)) 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hDC : D ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCW : 5 * Real.log 128 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC : 0 ≤ C := by linarith
  have hGlower (rank : Nat) (t : Real) (ht : 2 ≤ t) :
      Real.exp (-t * Real.log t - t * Real.log (Real.log t) - C * t) ≤ iwaniecAuxG rank t := by
    have hh := (hG rank t ht).1
    have hm := mul_le_mul_of_nonneg_right hDC (show 0 ≤ t by linarith)
    have he := Real.exp_le_exp.mpr
      (show -t * Real.log t - t * Real.log (Real.log t) - C * t ≤ -iwaniecAuxSharpExponent t - D * t by
        unfold iwaniecAuxSharpExponent
        linarith only [hm])
    exact he.trans hh
  obtain ⟨S, hS3, hanti⟩ := exists_iwaniecFarHighExponent_antitone hC
  have hcomparisons := tendsto_iwaniecPaperXi_atTop.eventually (eventually_iwaniec_far_exponent_comparisons C)
  filter_upwards [eventually_iwaniecPaperA_far_point_source_bound, eventually_iwaniecFar_log_comparisons,
    eventually_iwaniec_far_log_loss, hcomparisons,
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop (max (2 * S) 6)]
    with level hcount hlogs hloss hcomp hxi
  have hy := hlogs.1
  let ξ := iwaniecPaperXi level
  have hξ6 : 6 ≤ ξ := (le_max_right _ _).trans hxi
  have hξS : 2 * S ≤ ξ := (le_max_left _ _).trans hxi
  have hξ0 : 0 < ξ := by linarith
  have hlogξ1 : 1 ≤ Real.log ξ := by
    have he : Real.exp 1 ≤ ξ := Real.exp_one_lt_three.le.trans (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  refine ⟨hy, ?_⟩
  intro rank s hs hsξ
  have hExp : Real.exp (-ξ * Real.log ξ + ξ * Real.log (Real.log ξ) + 2 * ξ) ≤
      iwaniecAuxWeightPower level s * iwaniecAuxG (rank + 1) s / Real.log level ^ 4 := by
    by_cases hsmall : s ≤ ξ / 2
    · have hscale : 4 * Real.log (Real.log level) ≤ C * ξ := by
        have hh := mul_le_mul_of_nonneg_right hC1 hξ0.le
        nlinarith only [hloss.2, hh, hξ0]
      have hpoint := iwaniecFar_small_parameter_compare (rank + 1) hy hC hξ6 hlogξ1 hs hsmall hscale
        (hGlower (rank + 1) (ξ / 2) (by linarith))
      exact hcomp.2.1.le.trans hpoint
    · have hhalf : ξ / 2 ≤ s := le_of_not_ge hsmall
      obtain ⟨hs3, hloglo, hloghi⟩ := hlogs.2.2 s hhalf hsξ
      have hs0 : 0 ≤ s := by linarith
      have hWbase := iwaniecFar_weight_power_lower hy hs3 hlogs.2.1 hhalf hloglo hloghi
      have hCmul := mul_le_mul_of_nonneg_right hCW hs0
      have hW : Real.exp (3 * s * Real.log (Real.log s) - C * s) ≤ iwaniecAuxWeightPower level s :=
        (Real.exp_le_exp.mpr (by linarith only [hCmul])).trans hWbase
      have hscale : 4 * Real.log (Real.log level) ≤ C * s := by
        have hh := mul_le_mul_of_nonneg_right hC1 hs0
        nlinarith only [hloss.2, hhalf, hh]
      have hpoint := iwaniecFar_large_parameter_compare (rank + 1) hy hs3 hscale
        (hGlower (rank + 1) s (by linarith)) hW
      have hsS : S ≤ s := by linarith
      have hξSS : S ≤ ξ := by linarith
      have horder := hanti hsS hξSS hsξ
      exact hcomp.2.2.le.trans ((Real.exp_le_exp.mpr horder).trans hpoint)
  have hscaled := mul_le_mul_of_nonneg_left hExp (show 0 ≤ level by linarith)
  have hh := (hcount rank).trans hscaled
  convert hh using 1 <;> ring

end

end Erdos1212Kernel
