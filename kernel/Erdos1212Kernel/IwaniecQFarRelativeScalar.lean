import Erdos1212Kernel.IwaniecPaperAFarRelative

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 700000

theorem iwaniecFar_small_parameter_compare_unweighted (rank : Nat)
    {level C ξ s : Real} (hy : 1 < level) (hC : 0 ≤ C) (hξ : 6 ≤ ξ)
    (hlogξ : 1 ≤ Real.log ξ) (hs : iwaniecAuxGStart rank ≤ s) (hhalf : s ≤ ξ / 2)
    (hscale : 4 * Real.log (Real.log level) ≤ C * ξ)
    (hG : Real.exp (-(ξ / 2) * Real.log (ξ / 2) - (ξ / 2) * Real.log (Real.log (ξ / 2)) - C * (ξ / 2)) ≤
      iwaniecAuxG rank (ξ / 2)) :
    Real.exp (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) ≤
      iwaniecAuxG rank s / Real.log level ^ 4 := by
  have hL := Real.log_pos hy
  have hξ0 : 0 < ξ := by linarith
  have hhalf0 : 0 < ξ / 2 := by linarith
  have hloghalf : 0 < Real.log (ξ / 2) := Real.log_pos (by linarith)
  have hlogOrder := Real.log_le_log hhalf0 (show ξ / 2 ≤ ξ by linarith)
  have hloglogOrder := Real.log_le_log hloghalf hlogOrder
  have hloglog0 : 0 ≤ Real.log (Real.log ξ) := Real.log_nonneg hlogξ
  have hterm1 := mul_le_mul_of_nonneg_left hlogOrder hhalf0.le
  have hterm2a := mul_le_mul_of_nonneg_left hloglogOrder hhalf0.le
  have hterm2b := mul_le_mul_of_nonneg_right (show ξ / 2 ≤ ξ by linarith) hloglog0
  have hterm2 := hterm2a.trans hterm2b
  have hterm3 := mul_le_mul_of_nonneg_left (show ξ / 2 ≤ ξ by linarith) hC
  have hexponent :
      (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) +
        4 * Real.log (Real.log level) ≤
      -(ξ / 2) * Real.log (ξ / 2) - (ξ / 2) * Real.log (Real.log (ξ / 2)) - C * (ξ / 2) := by
    nlinarith only [hterm1, hterm2, hterm3, hscale]
  have hGorder := iwaniecAuxG_antitoneOn_exactDomain rank hs (hs.trans hhalf) hhalf
  have hGsource := hG.trans hGorder
  have hnormalized : Real.exp (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) ≤
      iwaniecAuxG rank s / Real.log level ^ 4 := by
    apply (le_div_iff₀ (pow_pos hL 4)).mpr
    rw [iwaniec_log_four_power_exp hL, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr hexponent).trans hGsource
  exact hnormalized

/-- Source scalar comparison on both sides of xi/2. The small-s
branch retains the stronger bound without the weight-power factor. -/
theorem eventually_iwaniecQFar_source_scalar :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      Real.exp (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) +
        iwaniecPaperXi level * Real.log (Real.log (iwaniecPaperXi level)) + 2 * iwaniecPaperXi level) ≤
      (if s ≤ iwaniecPaperXi level / 2 then iwaniecAuxG rank s / Real.log level ^ 4
       else iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4) := by
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
  filter_upwards [eventually_iwaniecFar_log_comparisons,
    eventually_iwaniec_far_log_loss, hcomparisons,
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop (max (2 * S) 6)]
    with level hlogs hloss hcomp hxi
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
      (if s ≤ ξ / 2 then iwaniecAuxG rank s / Real.log level ^ 4
       else iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4) := by
    by_cases hsmall : s ≤ ξ / 2
    · rw [if_pos hsmall]
      have hscale : 4 * Real.log (Real.log level) ≤ C * ξ := by
        have hh := mul_le_mul_of_nonneg_right hC1 hξ0.le
        nlinarith only [hloss.2, hh, hξ0]
      have hpoint := iwaniecFar_small_parameter_compare_unweighted rank hy hC hξ6 hlogξ1 hs hsmall hscale
        (hGlower rank (ξ / 2) (by linarith))
      exact hcomp.2.1.le.trans hpoint
    · rw [if_neg hsmall]
      have hhalf : ξ / 2 ≤ s := le_of_not_ge hsmall
      obtain ⟨hs3, hloglo, hloghi⟩ := hlogs.2.2 s hhalf hsξ
      have hs0 : 0 ≤ s := by linarith
      have hWbase := iwaniecFar_weight_power_lower hy hs3 hlogs.2.1 hhalf hloglo hloghi
      have hCmul := mul_le_mul_of_nonneg_right hCW hs0
      have hW : Real.exp (3 * s * Real.log (Real.log s) - C * s) ≤ iwaniecAuxWeightPower level s :=
        (Real.exp_le_exp.mpr (by linarith only [hCmul])).trans hWbase
      have hscale : 4 * Real.log (Real.log level) ≤ C * s := by
        have hh := mul_le_mul_of_nonneg_right hC1 hs0
        nlinarith only [hloss.2, hhalf, hh]
      have hpoint := iwaniecFar_large_parameter_compare rank hy hs3 hscale
        (hGlower rank s (by linarith)) hW
      have hsS : S ≤ s := by linarith
      have hξSS : S ≤ ξ := by linarith
      have horder := hanti hsS hξSS hsξ
      exact hcomp.2.2.le.trans ((Real.exp_le_exp.mpr horder).trans hpoint)
  exact hExp

end

end Erdos1212Kernel
