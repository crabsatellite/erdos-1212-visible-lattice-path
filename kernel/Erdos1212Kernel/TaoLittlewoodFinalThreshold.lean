import Erdos1212Kernel.TaoLittlewoodFinalBound

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

def TaoLittlewoodFinalFrequencyConditions (T : Real) : Prop :=
  TaoLittlewoodFrequencyConditions T ∧
  taoLittlewoodWidth T (taoLittlewoodR T) ≤ (1 : Real) / 8 ∧
  Real.log T ≤ T ^ (1 / 4 : Real) ∧
  2 ≤ T

theorem eventually_taoLittlewoodFinalFrequencyConditions :
    ∀ᶠ T : Real in atTop, TaoLittlewoodFinalFrequencyConditions T := by
  filter_upwards [eventually_taoLittlewoodFrequencyConditions,
    eventually_taoLittlewoodWidth_le_eighth,
    eventually_log_le_quarter_rpow, eventually_ge_atTop 2] with T hcond hwidth hlog hT
  exact ⟨hcond, hwidth, hlog, hT⟩

theorem exists_taoLittlewood_final_frequency_threshold :
    ∃ T₀ : Real, ∀ T, T₀ ≤ T → TaoLittlewoodFinalFrequencyConditions T := by
  exact Filter.eventually_atTop.1 eventually_taoLittlewoodFinalFrequencyConditions

/-- Standard eventual Littlewood bound with one absolute threshold and
no remaining scale, cutoff, or analytic hypotheses. -/
theorem exists_riemannZeta_norm_le_littlewood_log_sq :
    ∃ T₀ : Real, ∀ (t σ : Real), T₀ ≤ taoLogFrequency t →
      1 - taoLittlewoodWidth (taoLogFrequency t)
          (taoLittlewoodR (taoLogFrequency t)) ≤ σ →
      σ ≤ 1 →
      ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
        (2 : Real) ^ 46 * (Real.log (taoLogFrequency t)) ^ 2 := by
  obtain ⟨T₀, hT₀⟩ := exists_taoLittlewood_final_frequency_threshold
  refine ⟨T₀, fun t σ ht hσ0 hσ1 => ?_⟩
  obtain ⟨hcond, hwidth, hlog, hT⟩ := hT₀ _ ht
  exact riemannZeta_norm_le_littlewood_log_sq t σ hcond hwidth hlog hT hσ0 hσ1

end

end Erdos1212Kernel
