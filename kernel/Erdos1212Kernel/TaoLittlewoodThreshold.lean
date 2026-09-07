import Erdos1212Kernel.TaoLittlewoodCanonical

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

def TaoLittlewoodFrequencyConditions (T : Real) : Prop :=
  1 < T ∧
  1 < Real.log T ∧
  (Real.log (Real.log T) ^ 2 /
      (8 * Real.log 2 * Real.log T) ≤
    1 / (4 * (Real.log T) ^ (1 / 8 : Real))) ∧
  taoLittlewoodR T ≤ taoLittlewoodJ T

theorem eventually_taoLittlewoodFrequencyConditions :
    ∀ᶠ T : Real in atTop, TaoLittlewoodFrequencyConditions T := by
  have hlog : ∀ᶠ T : Real in atTop, 1 < Real.log T :=
    (Real.tendsto_log_atTop.eventually_gt_atTop 1)
  filter_upwards [eventually_gt_atTop 1, hlog,
    eventually_taoLittlewood_large_scalar,
    eventually_taoLittlewood_scale_separation] with T hT hL hlarge hsep
  exact ⟨hT, hL, hlarge, hsep⟩

theorem exists_taoLittlewood_frequency_threshold :
    ∃ T₀ : Real, ∀ T, T₀ ≤ T → TaoLittlewoodFrequencyConditions T := by
  exact Filter.eventually_atTop.1 eventually_taoLittlewoodFrequencyConditions

/-- Eventual Littlewood bound with no scale witnesses or analytic premises.
The only caller input is that the literal frequency has crossed one fixed
absolute threshold. -/
theorem exists_riemannZeta_norm_le_littlewood_canonical :
    ∃ T₀ : Real, ∀ (t σ : Real), T₀ ≤ taoLogFrequency t →
      1 - taoLittlewoodWidth (taoLogFrequency t)
          (taoLittlewoodR (taoLogFrequency t)) ≤ σ →
      σ ≤ 1 →
      ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
        (taoLittlewoodJ (taoLogFrequency t) : Real) *
          (Real.log (taoLogFrequency t) +
            (2 : Real) ^ 42 * Real.log (2 + taoLogFrequency t)) +
        (((2 ^ taoLittlewoodJ (taoLogFrequency t) : Nat) : Real)) ^ (1 - σ) /
          ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖ +
        ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
          (((2 ^ taoLittlewoodJ (taoLogFrequency t) : Nat) : Real)) ^ (-σ) *
            (1 + 1 / σ) := by
  obtain ⟨T₀, hT₀⟩ := exists_taoLittlewood_frequency_threshold
  refine ⟨T₀, fun t σ ht hσ0 hσ1 => ?_⟩
  obtain ⟨hT, hL, hlarge, hsep⟩ := hT₀ _ ht
  exact riemannZeta_norm_le_littlewood_canonical t σ hT hL hlarge hsep hσ0 hσ1

end

end Erdos1212Kernel
