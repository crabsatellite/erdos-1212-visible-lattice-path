import Erdos1212Kernel.TaoPNTArbitraryLogDerivative
import Erdos1212Kernel.TaoPNTLogDerivativeLow

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem exists_taoPNT_global_strip_any_parameter (d : Real) (hd : 0 < d) :
    ∃ C H₀ : Real, 0 < C ∧ 1 ≤ H₀ ∧ ∀ H t γ : Real, H₀ ≤ H → |t| ≤ H →
      let L := Real.log (3 + H)
      let δ := d / L
      0 < δ ∧ δ ≤ 1 / 2 ∧
      (1 - δ ≤ γ → γ ≤ 1 + δ →
        taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
        ‖logDeriv taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2) := by
  obtain ⟨Ch, U₀, hCh, hhigh⟩ := exists_taoPNT_logDerivative_log_sq_any_parameter d hd
  let A := max U₀ 0
  obtain ⟨e, K, he, hehalf, _hK, hlow⟩ :=
    exists_taoPNT_low_frequency_poleRemoved_bound A (le_max_right _ _)
  let C := max Ch K
  let B := max 1 (d / e)
  let H₀ := Real.exp B
  have hC : 0 < C := hCh.trans_le (le_max_left _ _)
  have hH₀ : 1 ≤ H₀ := Real.one_le_exp (by dsimp [B]; linarith [le_max_left 1 (d / e)])
  refine ⟨C, H₀, hC, hH₀, ?_⟩
  intro H t γ hH ht
  let L := Real.log (3 + H)
  let δ := d / L
  have hHone : 1 ≤ H := hH₀.trans hH
  have hB : B ≤ L := by
    have harg : Real.exp B ≤ 3 + H := by linarith only [hH]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos B) harg
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hB
  have hLpos : 0 < L := by linarith only [hL1]
  have hδ : 0 < δ := div_pos hd hLpos
  have hδe : δ ≤ e := by
    apply (div_le_iff₀ hLpos).mpr
    have hde : d / e ≤ L := (le_max_right _ _).trans hB
    have hm := (div_le_iff₀ he).mp hde
    linarith only [hm]
  refine ⟨hδ, hδe.trans hehalf, ?_⟩
  intro hγlo hγhi
  by_cases hfreq : U₀ ≤ taoLogFrequency t
  · let Lt := Real.log (taoPNTFrequency t)
    have hPt : 0 < taoPNTFrequency t := (taoPNTFrequency_gt_one t).trans' zero_lt_one
    have hLt : 0 < Lt := Real.log_pos (taoPNTFrequency_gt_one t)
    have hLtL : Lt ≤ L := by
      apply Real.log_le_log hPt
      dsimp [taoPNTFrequency]
      linarith only [ht]
    have hδt : δ ≤ d / Lt := div_le_div_of_nonneg_left hd.le hLt hLtL
    obtain ⟨hnz, hb⟩ := hhigh t hfreq γ (by linarith only [hγlo, hδt])
      (by linarith only [hγhi, hδt])
    have hsq : Lt ^ 2 ≤ L ^ 2 := by nlinarith only [hLt, hLtL]
    have hfactor := mul_le_mul (le_max_left Ch K) hsq (sq_nonneg Lt) hC.le
    exact ⟨hnz, hb.trans hfactor⟩
  · have hfreqA : taoLogFrequency t ≤ A := (le_of_not_ge hfreq).trans (le_max_left _ _)
    obtain ⟨hnz, hb⟩ := hlow t γ hfreqA (by linarith only [hγlo, hδe])
      (by linarith only [hγhi, hδe])
    have hsq : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have hCmul : C ≤ C * L ^ 2 := by nlinarith only [hsq, hC]
    exact ⟨hnz, hb.trans ((le_max_right Ch K).trans hCmul)⟩

end

end Erdos1212Kernel
