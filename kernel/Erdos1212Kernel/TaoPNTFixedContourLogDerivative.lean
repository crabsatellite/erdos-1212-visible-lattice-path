import Erdos1212Kernel.TaoPNTZetaLogDerivativeRate

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem exists_taoPNT_fixed_left_logDerivative_log_sq :
    ∃ d C U₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ H t : Real,
        0 ≤ H → |t| ≤ H → U₀ ≤ taoLogFrequency t →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        ∀ γ : Real, β ≤ γ → γ ≤ 1 →
          (‖taoZetaLogDerivative
              ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
            C * L ^ 2) ∧
            riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, C, U₀, hd, hC, hstrip⟩ :=
    exists_eventual_taoPNT_zetaLogDerivative_log_sq
  refine ⟨d, C, U₀, hd, hC, ?_⟩
  intro H t hH ht hhigh
  let Pt : Real := taoPNTFrequency t
  let PH : Real := 3 + H
  let Lt : Real := Real.log Pt
  let LH : Real := Real.log PH
  let βt : Real := 1 - d / Lt
  let βH : Real := 1 - d / LH
  have hPt : 1 < Pt := taoPNTFrequency_gt_one t
  have hPH : 1 < PH := by dsimp [PH]; linarith
  have hPtpos : 0 < Pt := hPt.trans' zero_lt_one
  have hPHpos : 0 < PH := hPH.trans' zero_lt_one
  have hPtPH : Pt ≤ PH := by
    dsimp [Pt, PH]
    unfold taoPNTFrequency
    linarith
  have hlogOrder : Lt ≤ LH := by
    dsimp [Lt, LH]
    exact Real.log_le_log hPtpos hPtPH
  have hLt : 0 < Lt := by dsimp [Lt]; exact Real.log_pos hPt
  have hLH : 0 < LH := by dsimp [LH]; exact Real.log_pos hPH
  have hdiv : d / LH ≤ d / Lt :=
    div_le_div_of_nonneg_left hd.le hLt hlogOrder
  have hβ : βt ≤ βH := by dsimp [βt, βH]; linarith
  have hβH1 : βH ≤ 1 := by
    dsimp [βH]
    have := div_pos hd hLH
    linarith
  change ∀ γ : Real, βH ≤ γ → γ ≤ 1 →
    (‖taoZetaLogDerivative
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * LH ^ 2) ∧
      riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0
  intro γ hβHγ hγ1
  obtain ⟨hbound, hzeta⟩ := hstrip t hhigh γ (hβ.trans hβHγ) hγ1
  have hsq : Lt ^ 2 ≤ LH ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · exact hbound.trans (mul_le_mul_of_nonneg_left hsq hC.le)
  · exact hzeta

end

end Erdos1212Kernel
