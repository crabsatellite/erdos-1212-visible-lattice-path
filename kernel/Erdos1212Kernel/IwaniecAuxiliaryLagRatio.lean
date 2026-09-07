import Erdos1212Kernel.IwaniecAuxiliaryHalfWindow
import Erdos1212Kernel.IwaniecAuxiliaryInitialHalf

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

theorem iwaniecAuxM_half_lag_upper {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM (s - 1 / 2) < (2 * (s - 1) ^ 2 / s) * iwaniecAuxM s := by
  have h := iwaniecAuxM_half_window_lower hs
  have hsPos : 0 < s := by linarith
  have hden : 0 < 2 * (s - 1) ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden] at h
  rw [div_mul_eq_mul_div, lt_div_iff₀ hsPos]
  nlinarith

theorem iwaniecAuxM_lag_lt_four_square_high {s : Real} (hs : 7 / 2 ≤ s) :
    iwaniecAuxM (s - 1) < 4 * s ^ 2 * iwaniecAuxM s := by
  have h1 := iwaniecAuxM_half_lag_upper (s := s) (by linarith)
  have h2 := iwaniecAuxM_half_lag_upper (s := s - 1 / 2) (by linarith)
  rw [show s - (1 / 2 : Real) - 1 / 2 = s - 1 by ring] at h2
  have hcoef1 : 2 * (s - 1) ^ 2 / s ≤ 2 * s := by
    rw [div_le_iff₀ (show 0 < s by linarith)]
    nlinarith
  have hcoef2 : 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) ≤ 2 * s := by
    rw [div_le_iff₀ (show 0 < s - 1 / 2 by linarith)]
    nlinarith
  have hM := iwaniecAuxM_pos (s := s) (by linarith)
  have hMid := iwaniecAuxM_pos (s := s - 1 / 2) (by linarith)
  have hfirst := h2.trans_le (mul_le_mul_of_nonneg_right hcoef2 hMid.le)
  have hsecond := h1.trans_le (mul_le_mul_of_nonneg_right hcoef1 hM.le)
  have hmul := mul_lt_mul_of_pos_left hsecond (show 0 < 2 * s by linarith)
  convert hfirst.trans hmul using 1 <;> ring

theorem iwaniecAuxM_lag_lt_four_square {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM (s - 1) < 4 * s ^ 2 * iwaniecAuxM s := by
  by_cases hsHigh : 7 / 2 ≤ s
  · exact iwaniecAuxM_lag_lt_four_square_high hsHigh
  · exact iwaniecAuxM_lag_lt_four_square_low ⟨hs, (lt_of_not_ge hsHigh).le⟩

/-- Source Lemma 8, with the precise denominator and the closed endpoint
`s=3`. Both the short initial branch and the double half-window branch
are consumed in this premise-free inequality. -/
theorem iwaniecAuxM_lag_ratio_lt {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM (s - 1) / iwaniecAuxM s < 4 * s ^ 2 := by
  rw [div_lt_iff₀ (iwaniecAuxM_pos (by linarith : 2 ≤ s))]
  exact iwaniecAuxM_lag_lt_four_square hs

end

end Erdos1212Kernel
