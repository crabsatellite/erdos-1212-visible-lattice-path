import Erdos1212Kernel.IwaniecLemma16Initial

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- Iwaniec 1971, Lemma 16, on the literal domain of the even d₂ mass.
The absolute constant precedes y and s. The actual double prime sum,
strict prime cutoffs, all y>1, and the source error exponent are retained. -/
theorem exists_iwaniecLemma16_constant :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s <
        iwaniecGTwo s / Real.log level + C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨A, hA, hhigh⟩ := exists_iwaniecLemma16_high_constant
  obtain ⟨B, hB, hinitial⟩ := exists_iwaniecLemma16_initial_constant
  let C := A + B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro level s hy hs
  by_cases hs4 : s ≤ 4
  · by_cases hL8 : 8 ≤ Real.log level
    · have hh := hhigh level s hy hL8 hs hs4
      have hAC : A < C := by dsimp [C]; linarith
      have hgain := mul_lt_mul_of_pos_right hAC (Real.exp_pos (-Real.sqrt (Real.log level / 6)))
      linarith only [hh, hgain]
    · have hh := hinitial level s hy (le_of_not_ge hL8) hs
      have hBC : B < C := by dsimp [C]; linarith
      have hgain := mul_lt_mul_of_pos_right hBC (Real.exp_pos (-Real.sqrt (Real.log level / 6)))
      linarith only [hh, hgain]
  · have hfour : 4 ≤ s := (lt_of_not_ge hs4).le
    simp only [iwaniecPaperD2_eq_zero_of_four_le hy hfour, iwaniecGTwo_eq_zero_of_four_le hfour,
      mul_zero, zero_div, zero_add]
    exact mul_pos hC (Real.exp_pos _)

end

end Erdos1212Kernel
