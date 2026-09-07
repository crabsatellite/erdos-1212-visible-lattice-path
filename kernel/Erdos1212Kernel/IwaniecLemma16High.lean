import Erdos1212Kernel.IwaniecPaperD2ClosedMain

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

theorem iwaniec_log_eight_implies_sixtyfour {level : Real} (hy : 0 < level)
    (hL : 8 ≤ Real.log level) : 64 ≤ level := by
  have hlog2 := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have hlog64 : Real.log (64 : Real) = 6 * Real.log 2 := by
    rw [show (64 : Real) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hh : Real.log (64 : Real) ≤ Real.log level := by rw [hlog64]; linarith
  have he := Real.exp_le_exp.mpr hh
  rwa [Real.exp_log (by norm_num : (0 : Real) < 64), Real.exp_log hy] at he

/-- Lemma 16 on its large-level range, consuming the actual summed
errors and the exact outer endpoint correction. -/
theorem exists_iwaniecLemma16_high_constant :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → 8 ≤ Real.log level → 2 ≤ s → s ≤ 4 →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s ≤
        iwaniecGTwo s / Real.log level + C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨A, hA, hsum⟩ := exists_iwaniecPaperD2_outer_main_error
  obtain ⟨B, hB, hmain⟩ := exists_iwaniecPaperD2_closed_outer_error
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro level s hy hL hs hs4
  have hy64 := iwaniec_log_eight_implies_sixtyfour (zero_lt_one.trans hy) hL
  have herr := (le_abs_self (Real.exp Real.eulerMascheroniConstant * iwaniecPaperD2 level s -
    iwaniecPaperD2OuterMain level s)).trans (hsum level s hy64 hs)
  have hout := iwaniecPaperD2_outer_main_le_closed hy hs
  have hclosed := (le_abs_self (iwaniecPaperD2ClosedOuterMain level s - iwaniecGTwo s / Real.log level)).trans
    (hmain level s hy hL hs hs4)
  have hdecay : Real.exp (-Real.sqrt (Real.log level / 4)) ≤ Real.exp (-Real.sqrt (Real.log level / 6)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply Real.sqrt_le_sqrt
    linarith [Real.log_pos hy]
  have hclosed' := hclosed.trans (mul_le_mul_of_nonneg_left hdecay hB.le)
  nlinarith only [herr, hout, hclosed']

end

end Erdos1212Kernel
