import Erdos1212Kernel.IwaniecPaperQPositiveParameter
import Erdos1212Kernel.IwaniecPaperABoundedLevel
import Erdos1212Kernel.IwaniecAuxiliaryLogRatio

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniec_seven_twelfths_le_log_two : (7 / 12 : Real) ≤ Real.log 2 := by
  have hfour := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 4 / 3)
  have hthree := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 3 / 2)
  have hsplit : Real.log (4 / 3 : Real) + Real.log (3 / 2 : Real) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (4 / 3 : Real) ≠ 0)
      (by norm_num : (3 / 2 : Real) ≠ 0)]
    norm_num
  norm_num at hfour hthree
  linarith only [hfour, hthree, hsplit]

/-- A strict margin inside the source's `2 log y` parameter range, paid
by the first admissible prime, not assumed for zero stopped mass. -/
theorem iwaniecPaperQ_positive_parameter_sharp (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart rank ≤ s)
    (hQ : 0 < iwaniecPaperQ rank level s) : s < (12 / 7) * Real.log level := by
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hs0 : 0 < s := by linarith
  have hcutoff : 2 < Real.exp (Real.log level / s) := by
    by_contra hn
    have hz := iwaniecPaperQ_zero_of_cutoff rank hy hs (le_of_not_gt hn)
    rw [hz] at hQ
    linarith
  have hlog := Real.log_lt_log (by norm_num : (0 : Real) < 2) hcutoff
  rw [Real.log_exp] at hlog
  have hmul := (lt_div_iff₀ hs0).mp hlog
  have hsmall := mul_le_mul_of_nonneg_right iwaniec_seven_twelfths_le_log_two hs0.le
  nlinarith only [hmul, hsmall]

theorem iwaniecPaperQ_positive_bounded_margin (rank : Nat) {level Y s : Real}
    (hy : 1 < level) (hyY : level ≤ Y) (hY : 4 ≤ Real.log Y)
    (hs : iwaniecAuxGStart rank ≤ s) (hQ : 0 < iwaniecPaperQ rank level s) :
    s ≤ 2 * Real.log Y - 1 := by
  have hsharp := iwaniecPaperQ_positive_parameter_sharp rank hy hs hQ
  have hlog := Real.log_le_log (zero_lt_one.trans hy) hyY
  linarith only [hsharp, hlog, hY]

/-- The one-step gain from the literal auxiliary window identity (3.12). -/
theorem iwaniecAuxM_one_step_lower {T : Real} (hT : 3 ≤ T) :
    (T - 2) * iwaniecAuxM T ≤ iwaniecAuxM (T - 1) := by
  have hratio := (iwaniecAuxEta_bounds hT).1
  exact (le_div_iff₀ (iwaniecAuxM_pos (by linarith : 2 ≤ T))).mp hratio

theorem iwaniecAuxG_bounded_shifted_anchor (rank : Nat) {s L : Real}
    (hL : 2 ≤ L) (hs : iwaniecAuxGStart rank ≤ s) (hsL : s ≤ 2 * L - 1) :
    L * iwaniecAuxM (2 * L) / 3 ≤ iwaniecAuxG rank s := by
  have hM := iwaniecAuxM_pos (show 2 ≤ 2 * L by linarith)
  have hstep := iwaniecAuxM_one_step_lower (show 3 ≤ 2 * L by linarith)
  have hlinear : L * iwaniecAuxM (2 * L) ≤ iwaniecAuxM (2 * L - 1) :=
    (mul_le_mul_of_nonneg_right (by linarith : L ≤ 2 * L - 2) hM.le).trans hstep
  exact (div_le_div_of_nonneg_right hlinear (by norm_num : (0 : Real) ≤ 3)).trans
    (iwaniecAuxG_lower_anchor rank hs (by linarith : 2 ≤ 2 * L - 1) hsL)

end

end Erdos1212Kernel
