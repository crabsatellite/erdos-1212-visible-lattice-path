import Erdos1212Kernel.IwaniecPaperQHarmonic

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecPaperStoppedPartial_zero_of_pool (offset : Nat) (level z : Real) (rank : Nat)
    (hpool : iwaniecStrictPrimePool z = ∅) : iwaniecPaperStoppedPartial offset level z rank = 0 := by
  simp [iwaniecPaperStoppedPartial, iwaniecCubicRealThresholdPartial, hpool, iwaniecDescendingFactors]

theorem iwaniecPaperQ_zero_of_cutoff (rank : Nat) {level s : Real} (hy : 1 < level)
    (hs : iwaniecAuxGStart rank ≤ s) (hcutoff : Real.exp (Real.log level / s) ≤ 2) :
    iwaniecPaperQ rank level s = 0 := by
  have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
  have hs0 : 0 < s := by linarith
  by_cases hr : Even rank
  · rw [iwaniecPaperQ_even_eq_partial hr]
    exact iwaniecPaperStoppedPartial_zero_of_pool _ _ _ _ (iwaniecStrictPrimePool_eq_empty hcutoff)
  · rw [iwaniecPaperQ_odd_eq_partial hr]
    have hcap : Real.exp (Real.log level / max 3 s) ≤ 2 :=
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (Real.log_pos hy).le hs0 (le_max_right 3 s))).trans hcutoff
    exact iwaniecPaperStoppedPartial_zero_of_pool _ _ _ _ (iwaniecStrictPrimePool_eq_empty hcap)

/-- The parameter bound used in source (4.8), derived from a genuinely
nonempty prime carrier. The empty stopped mass is handled separately. -/
theorem iwaniecPaperQ_positive_parameter (rank : Nat) {level s : Real} (hy : 1 < level)
    (hs : iwaniecAuxGStart rank ≤ s) (hQ : 0 < iwaniecPaperQ rank level s) : s < 2 * Real.log level := by
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
  have hhalf := mul_le_mul_of_nonneg_right iwaniec_half_le_log_two hs0.le
  nlinarith only [hmul, hhalf]

theorem iwaniecPaperQ_positive_bounded_parameter (rank : Nat) {level Y s : Real} (hy : 1 < level)
    (hY : level ≤ Y) (hs : iwaniecAuxGStart rank ≤ s) (hQ : 0 < iwaniecPaperQ rank level s) :
    s < 2 * Real.log Y := by
  have hh := iwaniecPaperQ_positive_parameter rank hy hs hQ
  have hlog := Real.log_le_log (zero_lt_one.trans hy) hY
  linarith

end

end Erdos1212Kernel
