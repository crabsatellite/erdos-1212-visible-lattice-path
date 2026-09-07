import Erdos1212Kernel.IwaniecAuxiliaryWindowComparison

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The lower unweighted average in the source's Lemma 9. -/
theorem iwaniecAuxM_gt_dickman_average {s : Real} (hs : 3 ≤ s) :
    (1 / s) * (∫ x in (s - 1)..s, iwaniecAuxM x) < iwaniecAuxM s := by
  have h := iwaniecAuxM_unweighted_window_lt hs
  have hM := iwaniecAuxM_pos (s := s) (by linarith)
  have hstrong : (∫ x in (s - 1)..s, iwaniecAuxM x) < s * iwaniecAuxM s := by nlinarith
  rw [one_div_mul_eq_div, div_lt_iff₀ (show 0 < s by linarith)]
  nlinarith

/-- The upper unweighted average in the same source proof, with its
different denominator `s-2` retained exactly. -/
theorem iwaniecAuxM_lt_shifted_dickman_average {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxM s < (1 / (s - 2)) * (∫ x in (s - 1)..s, iwaniecAuxM x) := by
  have hintW := iwaniecIntervalIntegrable_of_continuousOn_one _
    iwaniecAuxMWindowKernel_continuousOn (a := s - 1) (b := s) (by linarith) (by linarith)
  have hintM := iwaniecIntervalIntegrable_of_continuousOn_one _
    (iwaniecAuxFunction_continuousOn (-1)) (a := s - 1) (b := s) (by linarith) (by linarith)
  have hpoint : ∀ x ∈ Set.Icc (s - 1) s, iwaniecAuxMWindowKernel x ≤ iwaniecAuxM x := by
    intro x hx
    have hxTwo : 2 ≤ x := by linarith [hx.1]
    have hw : iwaniecAuxMWindowWeight x ≤ 1 := by
      unfold iwaniecAuxMWindowWeight
      have hnn : 0 ≤ (1 : Real) / (2 * x ^ 2) := by positivity
      linarith
    exact mul_le_of_le_one_left (iwaniecAuxM_pos hxTwo).le hw
  have hi := intervalIntegral.integral_mono_on (show s - 1 ≤ s by linarith) hintW hintM hpoint
  have hw := iwaniecAuxM_window_identity hs
  change iwaniecAuxMCoefficient s * iwaniecAuxM s =
    ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hw
  rw [← hw] at hi
  change iwaniecAuxMCoefficient s * iwaniecAuxM s ≤ ∫ x in (s - 1)..s, iwaniecAuxM x at hi
  have hcoef : s - 2 < iwaniecAuxMCoefficient s := by
    unfold iwaniecAuxMCoefficient
    rw [lt_div_iff₀ (show 0 < s by linarith)]
    nlinarith
  have hprod := mul_lt_mul_of_pos_right hcoef (iwaniecAuxM_pos (s := s) (by linarith))
  rw [one_div_mul_eq_div, lt_div_iff₀ (show 0 < s - 2 by linarith)]
  nlinarith

theorem iwaniecAuxM_add_two_lt_dickman_average {s : Real} (hs : 1 ≤ s) :
    iwaniecAuxM (s + 2) < (1 / s) * (∫ x in (s - 1)..s, iwaniecAuxM (x + 2)) := by
  have h := iwaniecAuxM_lt_shifted_dickman_average (s := s + 2) (by linarith)
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [show s + (2 : Real) - 2 = s by ring,
    show s - (1 : Real) + 2 = s + 2 - 1 by ring] using h

theorem iwaniecAuxM_initial_ge_three_halves {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    (3 / 2 : Real) ≤ iwaniecAuxM s := by
  have hu : 0 < s - 1 := by linarith [hs.1]
  have hinv : (1 / 2 : Real) ≤ 1 / (s - 1) := by
    rw [le_div_iff₀ hu]
    linarith [hs.2]
  have hlog := Real.log_le_sub_one_of_pos hu
  rw [iwaniecAuxM_initial hs.2]
  linarith [hs.2]

end

end Erdos1212Kernel
