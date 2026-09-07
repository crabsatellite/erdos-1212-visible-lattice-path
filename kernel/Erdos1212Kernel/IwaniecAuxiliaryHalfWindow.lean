import Erdos1212Kernel.IwaniecAuxiliaryWindowComparison

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-- First half of the literal conserved window, as in source Lemma 8. -/
theorem iwaniecAuxM_half_window_lower {s : Real} (hs : 3 ≤ s) :
    s / (2 * (s - 1) ^ 2) * iwaniecAuxM (s - 1 / 2) < iwaniecAuxM s := by
  let mid := s - (1 / 2 : Real)
  let w := iwaniecAuxMWindowWeight (s - 1)
  have hwPos : 0 < w := iwaniecAuxMWindowWeight_pos (by linarith)
  have hmid : 2 ≤ mid := by dsimp [mid]; linarith
  have hMmid := iwaniecAuxM_pos hmid
  have hLeftInt := iwaniecIntervalIntegrable_of_continuousOn_one _
    iwaniecAuxMWindowKernel_continuousOn (a := s - 1) (b := mid) (by linarith) (by dsimp [mid]; linarith)
  have hRightInt := iwaniecIntervalIntegrable_of_continuousOn_one _
    iwaniecAuxMWindowKernel_continuousOn (a := mid) (b := s) (by dsimp [mid]; linarith) (by linarith)
  have hleftBound : w * iwaniecAuxM mid / 2 ≤
      ∫ x in (s - 1)..mid, iwaniecAuxMWindowKernel x := by
    have hp : ∀ x ∈ Set.Icc (s - 1) mid,
        w * iwaniecAuxM mid ≤ iwaniecAuxMWindowKernel x := by
      intro x hx
      have hxTwo : 2 ≤ x := by linarith [hx.1]
      have hwle : w ≤ iwaniecAuxMWindowWeight x := by
        rcases eq_or_lt_of_le hx.1 with heq | hlt
        · rw [← heq]
        · exact (iwaniecAuxMWindowWeight_lt_of_lt (by linarith) hlt).le
      have hmle := iwaniecAuxM_antitoneOn hxTwo hmid hx.2
      exact mul_le_mul hwle hmle hMmid.le (iwaniecAuxMWindowWeight_pos hxTwo).le
    have h := intervalIntegral.integral_mono_on (show s - 1 ≤ mid by dsimp [mid]; linarith)
      (f := fun _x : Real => w * iwaniecAuxM mid) intervalIntegrable_const hLeftInt hp
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    convert h using 1 <;> dsimp [mid] <;> ring
  have hrightPos : 0 < ∫ x in mid..s, iwaniecAuxMWindowKernel x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hRightInt _ (by dsimp [mid]; linarith)
    intro x hx
    have hxTwo : 2 ≤ x := by dsimp [mid] at hx; linarith [hx.1]
    exact mul_pos (iwaniecAuxMWindowWeight_pos hxTwo) (iwaniecAuxM_pos hxTwo)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hLeftInt hRightInt
  have hstrict : w * iwaniecAuxM mid / 2 <
      ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x := by linarith
  have hdiv := (lt_div_iff₀ hwPos).mpr (show iwaniecAuxM mid / 2 * w <
      ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x by nlinarith)
  change iwaniecAuxM mid / 2 <
    (∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x) / iwaniecAuxMWindowWeight (s - 1) at hdiv
  rw [iwaniecAuxM_window_div_left_weight hs] at hdiv
  have hsPos : 0 < s := by linarith
  have hden : 0 < 2 * (s - 1) ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  have hmul := mul_lt_mul_of_pos_right hdiv hsPos
  have hcancel : ((s - 1) ^ 2 / s * iwaniecAuxM s) * s = (s - 1) ^ 2 * iwaniecAuxM s := by
    field_simp [hsPos.ne']
  rw [hcancel] at hmul
  dsimp [mid] at hmul
  nlinarith

end

end Erdos1212Kernel
