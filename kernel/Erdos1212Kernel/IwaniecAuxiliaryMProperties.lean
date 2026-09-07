import Erdos1212Kernel.IwaniecAuxiliaryPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxM_antitoneOn_initial :
    AntitoneOn iwaniecAuxM (Set.Icc (2 : Real) 3) := by
  intro x hx y hy hxy
  rw [iwaniecAuxM_initial hx.2, iwaniecAuxM_initial hy.2]
  have hinv : (1 : Real) / (y - 1) ≤ 1 / (x - 1) :=
    one_div_le_one_div_of_le (by linarith [hx.1]) (by linarith)
  have hlog : Real.log (x - 1) ≤ Real.log (y - 1) :=
    Real.log_le_log (by linarith [hx.1]) (by linarith)
  linarith

theorem iwaniecAuxM_strictAntiOn_high :
    StrictAntiOn iwaniecAuxM (Set.Ici (3 : Real)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (3 : Real))
    (iwaniecAuxM_continuousOn.mono (Set.Ici_subset_Ici.mpr (by norm_num)))
  intro s hs
  rw [interior_Ici] at hs
  exact iwaniecAuxM_hasDerivAt_negative hs

theorem iwaniecAuxM_antitoneOn : AntitoneOn iwaniecAuxM (Set.Ici (2 : Real)) := by
  intro x hx y hy hxy
  change (2 : Real) ≤ x at hx
  change (2 : Real) ≤ y at hy
  by_cases hyThree : y ≤ 3
  · exact iwaniecAuxM_antitoneOn_initial ⟨hx, hxy.trans hyThree⟩ ⟨hy, hyThree⟩ hxy
  · have hyHigh : 3 ≤ y := (lt_of_not_ge hyThree).le
    by_cases hxThree : x ≤ 3
    · exact (iwaniecAuxM_strictAntiOn_high.antitoneOn
        (show (3 : Real) ∈ Set.Ici 3 by simp) hyHigh hyHigh).trans
        (iwaniecAuxM_antitoneOn_initial ⟨hx, hxThree⟩ (by norm_num) hxThree)
    · exact iwaniecAuxM_strictAntiOn_high.antitoneOn
        (lt_of_not_ge hxThree).le hyHigh hxy

theorem iwaniecAuxM_le_three {s : Real} (hs : 2 ≤ s) : iwaniecAuxM s ≤ 3 := by
  have h := iwaniecAuxM_antitoneOn (show (2 : Real) ∈ Set.Ici 2 by simp) hs hs
  rw [iwaniecAuxM_initial (show (2 : Real) ≤ 3 by norm_num)] at h
  norm_num at h
  exact h

def iwaniecAuxMReciprocalKernel (s : Real) : Real := iwaniecAuxM s / s ^ 2

theorem iwaniecAuxMReciprocalKernel_continuousOn :
    ContinuousOn iwaniecAuxMReciprocalKernel (Set.Ioi (1 : Real)) := by
  apply (iwaniecAuxFunction_continuousOn (-1)).div (continuousOn_id.pow 2)
  intro s hs
  have hsOne : 1 < s := hs
  exact pow_ne_zero 2 (show s ≠ 0 by linarith)

theorem iwaniecAuxMReciprocal_point_lt
    {s x : Real} (hs : 3 ≤ s) (hx : s - 1 < x) :
    iwaniecAuxM x / x ^ 2 <
      iwaniecAuxMWindowKernel x / ((s - 1) ^ 2 - 1 / 2) := by
  have hxTwo : 2 ≤ x := by linarith
  have hxPos : 0 < x := by linarith
  have hR : 0 < (s - 1) ^ 2 - (1 / 2 : Real) := by nlinarith [sq_nonneg (s - 3)]
  have hsquare : (s - 1) ^ 2 - (1 / 2 : Real) < x ^ 2 - 1 / 2 := by nlinarith
  rw [div_lt_div_iff₀ (sq_pos_of_pos hxPos) hR]
  have hweight : iwaniecAuxMWindowKernel x * x ^ 2 =
      iwaniecAuxM x * (x ^ 2 - 1 / 2) := by
    unfold iwaniecAuxMWindowKernel iwaniecAuxMWindowWeight
    field_simp [hxPos.ne']
  rw [hweight]
  exact mul_lt_mul_of_pos_left hsquare (iwaniecAuxM_pos hxTwo)

/-- Strict weighted-window comparison consumed in the source's Lemma 6. -/
theorem iwaniecAuxM_reciprocal_window_lt
    {s : Real} (hs : 3 ≤ s) :
    s * (∫ x in (s - 1)..s, iwaniecAuxM x / x ^ 2) < iwaniecAuxM s := by
  let R := (s - 1) ^ 2 - (1 / 2 : Real)
  have hsPos : 0 < s := by linarith
  have hR : 0 < R := by dsimp [R]; nlinarith [sq_nonneg (s - 3)]
  have hcontLeft : ContinuousOn iwaniecAuxMReciprocalKernel (Set.Icc (s - 1) s) := by
    apply iwaniecAuxMReciprocalKernel_continuousOn.mono
    intro x hx
    change (1 : Real) < x
    linarith [hx.1]
  have hcontRight : ContinuousOn (fun x => iwaniecAuxMWindowKernel x / R)
      (Set.Icc (s - 1) s) := by
    apply (iwaniecAuxMWindowKernel_continuousOn.div_const R).mono
    intro x hx
    change (1 : Real) < x
    linarith [hx.1]
  have hlt : (∫ x in (s - 1)..s, iwaniecAuxMReciprocalKernel x) <
      ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x / R := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcontLeft hcontRight
    · intro x hx
      exact (iwaniecAuxMReciprocal_point_lt hs hx.1).le
    · exact ⟨s, ⟨by linarith, le_rfl⟩, iwaniecAuxMReciprocal_point_lt hs (by linarith)⟩
  have hright : (∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x / R) = iwaniecAuxM s / s := by
    rw [intervalIntegral.integral_div]
    have hwindow := iwaniecAuxM_window_identity hs
    change (R / s) * iwaniecAuxM s = ∫ x in (s - 1)..s, iwaniecAuxMWindowKernel x at hwindow
    rw [← hwindow]
    field_simp [hsPos.ne', hR.ne']
  rw [hright] at hlt
  have h := (lt_div_iff₀ hsPos).1 hlt
  simpa only [iwaniecAuxMReciprocalKernel, mul_comm] using h

end

end Erdos1212Kernel
