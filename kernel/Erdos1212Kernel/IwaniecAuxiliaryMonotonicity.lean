import Erdos1212Kernel.IwaniecAuxiliaryTailInitial
import Mathlib.Algebra.Group.Nat.Even

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem iwaniecAntitone_join (f : Real → Real) {a b : Real} (hab : a ≤ b)
    (hinit : AntitoneOn f (Set.Icc a b)) (hhigh : AntitoneOn f (Set.Ici b)) :
    AntitoneOn f (Set.Ici a) := by
  intro x hx y hy hxy
  change a ≤ x at hx
  change a ≤ y at hy
  by_cases hyb : y ≤ b
  · exact hinit ⟨hx, hxy.trans hyb⟩ ⟨hy, hyb⟩ hxy
  · have hby : b ≤ y := (lt_of_not_ge hyb).le
    by_cases hxb : x ≤ b
    · exact (hhigh (show b ∈ Set.Ici b by simp) hby hby).trans
        (hinit ⟨hx, hxb⟩ ⟨hab, le_rfl⟩ hxb)
    · exact hhigh (lt_of_not_ge hxb).le hby hxy

theorem iwaniecAuxLower_antitoneOn : AntitoneOn iwaniecAuxLower (Set.Ici (2 : Real)) := by
  apply iwaniecAntitone_join _ (b := 3) (by norm_num)
  · intro x hx y hy hxy
    have hM := iwaniecAuxM_antitoneOn_initial hx hy hxy
    rw [iwaniecAuxM_initial hx.2, iwaniecAuxM_initial hy.2] at hM
    rw [iwaniecAuxLower_initial hx.2, iwaniecAuxLower_initial hy.2]
    linarith
  · apply (strictAntiOn_of_deriv_neg (convex_Ici (3 : Real))
      (iwaniecAuxLower_continuousOn.mono (by
        intro s hs
        change (1 : Real) < s
        linarith [hs.out])) _).antitoneOn
    intro s hs
    rw [interior_Ici] at hs
    exact iwaniecAuxLower_deriv_neg hs

theorem iwaniecAuxUpper_antitoneOn : AntitoneOn iwaniecAuxUpper (Set.Ici (1 : Real)) := by
  apply iwaniecAntitone_join _ (b := 3) (by norm_num)
  · intro x hx y hy _
    rw [iwaniecAuxUpper_initial hx.2, iwaniecAuxUpper_initial hy.2]
  · apply (strictAntiOn_of_deriv_neg (convex_Ici (3 : Real))
      (iwaniecAuxUpper_continuousOn.mono (by
        intro s hs
        change (1 : Real) < s
        linarith [hs.out])) _).antitoneOn
    intro s hs
    rw [interior_Ici] at hs
    exact iwaniecAuxUpper_deriv_neg hs

def iwaniecAuxGStart (rank : Nat) : Real := if Even rank then 2 else 1

def iwaniecAuxGTailStart (rank : Nat) : Real := if Even rank then 2 else 3

theorem iwaniecAuxG_pos_exactDomain (rank : Nat) {s : Real} (hs : iwaniecAuxGStart rank ≤ s) :
    0 < iwaniecAuxG rank s := by
  unfold iwaniecAuxGStart at hs
  unfold iwaniecAuxG
  by_cases hr : Even rank
  · simp only [if_pos hr] at hs ⊢
    exact iwaniecAuxLower_pos hs
  · simp only [if_neg hr] at hs ⊢
    exact iwaniecAuxUpper_pos hs

theorem iwaniecAuxG_antitoneOn_exactDomain (rank : Nat) :
    AntitoneOn (iwaniecAuxG rank) (Set.Ici (iwaniecAuxGStart rank)) := by
  unfold iwaniecAuxG iwaniecAuxGStart
  split
  · exact iwaniecAuxLower_antitoneOn
  · exact iwaniecAuxUpper_antitoneOn

theorem iwaniecAuxG_tail_integrable (rank : Nat) {s : Real} (hs : iwaniecAuxGTailStart rank ≤ s) :
    IntegrableOn (fun t : Real => iwaniecAuxG (rank + 1) (t - 1) * t / (t - 1) ^ 2)
      (Set.Ioi s) := by
  by_cases hr : Even rank
  · have hsTwo : 2 ≤ s := by simpa only [iwaniecAuxGTailStart, if_pos hr] using hs
    simpa only [iwaniecAuxG, Nat.even_add_one, hr, not_true_eq_false, if_false,
      iwaniecAuxLowerTailKernel] using iwaniecAuxLowerTail_integrable hsTwo
  · have hsThree : 3 ≤ s := by simpa only [iwaniecAuxGTailStart, if_neg hr] using hs
    simpa only [iwaniecAuxG, Nat.even_add_one, hr, not_false_eq_true, if_true,
      iwaniecAuxUpperTailKernel] using iwaniecAuxUpperTail_integrable hsThree

/-- The paper's two auxiliary integral equations, with both parity and
their different lower endpoint restrictions retained literally. -/
theorem iwaniecAuxG_tail (rank : Nat) {s : Real} (hs : iwaniecAuxGTailStart rank ≤ s) :
    iwaniecAuxG rank s =
      ∫ t in Set.Ioi s, iwaniecAuxG (rank + 1) (t - 1) * t / (t - 1) ^ 2 := by
  by_cases hr : Even rank
  · have hsTwo : 2 ≤ s := by simpa only [iwaniecAuxGTailStart, if_pos hr] using hs
    simpa only [iwaniecAuxG, Nat.even_add_one, hr, not_true_eq_false, if_true, if_false,
      iwaniecAuxLowerTailKernel] using iwaniecAuxLower_tail hsTwo
  · have hsThree : 3 ≤ s := by simpa only [iwaniecAuxGTailStart, if_neg hr] using hs
    simpa only [iwaniecAuxG, Nat.even_add_one, hr, not_false_eq_true, if_true, if_false,
      iwaniecAuxUpperTailKernel] using iwaniecAuxUpper_tail hsThree

end

end Erdos1212Kernel
