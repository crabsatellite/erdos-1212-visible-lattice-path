import Erdos1212Kernel.IwaniecCorollaryThreeWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecReciprocalLog_coordinate_mem
    {level s T x : Real} (hy : 1 < level) (hs : 1 < s) (hsT : s ≤ T)
    (hx : x ∈ Set.Icc (iwaniecExpReciprocalScale (Real.log level) T)
      (iwaniecExpReciprocalScale (Real.log level) s)) :
    1 < x ∧ x < level ∧ Real.log level / Real.log x ∈ Set.Icc s T := by
  have hL : 0 < Real.log level := Real.log_pos hy
  have hT : 0 < T := by linarith
  have hs0 : 0 < s := by linarith
  have hleft : 1 < iwaniecExpReciprocalScale (Real.log level) T :=
    Real.one_lt_exp_iff.mpr (div_pos hL hT)
  have hx1 : 1 < x := hleft.trans_le hx.1
  have hx0 : 0 < x := by linarith
  have hright : iwaniecExpReciprocalScale (Real.log level) s < level := by
    calc
      _ < Real.exp (Real.log level) := Real.exp_lt_exp.mpr (div_lt_self hL hs)
      _ = _ := Real.exp_log (by linarith)
  have hxlevel : x < level := hx.2.trans_lt hright
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hloglo := Real.log_le_log (Real.exp_pos (Real.log level / T)) hx.1
  have hloghi := Real.log_le_log hx0 hx.2
  simp only [iwaniecExpReciprocalScale, Real.log_exp] at hloglo hloghi
  have htlow : s ≤ Real.log level / Real.log x := by
    apply (le_div_iff₀ hl).mpr
    have hh := (le_div_iff₀ hs0).mp hloghi
    linarith only [hh]
  have hthigh : Real.log level / Real.log x ≤ T := by
    apply (div_le_iff₀ hl).mpr
    have hh := (div_le_iff₀ hT).mp hloglo
    linarith only [hh]
  exact ⟨hx1, hxlevel, htlow, hthigh⟩

theorem iwaniecCorollaryThreeScaledProfile_pos (rank : Nat) (level : Real)
    {s : Real} (hs : 3 ≤ s) : 0 < iwaniecCorollaryThreeScaledProfile rank level s := by
  have hratio : 0 < s / (s - 1) := div_pos (by linarith) (by linarith)
  exact mul_pos (iwaniecCorollaryThreeProfile_pos rank level hs) (pow_pos hratio 2)

theorem iwaniecCorollaryThreePrimeWeight_monotoneOn (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecAuxSZero ≤ s) (hsxi : s ≤ iwaniecPaperXi level) :
    MonotoneOn (iwaniecCorollaryThreePrimeWeight rank level)
      (Set.Icc (iwaniecExpReciprocalScale (Real.log level) (iwaniecPaperXi level))
        (iwaniecExpReciprocalScale (Real.log level) s)) := by
  have hs1 : 1 < s := by linarith [iwaniecAuxSZero_large]
  intro x hx z hz hxz
  obtain ⟨hx1, hxlevel, hxt⟩ := iwaniecReciprocalLog_coordinate_mem hy hs1 hsxi hx
  obtain ⟨hz1, hzlevel, hzt⟩ := iwaniecReciprocalLog_coordinate_mem hy hs1 hsxi hz
  have htx : Real.log level / Real.log x ∈ Set.Icc iwaniecAuxSZero (iwaniecPaperXi level) :=
    ⟨hs.trans hxt.1, hxt.2⟩
  have htz : Real.log level / Real.log z ∈ Set.Icc iwaniecAuxSZero (iwaniecPaperXi level) :=
    ⟨hs.trans hzt.1, hzt.2⟩
  have horder : Real.log level / Real.log z ≤ Real.log level / Real.log x :=
    div_le_div_of_nonneg_left (Real.log_pos hy).le (Real.log_pos hx1)
      (Real.log_le_log (by linarith) hxz)
  have hprofile := iwaniecCorollaryThreeScaledProfile_antitoneOn rank hy htz htx horder
  rw [iwaniecCorollaryThreePrimeWeight_scaled_normalization rank hy hx1 hxlevel,
    iwaniecCorollaryThreePrimeWeight_scaled_normalization rank hy hz1 hzlevel]
  exact div_le_div_of_nonneg_right hprofile (sq_nonneg (Real.log level))

theorem iwaniecCorollaryThreePrimeWeight_pos_on (rank : Nat)
    {level s x : Real} (hy : 1 < level) (hs : iwaniecAuxSZero ≤ s) (hsxi : s ≤ iwaniecPaperXi level)
    (hx : x ∈ Set.Icc (iwaniecExpReciprocalScale (Real.log level) (iwaniecPaperXi level))
      (iwaniecExpReciprocalScale (Real.log level) s)) :
    0 < iwaniecCorollaryThreePrimeWeight rank level x := by
  have hs1 : 1 < s := by linarith [iwaniecAuxSZero_large]
  obtain ⟨hx1, hxlevel, hxt⟩ := iwaniecReciprocalLog_coordinate_mem hy hs1 hsxi hx
  have ht3 : 3 ≤ Real.log level / Real.log x := by linarith [hxt.1, iwaniecAuxSZero_large]
  rw [iwaniecCorollaryThreePrimeWeight_scaled_normalization rank hy hx1 hxlevel]
  exact div_pos (iwaniecCorollaryThreeScaledProfile_pos rank level ht3)
    (sq_pos_of_pos (Real.log_pos hy))

end

end Erdos1212Kernel
