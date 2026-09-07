import Erdos1212Kernel.IwaniecCorollaryThreeDomain
import Erdos1212Kernel.IwaniecCorollaryThreeMonotonicity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- The unweighted auxiliary prime weight used in the small-s part of
the printed proof, still at the literal real level y. -/
def iwaniecAuxPrimeSquaredWeight (rank : Nat) (level x : Real) : Real :=
  iwaniecAuxG rank (Real.log level / Real.log x - 1) / Real.log (level / x) ^ 2

theorem iwaniecAuxPrimeSquaredWeight_normalized (rank : Nat)
    {level x : Real} (hy : 1 < level) (hx : 1 < x) :
    iwaniecAuxPrimeSquaredWeight rank level x =
      iwaniecAuxG rank (Real.log level / Real.log x - 1) / (Real.log level - Real.log x) ^ 2 := by
  unfold iwaniecAuxPrimeSquaredWeight
  rw [Real.log_div (by linarith : level ≠ 0) (by linarith : x ≠ 0)]

theorem iwaniecAuxPrimeSquaredWeight_at_scale (rank : Nat)
    {level t : Real} (hy : 1 < level) (ht : 1 < t) :
    iwaniecAuxPrimeSquaredWeight rank level (iwaniecExpReciprocalScale (Real.log level) t) =
      (iwaniecAuxG rank (t - 1) * (t / (t - 1)) ^ 2) / Real.log level ^ 2 := by
  have hL := Real.log_pos hy
  have hx : 1 < iwaniecExpReciprocalScale (Real.log level) t :=
    Real.one_lt_exp_iff.mpr (div_pos hL (by linarith))
  rw [iwaniecAuxPrimeSquaredWeight_normalized rank hy hx]
  unfold iwaniecExpReciprocalScale
  rw [Real.log_exp]
  have hquot : Real.log level / (Real.log level / t) = t := by
    field_simp [hL.ne', (show t ≠ 0 by linarith)]
  rw [hquot]
  field_simp [hL.ne', (show t ≠ 0 by linarith), (show t - 1 ≠ 0 by linarith)]
  <;> ring

theorem iwaniecAuxPrimeSquaredWeight_pos_on (rank : Nat)
    {level s T x : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s)
    (hsT : s ≤ T) (hx : x ∈ Set.Icc (iwaniecExpReciprocalScale (Real.log level) T)
      (iwaniecExpReciprocalScale (Real.log level) s)) :
    0 < iwaniecAuxPrimeSquaredWeight rank level x := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  obtain ⟨hx1, hxy, htx⟩ := iwaniecReciprocalLog_coordinate_mem hy (by linarith) hsT hx
  have harg : iwaniecAuxGStart rank ≤ Real.log level / Real.log x - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at hs
    linarith only [hs, htx.1]
  have hden : 0 < Real.log level - Real.log x := sub_pos.mpr (Real.log_lt_log (by linarith) hxy)
  rw [iwaniecAuxPrimeSquaredWeight_normalized rank hy hx1]
  exact div_pos (iwaniecAuxG_pos_exactDomain rank harg) (sq_pos_of_pos hden)

theorem iwaniecAuxPrimeSquaredWeight_monotoneOn (rank : Nat)
    {level s T : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) (hsT : s ≤ T) :
    MonotoneOn (iwaniecAuxPrimeSquaredWeight rank level)
      (Set.Icc (iwaniecExpReciprocalScale (Real.log level) T)
        (iwaniecExpReciprocalScale (Real.log level) s)) := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  intro x hx z hz hxz
  obtain ⟨hx1, hxlevel, hxt⟩ := iwaniecReciprocalLog_coordinate_mem hy (by linarith) hsT hx
  obtain ⟨hz1, hzlevel, hzt⟩ := iwaniecReciprocalLog_coordinate_mem hy (by linarith) hsT hz
  have hxarg : iwaniecAuxGStart rank ≤ Real.log level / Real.log x - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at hs
    linarith only [hs, hxt.1]
  have hzarg : iwaniecAuxGStart rank ≤ Real.log level / Real.log z - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at hs
    linarith only [hs, hzt.1]
  have hlog := Real.log_le_log (by linarith : 0 < x) hxz
  have htorder := div_le_div_of_nonneg_left (Real.log_pos hy).le (Real.log_pos hx1) hlog
  have hG := iwaniecAuxG_antitoneOn_exactDomain rank hzarg hxarg (by linarith only [htorder])
  have hdenx : 0 < Real.log level - Real.log x := sub_pos.mpr (Real.log_lt_log (by linarith) hxlevel)
  have hdenz : 0 < Real.log level - Real.log z := sub_pos.mpr (Real.log_lt_log (by linarith) hzlevel)
  have hsquare := pow_le_pow_left₀ hdenz.le (sub_le_sub_left hlog (Real.log level)) 2
  rw [iwaniecAuxPrimeSquaredWeight_normalized rank hy hx1, iwaniecAuxPrimeSquaredWeight_normalized rank hy hz1]
  exact (div_le_div_of_nonneg_right hG (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (iwaniecAuxG_pos_exactDomain rank hzarg).le (sq_pos_of_pos hdenz) hsquare)

theorem iwaniecAuxPrimeSquaredWeight_endpoint_bound (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecAuxPrimeSquaredWeight rank level (iwaniecExpReciprocalScale (Real.log level) s) ≤
      32 * s ^ 2 * iwaniecAuxG (rank + 1) s / Real.log level ^ 2 := by
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  rw [iwaniecAuxPrimeSquaredWeight_at_scale rank hy (by linarith)]
  exact div_le_div_of_nonneg_right (iwaniecAuxG_squared_profile_bound rank hs) (sq_nonneg _)

end

end Erdos1212Kernel
