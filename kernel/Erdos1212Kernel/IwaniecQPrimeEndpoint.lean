import Erdos1212Kernel.IwaniecPaperQMiddleExpansion
import Erdos1212Kernel.IwaniecAuxiliaryComparison

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecParitySieveProfile_le_twelve_auxG_exactDomain (rank : Nat) {s : Real}
    (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecParitySieveProfile rank s ≤ 12 * iwaniecAuxG rank s := by
  by_cases hs2 : 2 ≤ s
  · exact (iwaniecParitySieveProfile_lt_twelve_auxG rank rank hs2).le
  · have hr : ¬Even rank := by
      intro hr
      have hh : 2 ≤ s := by simpa only [iwaniecAuxGStart, if_pos hr] using hs
      exact hs2 hh
    have hs1 : 1 ≤ s := by simpa only [iwaniecAuxGStart, if_neg hr] using hs
    have hthree := (iwaniecParitySieveProfile_lt_twelve_auxG rank rank (s := 3) (by norm_num)).le
    simp only [iwaniecParitySieveProfile, iwaniecAuxG, if_neg hr] at hthree ⊢
    rw [iwaniecOddSieveSeries_eq_three hs1 (by linarith), iwaniecAuxUpper_initial (by linarith)]
    rwa [iwaniecAuxUpper_initial (le_refl 3)] at hthree

theorem iwaniecParitySieveProfile_shift_bound (rank : Nat) {s : Real}
    (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecParitySieveProfile rank (s - 1) ≤ 96 * s ^ 2 * iwaniecAuxG (rank + 1) s := by
  have hstart : iwaniecAuxGStart rank ≤ s - 1 := by
    unfold iwaniecCorollaryThreeDomainStart at hs
    linarith only [hs]
  have hf := iwaniecParitySieveProfile_le_twelve_auxG_exactDomain rank hstart
  have hG := mul_le_mul_of_nonneg_left (iwaniecAuxG_shift_le_eight_square_exactDomain rank hs)
    (by norm_num : (0 : Real) ≤ 12)
  exact hf.trans (by convert hG using 1 <;> ring)

theorem iwaniecAuxGStart_le_recursion_start (rank : Nat) :
    iwaniecAuxGStart (rank + 1) ≤ iwaniecCorollaryThreeDomainStart rank := by
  by_cases hr : Even rank <;>
    norm_num [iwaniecAuxGStart, iwaniecCorollaryThreeDomainStart, Nat.even_add_one, hr]

theorem iwaniecParityReciprocalLogWeight_exp_endpoint (rank : Nat) {L s : Real}
    (hL : L ≠ 0) (hs : s ≠ 0) :
    iwaniecParityReciprocalLogWeight rank L (Real.exp (L / s)) =
      iwaniecParitySieveProfile rank (s - 1) / (L - L / s) := by
  have hquot : L / (L / s) = s := by field_simp [hL, hs]
  simp only [iwaniecParityReciprocalLogWeight, iwaniecReciprocalLogWeight, Real.log_exp, hquot]

/-- The actual endpoint weight of effective Corollary 1, bounded in
the successor G scale on the whole parity-dependent recursion domain. -/
theorem iwaniecQ_prime_endpoint_bound (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecParityReciprocalLogWeight rank (Real.log level) (Real.exp (Real.log level / s)) ≤
      192 * s ^ 2 * iwaniecAuxG (rank + 1) s / Real.log level := by
  let L := Real.log level
  have hL : 0 < L := Real.log_pos hy
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hs0 : 0 < s := by linarith
  have hdiv : L / s ≤ L / 2 := div_le_div_of_nonneg_left hL.le (by norm_num) hs2
  have hden : 0 < L - L / s := by linarith
  have hhalf : L / 2 ≤ L - L / s := by linarith
  have hG := (iwaniecAuxG_pos_exactDomain (rank + 1)
    ((iwaniecAuxGStart_le_recursion_start rank).trans hs)).le
  rw [iwaniecParityReciprocalLogWeight_exp_endpoint rank hL.ne' hs0.ne']
  calc
    _ ≤ (96 * s ^ 2 * iwaniecAuxG (rank + 1) s) / (L - L / s) :=
      div_le_div_of_nonneg_right (iwaniecParitySieveProfile_shift_bound rank hs) hden.le
    _ ≤ (96 * s ^ 2 * iwaniecAuxG (rank + 1) s) / (L / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
    _ = _ := by dsimp [L]; ring

end

end Erdos1212Kernel
