import Erdos1212Kernel.IwaniecCorollaryThreeEndpoint

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

/-- The actual shifted-G domain: 3 in the even case and 2 in the odd
case. This is not identified with the different lower range in the scan. -/
def iwaniecCorollaryThreeDomainStart (rank : Nat) : Real := iwaniecAuxGStart rank + 1

theorem iwaniecCorollaryThreeDomainStart_bounds (rank : Nat) :
    2 ≤ iwaniecCorollaryThreeDomainStart rank ∧ iwaniecCorollaryThreeDomainStart rank ≤ 3 := by
  unfold iwaniecCorollaryThreeDomainStart iwaniecAuxGStart
  split_ifs <;> norm_num

theorem iwaniecCorollaryThreeDomainStart_eq (rank : Nat) :
    iwaniecCorollaryThreeDomainStart rank = (5 + (-1 : Real) ^ rank) / 2 := by
  rw [neg_one_pow_eq_ite]
  unfold iwaniecCorollaryThreeDomainStart iwaniecAuxGStart
  split_ifs <;> norm_num

theorem iwaniecCorollaryThreeDomainStart_eq_tail (rank : Nat) :
    iwaniecCorollaryThreeDomainStart rank = iwaniecAuxGTailStart (rank + 1) := by
  unfold iwaniecCorollaryThreeDomainStart iwaniecAuxGStart iwaniecAuxGTailStart
  by_cases hr : Even rank <;> simp [Nat.even_add_one, hr] <;> norm_num

theorem iwaniecAuxG_shift_le_eight_square_exactDomain (rank : Nat)
    {s : Real} (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecAuxG rank (s - 1) ≤ 8 * s ^ 2 * iwaniecAuxG (rank + 1) s := by
  by_cases hs3 : 3 ≤ s
  · exact iwaniecAuxG_shift_le_eight_square rank hs3
  · have hs2 : 2 ≤ s := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
    have hr : ¬Even rank := by
      intro hr
      have hh := hs
      simp only [iwaniecCorollaryThreeDomainStart, iwaniecAuxGStart, if_pos hr] at hh
      linarith
    have hshift : iwaniecAuxG rank (s - 1) = 1 := by
      rw [iwaniecAuxG, if_neg hr, iwaniecAuxUpper_initial (by linarith)]
    have hnext : iwaniecAuxG (rank + 1) s = iwaniecAuxLower s := by
      simp only [iwaniecAuxG, Nat.even_add_one, hr, not_false_eq_true, if_true]
    have hhalf : (1 / 2 : Real) ≤ iwaniecAuxG (rank + 1) s := by
      rw [hnext, iwaniecAuxLower_initial (le_of_not_ge hs3)]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < s - 1 by linarith)
      have hinv := one_div_le_one_div_of_le (show 0 < s - 1 by linarith) (show s - 1 ≤ 2 by linarith)
      linarith
    have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 8 * s ^ 2 by positivity)
    rw [hshift]
    nlinarith only [hh, hs2]

theorem iwaniecAuxG_squared_profile_bound (rank : Nat)
    {s : Real} (hs : iwaniecCorollaryThreeDomainStart rank ≤ s) :
    iwaniecAuxG rank (s - 1) * (s / (s - 1)) ^ 2 ≤
      32 * s ^ 2 * iwaniecAuxG (rank + 1) s := by
  have hs2 : 2 ≤ s := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hratio : s / (s - 1) ≤ 2 := by
    apply (div_le_iff₀ (show 0 < s - 1 by linarith)).mpr
    linarith only [hs2]
  have hratio0 : 0 ≤ s / (s - 1) := div_nonneg (by linarith) (by linarith)
  have hsq : (s / (s - 1)) ^ 2 ≤ 4 := by
    have hh := pow_le_pow_left₀ hratio0 hratio 2
    norm_num at hh
    exact hh
  have hGnext := (iwaniecAuxG_pos (rank + 1) hs2).le
  have hh := mul_le_mul (iwaniecAuxG_shift_le_eight_square_exactDomain rank hs) hsq
    (sq_nonneg _) (by positivity : 0 ≤ 8 * s ^ 2 * iwaniecAuxG (rank + 1) s)
  nlinarith only [hh]

end

end Erdos1212Kernel
