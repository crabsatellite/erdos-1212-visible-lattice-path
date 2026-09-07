import Erdos1212Kernel.IwaniecAuxiliaryCorollaryHigh

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1400000

def iwaniecAuxCorollaryConstant : Real := 1000 / iwaniecAuxM 5

theorem iwaniecAuxCorollaryConstant_gt_three_hundred : (300 : Real) < iwaniecAuxCorollaryConstant := by
  unfold iwaniecAuxCorollaryConstant
  rw [lt_div_iff₀ (iwaniecAuxM_pos (by norm_num : (2 : Real) ≤ 5))]
  have hM := iwaniecAuxM_le_three (s := 5) (by norm_num)
  linarith

theorem iwaniecAuxCorollaryRatio_lt_constant_highDomain
    (rank : Nat) {s : Real} (hs : 3 ≤ s) :
    iwaniecAuxCorollaryRatio rank s < iwaniecAuxCorollaryConstant := by
  by_cases hsSix : 6 ≤ s
  · exact (iwaniecAuxCorollaryRatio_lt_eight rank hsSix).trans
      (lt_trans (by norm_num : (8 : Real) < 300) iwaniecAuxCorollaryConstant_gt_three_hundred)
  · have h := iwaniecAuxCorollaryRatio_initial_bound rank ⟨hs, (lt_of_not_ge hsSix).le⟩
    apply h.trans_lt
    unfold iwaniecAuxCorollaryConstant
    exact div_lt_div_of_pos_right (by norm_num) (iwaniecAuxM_pos (by norm_num : (2 : Real) ≤ 5))

theorem iwaniecAuxCorollaryRatio_odd_initial
    (rank : Nat) (hr : ¬Even rank) {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) :
    iwaniecAuxCorollaryRatio rank s ≤ 12 := by
  have hbottom : iwaniecAuxG rank (s - 1) = 1 := by
    rw [iwaniecAuxG, if_neg hr, iwaniecAuxUpper_initial (by linarith [hs.2])]
  have htop := iwaniecAuxG_le_two (rank + 1) hs.1
  have htopPos := iwaniecAuxG_pos (rank + 1) hs.1
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by linarith [hs.1])
  have hlogUpper : Real.log s ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s by linarith [hs.1])
    linarith [hs.2]
  have hsq : (s - 1) ^ 2 ≤ 4 := by nlinarith [hs.1, hs.2]
  have hprod := mul_le_mul htop hsq (sq_nonneg (s - 1)) (by norm_num : (0 : Real) ≤ 2)
  have hnum := mul_le_mul hprod hlogUpper hlog (by norm_num : (0 : Real) ≤ 2 * 4)
  unfold iwaniecAuxCorollaryRatio
  rw [hbottom, one_mul, div_le_iff₀ (show 0 < s by linarith [hs.1])]
  nlinarith [hs.1]

/-- Corollary to source Lemma 10 with one proved absolute constant and
the literal parity-dependent open endpoint `(5+(-1)^rank)/2`. -/
theorem iwaniecAuxLemmaTenCorollary (rank : Nat) {s : Real}
    (hs : (5 + (-1 : Real) ^ rank) / 2 < s) :
    iwaniecAuxG (rank + 1) s * (s - 1) ^ 2 * Real.log s /
        (iwaniecAuxG rank (s - 1) * s) < iwaniecAuxCorollaryConstant := by
  change iwaniecAuxCorollaryRatio rank s < iwaniecAuxCorollaryConstant
  by_cases hsThree : 3 ≤ s
  · exact iwaniecAuxCorollaryRatio_lt_constant_highDomain rank hsThree
  · have hr : ¬Even rank := by
      intro heven
      rw [neg_one_pow_eq_ite, if_pos heven] at hs
      norm_num at hs
      linarith
    have hsTwo : 2 ≤ s := by
      rw [neg_one_pow_eq_ite, if_neg hr] at hs
      norm_num at hs
      linarith
    exact (iwaniecAuxCorollaryRatio_odd_initial rank hr ⟨hsTwo, (lt_of_not_ge hsThree).le⟩).trans_lt
      (lt_trans (by norm_num : (12 : Real) < 300) iwaniecAuxCorollaryConstant_gt_three_hundred)

end

end Erdos1212Kernel
