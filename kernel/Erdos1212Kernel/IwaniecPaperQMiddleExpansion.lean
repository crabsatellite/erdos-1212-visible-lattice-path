import Erdos1212Kernel.IwaniecPaperQChildMainBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- Lemma 16 with its actual parity and quartic support. No exponential
base error is charged when s>=4 or the parent rank is odd. -/
theorem exists_iwaniecPaperQ_d2_correction_bound :
    ∃ D : Real, 0 < D ∧ ∀ (rank : Nat) (level s : Real), 1 < level → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant * (if Even rank then iwaniecPaperD2 level s else 0) ≤
        (if Even rank then iwaniecGTwo s else 0) / Real.log level +
        if Even rank ∧ s < 4 then D * Real.exp (-Real.sqrt (Real.log level / 6)) else 0 := by
  obtain ⟨D, hD, hbase⟩ := exists_iwaniecLemma16_constant
  refine ⟨D, hD, ?_⟩
  intro rank level s hy hs
  by_cases hr : Even rank
  · simp only [hr, if_true, true_and]
    by_cases hs4 : s < 4
    · rw [if_pos hs4]
      exact (hbase level s hy hs).le
    · rw [if_neg hs4, iwaniecPaperD2_eq_zero_of_four_le hy (le_of_not_gt hs4),
        iwaniecGTwo_eq_zero_of_four_le (le_of_not_gt hs4)]
      norm_num
  · simp [hr]

/-- The combined middle-rank estimate on printed page 24, before its
last error absorption. Every prime sum and correction is consumed here;
the remaining induction hypothesis is the literal rank-r Q statement. -/
theorem exists_iwaniecPaperQ_middle_expansion :
    ∃ Kmain Kerr D : Real, 0 < Kmain ∧ 0 < Kerr ∧ 0 < D ∧
      ∀ (C : Real) (rank : Nat) (level s : Real), 0 ≤ C → 1 < level →
        iwaniecAuxSZero ≤ iwaniecPaperXi level →
        iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level - 1 →
        (∀ y t : Real, 1 < y → iwaniecAuxGStart rank ≤ t → t ≤ iwaniecPaperXi y →
          Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ rank y t <
            iwaniecPaperQMajorant C rank y t) →
        Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (rank + 1) level s ≤
          iwaniecParitySieveProfile (rank + 1) s / Real.log level +
          Kmain * iwaniecParityReciprocalLogWeight rank (Real.log level) (Real.exp (Real.log level / s)) *
            Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)) +
          (C * ((rank : Real) / ((rank : Real) + 1))) *
            ((iwaniecAuxWeightPower level (max iwaniecAuxSZero s) * iwaniecAuxG (rank + 1) s /
              Real.log level ^ 2) *
              (1 + 100 * Kerr * iwaniecPaperXi level ^ 2 *
                Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)))) +
          (if Even (rank + 1) ∧ s < 4 then D * Real.exp (-Real.sqrt (Real.log level / 6)) else 0) +
          Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ (rank + 1) level (iwaniecPaperXi level - 1) := by
  obtain ⟨Kmain, hKmain, hmain⟩ := exists_iwaniecPaperQBand_child_main_profile_bound
  obtain ⟨Kerr, hKerr, herror⟩ := exists_iwaniecPaperQBand_child_error_bound
  obtain ⟨D, hD, hbase⟩ := exists_iwaniecPaperQ_d2_correction_bound
  refine ⟨Kmain, Kerr, D, hKmain, hKerr, hD, ?_⟩
  intro C rank level s hC hy hξ hs hsT hIH
  have hsξ : s ≤ iwaniecPaperXi level := by linarith only [hsT]
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hT : 4 ≤ iwaniecPaperXi level - 1 := by linarith [iwaniecAuxSZero_large]
  have hsum := iwaniecPaperQ_child_sum_le rank hy hξ hs hIH
  have hm := hmain rank level s hy hξ hs hsξ
  have he := mul_le_mul_of_nonneg_left (herror rank level s hy hξ hs hsξ)
    (show 0 ≤ C * ((rank : Real) / ((rank : Real) + 1)) by positivity)
  have hd := hbase (rank + 1) level s hy hs2
  rw [iwaniecPaperQ_successor_band_recursion rank hy hs hsT hT, mul_add, mul_add]
  linarith only [hsum, hm, he, hd]

end

end Erdos1212Kernel
