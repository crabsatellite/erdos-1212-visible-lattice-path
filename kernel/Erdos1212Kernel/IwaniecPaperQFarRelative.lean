import Erdos1212Kernel.IwaniecPaperQFarSource
import Erdos1212Kernel.IwaniecQFarRelativeScalar

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 550000

/-- The source's two far-tail comparisons, now applied to the actual
Q mass with its correct G_r index and no extra factor of level. -/
theorem eventually_iwaniecPaperQ_far_relative_piecewise :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      iwaniecPaperQ rank level (iwaniecPaperXi level - 1) <
        (if s ≤ iwaniecPaperXi level / 2 then iwaniecAuxG rank s / Real.log level ^ 4
         else iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4) := by
  filter_upwards [eventually_iwaniecPaperQ_far_source_bound, eventually_iwaniecQFar_source_scalar]
    with level hQ hscalar
  refine ⟨hQ.1, ?_⟩
  intro rank s hs hsxi
  exact (hQ.2 rank).trans_le (hscalar.2 rank s hs hsxi)

theorem eventually_iwaniecPaperQ_far_relative_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ (rank : Nat) (s : Real),
      iwaniecAuxGStart rank ≤ s → s ≤ iwaniecPaperXi level →
      iwaniecPaperQ rank level (iwaniecPaperXi level - 1) <
        iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4 := by
  filter_upwards [eventually_iwaniecPaperQ_far_relative_piecewise] with level hfar
  refine ⟨hfar.1, ?_⟩
  intro rank s hs hsxi
  have hh := hfar.2 rank s hs hsxi
  by_cases hsmall : s ≤ iwaniecPaperXi level / 2
  · rw [if_pos hsmall] at hh
    have hstart : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split <;> norm_num
    have hW : 1 ≤ iwaniecAuxWeightPower level s :=
      Real.one_le_rpow (iwaniecAuxWeightBase_one_le level (hstart.trans hs)) (by linarith)
    have hG : 0 ≤ iwaniecAuxG rank s := (iwaniecAuxG_pos_exactDomain rank hs).le
    have hWG : iwaniecAuxG rank s ≤ iwaniecAuxWeightPower level s * iwaniecAuxG rank s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hW hG
    exact hh.trans_le (div_le_div_of_nonneg_right hWG (pow_nonneg (Real.log_pos hfar.1).le 4))
  · rwa [if_neg hsmall] at hh

end

end Erdos1212Kernel
