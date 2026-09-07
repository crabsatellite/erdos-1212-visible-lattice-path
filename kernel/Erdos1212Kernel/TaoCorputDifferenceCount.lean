import Erdos1212Kernel.TaoCorputFiniteSums

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1200000

theorem taoCorput_difference_row (F : Nat → Real) (j : Nat) :
    (∑ i ∈ Finset.Ico 1 j, F (j - i)) = ∑ h ∈ Finset.Icc 1 (j - 1), F h := by
  apply Finset.sum_bij (fun i _hi => j - i)
  · intro i hi
    have hi' := Finset.mem_Ico.mp hi
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro i hi k hk heq
    have hi' := Finset.mem_Ico.mp hi
    have hk' := Finset.mem_Ico.mp hk
    omega
  · intro h hh
    have hh' := Finset.mem_Icc.mp hh
    refine ⟨j - h, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i _hi
    rfl

/-- Each positive difference is counted at most H times in the source
off-diagonal sum; the diagonal is not included in this estimate. -/
theorem taoCorput_difference_count_bound (F : Nat → Real) (H : Nat) (hF : ∀ h, 0 ≤ F h) :
    (∑ j ∈ Finset.Icc 1 H, ∑ i ∈ Finset.Ico 1 j, F (j - i)) ≤
      (H : Real) * ∑ h ∈ Finset.Icc 1 H, F h := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 H, ∑ h ∈ Finset.Icc 1 H, F h := by
      apply Finset.sum_le_sum
      intro j hj
      rw [taoCorput_difference_row]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        have hj' := Finset.mem_Icc.mp hj
        have hh' := Finset.mem_Icc.mp hh
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      · intro h _hh _hnot
        exact hF h
    _ = _ := by simp [nsmul_eq_mul]

end

end Erdos1212Kernel
