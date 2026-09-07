import Erdos1212Kernel.IwaniecCubicRealCount

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecCubicRealTotalCount (offset : Nat) (level : Real)
    (factors : List Nat) (depth : Nat) : Nat :=
  ∑ k ∈ Finset.range (depth + 1), iwaniecCubicRealCount offset level factors k

@[simp]
theorem iwaniecCubicRealTotalCount_zero
    (offset : Nat) (level : Real) (factors : List Nat) :
    iwaniecCubicRealTotalCount offset level factors 0 = 1 := by
  simp [iwaniecCubicRealTotalCount]

theorem iwaniecCubicRealTotalCount_add_two
    (offset : Nat) (level : Real) (factors : List Nat) (depth : Nat) :
    iwaniecCubicRealTotalCount (offset + 2) level factors depth =
      iwaniecCubicRealTotalCount offset level factors depth := by
  simp only [iwaniecCubicRealTotalCount, iwaniecCubicRealCount_add_two]

/-- Exact finite support recursion.  The `1` is the empty tuple and remains
present in both parity cases. -/
theorem iwaniecCubicRealTotalCount_succ
    (offset : Nat) (level : Real) (factors : List Nat) (depth : Nat) :
    iwaniecCubicRealTotalCount offset level factors (depth + 1) =
      1 + ∑ i : Fin factors.length,
        if Even offset ∨ (factors[i] : Real) ^ 3 < level then
          iwaniecCubicRealTotalCount (offset + 1) (level / factors[i])
            (factors.drop (i.val + 1)) depth
        else 0 := by
  classical
  unfold iwaniecCubicRealTotalCount
  rw [Finset.sum_range_succ', iwaniecCubicRealCount_zero]
  simp_rw [iwaniecCubicRealCount_eq_sum_firstPrime]
  rw [Finset.sum_comm, add_comm]
  apply congrArg (fun n : Nat => 1 + n)
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hallow : Even offset ∨ (factors[i] : Real) ^ 3 < level
  · simp only [if_pos hallow]
  · simp only [if_neg hallow, Finset.sum_const_zero]

theorem iwaniecCubicRealTotalCount_unrestricted_first
    (level : Real) (factors : List Nat) (depth : Nat) :
    iwaniecCubicRealTotalCount 0 level factors (depth + 1) =
      1 + ∑ i : Fin factors.length,
        iwaniecCubicRealTotalCount 1 (level / factors[i])
          (factors.drop (i.val + 1)) depth := by
  rw [iwaniecCubicRealTotalCount_succ]
  simp

theorem iwaniecCubicRealTotalCount_constrained_first
    (level : Real) (factors : List Nat) (depth : Nat) :
    iwaniecCubicRealTotalCount 1 level factors (depth + 1) =
      1 + ∑ i : Fin factors.length,
        if (factors[i] : Real) ^ 3 < level then
          iwaniecCubicRealTotalCount 0 (level / factors[i])
            (factors.drop (i.val + 1)) depth
        else 0 := by
  rw [iwaniecCubicRealTotalCount_succ]
  have hoff : 1 + 1 = 0 + 2 := rfl
  simp only [hoff, iwaniecCubicRealTotalCount_add_two]
  simp

@[simp]
theorem iwaniecCubicRealTotalCount_nil
    (offset : Nat) (level : Real) (depth : Nat) :
    iwaniecCubicRealTotalCount offset level [] depth = 1 := by
  cases depth with
  | zero => simp
  | succ depth => rw [iwaniecCubicRealTotalCount_succ]; simp

/-- The original error mass is now a single finite total-count object, and
not merely related by a majorant. -/
theorem iwaniecCubicShiftedErrorMass_eq_realTotalCount
    {r y : Nat} (hr : 0 < r) (Q : Finset Nat) :
    iwaniecCubicShiftedErrorMass r y Q =
      (iwaniecCubicRealTotalCount 0 y
        (iwaniecDescendingFactors (iwaniecReferencePrimePool Q.card))
        (2 * r - 1) : Real) := by
  rw [iwaniecCubicShiftedErrorMass_eq_realCounts hr]
  unfold iwaniecCubicRealTotalCount
  have hdepth : 2 * r - 1 + 1 = 2 * r := by omega
  rw [hdepth]
  simp

end

end Erdos1212Kernel
