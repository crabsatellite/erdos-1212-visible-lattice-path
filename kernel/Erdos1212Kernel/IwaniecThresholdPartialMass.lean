import Erdos1212Kernel.IwaniecThresholdLayer

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

def iwaniecThresholdPartialMass {α : Type*} (restriction : List α → α → Bool) (w : α → Real)
    (selected tail : List α) (depth : Nat) : Real :=
  ∑ k ∈ Finset.range (depth + 1), iwaniecThresholdLayer restriction w selected tail k

@[simp] theorem iwaniecThresholdPartialMass_zero {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) :
    iwaniecThresholdPartialMass restriction w selected tail 0 = 0 := by
  simp [iwaniecThresholdPartialMass]

@[simp] theorem iwaniecThresholdPartialMass_nil {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected : List α) (depth : Nat) :
    iwaniecThresholdPartialMass restriction w selected [] depth = 0 := by
  simp [iwaniecThresholdPartialMass]

theorem iwaniecThresholdPartialMass_nonneg {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (depth : Nat) :
    0 ≤ iwaniecThresholdPartialMass restriction w selected tail depth :=
  Finset.sum_nonneg (fun k _ => iwaniecThresholdLayer_nonneg restriction w selected tail k)

theorem iwaniecThresholdLayer_sum_shift {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (depth : Nat) :
    (∑ k ∈ Finset.range (depth + 1), iwaniecThresholdLayer restriction w selected tail (k + 1)) =
      iwaniecThresholdPartialMass restriction w selected tail (depth + 1) := by
  unfold iwaniecThresholdPartialMass
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [iwaniecThresholdLayer_zero, add_zero]

theorem iwaniecThresholdPartialMass_succ {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected tail : List α) (depth : Nat) :
    iwaniecThresholdPartialMass restriction w selected tail (depth + 1) =
      iwaniecThresholdPartialMass restriction w selected tail depth +
        iwaniecThresholdLayer restriction w selected tail (depth + 1) := by
  unfold iwaniecThresholdPartialMass
  rw [Finset.sum_range_succ]

/-- Literal cumulative first-failure recursion with the precise depth
decrement on a successful selection. -/
theorem iwaniecThresholdPartialMass_cons_succ {α : Type*} (restriction : List α → α → Bool)
    (w : α → Real) (selected : List α) (p : α) (tail : List α) (depth : Nat) :
    iwaniecThresholdPartialMass restriction w selected (p :: tail) (depth + 1) =
      iwaniecThresholdPartialMass restriction w selected tail (depth + 1) +
        if Even selected.length ∨ restriction selected p then
          |w p| * iwaniecThresholdPartialMass restriction w (selected ++ [p]) tail depth
        else |w p| * |iwaniecListEulerProduct w tail| := by
  rw [← iwaniecThresholdLayer_sum_shift, ← iwaniecThresholdLayer_sum_shift]
  by_cases hc : Even selected.length ∨ restriction selected p
  · simp only [iwaniecThresholdLayer, if_pos hc, Finset.sum_add_distrib,
      iwaniecThresholdPartialMass, Finset.mul_sum]
  · simp only [iwaniecThresholdLayer, if_neg hc, Finset.sum_add_distrib]
    simp

end

end Erdos1212Kernel
