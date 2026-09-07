import Erdos1212Kernel.IwaniecPaperStoppedLayer

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 550000

theorem iwaniecPaperStoppedPartial_eq_sum (offset : Nat) (level z : Real) (depth : Nat) :
    iwaniecPaperStoppedPartial offset level z depth =
      ∑ k ∈ Finset.range (depth + 1), iwaniecPaperStoppedLayer offset level z k := rfl

@[simp] theorem iwaniecPaperStoppedPartial_zero (offset : Nat) (level z : Real) :
    iwaniecPaperStoppedPartial offset level z 0 = 0 := by
  rw [iwaniecPaperStoppedPartial_eq_sum]
  simp

theorem iwaniecPaperStoppedPartial_nonneg (offset : Nat) (level z : Real) (depth : Nat) :
    0 ≤ iwaniecPaperStoppedPartial offset level z depth := by
  rw [iwaniecPaperStoppedPartial_eq_sum]
  exact Finset.sum_nonneg (fun k _ => iwaniecPaperStoppedLayer_nonneg offset level z k)

theorem iwaniecPaperStoppedPartial_succ (offset : Nat) (level z : Real) (depth : Nat) :
    iwaniecPaperStoppedPartial offset level z (depth + 1) =
      iwaniecPaperStoppedPartial offset level z depth + iwaniecPaperStoppedLayer offset level z (depth + 1) := by
  rw [iwaniecPaperStoppedPartial_eq_sum, iwaniecPaperStoppedPartial_eq_sum, Finset.sum_range_succ]

/-- Exact cumulative first-prime recursion. The immediate failure term
is explicit; it cannot be hidden in a higher-rank child. -/
theorem iwaniecPaperStoppedPartial_first_prime (offset : Nat) (level z : Real) (depth : Nat) :
    iwaniecPaperStoppedPartial offset level z (depth + 1) =
      ∑ p ∈ iwaniecStrictPrimePool z,
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecPaperStoppedPartial (offset + 1) (level / p) p depth
        else (p : Real)⁻¹ * iwaniecPaperR (p : Real) := by
  classical
  rw [iwaniecPaperStoppedPartial_eq_sum, Finset.sum_range_succ']
  simp only [iwaniecPaperStoppedLayer_zero, add_zero]
  simp_rw [iwaniecPaperStoppedLayer_first_prime]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc : Even offset ∨ (p : Real) ^ 3 < level
  · simp only [if_pos hc, iwaniecPaperStoppedPartial_eq_sum, Finset.mul_sum]
  · simp only [if_neg hc]
    simp

end

end Erdos1212Kernel
