import Erdos1212Kernel.TaoDyadicScaleAbsorption

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1700000

def taoDyadicBlock (f : Nat → Complex) (r : Nat) : Complex :=
  ∑ m ∈ Finset.range (2 ^ r), f (2 ^ r + m)

theorem taoDyadicBlock_eq_Ico (f : Nat → Complex) (r : Nat) :
    taoDyadicBlock f r = ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), f n := by
  unfold taoDyadicBlock
  rw [Finset.sum_Ico_eq_sum_range]
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  rw [hpow, Nat.add_sub_cancel_left]

theorem taoFiniteDyadic_decomposition (f : Nat → Complex) (J : Nat) :
    (∑ r ∈ Finset.range J, taoDyadicBlock f r) =
      ∑ n ∈ Finset.Ico 1 (2 ^ J), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, taoDyadicBlock_eq_Ico]
      rw [Finset.sum_Ico_consecutive]
      · exact one_le_pow₀ (by norm_num)
      · rw [pow_succ]
        omega

theorem taoFiniteDyadic_norm_bound (F : Nat → Complex) (J : Nat) {L : Real}
    (hL : 0 ≤ L) (hblock : ∀ r < J, ‖F r‖ ≤ L) :
    ‖∑ r ∈ Finset.range J, F r‖ ≤ (J : Real) * L := by
  calc
    _ ≤ ∑ r ∈ Finset.range J, ‖F r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range J, L := by
      apply Finset.sum_le_sum
      intro r hr
      exact hblock r (Finset.mem_range.mp hr)
    _ = _ := by simp [nsmul_eq_mul]

theorem taoFiniteDyadic_partial_sum_bound (f : Nat → Complex) (J : Nat) {L : Real}
    (hL : 0 ≤ L) (hblock : ∀ r < J, ‖taoDyadicBlock f r‖ ≤ L) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), f n‖ ≤ (J : Real) * L := by
  rw [← taoFiniteDyadic_decomposition]
  exact taoFiniteDyadic_norm_bound (taoDyadicBlock f) J hL hblock

end

end Erdos1212Kernel
