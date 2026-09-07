import Erdos1212Kernel.TaoLogDirichletShort

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

def taoPrefixSum (z : Nat → Complex) (m : Nat) : Complex := ∑ n ∈ Finset.range m, z n

theorem taoPrefixSum_zero (z : Nat → Complex) : taoPrefixSum z 0 = 0 := by simp [taoPrefixSum]

theorem taoPrefixSum_succ (z : Nat → Complex) (m : Nat) :
    taoPrefixSum z (m + 1) - taoPrefixSum z m = z m := by
  simp only [taoPrefixSum, Finset.sum_range_succ]
  ring

theorem taoWeightedPrefix_telescope (w : Nat → Real) (m : Nat) :
    w m + ∑ n ∈ Finset.range m, (w n - w (n + 1)) = w 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      linarith

/-- Exact finite Abel identity with prefix sums, retaining the final
prefix and every weight difference. -/
theorem taoWeightedPrefix_abel_identity (z : Nat → Complex) (w : Nat → Real) (m : Nat) :
    (∑ n ∈ Finset.range (m + 1), (w n : Complex) * z n) =
      (w m : Complex) * taoPrefixSum z (m + 1) +
        ∑ n ∈ Finset.range m, ((w n - w (n + 1) : Real) : Complex) * taoPrefixSum z (n + 1) := by
  have h := taoFirstDerivative_abel_identity (taoPrefixSum z) (fun n => (w n : Complex)) m
  simp only [taoPrefixSum_succ, taoPrefixSum_zero, zero_mul, sub_zero] at h
  calc
    _ = ∑ n ∈ Finset.range (m + 1), z n * (w n : Complex) := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = taoPrefixSum z (m + 1) * (w m : Complex) +
        ∑ n ∈ Finset.range m, taoPrefixSum z (n + 1) * ((w n : Complex) - (w (n + 1) : Complex)) := h
    _ = _ := by
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro n _hn
        push_cast
        ring

/-- A nonnegative decreasing real weight costs only its initial value
against a uniform bound for all literal prefixes. -/
theorem taoWeightedPrefix_norm_bound (z : Nat → Complex) (w : Nat → Real) (M : Nat) {B : Real}
    (hB : 0 ≤ B) (hw0 : ∀ n ≤ M, 0 ≤ w n)
    (hmono : ∀ n, n + 1 < M → w (n + 1) ≤ w n)
    (hprefix : ∀ m ≤ M, ‖taoPrefixSum z m‖ ≤ B) :
    ‖∑ n ∈ Finset.range M, (w n : Complex) * z n‖ ≤ B * w 0 := by
  cases M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
      exact mul_nonneg hB (hw0 0 le_rfl)
  | succ m =>
      rw [taoWeightedPrefix_abel_identity]
      have hwm : 0 ≤ w m := hw0 m (by omega)
      have hend : ‖(w m : Complex) * taoPrefixSum z (m + 1)‖ ≤ B * w m := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwm]
        nlinarith [hprefix (m + 1) le_rfl]
      have hdiff (n : Nat) (hn : n ∈ Finset.range m) : 0 ≤ w n - w (n + 1) := by
        exact sub_nonneg.mpr (hmono n (by have := Finset.mem_range.mp hn; omega))
      have hsum : ‖∑ n ∈ Finset.range m,
          ((w n - w (n + 1) : Real) : Complex) * taoPrefixSum z (n + 1)‖ ≤
          B * ∑ n ∈ Finset.range m, (w n - w (n + 1)) := by
        calc
          _ ≤ ∑ n ∈ Finset.range m,
              ‖((w n - w (n + 1) : Real) : Complex) * taoPrefixSum z (n + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.range m, B * (w n - w (n + 1)) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdiff n hn)]
            have hp := hprefix (n + 1) (by have := Finset.mem_range.mp hn; omega)
            simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (hdiff n hn)
          _ = _ := by rw [Finset.mul_sum]
      have hnorm := norm_add_le ((w m : Complex) * taoPrefixSum z (m + 1))
        (∑ n ∈ Finset.range m,
          ((w n - w (n + 1) : Real) : Complex) * taoPrefixSum z (n + 1))
      have htel := taoWeightedPrefix_telescope w m
      nlinarith

end

end Erdos1212Kernel
