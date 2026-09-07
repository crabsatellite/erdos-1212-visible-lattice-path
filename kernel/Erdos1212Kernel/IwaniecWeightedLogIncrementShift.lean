import Erdos1212Kernel.IwaniecLogKernelDistortion

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem sum_Icc_succ_shift
    (f : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    ∑ n ∈ Finset.Icc B A, f (n + 1) =
      ∑ m ∈ Finset.Icc (B + 1) (A + 1), f m := by
  apply Finset.sum_bij (fun n _hn => n + 1)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨m - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro n hn
    rfl

/-- Aggregate adjacent-interval distortion for a nonnegative increasing
weight.  Every factor and endpoint is finite and literal. -/
theorem iwaniecLogLogIncrementWeightedInterval_le_shift
    (b : Nat → Real) {B A : Nat} {rho : Real}
    (hB : 3 ≤ B) (hBA : B ≤ A) (hrho : 0 ≤ rho)
    (hbNonneg : ∀ n ∈ Finset.Icc B (A + 1), 0 ≤ b n)
    (hbIncreasing : ∀ n ∈ Finset.Icc B A, b n ≤ b (n + 1))
    (hratio : ∀ k : Nat, B - 1 ≤ k →
      iwaniecLogKernelTwoStepRatio k ≤ rho) :
    iwaniecLogLogIncrementWeightedInterval b B A ≤
      rho * iwaniecLogLogIncrementWeightedInterval b (B + 1) (A + 1) := by
  unfold iwaniecLogLogIncrementWeightedInterval
  calc
    (∑ n ∈ Finset.Icc B A,
        b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1))) ≤
      ∑ n ∈ Finset.Icc B A,
        rho * (b (n + 1) *
          (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData := Finset.mem_Icc.mp hn
      have hpoint := iwaniecWeightedLogLogIncrement_le_ratio_mul_next b
        (hB.trans hnData.1)
        (hbNonneg n (Finset.mem_Icc.mpr ⟨hnData.1, hnData.2.trans (Nat.le_succ A)⟩))
        (hbIncreasing n hn)
      have hnextNonneg :
          0 ≤ b (n + 1) *
            (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) := by
        apply mul_nonneg
        · apply hbNonneg (n + 1)
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · have hkernel := iwaniecLogKernel_at_nat_le_logLogIncrement
              (show 3 ≤ n + 1 by omega)
          exact (iwaniecLogKernel_pos (by norm_cast; omega)).le.trans hkernel
      exact hpoint.trans (mul_le_mul_of_nonneg_right
        (hratio (n - 1) (by omega)) hnextNonneg)
    _ = rho * ∑ n ∈ Finset.Icc B A,
        b (n + 1) *
          (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) := by
      rw [Finset.mul_sum]
    _ = rho * ∑ m ∈ Finset.Icc (B + 1) (A + 1),
        b m * (iwaniecLogLogValue m - iwaniecLogLogValue (m - 1)) := by
      apply congrArg (fun value : Real => rho * value)
      have hshift := sum_Icc_succ_shift
        (fun m => b m *
          (iwaniecLogLogValue m - iwaniecLogLogValue (m - 1))) hBA
      simpa using hshift

/-- Uniform `1 + delta` aggregate distortion once the lower endpoint is
large. -/
theorem eventually_iwaniecLogLogIncrementWeightedInterval_le_shift
    {delta : Real} (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ B A : Nat, ∀ b : Nat → Real,
      B₀ ≤ B → B ≤ A →
      (∀ n ∈ Finset.Icc B (A + 1), 0 ≤ b n) →
      (∀ n ∈ Finset.Icc B A, b n ≤ b (n + 1)) →
      iwaniecLogLogIncrementWeightedInterval b B A ≤
        (1 + delta) *
          iwaniecLogLogIncrementWeightedInterval b (B + 1) (A + 1) := by
  have hratioEvent :=
    eventually_iwaniecLogKernelTwoStepRatio_le_one_add hdelta
  rw [eventually_atTop] at hratioEvent
  obtain ⟨K₀, hK₀⟩ := hratioEvent
  refine ⟨max 3 (K₀ + 1), ?_⟩
  intro B A b hB hBA hbNonneg hbIncreasing
  apply iwaniecLogLogIncrementWeightedInterval_le_shift b
    (le_trans (Nat.le_max_left 3 (K₀ + 1)) hB) hBA
    (by linarith) hbNonneg hbIncreasing
  intro k hk
  apply hK₀
  omega

end

end Erdos1212Kernel
