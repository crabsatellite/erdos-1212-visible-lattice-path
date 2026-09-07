import Erdos1212Kernel.IwaniecPrimeWeightedAbel

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1200000

theorem sum_Ico_backwardDifference
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    ∑ n ∈ Finset.Ico B A, (b (n + 1) - b n) = b A - b B := by
  induction A, hBA using Nat.le_induction with
  | base => simp
  | succ A hBA ih =>
      rw [Finset.sum_Ico_succ_top hBA, ih]
      ring

theorem abs_iwaniecPrimeReciprocalRemainderAbel_le
    (b : Nat → Real) {B A : Nat} {epsilon : Real}
    (hBA : B ≤ A) (hepsilon : 0 ≤ epsilon)
    (hbNonneg : ∀ n ∈ Finset.Icc B A, 0 ≤ b n)
    (hbIncreasing : ∀ n ∈ Finset.Ico B A, b n ≤ b (n + 1))
    (hrem : ∀ n ∈ Finset.Icc (B - 1) A,
      |iwaniecPrimeReciprocalRemainder n| ≤ epsilon) :
    |iwaniecPrimeReciprocalRemainderAbel b B A| ≤
      2 * epsilon * b A := by
  have hbB : 0 ≤ b B := hbNonneg B (by simp [hBA])
  have hbA : 0 ≤ b A := hbNonneg A (by simp [hBA])
  have hremA : |iwaniecPrimeReciprocalRemainder A| ≤ epsilon := by
    apply hrem A
    simp
    omega
  have hremB : |iwaniecPrimeReciprocalRemainder (B - 1)| ≤ epsilon := by
    apply hrem (B - 1)
    simp
    omega
  have hinner :
      |(∑ n ∈ Finset.Ico B A,
        iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1)))| ≤
        epsilon * (b A - b B) := by
    calc
      |(∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1)))| ≤
          ∑ n ∈ Finset.Ico B A,
            |iwaniecPrimeReciprocalRemainder n *
              (b n - b (n + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico B A,
          epsilon * (b (n + 1) - b n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hbn := hbIncreasing n hn
        have hremn : |iwaniecPrimeReciprocalRemainder n| ≤ epsilon := by
          apply hrem n
          have hnData := Finset.mem_Ico.mp hn
          simp only [Finset.mem_Icc]
          omega
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hbn)]
        convert mul_le_mul_of_nonneg_right hremn
          (sub_nonneg.mpr hbn) using 1 <;> ring
      _ = epsilon * (b A - b B) := by
        rw [← Finset.mul_sum, sum_Ico_backwardDifference b hBA]
  have htermA :
      |iwaniecPrimeReciprocalRemainder A * b A| ≤ epsilon * b A := by
    rw [abs_mul, abs_of_nonneg hbA]
    exact mul_le_mul_of_nonneg_right hremA hbA
  have htermB :
      |iwaniecPrimeReciprocalRemainder (B - 1) * b B| ≤
        epsilon * b B := by
    rw [abs_mul, abs_of_nonneg hbB]
    exact mul_le_mul_of_nonneg_right hremB hbB
  unfold iwaniecPrimeReciprocalRemainderAbel
  calc
    |(∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1))) +
        iwaniecPrimeReciprocalRemainder A * b A -
        iwaniecPrimeReciprocalRemainder (B - 1) * b B| ≤
      |(∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1))) +
        iwaniecPrimeReciprocalRemainder A * b A| +
        |iwaniecPrimeReciprocalRemainder (B - 1) * b B| :=
      abs_sub _ _
    _ ≤
      (|(∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1)))| +
        |iwaniecPrimeReciprocalRemainder A * b A|) +
        |iwaniecPrimeReciprocalRemainder (B - 1) * b B| := by
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤
      (epsilon * (b A - b B) + epsilon * b A) +
        epsilon * b B := by
      exact add_le_add (add_le_add hinner htermA) htermB
    _ = 2 * epsilon * b A := by ring

/-- Effective Mertens remainder control implies the exact weighted prime-sum
error estimate used by Iwaniec's Lemma 13.  The analytic rate remains an
explicit producer hypothesis here; the Abel consumer itself is kernel-only. -/
theorem iwaniecPrimeReciprocalWeightedInterval_sub_logAbel_le
    (b : Nat → Real) {B A : Nat} {epsilon : Real}
    (hBA : B ≤ A) (hepsilon : 0 ≤ epsilon)
    (hbNonneg : ∀ n ∈ Finset.Icc B A, 0 ≤ b n)
    (hbIncreasing : ∀ n ∈ Finset.Ico B A, b n ≤ b (n + 1))
    (hrem : ∀ n ∈ Finset.Icc (B - 1) A,
      |iwaniecPrimeReciprocalRemainder n| ≤ epsilon) :
    |iwaniecPrimeReciprocalWeightedInterval b B A -
        iwaniecPrimeReciprocalLogAbel b B A| ≤
      2 * epsilon * b A := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_logAbel_add_remainderAbel
    b hBA]
  ring_nf
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (abs_iwaniecPrimeReciprocalRemainderAbel_le b hBA hepsilon
      hbNonneg hbIncreasing hrem)

/-- Uniform qualitative weighted form of the Mertens input.  This is the
exact quantifier order needed later: once the lower endpoint is large, every
upper endpoint and every nonnegative increasing weight are controlled. -/
theorem eventually_iwaniecPrimeReciprocalWeightedInterval_sub_logAbel_le
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ N₀ : Nat, ∀ B A : Nat, ∀ b : Nat → Real,
      N₀ + 1 ≤ B → B ≤ A →
      (∀ n ∈ Finset.Icc B A, 0 ≤ b n) →
      (∀ n ∈ Finset.Ico B A, b n ≤ b (n + 1)) →
      |iwaniecPrimeReciprocalWeightedInterval b B A -
          iwaniecPrimeReciprocalLogAbel b B A| ≤
        2 * epsilon * b A := by
  rcases Metric.tendsto_atTop.mp tendsto_iwaniecPrimeReciprocalRemainder_zero
      epsilon hepsilon with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro B A b hB hBA hbNonneg hbIncreasing
  apply iwaniecPrimeReciprocalWeightedInterval_sub_logAbel_le b hBA
    hepsilon.le hbNonneg hbIncreasing
  intro n hn
  have hnLower : N₀ ≤ n := by
    have hnData := Finset.mem_Icc.mp hn
    omega
  have hdist := hN₀ n hnLower
  rw [dist_zero_right, Real.norm_eq_abs] at hdist
  exact hdist.le

end

end Erdos1212Kernel
