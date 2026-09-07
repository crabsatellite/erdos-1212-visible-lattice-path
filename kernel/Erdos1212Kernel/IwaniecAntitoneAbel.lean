import Erdos1212Kernel.IwaniecPrimeWeightedRemainder

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- The same literal Abel remainder as in Lemma 13, with decreasing
weight variation. The bound is controlled by the lower endpoint b(B). -/
theorem abs_iwaniecPrimeReciprocalRemainderAbel_antitone_le
    (b : Nat → Real) {B A : Nat} {epsilon : Real}
    (hBA : B ≤ A) (hepsilon : 0 ≤ epsilon)
    (hbNonneg : ∀ n ∈ Finset.Icc B A, 0 ≤ b n)
    (hbDecreasing : ∀ n ∈ Finset.Ico B A, b (n + 1) ≤ b n)
    (hrem : ∀ n ∈ Finset.Icc (B - 1) A,
      |iwaniecPrimeReciprocalRemainder n| ≤ epsilon) :
    |iwaniecPrimeReciprocalRemainderAbel b B A| ≤
      2 * epsilon * b B := by
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
        epsilon * (b B - b A) := by
    calc
      |(∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1)))| ≤
          ∑ n ∈ Finset.Ico B A,
            |iwaniecPrimeReciprocalRemainder n *
              (b n - b (n + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico B A,
          epsilon * (b n - b (n + 1)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hbn := hbDecreasing n hn
        have hremn : |iwaniecPrimeReciprocalRemainder n| ≤ epsilon := by
          apply hrem n
          have hnData := Finset.mem_Ico.mp hn
          simp only [Finset.mem_Icc]
          omega
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hbn)]
        exact mul_le_mul_of_nonneg_right hremn (sub_nonneg.mpr hbn)
      _ = epsilon * (b B - b A) := by
        rw [← Finset.mul_sum, sum_Ico_forwardDifference b hBA]
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
      (epsilon * (b B - b A) + epsilon * b A) +
        epsilon * b B := by
      exact add_le_add (add_le_add hinner htermA) htermB
    _ = 2 * epsilon * b B := by ring

end

end Erdos1212Kernel
