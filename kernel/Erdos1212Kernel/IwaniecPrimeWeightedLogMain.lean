import Erdos1212Kernel.IwaniecPrimeWeightedRemainder

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecLogLogValue (n : Nat) : Real :=
  Real.log (Real.log n)

def iwaniecLogLogIncrementWeightedInterval
    (b : Nat → Real) (B A : Nat) : Real :=
  ∑ n ∈ Finset.Icc B A,
    b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1))

/-- The dual finite Abel identity, converting the paper's cumulative-sum
form into the weighted sum of consecutive logarithmic increments. -/
theorem iwaniecDiscreteDualPartialSummation
    (L b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    (∑ n ∈ Finset.Ico B A, L n * (b n - b (n + 1))) +
        L A * b A - L (B - 1) * b B =
      ∑ n ∈ Finset.Icc B A, b n * (L n - L (n - 1)) := by
  induction A, hBA using Nat.le_induction with
  | base =>
      simp
      ring
  | succ A hBA ih =>
      rw [Finset.sum_Ico_succ_top hBA,
        Finset.sum_Icc_succ_top (by omega)]
      have hpred : A + 1 - 1 = A := by omega
      rw [hpred]
      linear_combination ih

theorem iwaniecPrimeReciprocalLogMain_eq
    (n : Nat) :
    iwaniecPrimeReciprocalLogMain n =
      iwaniecLogLogValue n + Erdos696.Mertens.meisselMertensConstant := by
  rfl

theorem iwaniecPrimeReciprocalLogAbel_eq_logOnlyAbel
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalLogAbel b B A =
      (∑ n ∈ Finset.Ico B A,
        iwaniecLogLogValue n * (b n - b (n + 1))) +
      iwaniecLogLogValue A * b A -
      iwaniecLogLogValue (B - 1) * b B := by
  unfold iwaniecPrimeReciprocalLogAbel
  simp_rw [iwaniecPrimeReciprocalLogMain_eq, add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_Ico_forwardDifference b hBA]
  ring

/-- Exact discrete main term after Abel summation.  This is the line on
page 18 of Iwaniec 1971 immediately before comparison with the integral. -/
theorem iwaniecPrimeReciprocalLogAbel_eq_logLogIncrementWeightedInterval
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalLogAbel b B A =
      iwaniecLogLogIncrementWeightedInterval b B A := by
  rw [iwaniecPrimeReciprocalLogAbel_eq_logOnlyAbel b hBA]
  unfold iwaniecLogLogIncrementWeightedInterval
  exact iwaniecDiscreteDualPartialSummation
    iwaniecLogLogValue b hBA

/-- Weighted prime sum = logarithmic-increment main term + the isolated
Mertens remainder. -/
theorem iwaniecPrimeReciprocalWeightedInterval_eq_logLogIncrement_add_remainder
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      iwaniecLogLogIncrementWeightedInterval b B A +
        iwaniecPrimeReciprocalRemainderAbel b B A := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_logAbel_add_remainderAbel
    b hBA,
    iwaniecPrimeReciprocalLogAbel_eq_logLogIncrementWeightedInterval b hBA]

end

end Erdos1212Kernel
