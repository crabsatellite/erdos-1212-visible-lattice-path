import Erdos1212Kernel.IwaniecPrimeReciprocalInterval

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecPrimeReciprocalPoint (n : Nat) : Real :=
  if n.Prime then (n : Real)⁻¹ else 0

def iwaniecPrimeReciprocalWeightedInterval
    (b : Nat → Real) (B A : Nat) : Real :=
  ∑ p ∈ (Nat.primesLE A).filter (fun p => B ≤ p),
    (p : Real)⁻¹ * b p

def iwaniecDiscreteIntervalPartial
    (a : Nat → Real) (B A : Nat) : Real :=
  ∑ n ∈ Finset.Icc B A, a n

def iwaniecDiscreteWeightedInterval
    (a b : Nat → Real) (B A : Nat) : Real :=
  ∑ n ∈ Finset.Icc B A, a n * b n

theorem iwaniecDiscreteIntervalPartial_succ
    (a : Nat → Real) {B A : Nat} (hBA : B ≤ A + 1) :
    iwaniecDiscreteIntervalPartial a B (A + 1) =
      iwaniecDiscreteIntervalPartial a B A + a (A + 1) := by
  unfold iwaniecDiscreteIntervalPartial
  exact Finset.sum_Icc_succ_top hBA a

theorem iwaniecDiscreteWeightedInterval_succ
    (a b : Nat → Real) {B A : Nat} (hBA : B ≤ A + 1) :
    iwaniecDiscreteWeightedInterval a b B (A + 1) =
      iwaniecDiscreteWeightedInterval a b B A +
        a (A + 1) * b (A + 1) := by
  unfold iwaniecDiscreteWeightedInterval
  exact Finset.sum_Icc_succ_top hBA (fun n => a n * b n)

/-- Exact finite Abel summation, expressed with the interval partial sum.
This is the discrete identity used in Iwaniec 1971, Lemma 13. -/
theorem iwaniecDiscreteIntervalPartialSummation
    (a b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecDiscreteWeightedInterval a b B A =
      iwaniecDiscreteIntervalPartial a B A * b A +
        ∑ n ∈ Finset.Ico B A,
          iwaniecDiscreteIntervalPartial a B n * (b n - b (n + 1)) := by
  induction A, hBA using Nat.le_induction with
  | base =>
      simp [iwaniecDiscreteWeightedInterval,
        iwaniecDiscreteIntervalPartial]
  | succ A hBA ih =>
      rw [iwaniecDiscreteWeightedInterval_succ a b (by omega),
        iwaniecDiscreteIntervalPartial_succ a (by omega),
        Finset.sum_Ico_succ_top hBA, ih]
      ring

theorem iwaniecPrimeReciprocalPoint_interval_eq
    {B A : Nat} (hBA : B ≤ A) :
    iwaniecDiscreteIntervalPartial iwaniecPrimeReciprocalPoint B A =
      iwaniecPrimeReciprocalInterval B A := by
  classical
  unfold iwaniecDiscreteIntervalPartial iwaniecPrimeReciprocalInterval
    iwaniecPrimeReciprocalPoint
  have hsets :
      (Finset.Icc B A).filter Nat.Prime =
        (Nat.primesLE A).filter (fun p => B ≤ p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    aesop
  rw [← hsets]
  simp only [Finset.sum_filter]

theorem iwaniecPrimeReciprocalWeightedInterval_eq_discrete
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      iwaniecDiscreteWeightedInterval iwaniecPrimeReciprocalPoint b B A := by
  classical
  unfold iwaniecPrimeReciprocalWeightedInterval
    iwaniecDiscreteWeightedInterval iwaniecPrimeReciprocalPoint
  have hsets :
      (Nat.primesLE A).filter (fun p => B ≤ p) =
        (Finset.Icc B A).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    aesop
  rw [hsets]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split
  · rfl
  · simp

/-- Prime-specialized interval form of finite Abel summation. -/
theorem iwaniecPrimeReciprocalWeightedInterval_eq_intervalAbel
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      iwaniecPrimeReciprocalInterval B A * b A +
        ∑ n ∈ Finset.Ico B A,
          iwaniecPrimeReciprocalInterval B n * (b n - b (n + 1)) := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_discrete b hBA,
    iwaniecDiscreteIntervalPartialSummation _ _ hBA,
    iwaniecPrimeReciprocalPoint_interval_eq hBA]
  apply congrArg (fun value : Real =>
    iwaniecPrimeReciprocalInterval B A * b A + value)
  apply Finset.sum_congr rfl
  intro n hn
  rw [iwaniecPrimeReciprocalPoint_interval_eq]
  exact (Finset.mem_Ico.mp hn).1

theorem sum_Ico_forwardDifference
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    ∑ n ∈ Finset.Ico B A, (b n - b (n + 1)) = b B - b A := by
  induction A, hBA using Nat.le_induction with
  | base => simp
  | succ A hBA ih =>
      rw [Finset.sum_Ico_succ_top hBA, ih]
      ring

/-- The literal `S(n)` Abel identity displayed in the proof of Iwaniec 1971,
Lemma 13, where `S(n)` is the prime reciprocal cumulative sum. -/
theorem iwaniecPrimeReciprocalWeightedInterval_eq_paperAbel
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      (∑ n ∈ Finset.Ico B A,
        Erdos696.Mertens.primeReciprocalSum n * (b n - b (n + 1))) +
      Erdos696.Mertens.primeReciprocalSum A * b A -
      Erdos696.Mertens.primeReciprocalSum (B - 1) * b B := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_intervalAbel b hBA]
  have hinter : ∀ n ∈ Finset.Ico B A,
      iwaniecPrimeReciprocalInterval B n =
        Erdos696.Mertens.primeReciprocalSum n -
          Erdos696.Mertens.primeReciprocalSum (B - 1) := by
    intro n hn
    exact iwaniecPrimeReciprocalInterval_eq_sub
      (Finset.mem_Ico.mp hn).1
  have hsum :
      (∑ n ∈ Finset.Ico B A,
        iwaniecPrimeReciprocalInterval B n * (b n - b (n + 1))) =
      ∑ n ∈ Finset.Ico B A,
        (Erdos696.Mertens.primeReciprocalSum n -
          Erdos696.Mertens.primeReciprocalSum (B - 1)) *
            (b n - b (n + 1)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hinter n hn]
  rw [hsum]
  rw [iwaniecPrimeReciprocalInterval_eq_sub hBA]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_Ico_forwardDifference b hBA]
  ring

def iwaniecPrimeReciprocalLogMain (n : Nat) : Real :=
  Real.log (Real.log n) + Erdos696.Mertens.meisselMertensConstant

theorem primeReciprocalSum_eq_logMain_add_remainder (n : Nat) :
    Erdos696.Mertens.primeReciprocalSum n =
      iwaniecPrimeReciprocalLogMain n +
        iwaniecPrimeReciprocalRemainder n := by
  unfold iwaniecPrimeReciprocalLogMain iwaniecPrimeReciprocalRemainder
  ring

def iwaniecPrimeReciprocalLogAbel
    (b : Nat → Real) (B A : Nat) : Real :=
  (∑ n ∈ Finset.Ico B A,
    iwaniecPrimeReciprocalLogMain n * (b n - b (n + 1))) +
  iwaniecPrimeReciprocalLogMain A * b A -
  iwaniecPrimeReciprocalLogMain (B - 1) * b B

def iwaniecPrimeReciprocalRemainderAbel
    (b : Nat → Real) (B A : Nat) : Real :=
  (∑ n ∈ Finset.Ico B A,
    iwaniecPrimeReciprocalRemainder n * (b n - b (n + 1))) +
  iwaniecPrimeReciprocalRemainder A * b A -
  iwaniecPrimeReciprocalRemainder (B - 1) * b B

/-- Exact main/remainder split after the paper's finite Abel summation. -/
theorem iwaniecPrimeReciprocalWeightedInterval_eq_logAbel_add_remainderAbel
    (b : Nat → Real) {B A : Nat} (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      iwaniecPrimeReciprocalLogAbel b B A +
        iwaniecPrimeReciprocalRemainderAbel b B A := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_paperAbel b hBA]
  simp_rw [primeReciprocalSum_eq_logMain_add_remainder]
  unfold iwaniecPrimeReciprocalLogAbel
    iwaniecPrimeReciprocalRemainderAbel
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

end

end Erdos1212Kernel
