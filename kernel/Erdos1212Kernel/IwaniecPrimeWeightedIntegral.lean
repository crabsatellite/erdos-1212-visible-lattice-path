import Erdos1212Kernel.IwaniecPrimeWeightedLogMain

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

def iwaniecLogKernel (x : Real) : Real :=
  1 / (x * Real.log x)

theorem iwaniecLogKernel_pos
    {x : Real} (hx : 1 < x) :
    0 < iwaniecLogKernel x := by
  unfold iwaniecLogKernel
  exact one_div_pos.mpr
    (mul_pos (zero_lt_one.trans hx) (Real.log_pos hx))

theorem iwaniecLogKernel_continuousOn_Ioi_one :
    ContinuousOn iwaniecLogKernel (Set.Ioi (1 : Real)) := by
  intro x hx
  have hxOne : 1 < x := hx
  unfold iwaniecLogKernel
  exact (continuousAt_const.div
    (continuousAt_id.mul (Real.continuousAt_log
      (ne_of_gt (zero_lt_one.trans hxOne))))
    (mul_ne_zero (ne_of_gt (zero_lt_one.trans hxOne))
      (ne_of_gt (Real.log_pos hxOne)))).continuousWithinAt

theorem iwaniecLogKernel_antitoneOn_Ici_two :
    AntitoneOn iwaniecLogKernel (Set.Ici (2 : Real)) := by
  intro x hx y hy hxy
  change (2 : Real) ≤ x at hx
  change (2 : Real) ≤ y at hy
  have hxPos : 0 < x := by linarith [hx]
  have hyPos : 0 < y := by linarith [hy]
  have hxLogPos : 0 < Real.log x := Real.log_pos (by linarith [hx])
  have hyLogPos : 0 < Real.log y := Real.log_pos (by linarith [hy])
  have hlog : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxPos hyPos hxy
  have hden : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy hlog hxLogPos.le hyPos.le
  unfold iwaniecLogKernel
  exact one_div_le_one_div_of_le (mul_pos hxPos hxLogPos) hden

theorem iwaniecLogLogIncrement_eq_intervalIntegral
    {n : Nat} (hn : 3 ≤ n) :
    iwaniecLogLogValue n - iwaniecLogLogValue (n - 1) =
      ∫ x in ((n - 1 : Nat) : Real)..(n : Real), iwaniecLogKernel x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
  rotate_right
  use fun x : Real => Real.log (Real.log x)
  · rfl
  · exact fun x hx => by
      have hxLower : 1 < x := by
        have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
          norm_cast
          omega
        have horder : ((n - 1 : Nat) : Real) ≤ (n : Real) := by
          norm_cast
          omega
        rw [Set.uIcc_of_le horder] at hx
        linarith [hx.1]
      unfold iwaniecLogKernel
      convert HasDerivAt.log
        (Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans hxLower)))
        (ne_of_gt (Real.log_pos hxLower)) using 1 <;> ring
  · apply ContinuousOn.intervalIntegrable
    exact continuousOn_of_forall_continuousAt fun x hx => by
      have hxLower : 1 < x := by
        have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
          norm_cast
          omega
        have horder : ((n - 1 : Nat) : Real) ≤ (n : Real) := by
          norm_cast
          omega
        rw [Set.uIcc_of_le horder] at hx
        linarith [hx.1]
      unfold iwaniecLogKernel
      exact continuousAt_const.div
        (continuousAt_id.mul (Real.continuousAt_log
          (ne_of_gt (zero_lt_one.trans hxLower))))
        (mul_ne_zero (ne_of_gt (zero_lt_one.trans hxLower))
          (ne_of_gt (Real.log_pos hxLower)))

/-- The exact logarithmic-increment main term as a sum of unit-interval
integrals.  This is the integral bridge used in Iwaniec 1971, Lemma 13,
before estimating the variation of the weight on each unit interval. -/
theorem iwaniecLogLogIncrementWeightedInterval_eq_sum_unitIntegrals
    (b : Nat → Real) {B A : Nat} (hB : 3 ≤ B) :
    iwaniecLogLogIncrementWeightedInterval b B A =
      ∑ n ∈ Finset.Icc B A,
        b n * (∫ x in ((n - 1 : Nat) : Real)..(n : Real),
          iwaniecLogKernel x) := by
  unfold iwaniecLogLogIncrementWeightedInterval
  apply Finset.sum_congr rfl
  intro n hn
  rw [iwaniecLogLogIncrement_eq_intervalIntegral]
  exact hB.trans (Finset.mem_Icc.mp hn).1

theorem iwaniecPrimeReciprocalWeightedInterval_eq_unitIntegrals_add_remainder
    (b : Nat → Real) {B A : Nat} (hB : 3 ≤ B) (hBA : B ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b B A =
      (∑ n ∈ Finset.Icc B A,
        b n * (∫ x in ((n - 1 : Nat) : Real)..(n : Real),
          iwaniecLogKernel x)) +
        iwaniecPrimeReciprocalRemainderAbel b B A := by
  rw [iwaniecPrimeReciprocalWeightedInterval_eq_logLogIncrement_add_remainder
    b hBA,
    iwaniecLogLogIncrementWeightedInterval_eq_sum_unitIntegrals b hB]

theorem iwaniecLogKernel_at_nat_le_logLogIncrement
    {n : Nat} (hn : 3 ≤ n) :
    iwaniecLogKernel (n : Real) ≤
      iwaniecLogLogValue n - iwaniecLogLogValue (n - 1) := by
  rw [iwaniecLogLogIncrement_eq_intervalIntegral hn]
  have horder : ((n - 1 : Nat) : Real) ≤ (n : Real) := by
    norm_cast
    omega
  have hkernelInt : IntervalIntegrable iwaniecLogKernel volume
      ((n - 1 : Nat) : Real) (n : Real) := by
    apply ContinuousOn.intervalIntegrable
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
      norm_cast
      omega
    exact lt_of_lt_of_le one_lt_two (le_trans hpred hx.1)
  have hconstInt : IntervalIntegrable
      (fun _x : Real => iwaniecLogKernel (n : Real))
      volume ((n - 1 : Nat) : Real) (n : Real) :=
    intervalIntegral.intervalIntegrable_const
  have hmono :
      (∫ _x in ((n - 1 : Nat) : Real)..(n : Real),
          iwaniecLogKernel (n : Real)) ≤
        ∫ x in ((n - 1 : Nat) : Real)..(n : Real), iwaniecLogKernel x := by
    apply intervalIntegral.integral_mono_on horder hconstInt hkernelInt
    intro x hx
    apply iwaniecLogKernel_antitoneOn_Ici_two
    · have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
        norm_cast
        omega
      exact le_trans hpred hx.1
    · show (2 : Real) ≤ (n : Real)
      exact_mod_cast (show 2 ≤ n by omega)
    · exact hx.2
  have hwidth : (n : Real) - ((n - 1 : Nat) : Real) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  simpa [hwidth] using hmono

theorem logLogIncrement_le_iwaniecLogKernel_at_pred
    {n : Nat} (hn : 3 ≤ n) :
    iwaniecLogLogValue n - iwaniecLogLogValue (n - 1) ≤
      iwaniecLogKernel ((n - 1 : Nat) : Real) := by
  rw [iwaniecLogLogIncrement_eq_intervalIntegral hn]
  have horder : ((n - 1 : Nat) : Real) ≤ (n : Real) := by
    norm_cast
    omega
  have hkernelInt : IntervalIntegrable iwaniecLogKernel volume
      ((n - 1 : Nat) : Real) (n : Real) := by
    apply ContinuousOn.intervalIntegrable
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
      norm_cast
      omega
    exact lt_of_lt_of_le one_lt_two (le_trans hpred hx.1)
  have hconstInt : IntervalIntegrable
      (fun _x : Real => iwaniecLogKernel ((n - 1 : Nat) : Real)) volume
      ((n - 1 : Nat) : Real) (n : Real) :=
    intervalIntegral.intervalIntegrable_const
  have hmono :
      (∫ x in ((n - 1 : Nat) : Real)..(n : Real), iwaniecLogKernel x) ≤
        ∫ _x in ((n - 1 : Nat) : Real)..(n : Real),
          iwaniecLogKernel ((n - 1 : Nat) : Real) := by
    apply intervalIntegral.integral_mono_on horder hkernelInt hconstInt
    intro x hx
    apply iwaniecLogKernel_antitoneOn_Ici_two
    · show (2 : Real) ≤ ((n - 1 : Nat) : Real)
      exact_mod_cast (show 2 ≤ n - 1 by omega)
    · have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
        norm_cast
        omega
      exact hpred.trans hx.1
    · exact hx.1
  have hwidth : (n : Real) - ((n - 1 : Nat) : Real) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  simpa [hwidth] using hmono

end

end Erdos1212Kernel
