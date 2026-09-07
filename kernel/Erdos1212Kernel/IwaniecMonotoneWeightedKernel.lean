import Erdos1212Kernel.IwaniecWeightedIntegralSandwich

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecLogKernel_intervalIntegrable {a c : Real} (ha : 1 < a) (hc : 1 < c) :
    IntervalIntegrable iwaniecLogKernel volume a c := by
  apply ContinuousOn.intervalIntegrable
  apply iwaniecLogKernel_continuousOn_Ioi_one.mono
  intro x hx
  exact (lt_min ha hc).trans_le hx.1

/-- The source requires monotonicity, not continuity of the weight.
Monotone weights are integrable on the exact closed interval in question. -/
theorem iwaniecMonotoneWeightedLogKernel_intervalIntegrable (b : Real → Real) {a c : Real}
    (ha : 1 < a) (hac : a ≤ c) (hb : MonotoneOn b (Set.Icc a c)) :
    IntervalIntegrable (fun x => b x * iwaniecLogKernel x) volume a c := by
  have hbi : IntervalIntegrable b volume a c := by
    apply MonotoneOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hac] using hb
  apply hbi.mul_continuousOn
  apply iwaniecLogKernel_continuousOn_Ioi_one.mono
  intro x hx
  rw [Set.uIcc_of_le hac] at hx
  exact ha.trans_le hx.1

theorem iwaniecMonotoneWeightedLogKernel_bounds (b : Real → Real) {a c : Real}
    (ha : 1 < a) (hac : a ≤ c) (hb : MonotoneOn b (Set.Icc a c)) :
    b a * (∫ x in a..c, iwaniecLogKernel x) ≤ iwaniecWeightedLogKernelIntegral b a c ∧
      iwaniecWeightedLogKernelIntegral b a c ≤ b c * (∫ x in a..c, iwaniecLogKernel x) := by
  have hiK := iwaniecLogKernel_intervalIntegrable ha (ha.trans_le hac)
  have hi := iwaniecMonotoneWeightedLogKernel_intervalIntegrable b ha hac hb
  have hlo := intervalIntegral.integral_mono_on hac (hiK.const_mul (b a)) hi (by
    intro x hx
    exact mul_le_mul_of_nonneg_right (hb ⟨le_rfl, hac⟩ hx hx.1) (iwaniecLogKernel_pos (ha.trans_le hx.1)).le)
  have hhi := intervalIntegral.integral_mono_on hac hi (hiK.const_mul (b c)) (by
    intro x hx
    exact mul_le_mul_of_nonneg_right (hb hx ⟨hac, le_rfl⟩ hx.2) (iwaniecLogKernel_pos (ha.trans_le hx.1)).le)
  rw [intervalIntegral.integral_const_mul] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- The full local quadrature defect is paid by the actual increment of
the weight, which telescopes; no A+1 endpoint is introduced in the final sum. -/
theorem iwaniecMonotoneWeightedLogKernel_unit_error (b : Real → Real) {n : Nat} (hn : 2 ≤ n)
    (hb : MonotoneOn b (Set.Icc (n : Real) ((n + 1 : Nat) : Real))) :
    0 ≤ b (n + 1 : Nat) * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) -
      iwaniecWeightedLogKernelIntegral b n (n + 1 : Nat) ∧
    b (n + 1 : Nat) * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) -
      iwaniecWeightedLogKernelIntegral b n (n + 1 : Nat) ≤
        (b (n + 1 : Nat) - b n) * iwaniecLogKernel n := by
  have hn0 : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hnc : (n : Real) ≤ ((n + 1 : Nat) : Real) := by exact_mod_cast Nat.le_succ n
  have h := iwaniecMonotoneWeightedLogKernel_bounds b hn0 hnc hb
  have hw := iwaniecLogLogIncrement_eq_intervalIntegral (n := n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hw
  rw [← hw] at h
  have hdelta : 0 ≤ b (n + 1 : Nat) - b n :=
    sub_nonneg.mpr (hb ⟨le_rfl, hnc⟩ ⟨hnc, le_rfl⟩ hnc)
  have hK := logLogIncrement_le_iwaniecLogKernel_at_pred (n := n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hK
  have hmul := mul_le_mul_of_nonneg_left hK hdelta
  constructor <;> nlinarith [h.1, h.2]

end

end Erdos1212Kernel
