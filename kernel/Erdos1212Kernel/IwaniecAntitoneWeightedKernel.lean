import Erdos1212Kernel.IwaniecMonotoneWeightedKernel
import Erdos1212Kernel.IwaniecAntitoneAbel

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 550000

theorem iwaniecAntitoneWeightedLogKernel_intervalIntegrable (b : Real → Real) {a c : Real}
    (ha : 1 < a) (hac : a ≤ c) (hb : AntitoneOn b (Set.Icc a c)) :
    IntervalIntegrable (fun x => b x * iwaniecLogKernel x) volume a c := by
  have hbi : IntervalIntegrable b volume a c := by
    apply AntitoneOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hac] using hb
  apply hbi.mul_continuousOn
  apply iwaniecLogKernel_continuousOn_Ioi_one.mono
  intro x hx
  rw [Set.uIcc_of_le hac] at hx
  exact ha.trans_le hx.1

theorem iwaniecAntitoneWeightedLogKernel_bounds (b : Real → Real) {a c : Real}
    (ha : 1 < a) (hac : a ≤ c) (hb : AntitoneOn b (Set.Icc a c)) :
    b c * (∫ x in a..c, iwaniecLogKernel x) ≤ iwaniecWeightedLogKernelIntegral b a c ∧
      iwaniecWeightedLogKernelIntegral b a c ≤ b a * (∫ x in a..c, iwaniecLogKernel x) := by
  have hiK := iwaniecLogKernel_intervalIntegrable ha (ha.trans_le hac)
  have hi := iwaniecAntitoneWeightedLogKernel_intervalIntegrable b ha hac hb
  have hlo := intervalIntegral.integral_mono_on hac (hiK.const_mul (b c)) hi (by
    intro x hx
    exact mul_le_mul_of_nonneg_right (hb hx ⟨hac, le_rfl⟩ hx.2) (iwaniecLogKernel_pos (ha.trans_le hx.1)).le)
  have hhi := intervalIntegral.integral_mono_on hac hi (hiK.const_mul (b a)) (by
    intro x hx
    exact mul_le_mul_of_nonneg_right (hb ⟨le_rfl, hac⟩ hx hx.1) (iwaniecLogKernel_pos (ha.trans_le hx.1)).le)
  rw [intervalIntegral.integral_const_mul] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- The decreasing-weight unit defect has the reverse sign. Its cost
is the actual decrement, which will telescope over the original interval. -/
theorem iwaniecAntitoneWeightedLogKernel_unit_error (b : Real → Real) {n : Nat} (hn : 2 ≤ n)
    (hb : AntitoneOn b (Set.Icc (n : Real) ((n + 1 : Nat) : Real))) :
    0 ≤ iwaniecWeightedLogKernelIntegral b n (n + 1 : Nat) -
      b (n + 1 : Nat) * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) ∧
    iwaniecWeightedLogKernelIntegral b n (n + 1 : Nat) -
      b (n + 1 : Nat) * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) ≤
        (b n - b (n + 1 : Nat)) * iwaniecLogKernel n := by
  have hn0 : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hnc : (n : Real) ≤ ((n + 1 : Nat) : Real) := by exact_mod_cast Nat.le_succ n
  have h := iwaniecAntitoneWeightedLogKernel_bounds b hn0 hnc hb
  have hw := iwaniecLogLogIncrement_eq_intervalIntegral (n := n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hw
  rw [← hw] at h
  have hdelta : 0 ≤ b n - b (n + 1 : Nat) :=
    sub_nonneg.mpr (hb ⟨le_rfl, hnc⟩ ⟨hnc, le_rfl⟩ hnc)
  have hK := logLogIncrement_le_iwaniecLogKernel_at_pred (n := n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hK
  have hmul := mul_le_mul_of_nonneg_left hK hdelta
  constructor <;> nlinarith [h.1, h.2]

end

end Erdos1212Kernel
