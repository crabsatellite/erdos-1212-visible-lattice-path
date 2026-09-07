import Erdos1212Kernel.IwaniecLemma13Natural

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 550000

theorem iwaniecShortWeightedIntegral_bound (b : Real → Real) {B u v M : Real}
    (hB : 2 ≤ B) (hBu : B ≤ u) (huv : u ≤ v)
    (hb : ∀ x ∈ Icc u v, 0 ≤ b x ∧ b x ≤ M) :
    |∫ x in u..v, b x / (x * Real.log x)| ≤ (v - u) * M * iwaniecLogKernel B := by
  have hM : 0 ≤ M := (hb u ⟨le_rfl, huv⟩).1.trans (hb u ⟨le_rfl, huv⟩).2
  have hbound : ∀ x ∈ Set.uIoc u v, ‖b x / (x * Real.log x)‖ ≤ M * iwaniecLogKernel B := by
    intro x hx
    rw [Set.uIoc_of_le huv] at hx
    have hxb : B ≤ x := hBu.trans hx.1.le
    have hxn : 2 ≤ x := hB.trans hxb
    have hbdata := hb x ⟨hx.1.le, hx.2⟩
    have hKpos := (iwaniecLogKernel_pos (by linarith : 1 < x)).le
    have hK := iwaniecLogKernel_antitoneOn_Ici_two hB hxn hxb
    have heq : b x / (x * Real.log x) = b x * iwaniecLogKernel x := by
      unfold iwaniecLogKernel
      ring
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbdata.1 hKpos)]
    exact mul_le_mul hbdata.2 hK hKpos hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at hi
  convert hi using 1 <;> ring

theorem iwaniecWeightedIntegral_intervalIntegrable (b : Real → Real) {u v : Real}
    (hu : 1 < u) (huv : u ≤ v) (hb : MonotoneOn b (Icc u v)) :
    IntervalIntegrable (fun x => b x / (x * Real.log x)) volume u v := by
  simpa only [iwaniecLogKernel, one_div, div_eq_mul_inv, one_mul] using
    iwaniecMonotoneWeightedLogKernel_intervalIntegrable b hu huv hb

theorem iwaniecWeightedPrimeInterval_initial_two (b : Nat → Real) {A : Nat} (hA : 2 ≤ A) :
    iwaniecPrimeReciprocalWeightedInterval b 2 A =
      (1 / 2 : Real) * b 2 + iwaniecPrimeReciprocalWeightedInterval b 3 A := by
  have hset : (Nat.primesLE A).filter (fun p => 2 ≤ p) =
      insert 2 ((Nat.primesLE A).filter (fun p => 3 ≤ p)) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hpA, hp⟩, hp2⟩
      by_cases heq : p = 2
      · exact Or.inl heq
      · exact Or.inr ⟨⟨hpA, hp⟩, by omega⟩
    · rintro (rfl | ⟨⟨hpA, hp⟩, hp3⟩)
      · exact ⟨⟨hA, Nat.prime_two⟩, le_rfl⟩
      · exact ⟨⟨hpA, hp⟩, by omega⟩
  have hnot : 2 ∉ (Nat.primesLE A).filter (fun p => 3 ≤ p) := by simp
  unfold iwaniecPrimeReciprocalWeightedInterval
  rw [hset, Finset.sum_insert hnot]
  norm_num

end

end Erdos1212Kernel
