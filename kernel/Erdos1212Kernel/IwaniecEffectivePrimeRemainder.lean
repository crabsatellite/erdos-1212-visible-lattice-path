import Erdos1212Kernel.TaoMertensUnitError

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 600000

theorem exists_iwaniecPrimeReciprocalRemainder_unit_error_all :
    ∃ C : Real, 0 < C ∧ ∀ N : Nat,
      |iwaniecPrimeReciprocalRemainder N| ≤ C * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  obtain ⟨A, N₀, hA, _hN₀, herr⟩ := exists_iwaniecPrimeReciprocalRemainder_unit_root_log_error
  let E : Nat → Real := fun n => |iwaniecPrimeReciprocalRemainder n| /
    Real.exp (-Real.sqrt (Real.log (n : Real)))
  let S : Real := ∑ n ∈ Finset.range N₀, E n
  let C : Real := A + 1 + S
  have hE : ∀ n, 0 ≤ E n := fun n => div_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => hE n)
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hN : N₀ ≤ N
  · exact (herr N hN).trans (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  · have hNS : E N ≤ S := Finset.single_le_sum (fun n _ => hE n)
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hN))
    have hNC : E N ≤ C := by dsimp [C]; linarith
    exact (div_le_iff₀ (Real.exp_pos _)).mp hNC

theorem iwaniec_sqrt_log_pred_gap {x : Real} (hx : 3 ≤ x) :
    Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x - 1)) + 1 := by
  have hx0 : 0 < x := by linarith
  have hp0 : 0 < x - 1 := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogp : 0 ≤ Real.log (x - 1) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hlog := Real.log_le_log hx0 (show x ≤ 2 * (x - 1) by linarith)
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hp0.ne'] at hlog
  have hsx := Real.sq_sqrt hlogx
  have hsp := Real.sq_sqrt hlogp
  have hpx := Real.sqrt_nonneg (Real.log x)
  have hpp := Real.sqrt_nonneg (Real.log (x - 1))
  nlinarith

theorem iwaniec_unit_decay_le_pred_envelope {x y : Real}
    (hx : 3 ≤ x) (hy : x - 1 ≤ y) :
    Real.exp (-Real.sqrt (Real.log y)) ≤
      Real.exp 1 * Real.exp (-Real.sqrt (Real.log x)) := by
  have hpred := iwaniec_sqrt_log_pred_gap hx
  have hlog := Real.log_le_log (by linarith : 0 < x - 1) hy
  have hsqrt := Real.sqrt_le_sqrt hlog
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end

end Erdos1212Kernel
