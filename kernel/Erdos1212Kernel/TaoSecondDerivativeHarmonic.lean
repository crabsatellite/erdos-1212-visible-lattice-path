import Erdos1212Kernel.TaoDifferencedOverlapBound
import Erdos1212Kernel.TaoCorputShortInterval
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

theorem taoSecondDerivative_reciprocal_sum_le_log (H : Nat) :
    (∑ h ∈ Finset.Icc 1 H, 1 / (h : Real)) ≤ 1 + Real.log H := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using
    harmonic_le_one_add_log H

/-- One full differencing step with the actual harmonic sum, before
choosing H or replacing any logarithm by a different parameter. -/
theorem taoSecondDerivative_harmonic_bound (f f' f'' f''' : Real → Real) (a : Int) (M N H : Nat)
    {A T : Real} (hA : 1 ≤ A) (hT : 0 < T) (hMN : M ≤ N) (hH : 0 < H) (hHN : H ≤ N)
    (hsmall : (H : Real) * T / N ≤ (N : Real) / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f'' (f''' t) t)
    (hc''' : ContinuousOn f''' (Set.Icc (a : Real) (a + M)))
    (hsecond : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 2) ≤ |f'' t| ∧ |f'' t| ≤ A * T / (N : Real) ^ 2)
    (hthird : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 3) ≤ |f''' t| ∧ |f''' t| ≤ A * T / (N : Real) ^ 3) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt
        (((2 + 2 * Real.pi) * A ^ 3 * N / (T * H)) * ∑ h ∈ Finset.Icc 1 H, 1 / (h : Real))) := by
  have hN : 0 < N := hH.trans_le hHN
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hHp : 0 < (H : Real) := by exact_mod_cast hH
  have hAp : 0 < A := by linarith
  have hbase := taoCorput_short_exponential_sum_bound (fun n : Int => f (n : Real)) a M N H hMN hH hHN
  have hinner (h : Nat) (hh : h ∈ Finset.Icc 1 H) :
      ‖∑ n ∈ taoCorputOverlap a M h, taoCorputPhase (f (((n + h : Int) : Real)) - f n)‖ / (N : Real) ≤
        (2 + 2 * Real.pi) * A ^ 3 * N / (T * h) := by
    have hh' := Finset.mem_Icc.mp hh
    have hhp : 0 < h := by omega
    have hhR : (h : Real) ≤ H := by exact_mod_cast hh'.2
    have hhsmall : (h : Real) * T / N ≤ (N : Real) / (2 * A) :=
      ((div_le_div_iff_of_pos_right hNp).2 (mul_le_mul_of_nonneg_right hhR hT.le)).trans hsmall
    simpa only [Int.cast_add, Int.cast_natCast] using
      taoDifferenced_overlap_bound f f' f'' f''' a M N h hA hN hT hMN hhp hhsmall hf hf' hf'' hc''' hsecond hthird
  have hsum := Finset.sum_le_sum hinner
  have hsumEq : (∑ h ∈ Finset.Icc 1 H, (2 + 2 * Real.pi) * A ^ 3 * N / (T * h)) =
      ((2 + 2 * Real.pi) * A ^ 3 * N / T) * ∑ h ∈ Finset.Icc 1 H, 1 / (h : Real) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  have hbound := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / (H : Real) by positivity)
  rw [hsumEq] at hbound
  have hproduct : 1 / (H : Real) * (((2 + 2 * Real.pi) * A ^ 3 * N / T) *
      ∑ h ∈ Finset.Icc 1 H, 1 / (h : Real)) =
      ((2 + 2 * Real.pi) * A ^ 3 * N / (T * H)) * ∑ h ∈ Finset.Icc 1 H, 1 / (h : Real) := by ring
  rw [hproduct] at hbound
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (Real.sqrt_le_sqrt hbound)) (by norm_num))

theorem taoSecondDerivative_log_bound (f f' f'' f''' : Real → Real) (a : Int) (M N H : Nat)
    {A T : Real} (hA : 1 ≤ A) (hT : 0 < T) (hMN : M ≤ N) (hH : 0 < H) (hHN : H ≤ N)
    (hsmall : (H : Real) * T / N ≤ (N : Real) / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f'' (f''' t) t)
    (hc''' : ContinuousOn f''' (Set.Icc (a : Real) (a + M)))
    (hsecond : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 2) ≤ |f'' t| ∧ |f'' t| ≤ A * T / (N : Real) ^ 2)
    (hthird : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 3) ≤ |f''' t| ∧ |f''' t| ≤ A * T / (N : Real) ^ 3) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤
      2 * (1 / Real.sqrt (H : Real) + Real.sqrt
        (((2 + 2 * Real.pi) * A ^ 3 * N / (T * H)) * (1 + Real.log H))) := by
  have hbase := taoSecondDerivative_harmonic_bound f f' f'' f''' a M N H hA hT hMN hH hHN hsmall
    hf hf' hf'' hc''' hsecond hthird
  have hAp : 0 < A := by linarith
  have hC : 0 ≤ (2 + 2 * Real.pi) * A ^ 3 * N / (T * H) := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (taoSecondDerivative_reciprocal_sum_le_log H) hC)))
    (by norm_num))

end

end Erdos1212Kernel
