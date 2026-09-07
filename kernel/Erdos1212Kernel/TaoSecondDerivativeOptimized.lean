import Erdos1212Kernel.TaoSecondDerivativeHarmonic
import Erdos1212Kernel.TaoSecondDerivativeShift

namespace Erdos1212Kernel

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1600000

theorem taoSecondDerivative_shift_log_coefficient_bound {A T : Real} {N : Nat}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T)
    (hlo : (N : Real) / (2 * A) ≤ T) (hhi : T ≤ (N : Real) ^ 2 / (2 * A)) :
    ((2 + 2 * Real.pi) * A ^ 3 * N / (T * taoSecondDerivativeShift A T N)) *
      (1 + Real.log (taoSecondDerivativeShift A T N)) ≤
        (4 * (2 + 2 * Real.pi) * A ^ 4 / N) * (1 + Real.log N) := by
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  obtain ⟨hH, hHN, _hsmall⟩ := taoSecondDerivative_shift_admissible hA hN hT hlo hhi
  have hHp : 0 < (taoSecondDerivativeShift A T N : Real) := by exact_mod_cast hH
  have hHone : 1 ≤ (taoSecondDerivativeShift A T N : Real) := by exact_mod_cast hH
  have hHNR : (taoSecondDerivativeShift A T N : Real) ≤ N := by exact_mod_cast hHN
  have hlogle : 1 + Real.log (taoSecondDerivativeShift A T N) ≤ 1 + Real.log N :=
    add_le_add le_rfl (Real.log_le_log hHp hHNR)
  have hlognonneg : 0 ≤ 1 + Real.log (taoSecondDerivativeShift A T N) := by
    linarith [Real.log_nonneg hHone]
  have hC : 0 ≤ (2 + 2 * Real.pi) * A ^ 3 * N / T := by positivity
  have hinv := taoSecondDerivative_shift_inverse_bound hA hN hT hlo hhi
  calc
    _ = (((2 + 2 * Real.pi) * A ^ 3 * N / T) * (1 / (taoSecondDerivativeShift A T N : Real))) *
        (1 + Real.log (taoSecondDerivativeShift A T N)) := by ring
    _ ≤ (((2 + 2 * Real.pi) * A ^ 3 * N / T) * (4 * A * T / (N : Real) ^ 2)) *
        (1 + Real.log N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hinv hC) hlogle hlognonneg (by positivity)
    _ = _ := by field_simp
      <;> ring

/-- The source's chosen shift is an actual natural number, and is
eliminated from the bound. This is the nontrivial middle parameter regime;
the small/large-T cases and the final log(T) simplification are separate. -/
theorem taoSecondDerivative_middle_bound (f f' f'' f''' : Real → Real) (a : Int) (M N : Nat)
    {A T : Real} (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hMN : M ≤ N)
    (hlo : (N : Real) / (2 * A) ≤ T) (hhi : T ≤ (N : Real) ^ 2 / (2 * A))
    (hf : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f' (f'' t) t)
    (hf'' : ∀ t ∈ Set.Icc (a : Real) (a + M), HasDerivAt f'' (f''' t) t)
    (hc''' : ContinuousOn f''' (Set.Icc (a : Real) (a + M)))
    (hsecond : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 2) ≤ |f'' t| ∧ |f'' t| ≤ A * T / (N : Real) ^ 2)
    (hthird : ∀ t ∈ Set.Icc (a : Real) (a + M), T / (A * (N : Real) ^ 3) ≤ |f''' t| ∧ |f''' t| ≤ A * T / (N : Real) ^ 3) :
    ‖∑ n ∈ taoCorputInterval a M, taoCorputPhase (f (n : Real))‖ / (N : Real) ≤
      2 * (Real.sqrt (4 * A * T / (N : Real) ^ 2) +
        Real.sqrt ((4 * (2 + 2 * Real.pi) * A ^ 4 / N) * (1 + Real.log N))) := by
  obtain ⟨hH, hHN, hsmall⟩ := taoSecondDerivative_shift_admissible hA hN hT hlo hhi
  have hbase := taoSecondDerivative_log_bound f f' f'' f''' a M N (taoSecondDerivativeShift A T N)
    hA hT hMN hH hHN hsmall hf hf' hf'' hc''' hsecond hthird
  have hroot : 1 / Real.sqrt (taoSecondDerivativeShift A T N : Real) ≤
      Real.sqrt (4 * A * T / (N : Real) ^ 2) := by
    calc
      _ = Real.sqrt (1 / (taoSecondDerivativeShift A T N : Real)) := by
        rw [Real.sqrt_div (by norm_num : (0 : Real) ≤ 1), Real.sqrt_one]
      _ ≤ _ := Real.sqrt_le_sqrt (taoSecondDerivative_shift_inverse_bound hA hN hT hlo hhi)
  exact hbase.trans (mul_le_mul_of_nonneg_left (add_le_add hroot
    (Real.sqrt_le_sqrt (taoSecondDerivative_shift_log_coefficient_bound hA hN hT hlo hhi))) (by norm_num))

end

end Erdos1212Kernel
