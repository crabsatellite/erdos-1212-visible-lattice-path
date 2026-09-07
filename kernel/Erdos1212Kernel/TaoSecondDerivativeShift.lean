import Erdos1212Kernel.TaoShiftDifferenceScale
import Mathlib.Algebra.Order.Floor.Semiring

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

def taoSecondDerivativeShift (A T : Real) (N : Nat) : Nat :=
  ⌊(N : Real) ^ 2 / (2 * A * T)⌋₊

theorem taoSecondDerivative_shift_scale_bounds {A T : Real} {N : Nat}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T)
    (hlo : (N : Real) / (2 * A) ≤ T) (hhi : T ≤ (N : Real) ^ 2 / (2 * A)) :
    1 ≤ (N : Real) ^ 2 / (2 * A * T) ∧ (N : Real) ^ 2 / (2 * A * T) ≤ N := by
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have h2A : 0 < 2 * A := by positivity
  have hden : 0 < 2 * A * T := by positivity
  have hlow := (div_le_iff₀ h2A).mp hlo
  have hhigh := (le_div_iff₀ h2A).mp hhi
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_left hlow hNp.le]

theorem taoSecondDerivative_floor_half {X : Real} (hX : 1 ≤ X) :
    X / 2 ≤ (⌊X⌋₊ : Real) ∧ (⌊X⌋₊ : Real) ≤ X := by
  have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).2 hX
  have hfloorR : 1 ≤ (⌊X⌋₊ : Real) := by exact_mod_cast hfloor
  exact ⟨by linarith [Nat.lt_floor_add_one X], Nat.floor_le (by linarith)⟩

/-- Rounding the source H=N^2/(2*A*T) down loses at most a factor two.
The three admissibility facts are proved, not supplied as extra inputs. -/
theorem taoSecondDerivative_shift_admissible {A T : Real} {N : Nat}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T)
    (hlo : (N : Real) / (2 * A) ≤ T) (hhi : T ≤ (N : Real) ^ 2 / (2 * A)) :
    0 < taoSecondDerivativeShift A T N ∧ taoSecondDerivativeShift A T N ≤ N ∧
      (taoSecondDerivativeShift A T N : Real) * T / N ≤ (N : Real) / (2 * A) := by
  obtain ⟨hXlo, hXhi⟩ := taoSecondDerivative_shift_scale_bounds hA hN hT hlo hhi
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hfloor := (taoSecondDerivative_floor_half hXlo).2
  refine ⟨Nat.floor_pos.mpr hXlo, Nat.floor_le_of_le hXhi, ?_⟩
  calc
    _ ≤ ((N : Real) ^ 2 / (2 * A * T)) * T / N :=
      (div_le_div_iff_of_pos_right hNp).2 (mul_le_mul_of_nonneg_right hfloor hT.le)
    _ = (N : Real) / (2 * A) := by field_simp
      <;> ring

theorem taoSecondDerivative_shift_inverse_bound {A T : Real} {N : Nat}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T)
    (hlo : (N : Real) / (2 * A) ≤ T) (hhi : T ≤ (N : Real) ^ 2 / (2 * A)) :
    1 / (taoSecondDerivativeShift A T N : Real) ≤ 4 * A * T / (N : Real) ^ 2 := by
  have hX := (taoSecondDerivative_shift_scale_bounds hA hN hT hlo hhi).1
  have hAp : 0 < A := by linarith
  have hNp : 0 < (N : Real) := by exact_mod_cast hN
  have hhalf := (taoSecondDerivative_floor_half hX).1
  calc
    _ ≤ 1 / (((N : Real) ^ 2 / (2 * A * T)) / 2) :=
      one_div_le_one_div_of_le (by positivity) hhalf
    _ = 4 * A * T / (N : Real) ^ 2 := by field_simp
      <;> ring

end

end Erdos1212Kernel
