import Erdos1212Kernel.TaoSecondDerivativeShift

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

def taoSecondDerivativeRate (N T : Real) : Real :=
  Real.log (2 + T) / Real.sqrt T + Real.sqrt T / N

theorem taoSecondDerivative_log_lower {T : Real} (hT : 0 ≤ T) : 1 / 2 ≤ Real.log (2 + T) := by
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
  norm_num at htwo
  exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))

theorem taoSecondDerivative_rate_nonneg {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    0 ≤ taoSecondDerivativeRate N T := by
  have hL : 0 ≤ Real.log (2 + T) := by linarith [taoSecondDerivative_log_lower hT.le]
  unfold taoSecondDerivativeRate
  positivity

theorem taoSecondDerivative_inverse_sqrt_le_rate {N T : Real} (hN : 0 < N) (hT : 0 < T) :
    1 / Real.sqrt T ≤ 2 * taoSecondDerivativeRate N T := by
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hL : 1 ≤ 2 * Real.log (2 + T) := by linarith [taoSecondDerivative_log_lower hT.le]
  have hdiv := (div_le_div_iff_of_pos_right hq).2 hL
  have hterm : 0 ≤ Real.sqrt T / N := by positivity
  unfold taoSecondDerivativeRate
  calc
    _ ≤ 2 * Real.log (2 + T) / Real.sqrt T := hdiv
    _ ≤ 2 * Real.log (2 + T) / Real.sqrt T + 2 * (Real.sqrt T / N) := by linarith
    _ = _ := by ring

theorem taoSecondDerivative_trivial_large_A {A N T : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hbig : Real.sqrt T ≤ A ^ 2) :
    1 ≤ 2 * A ^ 2 * taoSecondDerivativeRate N T := by
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hratio : 1 ≤ A ^ 2 / Real.sqrt T := (le_div_iff₀ hq).2 (by simpa using hbig)
  have hr := mul_le_mul_of_nonneg_left (taoSecondDerivative_inverse_sqrt_le_rate hN hT) (sq_nonneg A)
  apply hratio.trans
  calc
    _ = A ^ 2 * (1 / Real.sqrt T) := by ring
    _ ≤ A ^ 2 * (2 * taoSecondDerivativeRate N T) := hr
    _ = _ := by ring

theorem taoSecondDerivative_small_T_comparison {A N T : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hsmallA : A ^ 2 ≤ Real.sqrt T) :
    A ^ 3 / T ≤ 2 * A ^ 2 * taoSecondDerivativeRate N T := by
  have hAp : 0 < A := by linarith
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hAq : A ≤ Real.sqrt T := by nlinarith
  have hsq := Real.sq_sqrt hT.le
  have hcompare : A ^ 3 / T ≤ A ^ 2 / Real.sqrt T := by
    apply (div_le_div_iff₀ hT hq).2
    have hmul := mul_le_mul_of_nonneg_left hAq (show 0 ≤ A ^ 2 * Real.sqrt T by positivity)
    have he : A ^ 2 * Real.sqrt T * Real.sqrt T = A ^ 2 * T := by
      rw [mul_assoc, ← sq, hsq]
    nlinarith
  have hr := mul_le_mul_of_nonneg_left (taoSecondDerivative_inverse_sqrt_le_rate hN hT) (sq_nonneg A)
  apply hcompare.trans
  calc
    _ = A ^ 2 * (1 / Real.sqrt T) := by ring
    _ ≤ A ^ 2 * (2 * taoSecondDerivativeRate N T) := hr
    _ = _ := by ring

theorem taoSecondDerivative_trivial_large_T {A N T : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hlarge : N ^ 2 / (2 * A) ≤ T) :
    1 ≤ 2 * A ^ 2 * taoSecondDerivativeRate N T := by
  have hAp : 0 < A := by linarith
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hA4 : A ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  have hlarge' := (div_le_iff₀ (show 0 < 2 * A by positivity)).mp hlarge
  have hsq := Real.sq_sqrt hT.le
  have hNbound : N ≤ 2 * A ^ 2 * Real.sqrt T := by
    have hmul := mul_le_mul_of_nonneg_right hA4 hT.le
    have hright : (2 * A ^ 2 * Real.sqrt T) ^ 2 = 4 * A ^ 4 * T := by
      calc
        _ = 4 * A ^ 4 * (Real.sqrt T) ^ 2 := by ring
        _ = _ := by rw [hsq]
    apply (sq_le_sq₀ hN.le (show 0 ≤ 2 * A ^ 2 * Real.sqrt T by positivity)).mp
    rw [hright]
    nlinarith [mul_pos hAp hT]
  have hratio : 1 ≤ 2 * A ^ 2 * Real.sqrt T / N := (le_div_iff₀ hN).2 (by simpa using hNbound)
  have hL : 0 ≤ Real.log (2 + T) / Real.sqrt T :=
    div_nonneg (by linarith [taoSecondDerivative_log_lower hT.le]) hq.le
  unfold taoSecondDerivativeRate
  calc
    _ ≤ 2 * A ^ 2 * Real.sqrt T / N := hratio
    _ = (2 * A ^ 2) * (Real.sqrt T / N) := by ring
    _ ≤ (2 * A ^ 2) * (Real.log (2 + T) / Real.sqrt T + Real.sqrt T / N) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL) (by positivity)

end

end Erdos1212Kernel
