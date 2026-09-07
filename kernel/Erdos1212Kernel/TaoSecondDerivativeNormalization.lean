import Erdos1212Kernel.TaoSecondDerivativeRate

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

theorem taoSecondDerivative_middle_log_comparison {A N T : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hsmallA : A ^ 2 ≤ Real.sqrt T)
    (hlo : N / (2 * A) ≤ T) : 1 + Real.log N ≤ 5 * Real.log (2 + T) := by
  have hAp : 0 < A := by linarith
  have hsq := Real.sq_sqrt hT.le
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hAq : A ≤ Real.sqrt T := by nlinarith
  have hq1 : 1 ≤ Real.sqrt T := hA2.trans hsmallA
  have hAT : A ≤ T := by nlinarith
  have hlo' := (div_le_iff₀ (show 0 < 2 * A by positivity)).mp hlo
  have hNbound : N ≤ 2 * T ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hAT hT.le]
  have hlog := Real.log_le_log hN hNbound
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) (pow_ne_zero 2 hT.ne'), Real.log_pow] at hlog
  have hlogtwo := Real.log_le_log (by norm_num : (0 : Real) < 2) (by linarith : 2 ≤ 2 + T)
  have hlogT := Real.log_le_log hT (by linarith : T ≤ 2 + T)
  have hL := taoSecondDerivative_log_lower hT.le
  norm_num at hlog
  linarith

theorem taoSecondDerivative_log_root_bound {N T : Real} (hN : 0 < N) (hT : 0 < T)
    (hlog : 1 + Real.log N ≤ 5 * Real.log (2 + T)) :
    Real.sqrt ((1 + Real.log N) / N) ≤ 2 * taoSecondDerivativeRate N T := by
  have hq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hL : 0 ≤ Real.log (2 + T) := by linarith [taoSecondDerivative_log_lower hT.le]
  have hproduct : (Real.log (2 + T) / Real.sqrt T) * (Real.sqrt T / N) = Real.log (2 + T) / N := by
    field_simp
  have hAMGM : 4 * (Real.log (2 + T) / N) ≤ (taoSecondDerivativeRate N T) ^ 2 := by
    unfold taoSecondDerivativeRate
    nlinarith [sq_nonneg (Real.log (2 + T) / Real.sqrt T - Real.sqrt T / N)]
  have hdiv := (div_le_div_iff_of_pos_right hN).2 hlog
  rw [mul_div_assoc] at hdiv
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (by norm_num) (taoSecondDerivative_rate_nonneg hN hT), ?_⟩
  have hterm : 0 ≤ Real.log (2 + T) / N := by positivity
  nlinarith

theorem taoSecondDerivative_first_root_bound {A N T : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) :
    Real.sqrt (4 * A * T / N ^ 2) ≤ 2 * A ^ 2 * Real.sqrt T / N := by
  have hAp : 0 < A := by linarith
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hA4 : A ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 4 * A ^ 4 * T / N ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hN)).2 (by nlinarith [mul_le_mul_of_nonneg_right hA4 hT.le])
    _ = (2 * A ^ 2 * Real.sqrt T / N) ^ 2 := by
      rw [div_pow, show (2 * A ^ 2 * Real.sqrt T) ^ 2 = 4 * A ^ 4 * (Real.sqrt T) ^ 2 by ring,
        Real.sq_sqrt hT.le]

theorem taoSecondDerivative_middle_rate_comparison {A N T C : Real}
    (hA : 1 ≤ A) (hN : 0 < N) (hT : 0 < T) (hC : 1 ≤ C)
    (hsmallA : A ^ 2 ≤ Real.sqrt T) (hlo : N / (2 * A) ≤ T) :
    2 * (Real.sqrt (4 * A * T / N ^ 2) + Real.sqrt ((4 * C * A ^ 4 / N) * (1 + Real.log N))) ≤
      16 * C * A ^ 2 * taoSecondDerivativeRate N T := by
  have hAp : 0 < A := by linarith
  have hCp : 0 < C := by linarith
  have hR := taoSecondDerivative_rate_nonneg hN hT
  have hlog := taoSecondDerivative_middle_log_comparison hA hN hT hsmallA hlo
  have hroot := taoSecondDerivative_log_root_bound hN hT hlog
  have hsqrtC : Real.sqrt C ≤ C := Real.sqrt_le_iff.mpr ⟨hCp.le, by nlinarith⟩
  have hcoeff : (2 * Real.sqrt C * A ^ 2) ^ 2 = 4 * C * A ^ 4 := by
    calc
      _ = 4 * (Real.sqrt C) ^ 2 * A ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hCp.le]
  have hsecond : Real.sqrt ((4 * C * A ^ 4 / N) * (1 + Real.log N)) ≤
      4 * C * A ^ 2 * taoSecondDerivativeRate N T := by
    calc
      _ = Real.sqrt ((2 * Real.sqrt C * A ^ 2) ^ 2 * ((1 + Real.log N) / N)) := by rw [hcoeff]; congr 1 <;> ring
      _ = (2 * Real.sqrt C * A ^ 2) * Real.sqrt ((1 + Real.log N) / N) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      _ ≤ (2 * C * A ^ 2) * (2 * taoSecondDerivativeRate N T) :=
        mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_right hsqrtC (sq_nonneg A)]) hroot (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hfirst : Real.sqrt (4 * A * T / N ^ 2) ≤ 2 * A ^ 2 * taoSecondDerivativeRate N T := by
    have hbase := taoSecondDerivative_first_root_bound hA hN hT
    have hL : 0 ≤ Real.log (2 + T) / Real.sqrt T :=
      div_nonneg (by linarith [taoSecondDerivative_log_lower hT.le]) (Real.sqrt_nonneg _)
    unfold taoSecondDerivativeRate
    calc
      _ ≤ 2 * A ^ 2 * Real.sqrt T / N := hbase
      _ = (2 * A ^ 2) * (Real.sqrt T / N) := by ring
      _ ≤ (2 * A ^ 2) * (Real.log (2 + T) / Real.sqrt T + Real.sqrt T / N) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hL) (by positivity)
  have hP : 0 ≤ A ^ 2 * taoSecondDerivativeRate N T := mul_nonneg (sq_nonneg _) hR
  have hCP := mul_le_mul_of_nonneg_right hC hP
  nlinarith

end

end Erdos1212Kernel
