import Erdos1212Kernel.TaoRieszUnsmoothing

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem tao_sqrt_log_neighborhood_lower {x y : Real}
    (hx : 4 ≤ x) (hxy : x / 2 ≤ y) :
    Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log y) := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 2 * Real.log 2 ≤ Real.log x := by
    have ht := Real.log_le_log (by norm_num : (0 : Real) < 4) hx
    have heq : Real.log (4 : Real) = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rwa [heq] at ht
  have hlxy := Real.log_le_log (div_pos hx0 (by norm_num)) hxy
  rw [Real.log_div hx0.ne' (by norm_num : (2 : Real) ≠ 0)] at hlxy
  have hsx := Real.sq_sqrt hlx
  have hsy := Real.sq_sqrt hly
  have hpx := Real.sqrt_nonneg (Real.log x)
  have hpy := Real.sqrt_nonneg (Real.log y)
  nlinarith

theorem taoVonMangoldtIntegrated_neighborhood_error
    {a A X₀ x y : Real} (ha : 0 < a) (hA : 0 ≤ A) (hX : 1 ≤ X₀)
    (herr : ∀ z : Real, X₀ ≤ z →
      ‖taoVonMangoldtRieszSum z - (z : Complex) / 2‖ ≤
        A * z * Real.exp (-a * Real.sqrt (Real.log z)))
    (hx : 4 ≤ x) (hXx : 2 * X₀ ≤ x) (hylow : x / 2 ≤ y) (hyhigh : y ≤ 2 * x) :
    |taoVonMangoldtIntegrated y - y ^ 2 / 2| ≤
      4 * A * x ^ 2 * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
  have hyX : X₀ ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hs := tao_sqrt_log_neighborhood_lower hx hylow
  have hexp : Real.exp (-a * Real.sqrt (Real.log y)) ≤
      Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hysq : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  calc
    _ ≤ y * (A * y * Real.exp (-a * Real.sqrt (Real.log y))) :=
      taoVonMangoldtIntegrated_error hy0 (herr y hyX)
    _ = A * y ^ 2 * Real.exp (-a * Real.sqrt (Real.log y)) := by ring
    _ ≤ A * (4 * x ^ 2) * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hysq hA) hexp (by positivity) (by positivity)
    _ = _ := by ring

theorem tao_unsmoothing_step_decay {a x : Real} (ha : 0 < a)
    (hx : Real.exp ((4 * Real.log 2 / a) ^ 2) ≤ x) :
    Real.exp (-(a / 4) * Real.sqrt (Real.log x)) ≤ 1 / 2 := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have ht0 : 0 ≤ 4 * Real.log 2 / a := by
    have hlog := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
    positivity
  have ht := Real.log_le_log (Real.exp_pos _) hx
  rw [Real.log_exp] at ht
  have hs := Real.sqrt_le_sqrt ht
  rw [Real.sqrt_sq ht0] at hs
  have hh : Real.log 2 ≤ (a / 4) * Real.sqrt (Real.log x) := by
    have hh' := mul_le_mul_of_nonneg_left hs (show 0 ≤ a / 4 by positivity)
    have heq : (a / 4) * (4 * Real.log 2 / a) = Real.log 2 := by field_simp
    rwa [heq] at hh'
  calc
    _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]; norm_num

end

end Erdos1212Kernel
