import Erdos1212Kernel.TaoZetaSharpRealCenterRepulsion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

/-- The elementary Euler truncation also gives a uniform log-squared
bound immediately to the right of one, with no singular loss as the
real part approaches one at nonzero height. -/
theorem riemannZeta_norm_le_right_log_sq
    (y α : Real) (hU4 : 4 ≤ taoLogFrequency y)
    (hlog1 : 1 ≤ Real.log (taoLogFrequency y))
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) :
    ‖riemannZeta ((α : Complex) + (y : Complex) * Complex.I)‖ ≤
      (2 : Real) ^ 10 * (Real.log (taoLogFrequency y)) ^ 2 := by
  let U : Real := taoLogFrequency y
  let N : Nat := Nat.ceil (U ^ 2)
  have hUpos : 0 < U := by unfold U; exact taoLogFrequency_pos (by
    intro hy
    subst y
    norm_num [taoLogFrequency] at hU4)
  have hU2nonneg : 0 ≤ U ^ 2 := sq_nonneg U
  have hNlow : U ^ 2 ≤ (N : Real) := by
    unfold N
    exact Nat.le_ceil _
  have hN2 : 2 ≤ N := by
    have hfour : (4 : Real) ≤ U ^ 2 := by nlinarith
    have hN4 : 4 ≤ N := by exact_mod_cast hfour.trans hNlow
    omega
  have hNup : (N : Real) < U ^ 2 + 1 := by
    unfold N
    exact Nat.ceil_lt_add_one hU2nonneg
  have hyne : y ≠ 0 := by
    intro hy
    subst y
    norm_num [U, taoLogFrequency] at hU4
  have hbase := riemannZeta_norm_le_right_strip_harmonic α y hα1 hyne N hN2
  have hlogN : Real.log N ≤ 3 * Real.log U := by
    have hNU : (N : Real) ≤ 2 * U ^ 2 := by
      have hU1 : 1 ≤ U ^ 2 := by nlinarith
      linarith
    calc
      Real.log N ≤ Real.log (2 * U ^ 2) :=
        Real.log_le_log (by positivity : (0 : Real) < N) hNU
      _ = Real.log 2 + 2 * Real.log U := by
        rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) (pow_ne_zero 2 hUpos.ne'),
          Real.log_pow]
        norm_num
      _ ≤ 3 * Real.log U := by
        have hlog2 : Real.log 2 ≤ Real.log U :=
          Real.log_le_log (by norm_num) (by linarith)
        linarith
  have hcorrectionPower : (N : Real) ^ (1 - α) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  have himag : |y| = (2 * Real.pi) * U := by
    unfold U taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hden : (2 * Real.pi) * U ≤
      ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖ := by
    have him : |y| ≤ ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖ := by
      convert Complex.abs_im_le_norm
        (((α : Complex) + (y : Complex) * Complex.I) - 1) using 1 <;> simp
    simpa only [himag] using him
  have hden1 : 1 ≤
      ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖ := by
    have hmul := mul_le_mul_of_nonneg_left hU4
      (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  have hcorrection :
      (N : Real) ^ (1 - α) /
        ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖ ≤ 1 := by
    apply (div_le_one₀ (by positivity :
      0 < ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖)).2
    exact hcorrectionPower.trans hden1
  have hsNorm : ‖(α : Complex) + (y : Complex) * Complex.I‖ ≤ 10 * U := by
    calc
      _ ≤ ‖(α : Complex)‖ + ‖(y : Complex) * Complex.I‖ := norm_add_le _ _
      _ = |α| + |y| := by simp
      _ ≤ 2 + |y| := by
        have hα0 : 0 ≤ α := by linarith
        rw [abs_of_nonneg hα0]
        linarith
      _ ≤ 10 * U := by
        rw [himag]
        have hpi := Real.pi_le_four
        nlinarith
  have hNinv : (N : Real) ^ (-α) ≤ 1 / U ^ 2 := by
    have hNpos : 0 < (N : Real) := by positivity
    have hpow1 : (N : Real) ^ (-α) ≤ (N : Real) ^ (-1 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        (by linarith)
    calc
      _ ≤ (N : Real) ^ (-1 : Real) := hpow1
      _ = 1 / (N : Real) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / U ^ 2 := one_div_le_one_div_of_le (by positivity) hNlow
  have hreciprocal : 1 + 1 / α ≤ 2 := by
    have hinv : 1 / α ≤ 1 := (div_le_one (by linarith : 0 < α)).2 hα1
    linarith
  have herror :
      ‖(α : Complex) + (y : Complex) * Complex.I‖ *
        (N : Real) ^ (-α) * (1 + 1 / α) ≤ 5 := by
    have hUinv : 20 / U ≤ 5 := by
      apply (div_le_iff₀ hUpos).2
      nlinarith
    calc
      _ ≤ (10 * U) * (1 / U ^ 2) * 2 := by
        gcongr
      _ = 20 / U := by field_simp [hUpos.ne']; ring
      _ ≤ 5 := hUinv
  have hrough :
      ‖riemannZeta ((α : Complex) + (y : Complex) * Complex.I)‖ ≤
        7 + 3 * Real.log U := by
    calc
      _ ≤ 1 + Real.log N +
          (N : Real) ^ (1 - α) /
            ‖((α : Complex) + (y : Complex) * Complex.I) - 1‖ +
          ‖(α : Complex) + (y : Complex) * Complex.I‖ *
            (N : Real) ^ (-α) * (1 + 1 / α) := hbase
      _ ≤ 1 + (3 * Real.log U) + 1 + 5 := by linarith
      _ = 7 + 3 * Real.log U := by ring
  have hlogpos : 0 ≤ Real.log U := by linarith
  have hfinal : 7 + 3 * Real.log U ≤
      (2 : Real) ^ 10 * (Real.log U) ^ 2 := by
    have hlogSq : 1 ≤ (Real.log U) ^ 2 := one_le_pow₀ hlog1
    nlinarith
  simpa only [U] using hrough.trans hfinal

theorem riemannZeta_norm_le_two_sided_littlewood_log_sq
    (y α : Real)
    (hcond : TaoLittlewoodFinalFrequencyConditions (taoLogFrequency y))
    (hU4 : 4 ≤ taoLogFrequency y)
    (hlog1 : 1 ≤ Real.log (taoLogFrequency y))
    (hαlower : 1 - taoLittlewoodWidth (taoLogFrequency y)
      (taoLittlewoodR (taoLogFrequency y)) ≤ α)
    (hαupper : α ≤ 2) :
    ‖riemannZeta ((α : Complex) + (y : Complex) * Complex.I)‖ ≤
      (2 : Real) ^ 46 * (Real.log (taoLogFrequency y)) ^ 2 := by
  rcases le_total α 1 with hα1 | hα1
  · exact riemannZeta_norm_le_littlewood_log_sq y α
      hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2 hαlower hα1
  · have hright := riemannZeta_norm_le_right_log_sq y α hU4 hlog1 hα1 hαupper
    exact hright.trans (mul_le_mul_of_nonneg_right (by norm_num)
      (sq_nonneg (Real.log (taoLogFrequency y))))

end

end Erdos1212Kernel
