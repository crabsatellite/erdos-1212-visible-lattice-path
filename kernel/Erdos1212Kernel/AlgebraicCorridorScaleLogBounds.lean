import Erdos1212Kernel.AlgebraicCorridorScales
import Erdos1212Kernel.Analytic.BrunTitchmarsh

namespace Erdos1212Kernel.CorridorScale

noncomputable section

/-- The literal rounded radius 2 ceil(ell^11) + ceil(10000 ell^2). -/
theorem radius_bounds {N : ℝ} (hell : 1 ≤ ell N) :
    1 ≤ radius N ∧ (radius N : ℝ) ≤ 10005 * ell N ^ 11 := by
  have hell0 : 0 ≤ ell N := zero_le_one.trans hell
  have hp1 : (1 : ℝ) ≤ ell N ^ 11 := one_le_pow₀ hell
  have hp2 : ell N ^ 2 ≤ ell N ^ 11 := pow_le_pow_right₀ hell (by norm_num)
  have hD : (supportGap N : ℝ) ≤ ell N ^ 11 + 1 :=
    (Nat.ceil_lt_add_one (pow_nonneg hell0 11)).le
  have hB : (band N : ℝ) ≤ 10000 * ell N ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (sq_nonneg (ell N)))).le
  have hD1Real : (1 : ℝ) ≤ supportGap N := hp1.trans (Nat.le_ceil _)
  have hD1 : 1 ≤ supportGap N := by exact_mod_cast hD1Real
  constructor
  · unfold radius
    omega
  · simp only [radius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith

theorem radius_pos {N : ℝ} (hell : 1 ≤ ell N) : 0 < (radius N : ℝ) := by
  exact_mod_cast (show 0 < radius N from (radius_bounds hell).1)

theorem log_radius_le {N : ℝ} (hell : 1 ≤ ell N) (hL : 1 ≤ L N) :
    Real.log (radius N : ℝ) ≤ 10015 * L N := by
  have he0 : 0 < ell N := zero_lt_one.trans_le hell
  have hbound := Real.log_le_log (radius_pos hell) (radius_bounds hell).2
  rw [Real.log_mul (by norm_num : (10005 : ℝ) ≠ 0) (pow_ne_zero _ he0.ne'), Real.log_pow] at hbound
  norm_num only [Nat.cast_ofNat] at hbound
  have hconst := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10005)
  change Real.log (radius N : ℝ) ≤ 10015 * Real.log (ell N)
  change 1 ≤ Real.log (ell N) at hL
  linarith

theorem log_rows_le {N : ℝ} (hL : 1 ≤ L N) :
    Real.log (rows N : ℝ) ≤ 20000002 * L N := by
  obtain ⟨hr, hrUpper⟩ := rows_bounds hL
  have hr0 : (0 : ℝ) < rows N := by exact_mod_cast (show 0 < rows N from hr)
  have hL0 : 0 < L N := zero_lt_one.trans_le hL
  have hb := Real.log_le_log hr0 hrUpper
  rw [Real.log_mul (by norm_num : (20000000 : ℝ) ≠ 0) (pow_ne_zero _ hL0.ne'), Real.log_pow] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20000000)
  have hlogL := Real.log_le_sub_one_of_pos hL0
  linarith

theorem coefficientBound_pos {N : ℝ} (hell : 1 ≤ ell N) : 0 < coefficientBound N := by
  exact mul_pos (by exact_mod_cast Nat.factorial_pos (rows N))
    (pow_pos (radius_pos hell) _)

/-- An explicit witness for the paper's O(L^4) coefficient-log estimate. -/
theorem log_coefficientBound_le {N : ℝ} (hell : 1 ≤ ell N) (hL : 1 ≤ L N) :
    Real.log (coefficientBound N) ≤ 2000000000000000 * L N ^ 4 := by
  obtain ⟨hr, hrUpper⟩ := rows_bounds hL
  have hdUpper := (degree_bounds hL).2
  have hr0 : (0 : ℝ) ≤ rows N := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ degree N := Nat.cast_nonneg _
  have hL0 : 0 ≤ L N := zero_le_one.trans hL
  have hfact := Erdos696.Mertens.log_factorial_le (rows N) hr
  have hrowlog : (rows N : ℝ) * Real.log (rows N : ℝ) ≤
      (20000000 * L N ^ 2) * (20000002 * L N) := by
    exact (mul_le_mul_of_nonneg_left (log_rows_le hL) hr0).trans
      (mul_le_mul_of_nonneg_right hrUpper (mul_nonneg (by norm_num) hL0))
  have hdr : (degree N : ℝ) * (rows N : ℝ) ≤ (5000 * L N) * (20000000 * L N ^ 2) :=
    mul_le_mul hdUpper hrUpper hr0 (mul_nonneg (by norm_num) hL0)
  have hradiuslog : (degree N : ℝ) * (rows N : ℝ) * Real.log (radius N : ℝ) ≤
      ((5000 * L N) * (20000000 * L N ^ 2)) * (10015 * L N) := by
    exact (mul_le_mul_of_nonneg_left (log_radius_le hell hL) (mul_nonneg hd0 hr0)).trans
      (mul_le_mul_of_nonneg_right hdr (mul_nonneg (by norm_num) hL0))
  have hL34 : L N ^ 3 ≤ L N ^ 4 := pow_le_pow_right₀ hL (by norm_num)
  rw [coefficientBound,
    Real.log_mul (by exact_mod_cast (Nat.factorial_ne_zero (rows N)))
      (pow_ne_zero _ (radius_pos hell).ne'), Real.log_pow, Nat.cast_mul]
  calc
    Real.log ((rows N).factorial : ℝ) + (degree N : ℝ) * (rows N : ℝ) * Real.log (radius N : ℝ) ≤
        (20000000 * L N ^ 2) * (20000002 * L N) +
          ((5000 * L N) * (20000000 * L N ^ 2)) * (10015 * L N) :=
      add_le_add (hfact.trans hrowlog) hradiuslog
    _ ≤ 2000000000000000 * L N ^ 4 := by
      nlinarith [pow_nonneg hL0 4]

theorem valueBound_pos {N : ℝ} (hN : 0 < N) (hell : 1 ≤ ell N) : 0 < valueBound N := by
  unfold valueBound
  exact mul_pos (mul_pos (by positivity) (coefficientBound_pos hell))
    (pow_pos (mul_pos (by norm_num) hN) _)

/-- An explicit O(L^4) remainder after the leading d log N term. -/
theorem log_valueBound_le {N : ℝ} (hN : 0 < N) (hell : 1 ≤ ell N) (hL : 1 ≤ L N) :
    Real.log (valueBound N) ≤ (degree N : ℝ) * ell N + 3000000000000000 * L N ^ 4 := by
  have hr0 : (0 : ℝ) ≤ rows N := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ degree N := Nat.cast_nonneg _
  have hr1 : (0 : ℝ) < (rows N : ℝ) + 1 := by positivity
  have hc := coefficientBound_pos hell
  have hcoef := log_coefficientBound_le hell hL
  have hrows := (rows_bounds hL).2
  have hdegree := (degree_bounds hL).2
  have hcard := Real.log_le_sub_one_of_pos hr1
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hdlog : (degree N : ℝ) * Real.log 4 ≤ 15000 * L N := by
    have ht := mul_le_mul_of_nonneg_left hlog4 hd0
    nlinarith
  have hL24 : L N ^ 2 ≤ L N ^ 4 := pow_le_pow_right₀ hL (by norm_num)
  have hL14 : L N ≤ L N ^ 4 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (by norm_num : 1 ≤ 4))
  rw [valueBound, Real.log_mul (mul_ne_zero hr1.ne' hc.ne')
    (pow_ne_zero _ (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hN.ne')),
    Real.log_mul hr1.ne' hc.ne', Real.log_pow,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hN.ne']
  change _ ≤ (degree N : ℝ) * Real.log N + 3000000000000000 * L N ^ 4
  nlinarith [pow_nonneg (zero_le_one.trans hL) 4]

end

end Erdos1212Kernel.CorridorScale
