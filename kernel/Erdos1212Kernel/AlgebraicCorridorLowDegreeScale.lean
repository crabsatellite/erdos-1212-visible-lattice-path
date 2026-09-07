import Erdos1212Kernel.AlgebraicCorridorScaleLogBounds

namespace Erdos1212Kernel.CorridorScale

noncomputable section

open Filter

def homogeneousNumerator (N : ℝ) : ℝ :=
  2 * ((rows N : ℝ) + 1) * (2 : ℝ) ^ degree N * (height N : ℝ)

theorem log_height_le {N : ℝ} (hL : 1 ≤ L N) :
    Real.log (height N : ℝ) ≤ 2 * L N ^ 6 := by
  have hpow : (1 : ℝ) ≤ L N ^ 6 := one_le_pow₀ hL
  have hexp1 := Real.add_one_le_exp (L N ^ 6)
  have hceil : (height N : ℝ) ≤ Real.exp (L N ^ 6) + 1 :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hh0 : (0 : ℝ) < height N := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have hu : (height N : ℝ) ≤ 2 * Real.exp (L N ^ 6) := by linarith
  have hlog := Real.log_le_log hh0 hu
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem homogeneousNumerator_pos (N : ℝ) : 0 < homogeneousNumerator N := by
  have hh0 : (0 : ℝ) < height N := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  unfold homogeneousNumerator
  positivity

/-- The low-degree numerator in Lemma 6.1 has logarithm O(L^6). -/
theorem log_homogeneousNumerator_le {N : ℝ} (hL : 1 ≤ L N) :
    Real.log (homogeneousNumerator N) ≤ 30000000 * L N ^ 6 := by
  have hrp : (0 : ℝ) < (rows N : ℝ) + 1 := by positivity
  have hhp : (0 : ℝ) < height N := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have ht : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 : ℝ) ^ degree N ≠ 0 := pow_ne_zero _ ht
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hcard := Real.log_le_sub_one_of_pos hrp
  have hheight := log_height_le hL
  have hrows := (rows_bounds hL).2
  have hdegree := (degree_bounds hL).2
  have hd0 : (0 : ℝ) ≤ degree N := Nat.cast_nonneg _
  have hdlog : (degree N : ℝ) * Real.log 2 ≤ (degree N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left htwo hd0
    nlinarith
  have hL16 : L N ≤ L N ^ 6 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (by norm_num : 1 ≤ 6))
  have hL26 : L N ^ 2 ≤ L N ^ 6 := pow_le_pow_right₀ hL (by norm_num)
  have hL06 : (1 : ℝ) ≤ L N ^ 6 := one_le_pow₀ hL
  rw [homogeneousNumerator,
    Real.log_mul (mul_ne_zero (mul_ne_zero ht hrp.ne') hpow) hhp.ne',
    Real.log_mul (mul_ne_zero ht hrp.ne') hpow, Real.log_mul ht hrp.ne', Real.log_pow]
  nlinarith

/-- The displayed low-degree error estimate in Lemma 6.1, with its exact factor 2^(d). -/
theorem eventually_low_degree_error_le :
    ∀ᶠ N : ℝ in atTop, homogeneousNumerator N / N ≤ N ^ ((-1 : ℝ) / 2) := by
  filter_upwards [eventually_large_domain,
    eventually_C_mul_L_pow_lt_ell 60000000 6] with N hdom hsmall
  have hN : 0 < N := zero_lt_one.trans hdom.1
  have hlog : Real.log (homogeneousNumerator N) < ell N / 2 := by
    have hbound := log_homogeneousNumerator_le hdom.2.2
    linarith
  have hnum : homogeneousNumerator N < N ^ ((1 : ℝ) / 2) := by
    have h := (Real.log_lt_iff_lt_exp (homogeneousNumerator_pos N)).mp hlog
    convert h using 1
    rw [Real.rpow_def_of_pos hN]
    congr 1
    unfold ell
    ring
  have hpower : N ^ ((-1 : ℝ) / 2) * N = N ^ ((1 : ℝ) / 2) := by
    calc
      _ = N ^ ((-1 : ℝ) / 2) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ (((-1 : ℝ) / 2) + 1) := (Real.rpow_add hN _ _).symm
      _ = _ := by congr 1; norm_num
  apply (div_le_iff₀ hN).mpr
  rw [hpower]
  exact hnum.le

end

end Erdos1212Kernel.CorridorScale
