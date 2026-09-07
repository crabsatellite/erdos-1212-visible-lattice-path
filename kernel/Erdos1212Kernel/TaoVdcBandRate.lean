import Erdos1212Kernel.TaoLogAmplitudeUniform

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1800000

def taoVdcBareFirst (k : Nat) (N T : Real) : Real :=
  (1 / N ^ (taoVdcAlpha k)) * (N ^ k / T) ^ (taoVdcBeta k)

theorem taoVdc_pow_half_gap {k : Nat} (hk : 2 ≤ k) : 2 ^ (k - 1) + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hindex : n + 1 - 1 = n := by omega
      rw [hindex, pow_succ]
      have hp : 2 ≤ 2 ^ n := by
        have : 1 ≤ n := by omega
        exact (pow_le_pow_right₀ (by norm_num) this : 2 ^ 1 ≤ 2 ^ n)
      omega

theorem taoVdc_double_beta_le_alpha {k : Nat} (hk : 2 ≤ k) :
    2 * taoVdcBeta k ≤ taoVdcAlpha k := by
  have hpowNat := taoVdc_pow_half_gap hk
  have hpow : (2 : Real) ^ (k - 1) + 2 ≤ 2 ^ k := by exact_mod_cast hpowNat
  have hkm : k - 1 = (k - 2) + 1 := by omega
  rw [hkm, pow_succ] at hpow
  have hden : 0 < (2 : Real) ^ k - 2 := by
    have hp : 0 < (2 : Real) ^ (k - 2) * 2 := by positivity
    linarith
  have hpowpos : 0 < (2 : Real) ^ (k - 2) := by positivity
  unfold taoVdcBeta taoVdcAlpha
  rw [show 2 * (1 / ((2 : Real) ^ k - 2)) = 2 / ((2 : Real) ^ k - 2) by ring]
  apply (div_le_div_iff₀ hden hpowpos).2
  nlinarith

theorem taoVdc_band_ratio_le (k : Nat) {N T : Real} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hT : 0 < T) (hlow : N ^ (k - 1) ≤ T) :
    taoVdcBareFirst k N T ≤ taoVdcSecond k N T := by
  have hNp : 0 < N := by linarith
  have hb := taoVdcBeta_pos hk
  have hba := taoVdc_double_beta_le_alpha hk
  have hindex : k = (k - 1) + 1 := by omega
  have hratio : N ^ k / T ≤ N := by
    apply (div_le_iff₀ hT).2
    rw [hindex, pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlow hNp.le
  have hq : 1 / N ≤ T / N ^ k := by
    apply (div_le_div_iff₀ hNp (pow_pos hNp k)).2
    rw [one_mul, hindex, pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlow hNp.le
  have hratioPow := Real.rpow_le_rpow (by positivity) hratio hb.le
  have hqPow := Real.rpow_le_rpow (by positivity) hq hb.le
  have hexp : taoVdcBeta k - taoVdcAlpha k ≤ -taoVdcBeta k := by linarith
  have hNexp := Real.rpow_le_rpow_of_exponent_le hN hexp
  unfold taoVdcBareFirst taoVdcSecond
  calc
    _ = N ^ (-taoVdcAlpha k) * (N ^ k / T) ^ (taoVdcBeta k) := by
      rw [one_div, Real.rpow_neg hNp.le]
    _ ≤ N ^ (-taoVdcAlpha k) * N ^ (taoVdcBeta k) :=
      mul_le_mul_of_nonneg_left hratioPow (Real.rpow_nonneg hNp.le _)
    _ = N ^ (taoVdcBeta k - taoVdcAlpha k) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N ^ (-taoVdcBeta k) := hNexp
    _ = (1 / N) ^ (taoVdcBeta k) := by
      rw [Real.div_rpow (by norm_num : (0 : Real) ≤ 1) hNp.le, Real.one_rpow,
        one_div, Real.rpow_neg hNp.le]
    _ ≤ (T / N ^ k) ^ (taoVdcBeta k) := hqPow

theorem taoVdc_log_power_le_four_log (k : Nat) {T : Real} (hT : 0 ≤ T) :
    (Real.log (2 + T)) ^ (taoVdcAlpha k) + 1 ≤ 4 * Real.log (2 + T) := by
  have hL : (1 : Real) / 2 ≤ Real.log (2 + T) := taoSecondDerivative_log_lower hT
  by_cases hL1 : Real.log (2 + T) ≤ 1
  · have hp := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hL1 (taoVdcAlpha_pos k).le
    rw [Real.one_rpow] at hp
    linarith
  · have hLone : 1 ≤ Real.log (2 + T) := (lt_of_not_ge hL1).le
    have hp := Real.rpow_le_rpow_of_exponent_le hLone (taoVdcAlpha_le_one k)
    rw [Real.rpow_one] at hp
    linarith

theorem taoVdcRate_band_bound (k : Nat) {N T : Real} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hT : 0 < T) (hlow : N ^ (k - 1) ≤ T) :
    taoVdcRate k N T ≤ 4 * Real.log (2 + T) * taoVdcSecond k N T := by
  have hbare := taoVdc_band_ratio_le k hk hN hT hlow
  have hLnonneg : 0 ≤ Real.log (2 + T) ^ (taoVdcAlpha k) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hSnonneg : 0 ≤ taoVdcSecond k N T := by
    unfold taoVdcSecond
    positivity
  have hfirst : taoVdcFirst k N T ≤ taoVdcSecond k N T *
      Real.log (2 + T) ^ (taoVdcAlpha k) := by
    unfold taoVdcFirst taoVdcBareFirst at *
    exact mul_le_mul_of_nonneg_right hbare hLnonneg
  rw [taoVdcRate_split]
  calc
    _ ≤ taoVdcSecond k N T * Real.log (2 + T) ^ (taoVdcAlpha k) +
        taoVdcSecond k N T := add_le_add hfirst le_rfl
    _ = taoVdcSecond k N T *
        (Real.log (2 + T) ^ (taoVdcAlpha k) + 1) := by ring
    _ ≤ taoVdcSecond k N T * (4 * Real.log (2 + T)) :=
      mul_le_mul_of_nonneg_left (taoVdc_log_power_le_four_log k hT.le) hSnonneg
    _ = _ := by ring

end

end Erdos1212Kernel
