import Erdos1212Kernel.TaoVdcExponents

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

theorem taoVdc_two_order_le_pow {k : Nat} (hk : 3 ≤ k) : 2 * k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      nlinarith

theorem taoVdc_order_beta_le_half {k : Nat} (hk : 3 ≤ k) :
    (k : Real) * (2 * taoVdcBeta k) ≤ 1 := by
  have hk2 : 2 ≤ k := by omega
  have hden : 0 < (2 : Real) ^ k - 2 := by
    have hpow : (2 : Real) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    norm_num at hpow
    linarith
  have hpow : 2 * (k : Real) + 2 ≤ (2 : Real) ^ k := by exact_mod_cast taoVdc_two_order_le_pow hk
  unfold taoVdcBeta
  calc
    _ = (2 * (k : Real)) / ((2 : Real) ^ k - 2) := by ring
    _ ≤ 1 := (div_le_iff₀ hden).2 (by linarith)

theorem taoVdc_order_beta_ge_alpha {k : Nat} (hk : 3 ≤ k) :
    taoVdcAlpha k ≤ (k : Real) * taoVdcBeta k := by
  by_cases hk3 : k = 3
  · norm_num [hk3, taoVdcAlpha, taoVdcBeta]
  have hk4 : 4 ≤ k := by omega
  have hkR : (4 : Real) ≤ k := by exact_mod_cast hk4
  have hpow : (2 : Real) ^ k = 4 * (2 : Real) ^ (k - 2) := by
    rw [show k = (k - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hden : 0 < (2 : Real) ^ k - 2 := by
    have hh : (2 : Real) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ k)
    norm_num at hh
    linarith
  unfold taoVdcAlpha taoVdcBeta
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : Real) < 2 ^ (k - 2)) hden).2
  have hm := mul_le_mul_of_nonneg_right hkR (show 0 ≤ (2 : Real) ^ (k - 2) by positivity)
  nlinarith

end

end Erdos1212Kernel
